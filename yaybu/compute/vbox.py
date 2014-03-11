# Licensed to the Apache Software Foundation (ASF) under one or more
# contributor license agreements.  See the NOTICE file distributed with
# this work for additional information regarding copyright ownership.
# The ASF licenses this file to You under the Apache License, Version 2.0
# (the "License"); you may not use this file except in compliance with
# the License.  You may obtain a copy of the License at
#
#     http://www.apache.org/licenses/LICENSE-2.0
#
# Unless required by applicable law or agreed to in writing, software
# distributed under the License is distributed on an "AS IS" BASIS,
# WITHOUT WARRANTIES OR CONDITIONS OF ANY KIND, either express or implied.
# See the License for the specific language governing permissions and
# limitations under the License.

# This driver presents a libcloud interface around VirtualBox - the command
# line API for controlling VirtualBox VM's.

# Base image notes:
# 1. Install VirtualBox
# 2. There needs to be a user with a password/key that can get to root
# without sudo requiring a passphrase.

#=========================================================================
# libcloud/common/process.py

import binascii
import datetime
from functools import partial
import json
import logging
import os
from pipes import quote
import shlex
import subprocess
import tempfile
import time
import urllib2
import urlparse
import uuid

from libcloud.common.types import LibcloudError, ProviderError
from libcloud.compute.base import NodeAuthPassword, NodeAuthSSHKey


logger = logging.getLogger("yaybu.parts.compute.vbox")


class VMRunError(LibcloudError):
    pass


class FileAlreadyExistsError(VMRunError):

    def __init__(self):
        self.value = "File or directory already exists"


class Response(object):

    def __init__(self, status, body, error):
        self.status = status
        self.body = body
        self.error = error

        if not self.success():
            raise self.parse_error()

        self.object = self.parse_body()

    def parse_body(self):
        return self.body

    def parse_error(self):
        if self.body == 'Error: The file already exists\n':
            raise FileAlreadyExistsError()
        raise ProviderError(self.body + " " + self.error, self.error)

    def success(self):
        return self.status == 0


class Connection(object):

    responseCls = Response
    log = None

    def __init__(self, secure=True, host=None, port=None, url=None,
                 timeout=None):
        pass

    def connect(self):
        pass

    def request(self, command, data='', capture_output=True):
        if not isinstance(command, list):
            command = shlex.split(command)

        if self.log:
            self.log.write(' '.join(quote(c) for c in command) + '\n')

        if not capture_output:
            stdout, stderr = '', ''
            returncode = self._silent_request(command, data)
        else:
            returncode, stdout, stderr = self._request(command, data)

        if self.log:
            self.log.write("# returncode is %d\n" % returncode)
            self.log.write("# -------- begin stdout ----------\n")
            self.log.write(stdout)
            self.log.write("# -------- begin stderr ----------\n")
            self.log.write(stderr)
            self.log.write("# -------- end ----------\n")

        return self.responseCls(returncode, stdout, stderr)

    def _request(self, command, data):
        stdin = subprocess.PIPE if data else None
        p = subprocess.Popen(
            command,
            stdin=stdin,
            stdout=subprocess.PIPE,
            stderr=subprocess.PIPE)
        stdout, stderr = p.communicate(data)
        return p.returncode, stdout, stderr

    def _silent_request(self, command, data):
        stdin = subprocess.PIPE if data else None
        with open(os.devnull, "w") as null:
            p = subprocess.Popen(
                command, stdin=stdin, stdout=null, stderr=null)
            if data:
                p.stdin.write(data)
                p.stdin.close()
            return p.wait()

#=========================================================================

from xml.etree import ElementTree
import hashlib
import re
import shutil
import sys
import tarfile

from libcloud.compute.base import Node
from libcloud.compute.base import NodeDriver
from libcloud.compute.base import NodeState
from libcloud.compute.types import Provider


# FIXME:
Provider.VBOX = 98


IFCONFIG_IP_PATTERN = (
    'inet addr:\\s*('
    '[1-9][0-9]{0,2}\\.'
    '[1-9][0-9]{0,2}\\.'
    '[1-9][0-9]{0,2}\\.'
    '[1-9][0-9]{0,2}'
    ')'
    )


def get_global_config_directory(self):
    if os.environ.get('VBOX_USER_HOME'):
        return os.environ['VBOX_USER_HOME']
    if os.environ.get('XDG_CONFIG_HOME'):
        return os.path.join(os.environ['XDG_CONFIG_HOME'], '.VirtualBox')
    if sys.platform == "darwin":
        return os.path.expanduser(os.path.join('~', 'Library', 'VirtualBox'))
    return os.path.expanduser(os.path.join('~', '.VirtualBox'))


class VBoxVM(object):

    _name = None
    uuid = None
    _info = None
    _directory = None

    def __init__(self, driver, id_=None, path=None, base_folder=None,
                 name=None):
        self.driver = driver
        if id_ is None and path is not None:
            self._load_info_from_config(path)
        else:
            self.uuid = id_ or self._gen_id()
            self._name = name
            self._directory = os.path.join(base_folder, self.uuid.hex())

    def _gen_id(self):
        return uuid.uuid4()

    def get_info(self, key, default=None):
        if self._info is None:
            info = {}
            info_output = self.driver._action('showvminfo', self.uuid,
                                              '--machinereadable')
            if 'Could not find a registered machine named' in info_output:
                return default

            for line in info_output.split('\n'):
                key, value_str = line.split('=', 1)
                if (len(value_str) >= 2
                    and value_str[0] == '"'
                    and value_str[-1] == '"'):

                    value = value_str[1:-1]
                else:
                    value = int(value_str, 10)
                info[key.lower()] = value

            self._info = info

        return self._info.get(key.lower(), default)

    def _load_info_from_config(self, path):
        tree = ElementTree.parse(path)
        machine = tree.find('Machine')
        uuid_str = machine.get('uuid')
        self.uuid = uuid.UUID(uuid_str)
        self._name = machine.get('name')

    @property
    def instance_config_file_path(self):
        return self.get_info("cfgfile")

    @property
    def directory(self):
        config_file = self.instance_config_file_path
        if config_file is None:
            return self._directory
        return os.path.dirname(config_file)

    def _get_name(self):
        return self.get_info('name')

    def _set_name(self, name):
        self.driver._action('modifyvm', self.uuid, '--name', name)
        self._name = name

    name = property(_get_name, _set_name)

    @property
    def parent(self):
        directory = self.directory
        if directory is not None:
            return os.path.dirname(self.directory)
        return None

    def setup(self):
        """ Create the parent directories if required """
        if self.parent is not None:
            if not os.path.isdir(self.parent):
                os.mkdir(self.parent)


class VBoxDriver(NodeDriver):

    """ This is an implementation of a libcloud driver for VMWare, that is
    used in preference to libvirt because it is better. """

    type = Provider.VBOX
    name = "vbox"
    website = "http://www.virtualbox.org/"
    connectionCls = Connection
    features = {'create_node': ['ssh_key', 'password']}

    def __init__(self, yaybu_root="~/.yaybu", vboxmanage=None):
        super(VBoxDriver, self).__init__(None)
        self.vboxmanage = vboxmanage or self._find_vboxmanage()
        self.machines = VBoxLibrary(root=yaybu_root)

    def ex_start(self, node, timeout=60):
        """
        Start a stopped node.

        @param node: Node which should be used
        @type  node: L{Node}

        @rtype: C{bool}
        """
        with self.yaybu_context.ui.throbber("Start VM"):
            self._action("startvm", node.id, "--type", "headless",
                         capture_output=False)
            node.state = NodeState.RUNNING
        with self.yaybu_context.ui.throbber("Wait for VM to boot completely"):
            start = time.time()
            decorated = self._decorate_node(node)
            while not decorated:
                decorated = self._decorate_node(node)
                time.sleep(1)
                if (time.time() - start) > timeout and decorated is False:
                    # None would indicate that it's not running at all
                    # False may be returned simply because the VM won't tell
                    # us the IP.
                    break

    def _find_vboxmanage(self):
        known_locations = [
            "/Applications/VirtualBox.app/Contents/MacOS/",
            "/usr/bin",
        ]
        for dir_ in known_locations:
            path = os.path.join(dir_, "VBoxManage")
            if os.path.exists(path):
                return path
        raise LibcloudError(
            'VBoxDriver requires \'VBoxManage\' executable to be present on '
            'system')

    def _action(self, *params, **kwargs):
        capture_output = kwargs.get('capture_output', True)
        command = [self.vboxmanage] + list(params)
        logger.debug("Executing %r" % (" ".join(command),))
        return (
            self.connection.request(
                command,
                capture_output=capture_output).body
        )

    def _guest_action(self, target, command, *params):
        credentials = ["--username", target.username,
                       "--password", target.password]
        params = list(params)
        if command.lower() in ('exec', 'execute'):
            params = (
                credentials +
                [
                    '--wait-exit',
                    '--wait-stdout',
                    '--wait-stderr',
                    '--image', params[0],
                    '--'
                ] +
                params[1:]
                )
        else:
            params = params + credentials
        self._action('guestcontrol',
                     command,
                     target.uuid.hex(),
                     *params,
                     capture_output=True)

    def list_images(self, location=None):
        # TODO
        # list the template images from the cache
        # provide friendly names somehow, perhaps deduping on leafname or
        # something
        raise NotImplementedError
        #if not location:
        #    location = self.vm_library
        #locs = []
        #for match in glob.glob(os.path.join(location, "*", "*.vmx")):
        #    locs.append(NodeImage(id=match, name="VMWare Image", driver=self))
        #return locs

    def list_sizes(self, location=None):
        raise NotImplementedError
        #return [
        #    NodeSize("small", "small", 1024, 0, 0, 0, self),
        #    NodeSize("medium", "medium", 4096, 0, 0, 0, self),
        #    NodeSize("large", "large", 8192, 0, 0, 0, self),
        #]

    def list_locations(self):
        return []

    def _list_running(self):
        """ List running virtual machines """
        lines = iter(self._action("list", "runningvms").strip().splitlines())
        lines.next()  # Skip the summary line
        for line in lines:
            if not line.strip():
                continue
            _name, uuid_ = line.split()
            yield uuid.UUID(uuid_)

    def _decorate_node(self, node):
        """ Add ips. Returns True if it successfully decorated it, False if
        it failed and None if the node was not running. """
        if node.state == NodeState.RUNNING:
            result = self._action(
                "guestproperty", "get", node.id, "get",
                "/VirtualBox/GuestInfo/Net/0/V4/IP").strip()
            if result.startswith('Value:'):
                node.public_ips = [result.split(None, 1)[1]]
                return True
            else:
                # Some guest don't return this info. Try the long approach.
                ifconfig_output = self._guest_action('execute', 'ifconfig')
                public_ips = []
                for line in ifconfig_output:
                    m = re.match(IFCONFIG_IP_PATTERN, line)
                    if m and m.group(1)[:4] != '127.':
                        public_ips.append(m.group(1))

                if public_ips:
                    node.public_ips = public_ips
                    return True

            return False
        return None

    def list_nodes(self):
        """ List all of the nodes the driver knows about. """
        nodes = []
        running = list(self._list_running())
        for vm in self.machines.instances(self):
            state = (
                NodeState.RUNNING if vm.uuid in running
                else NodeState.UNKNOWN
                )
            n = Node(vm.uuid, vm.name, state, None, None, self)
            self._decorate_node(n)
            nodes.append(n)
        return nodes

    def _image_smells_remote(self, imageid):
        remote_smells = ('http://', 'https://', 'file://')
        for smell in remote_smells:
            if imageid.startswith(smell):
                return True
        return False

    def apply_auth_password(self, vmrun, username, password):
        """Set the password of the specified username to the provided
           password.
        """

        with self.yaybu_context.ui.throbber("Apply new password credentials"):
            vmrun("execute", "/usr/bin/sudo", "/bin/bash", "-c",
                  "echo '%s:%s'|/usr/sbin/chpasswd" % (username, password))

    def apply_auth_ssh(self, vmrun, username, pubkey):
        """Add the provided ssh public key to the specified user's
           authorised keys.
        """

        # TODO actually find homedir properly
        # TODO find sudo properly
        with self.yaybu_context.ui.throbber("Apply new SSH credentials"):
            homedir = "/home/%s" % username
            tmpfile = tempfile.NamedTemporaryFile(delete=False)
            tmpfile.write(pubkey)
            tmpfile.close()
            try:
                vmrun("createdirectory", "%s/.ssh" % homedir)
            except FileAlreadyExistsError:
                pass
            vmrun("copyto", tmpfile.name,
                  "%s/.ssh/authorized_keys" % homedir)
            vmrun("execute", "/bin/chmod",
                  "0700", "%s/.ssh" % homedir)
            vmrun("execute", "/bin/chmod",
                  "0600", "%s/.ssh/authorized_keys" % homedir)
            os.unlink(tmpfile.name)

    def apply_auth(self, target, auth):
        """Apply the specified authentication credentials to the
           virtual machine.
        """

        vmrun = partial(self._guest_action, target)
        if isinstance(auth, NodeAuthPassword):
            self.apply_auth_password(vmrun, auth.username, auth.password)
        if isinstance(auth, NodeAuthSSHKey):
            self.apply_auth_ssh(vmrun, auth.username, auth.pubkey)

    def _get_and_check_auth(self, auth):
        """
        Helper function for providers supporting L{NodeAuthPassword} or
        L{NodeAuthSSHKey}

        Validates that only a supported object type is passed to the auth
        parameter and raises an exception if it is not.

        If no L{NodeAuthPassword} object is provided but one is expected then a
        password is automatically generated.
        """

        if isinstance(auth, NodeAuthPassword):
            if 'password' in self.features['create_node']:
                return auth
            raise LibcloudError(
                'Password provided as authentication information, but password'
                'not supported', driver=self)

        if isinstance(auth, NodeAuthSSHKey):
            if 'ssh_key' in self.features['create_node']:
                return auth
            raise LibcloudError(
                'SSH Key provided as authentication information, but SSH Key'
                'not supported', driver=self)

        if 'password' in self.features['create_node']:
            value = os.urandom(16)
            value = binascii.hexlify(value).decode('ascii')
            return NodeAuthPassword(value, generated=True)

        if auth:
            raise LibcloudError(
                '"auth" argument provided, but it was not a NodeAuthPassword'
                'or NodeAuthSSHKey object', driver=self)

    def _get_source(self, image):
        """ If the source looks like it is remote then fetch the image and
        extract it into the library directory, otherwise use it directly. """
        ova = False
        try:
            source = uuid.UUID(image.id)
        except (TypeError, ValueError):
            ova = True
            if not self._image_smells_remote(image.id):
                source = 'file://' + os.path.expanduser(image.id)
            source = self.machines.get(image.id, context=self.yaybu_context)
            if not os.path.exists(source):
                raise LibcloudError("Base image %s not found" % source)

        return ova, source

    def _get_target(self):
        """ Create a new target in the instance directory """
        target = VBoxVM(self, base_folder=self.library.instancedir)
        target.setup()
        return target

    def _import(self, image, target):
        """ Try to import a virtual appliance with the VirtualBox commands."""

        with self.yaybu_context.ui.throbber("Import virtual appliance"):
            self._action("import", image.name)

    def _clone(self, source, target):
        """ Try to clone the VM with the VirtualBox commands. We do this in
        the hope that they know what the fastest and most efficient way to
        clone an image is.
        """
        with self.yaybu_context.ui.throbber("Clone template VM"):
            self._action("clonevm", source, '--uuid', target.id, '--register',
                         '--basefolder', target.directory)

    def create_node(self, name, size, image, auth=None, **kwargs):
        """ Create a new VM from a template VM and start it.
        """

        auth = self._get_and_check_auth(auth)
        target = self._get_target()
        ova, source = self._get_source(image)
        if ova:
            self._import(image, target)
        else:
            self._clone(source, target)
        target.name = name
        node = Node(target.uuid, name, NodeState.PENDING, None, None, self)
        node.extra['target', target]

        # If a NodeSize is provided then we can control the amount of RAM the
        # VM has. Number of CPU's would be easy to scale too, but this isn't
        # exposed on a NodeSize

        self.ex_start(node)
        self.apply_auth(target, auth)
        return node

    def reboot_node(self, node):
        logger.debug("Rebooting node %r" % (node.id,))
        self._action("controlvm", node.id, "reset")
        node.state = NodeState.REBOOTING

    def destroy_node(self, node):
        logger.debug("Destroying node %r" % (node.id,))
        self._action("controlvm", node.id, "poweroff")
        self._action("unregister", node.id)
        shutil.rmtree(node.extra['target'].directory)


class VMException(Exception):
    pass


class OVF(object):

    NAMESPACES = {
        'ovf': 'http://schemas.dmtf.org/ovf/envelope/1',
        'rasd': (
            'http://schemas.dmtf.org/wbem/wscim/1/cim-schema/2'
            '/CIM_ResourceAllocationSettingData'),
        'vssd': (
            'http://schemas.dmtf.org/wbem/wscim/1/cim-schema/2'
            '/CIM_VirtualSystemSettingData'),
        'xsi': 'http://www.w3.org/2001/XMLSchema-instance',
        'vbox': 'http://www.virtualbox.org/ovf/machine',
    }
    DEFAULT_NAMESPACE = 'ovf'

    _CAPACITY_CONVERSION = {
        'bytes': 1,
        'kilobytes': 1024,
        'megabytes': 1024 ** 2,
        'gigabytes': 1024 ** 3,
        'words': 2,
        'doublewords': 4,
        'quadwords': 8,
    }

    @classmethod
    def open(cls, path_or_data):
        if hasattr(path_or_data, 'read'):
            data = open(path_or_data, 'r').read()
        else:
            data = path_or_data
        return cls(data)

    def __init__(self, xml):
        self.tree = ElementTree.fromstring(xml)

        self.files = self._parse_files()
        self.properties = self._parse_properties()
        self.disks = self._parse_disks()
        self.networks = self._parse_networks()
        self.systems = self._parse_systems()

    def _name_with_namespace(self, name, namespace=DEFAULT_NAMESPACE):
        ns = self.NAMESPACES.get(namespace.lower())
        return '{{{}}}{}'.format(ns, name)

    def _parse_properties(self, root=None):
        if root is None:
            root = self.tree

        product_section = root.find(_('ProductSection'))
        properties = {}
        _ = self._name_with_namespace
        if product_section:
            for p in product_section.findall(_('Property')):
                # TODO: complete
                p

        return properties

    def _parse_files(self):
        references = self.tree.find(_('References'))
        if not references:
            return {}
        files = {}
        _ = self._name_with_namespace
        for f in references.findall(_('File')):
            files[f.get(_('id'))] = f.get(_('href'))

        return files

    def _parse_disks(self):
        disk_section = self.tree.find(_('DiskSection'))
        disks = {}
        _ = self._name_with_namespace
        for disk in disk_section.findall(_('Disk')):
            uuid_str = disk.get(_('uuid', 'vbox'))
            uuid_ = None
            try:
                uuid_ = uuid.UUID(uuid_str)
            except (TypeError, ValueError):
                pass
            capacity = None
            try:
                capacity_value = long(disk.get(_('capacity')))
            except (TypeError, ValueError):
                # TODO: may happen if using a property
                pass
            else:
                units = disk.get(_('capacityAllocationUnits'),
                                 'bytes').lower()
                units = units.lower()
                if units in self._CAPACITY_CONVERSION:
                    capacity_conversion = self._CAPACITY_CONVERSION[units]
                    capacity = capacity_value * capacity_conversion

            disks[disk.get(_('diskId'))] = {
                'capacity': capacity,
                'file_id': disk.get(_('fileRef')),
                'file_href': self.files.get(disk.get(_('fileRef')), None),
                'format': disk.get(_('format')),
                'uuid': uuid_,
                }
        return disks

    def _parse_networks(self):
        network_section = self.tree.find(_('NetworkSection'))
        networks = {}
        _ = self._name_with_namespace
        for network in network_section.findall(_('Network')):
            networks[network.get(_('name'))] = {}

        return networks

    def _parse_systems(self):
        systems = {}
        _ = self._name_with_namespace
        for system in self.tree.findall(_('VirtualSystem')):
            system_properties = {}
            system_properties.update(self.properties)
            system_properties.update(self._parse_properties(system))
            id_ = system.get(_('id'))
            os = system.find(_('OperatingSystemSection'))
            os_type = os.get(_('id'))
            os_description = os.find(_('Description')).text
            hardware = system.find(_('VirtualHardwareSection'))
            disks = []
            files = []
            uuid_ = None
            name = id_
            vbox_machine = system.find(_('Machine', 'vbox'))
            if vbox_machine:
                name = vbox_machine.get(_('name', 'vbox'))
                uuid_ = uuid.UUID(vbox_machine.get(_('uuid', 'vbox')))

            for item in hardware.findall(_('Item')):
                resource_type = int(item.find(_('ResourceType', 'rasd')).text)
                if resource_type not in (17,):
                    continue
                host_resource = item.find(_('HostResource', 'rasd'))
                if host_resource:
                    resource_id = host_resource.text
                    if resource_id.startswith('/file/'):
                        files.append(resource_id[6:])
                    elif resource_id.startswith('/disk/'):
                        disks.append(resource_id[6:])

            systems[id_] = {
                'os_type': os_type,
                'os': os_description,
                'disks': disks,
                'files': files,
                'name': name,
                'uuid': uuid_,
                }

        return systems

    def as_string(self):
        return ElementTree.tostring(self.tree)


class OVAError(tarfile.TarError):

    pass


class _OVA(tarfile.TarFile):

    @classmethod
    def is_ova(cls, name):
        if not tarfile.is_tarfile(name):
            return False

        try:
            tf = tarfile.open(name, 'r')
        except tarfile.TarError:
            return False
        else:
            for name in tf.getnames():
                if name.lower().endswith('.ovf'):
                    return True
        finally:
            tf.close()

        return False

    def __init__(self, *args, **kwargs):
        tarfile.TarFile.__init__(self, *args, **kwargs)
        self.filename = self.name
        self.metadata = self._parse_metadata()
        if self.get_ovf() is None:
            raise OVAError('Invalid OVA file: missing an OVF file.')

    def _get_ovf_tarinfo(self):
        for tarinfo in self.getmembers():
            if tarinfo.name.lower().endwith('.ovf') and tarinfo.isfile():
                return tarinfo
        return None

    def get_ovf(self):
        tarinfo = self._get_ovf_tarinfo()
        if tarinfo is not None:
            return OVF.open(self.extractfile(tarinfo))

        return None

    def _parse_metadata(self):
        metadata = {}
        for ti in self.getmembers():
            if ti.name == "VM-INFO":
                metadata = json.loads(self.extractfile(ti).read())
                break

        return metadata

    def extract_metadata(self, destdir, context, metadata):
        with context.ui.throbber("Extract virtual appliance metadata"):
            metadata.update(self.metadata)
            self._store_metadata(destdir, metadata)

    def add_metadata(self, username, password):
        """ Create the package from the specified source directory. """
        ovf = self.get_ovf()
        system = next(ovf.systems.values())
        (_fd, filename) = tempfile.mkstemp()
        try:
            with open(filename, 'w') as f:
                f.write(json.dumps(
                           {'username': username,
                            'password': password,
                            'name': system['name'],
                            'uuid': system['uuid'],
                            })
                        )
            self.add(filename, 'VM-INFO')
        finally:
            os.unlink(filename)
        print "Done."


is_ova = _OVA.is_ova
OVA = _OVA.open


class RemoteVBox:

    """ Provides tooling around remote images, specifically hash verification
    and image signing. """

    def __init__(self, location, tempdir, context):
        self.location = location
        self._tempdir = tempdir
        self.context = context

    def __enter__(self):
        """ Fetch an item into the temporary directory from a remote location

        Args:
            location: A url to the compressed box
            context: A context object used for progress reporting

        Returns: the full path to the downloaded package directory

        """
        self.dir = tempfile.mkdtemp(dir=self._tempdir)
        self.image = os.path.join(self.dir, "image")
        with self.context.ui.throbber("Download packed VM") as p:
            self.download(self.image, p.set_current)
        self.metadata = {
            'url': self.location,
            'created': str(datetime.datetime.now()),
            'hash': self.hash
        }
        return self

    def __exit__(self, exc_type, exc_value, traceback):
        shutil.rmtree(self.dir)

    def get_hash(self):
        """ Try methods in order until one returns something other than None.
        This is the MD5. """
        methods = (self._hash_headers,
                   self._hash_detached)
        for m in methods:
            md5 = m()
            if md5 is not None:
                return md5

    def _hash_headers(self):
        """ Fetch the MD5 hash from the first "Content-MD5" header if
        present. """
        rq = urllib2.Request(self.location)
        rq.get_method = lambda: 'HEAD'
        rs = urllib2.urlopen(rq)
        headers = rs.info().getheaders("Content-MD5")
        if headers:
            md5 = headers[0]
        else:
            md5 = None
        return md5

    def _hash_detached(self):
        """ Fetch the hash from a detached text file alongside the original
        """
        md5_location = self.location + ".md5"
        try:
            md5 = urllib2.urlopen(md5_location).read()
        except urllib2.URLError:
            md5 = None
        return md5

    def download(self, dst, progress, batch_size=8192):
        """ Download the file and calculate its hash """
        self.hash = self.get_hash()
        h = hashlib.md5()
        downloaded = 0
        percent = 0
        fout = open(dst, "w")
        fin = urllib2.urlopen(self.location)
        content_length = int(fin.headers['content-length'])
        while True:
            data = fin.read(batch_size)
            if not data:
                break
            h.update(data)
            fout.write(data)
            downloaded += len(data)
            percent = int(float(downloaded) / content_length * 100)
            progress(percent)
        fin.close()
        fout.close()
        if self.hash is None:
            self.hash = h.hexdigest()
        else:
            if h.hexdigest() != self.hash:
                raise ValueError(
                    "Wrong hash. Calculated %r != Correct %r" %
                    (h.hexdigest(), self.hash)
                    )


class VBoxLibrary(object):

    """ A library of virtual machines, and a mechanism for adding packaged
    virtual machines to the library from local or remote locations.

    Some of these VMs are "templates" and not intended to be run from their
    existing location. Some are copies of the templates and are in use.

    The directory structure resembles:

    ~/.yaybu/vbox/
        /instances/
            /<UUID>/
                <name>.vbox
                <virtual disk files>
        /library/
            /<UUID>/
                image/
                    VM-INFO
                    <ova files>
        /temp/
            <UUID>/
                <files created during download and extraction>

    """

    # This is the class that represents the images
    ImageClass = OVA

    def __init__(self, root="~/.yaybu"):
        self.root = os.path.expanduser(root)
        self.library = {}
        # a set of images that are only cloned
        self.librarydir = os.path.join(self.root, "vbox", "library")
        # instances that may be started and running
        self.instancedir = os.path.join(self.root, "vbox", "instances")
        # A temporary directory, we put it here so we know we have enough room
        self.tempdir = os.path.join(self.root, "vbox", "temp")
        self.setupdirs()
        self.scan()

    def setupdirs(self):
        """ Create directories if required """
        for d in self.librarydir, self.instancedir, self.tempdir:
            if not os.path.exists(d):
                os.makedirs(d)

    def scan(self):
        """ Scan the library and populate self.library """
        for item in os.listdir(self.librarydir):
            ip = os.path.join(self.librarydir, item)
            if os.path.isdir(ip):
                mp = os.path.join(ip, "VM-INFO")
                if os.path.exists(mp):
                    md = json.load(open(mp))
                    self.library[md['url']] = item
                    if md.get('uuid'):
                        self.library[uuid.UUID(md['uuid'])] = item

    def guess_name(self, uri):
        """ Use the name of the file with the extension stripped off """
        path = urlparse.urlparse(uri).path
        leaf = path.split("/")[-1]
        if not leaf:
            raise VMException("Cannot guess name for %r" % (uri,))
        return leaf.rsplit(".", 1)[0]

    def _locate_image(self, path):
        for f in os.listdir(path):
            if f.endswith('.ova') or f.endswith('.ovf'):
                return os.path.join(path, f)

    def fetch(self, uri, name, context):
        """ Fetch the URI """
        if name is None:
            name = self.guess_name(uri)
        destdir = os.path.join(self.librarydir, name)
        if os.path.exists(destdir):
            vminfo = os.path.join(destdir, 'VM-INFO')
            origuri = json.load(open(vminfo))['url']
            raise VMException((
                "Requested to download %s from %s but already downloaded from "
                "%s") %
                (name, uri, origuri)
                )
        with RemoteVBox(uri, self.tempdir, context) as box:
            tmp = tempfile.mkdtemp(dir=self.tempdir)
            ova = self.ImageClass(box.image)
            ova.extract_metadata(tmp, context, box.metadata)
            os.rename(tmp, destdir)
            self.library[uri] = name

    def get(self, uri, context=None, name=None):
        """ Fetches the specified uri into the cache and then extracts
        it into the library.  If name is None then a name is made up.

        Arguments:
            name: the suggested name for the downloaded VM. Note that
                  if the VM is already present it may have a different
                  name, but will be used anyway.


        """
        if not uri in self.library:
            self.fetch(uri, name, context)
        name = self.library[uri]
        return self._locate_image(os.path.join(self.librarydir, name))

    def instances(self, driver):
        """ Return a generator of VBoxVM objects. """
        for i in os.listdir(self.instancedir):
            yield VBoxVM(driver, uuid.UUID(i))
