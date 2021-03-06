# Copyright 2011 Isotoma Limited
#
# Licensed under the Apache License, Version 2.0 (the "License");
# you may not use this file except in compliance with the License.
# You may obtain a copy of the License at
#
#   http://www.apache.org/licenses/LICENSE-2.0
#
# Unless required by applicable law or agreed to in writing, software
# distributed under the License is distributed on an "AS IS" BASIS,
# WITHOUT WARRANTIES OR CONDITIONS OF ANY KIND, either express or implied.
# See the License for the specific language governing permissions and
# limitations under the License.

""" Resources for handling the creation and removal of files. These deal with
both the metadata associated with the file (for example owner and permission)
and the contents of the files themselves. """

import hashlib

from yaybu.provisioner.resource import Resource
from yaybu.core.policy import (Policy,
                               Absent,
                               Present,
                               NAND)

from yaybu.core.argument import (
    Property,
    FullPath,
    String,
    Octal,
    File,
    Dict,
)


class File(Resource):

    """ A provider for this resource will create or amend an existing file to
    the provided specification.

    For example, the following will create the /etc/hosts file based on a static local file::

        File:
          name: /etc/hosts
          owner: root
          group: root
          mode: 644
          static: my_hosts_file

    The following will create a file using a jinja2 template, and will back up
    the old version of the file if necessary::

        File:
          name: /etc/email_addresses
          owner: root
          group: root
          mode: 644
          template: email_addresses.j2
          template_args:
              foo: foo@example.com
              bar: bar@example.com
          backup: /etc/email_addresses.{year}-{month}-{day}

    """

    name = Property(FullPath)
    """The full path to the file this resource represents."""

    owner = Property(String, default="root")
    """A unix username or UID who will own created objects. An owner that
    begins with a digit will be interpreted as a UID, otherwise it will be
    looked up using the python 'pwd' module."""

    group = Property(String, default="root")
    """A unix group or GID who will own created objects. A group that begins
    with a digit will be interpreted as a GID, otherwise it will be looked up
    using the python 'grp' module."""

    mode = Property(Octal, default="644")
    """A mode representation as an octal. This can begin with leading zeros if
    you like, but this is not required. DO NOT use yaml Octal representation
    (0o666), this will NOT work."""

    source = Property(File)
    """A file that will be rendered and applied to this resource. """

    renderer = Property(String, default="guess")
    """ How to render the file. 'static' just copies the file, 'jinja2' applies
    a Jinja2 template and 'json' transforms the args dictionary into a JSON
    file """

    args = Property(Dict, default={})
    """ The arguments passed to the renderer."""

    static = Property(File)
    """ DEPRECATED: A static file to copy into this resource. The file is
    located on the yaybu path, so can be colocated with your recipes."""

    template = Property(File)
    """ DEPRECATED: A jinja2 template, used to generate the contents of this
    resource. The template is located on the yaybu path, so can be colocated
    with your recipes"""

    template_args = Property(Dict, default={})
    """ DEPRECATED: The arguments passed to the template."""

    def hash(self, ctx):
        name = self.name.as_string()
        if not ctx.transport.exists(name):
            return ""
        return hashlib.sha1(ctx.transport.get(name)).hexdigest() + \
            str(ctx.transport.stat(name).st_mtime)


class FileApplyPolicy(Policy):

    """ Create a file and populate it's contents if required.

    You must provide a name.

    You may provide one of template, static, or encrypted to act as a file source.
    """

    resource = File
    name = "apply"
    default = True
    signature = (Present("name"),
                 NAND(Present("template"),
                      Present("static")),
                 )


class FileRemovePolicy(Policy):

    """ Delete a file if it exists. You should only provide the name in this
    case. """

    resource = File
    name = "remove"
    default = False
    signature = (Present("name"),
                 Absent("owner"),
                 Absent("group"),
                 Absent("mode"),
                 Absent("static"),
                 Absent("template"),
                 Absent("template_args"),
                 )


class FileWatchedPolicy(Policy):

    """ Watches a file to see if it changes when a resource a file.

    This policy is used internally and shouldn't be used directly.
    """

    resource = File
    name = "watched"
    default = False
    signature = FileRemovePolicy.signature
