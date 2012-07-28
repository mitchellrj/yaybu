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

from yaybu.core.protocol.server import Server, HttpResource, StaticResource, AboutResource
from yaybu.core.protocol.file import FileResource, EncryptedResource
from yaybu.core.protocol.changelog import ChangeLogResource

from yaybu.core.runner import Runner
from yaybu.core.runcontext import RunContext
from yaybu.core import error


import yay

import ssh
import socket
import logging
import time
import subprocess
import pickle
import sys
import os


logger = logging.getLogger("yaybu.core.remote")

class RemoteRunner(Runner):
    
    connection_attempts = 10
    missing_host_key_policy = ssh.AutoAddPolicy()
    
    def __init__(self, hostname, key=None, username="ubuntu"):
        self.hostname = hostname
        self.key = key
        self.username = username
        
    def connect(self):
        client = ssh.SSHClient()
        client.set_missing_host_key_policy(self.missing_host_key_policy)
        for tries in range(self.connection_attempts):
            try:
                if self.key is not None:
                    client.connect(hostname=self.hostname,
                                   username=self.username,
                                   pkey=self.key,
                                   look_for_keys=False)
                else:
                    client.connect(hostname=self.hostname,
                                   username=self.username,
                                   look_for_keys=True)
                break

            except ssh.PasswordRequiredException:
                raise error.ConnectionError("Unable to authenticate with remote server")

            except (socket.error, EOFError):
                logger.warning("connection refused. retrying.")
                time.sleep(1)
        else:
            raise error.ConnectionError("Connection refused %d times, giving up." % self.connection_attempts)
        return client
        
    def install_yaybu(self):
        client = self.connect()
        try:
            self.execute(client, "sudo apt-get -y update")
            self.execute(client, "sudo apt-get -y safe-upgrade")
            self.execute(client, "sudo apt-get -y install python-setuptools")
            self.execute(client, "sudo easy_install Yaybu")
        finally:
            client.close()
        
    def serve(self, ctx):
        command = self.get_yaybu_command(ctx)
        client = self.connect()
        stdin, stdout, stderr = client.exec_command(command)
        self.get_server(ctx, stdin, stdout).serve_forever()
        ## TODO: work out how to get exit status - probably SSHException raised
        return 0

    def execute(self, client, command):
        stdin, stdout, stderr = client.exec_command(command)
        stdin.close()
        for l in stdout:
            logger.debug(l.strip())
            
    def get_yaybu_command(self, ctx):
        command = ["yaybu", "--remote"]

        if ctx.user:
            command.extend(["--user", ctx.user])

        if ctx.simulate:
            command.append("-s")

        if ctx.verbose:
            command.extend(list("-v" for x in range(ctx.verbose)))

        if ctx.resume:
            command.append("--resume")

        if ctx.no_resume:
            command.append("--no-resume")

        command.append("-")
        return " ".join(command)

    def get_server(self, ctx, stdin, stdout):
        root = HttpResource()
        root.put_child("config", StaticResource(pickle.dumps(ctx.get_config().get())))
        root.put_child("files", FileResource())
        root.put_child("encrypted", EncryptedResource())
        root.put_child("changelog", ChangeLogResource())
        root.put_child("about", AboutResource())

        return Server(ctx, root, stdout, stdin)

    def run(self, ctx):
        # Get a bundle straight away - allows us to validate the bundle before
        # sending it remotely.
        try:
            bundle = ctx.get_bundle()
        except error.Error as e:
            ctx.changelog.error(str(e))
            return e.returncode

        try:
            return self.serve(ctx)
        except error.Error as e:
            print >>sys.stderr, "Error: %s" % str(e)
            return e.returncode

