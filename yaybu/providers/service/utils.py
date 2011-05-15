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

import os

from yaybu.core import error


class _ServiceMixin(object):

    def status(self, context):
        if not self.resource.pidfile:
            return "unknown"

        pid = open(self.resource.pidfile).read().strip()
        try:
            pid = int(pid)
        except:
            return "unknown"

        try:
            os.kill(pid, 0)
            return "running"
        except OSError, e:
            return "not-running"

    def do(self, context, action):
        print self.get_command(action)
        returncode, stdout, stderr = context.shell.execute(self.get_command(action), exceptions=False)

        if returncode != 0:
            raise error.CommandError("%s failed with return code %d" % (" ".join(action), returncode))



class _Start(object):

    def apply(self, context):
        if self.status(context) == "running":
            return False

        self.do(context, "start")

        return True


class _Stop(object):

    def apply(self, context):
        if self.status(context) == "not-running":
            return False

        self.do(context, "stop")

        return True


class _Restart(object):

    def apply(self, context):
        if self.status(context) == "not-running":
            self.do(context, "start")
            return True

        if self.resource.supports_restart:
            self.do(context, "restart")
        else:
            self.do(context, "stop")
            self.do(context, "start")

        return True


