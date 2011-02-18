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
import shlex

from yaybu.core import provider
from yaybu.core import error
from yaybu import resources

import logging

logger = logging.getLogger("provider")

class Execute(provider.Provider):

    policies = (resources.system.ExecutePolicy,)

    @classmethod
    def isvalid(self, *args, **kwargs):
        return super(Execute, self).isvalid(*args, **kwargs)

    def apply(self, shell):
        if self.resource.creates is not None \
           and os.path.exists(self.resource.creates):
            logging.info("%r: %s exists, not executing" % (self.resource, self.resource.creates))
            return

        logging.debug("Parsing command %r" % self.resource.command)
        command = shlex.split(self.resource.command.encode("UTF-8"))
        logging.debug("Split into: %r" % command)
        command[0] = shell.locate_file(command[0])
        returncode, stdout, stderr = shell.execute(command)

        expected_returncode = self.resource.returncode or 0

        if expected_returncode != returncode:
            raise error.ExecutionError("%s failed with return code %d" % (self.resource, returncode))
