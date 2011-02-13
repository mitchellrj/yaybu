
import os
import stat
import pwd
import grp
import difflib
import logging

from jinja2 import Template

from yaybu.core import abstract
from yaybu.resource import filesystem as resource

simlog = logging.getLogger("simulation")

class File(abstract.Provider):

    @classmethod
    def isvalid(self, *args, **kwargs):
        return super(File, self).isvalid(*args, **kwargs)

    def action_create(self, shell):
        name = self.resource.name
        exists = False
        uid = None
        gid=None
        mode=None
        if os.path.exists(name):
            exists = True
            st = os.stat(name)
            uid = st.st_uid
            gid = st.st_gid
            mode = st.st_mode
            if mode > 32767:
                mode = mode - 32768
        if self.resource.template is None:
            if not exists:
                shell.execute(["touch", name])
        else:
            template = Template(open(self.resource.template).read())
            output = template.render(**self.resource.template_args)
            if exists:
                current = open(self.resource.name).read()
                if output != current:
                    if shell.simulate:
                        simlog.info("Updating file '%s':" % self.resource.name)
                        diff = "".join(difflib.context_diff(current.splitlines(1), output.splitlines(1)))
                        for l in diff.splitlines():
                            simlog.info("    %s" % l)
                    else:
                        open(self.resource.name).write(output)
            else:
                if shell.simulate:
                    simlog.info("Writing new file '%s':" % self.resource.name)
                    for l in output.splitlines():
                        simlog.info("    %s" % l)
                else:
                    open(self.resource.name).write(output)
        if self.resource.owner is not None:
            owner = pwd.getpwnam(self.resource.owner)
            if owner.pw_uid != uid:
                shell.execute(["chown", self.resource.owner, name])
        if self.resource.group is not None:
            group = grp.getgrnam(self.resource.group)
            if group.gr_gid != gid:
                shell.execute(["chgrp", self.resource.group, name])
        if self.resource.mode is not None:
            if mode != self.resource.mode:
                shell.execute(["chmod", "%o" % self.resource.mode, name])

resource.File.providers.append(File)
