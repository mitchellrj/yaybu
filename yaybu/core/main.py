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
import sys
import optparse
import logging, atexit
import signal

try:
    import wingdbstub
except ImportError:
    pass

from yaybu import util
from yaybu.core.util import version
from yaybu.core import command

usage = """usage: %prog [options] [command]
when run without any commands yaybu drops to a command prompt.
for more information on a command:
    %prog [command] -h
"""

def main():
    parser = optparse.OptionParser(version=version(), usage=usage)
    parser.disable_interspersed_args()
    parser.add_option("-p", "--ypath", default=[], action="append")
    parser.add_option("", "--log-facility", default="2", help="the syslog local facility number to which to write the audit trail")
    parser.add_option("", "--log-level", default="info", help="the minimum log level to write to the audit trail")
    parser.add_option("-d", "--debug", default=False, action="store_true", help="switch all logging to maximum, and write out to the console")
    parser.add_option("-l", "--logfile", default=None, help="The filename to write the audit log to, instead of syslog. Note: the standard console log will still be written to the console.")
    parser.add_option("-v", "--verbose", default=2, action="count", help="Write additional informational messages to the console log. repeat for even more verbosity.")
    parser.add_option("-C", "--config", default=None, action="store", help="Path to main yay config file")
    opts, args = parser.parse_args()

    # we need to revisit how logging is handled
    logging.basicConfig(format="%(asctime)s %(name)s %(levelname)s %(message)s")
    if opts.debug:
        root = logging.getLogger()
        root.setLevel(logging.DEBUG)
        opts.logfile = "-"
        opts.verbose = 2

    if sys.platform == "darwin":
        # CA certs on darwin are in the system keyring - they can be readily accessed with commands like:
        #   security export -k /System/Library/Keychains/SystemCACertificates.keychain -t certs
        # However i'm not sure how libcloud/python can take a stream of certs - it looks like the certs have to exist on disk!!
        # For now, turning cert verification off on Macs.
        import libcloud.security
        libcloud.security.VERIFY_SSL_CERT = False
        libcloud.security.VERIFY_SSL_CERT_STRICT = False


    logging.getLogger("paramiko.transport").setLevel(logging.CRITICAL)

    atexit.register(logging.shutdown)

    com = command.YaybuCmd(config=opts.config, verbose=opts.verbose, ypath=opts.ypath, logfile=opts.logfile)

    pid = None
    if util.is_mac_bundle() and not "GPG_AGENT_INFO" in os.environ:
        path = util.get_bundle_path("Resources/bin/gpg-agent")
        pinentry = util.get_bundle_path("Resources/libexec/pinentry-mac.app/Contents/MacOS/pinentry-mac")

        # Starting gpg-agent on a fresh computer causes us to hang!
        # Precreating .gnupg seems to 'fix' it...
        def ensure_directory(path, mode=0700):
            if not os.path.exists(path):
                os.makedirs(path)
                os.chown(path, mode)
        ensure_directory(os.path.expanduser("~/.gnupg"))
        ensure_directory(os.path.expanduser("~/.gnupg/private-keys-v1.d"))

        import subprocess
        p = subprocess.Popen([path, "--daemon", "--sh", "--pinentry-program", pinentry], stdout=subprocess.PIPE, stderr=subprocess.PIPE)
        stdout, stderr = p.communicate()
        os.environ["GPG_AGENT_INFO"] = GPG_AGENT_INFO = stdout.strip().rsplit(";", 1)[0].split("=", 1)[1]
        sock, pid, umm = GPG_AGENT_INFO.split(":")
        pid = int(pid)

    try:
        if args:
            com.interactive_shell = False
            sys.exit(com.onecmd(" ".join(args)) or 0)
        else:
            com.cmdloop()
    finally:
        if not pid is None:
            os.kill(pid, signal.SIGKILL)
            del os.environ["GPG_AGENT_INFO"]


if __name__ == "__main__":
    main()

