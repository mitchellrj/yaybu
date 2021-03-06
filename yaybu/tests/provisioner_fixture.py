# Copyright 2011-2013 Isotoma Limited
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
import json
import inspect
import pkgutil

try:
    from unittest2 import SkipTest
except ImportError:
    try:
        from unittest import SkipTest
    except ImportError:
        class SkipTest(Exception):
            pass

from fakechroot import FakeChroot

from yaybu.tests.base import TestCase as BaseTestCase
from yaybu.provisioner.transports.remote import stat_result, \
    struct_group, struct_passwd, struct_spwd


class ChangeStillOutstanding(Exception):
    pass


class TransportRecorder(object):

    # path =...
    # id = ...
    # Transport = ...

    def __init__(self, *args, **kwargs):
        self.inner = self.Transport(*args, **kwargs)

    def __getattr__(self, function_name):
        attr = getattr(self.inner, function_name)
        if function_name.startswith("_"):
            return attr

        def _(*args, **kwargs):
            e = None
            try:
                results = attr(*args, **kwargs)
                exception = None
            except KeyError as e:
                results = None
                exception = "KeyError"
            except OSError as e:
                results = None
                exception = "OSError"
            self.results.append((function_name, results, exception))
            if e:
                raise e
            return results
        return _


class TransportPlayback(object):

    # path = ...
    # id = ...

    def __init__(self, *args, **kwargs):
        pass

    def __getattr__(self, function_name):
        f, results, exception = self.results.pop(0)
        assert function_name == f, "'%s' != '%s'" % (function_name, f)

        def _(*args, **kwargs):
            if exception:
                raise {
                    "KeyError": KeyError,
                    "OSError": OSError,
                }[exception]()
            return {
                "stat": lambda x: stat_result(*x),
                "lstat": lambda x: stat_result(*x),
                "getgrall": lambda x: [struct_group(*y) for y in x],
                "getgrnam": lambda x: struct_group(*x),
                "getgrgid": lambda x: struct_group(*x),
                "getpwall": lambda x: [struct_passwd(*y) for y in x],
                "getpwnam": lambda x: struct_passwd(*x),
                "getpwuid": lambda x: struct_passwd(*x),
                "getspall": lambda x: [struct_spwd(*y) for y in x],
                "getspnam": lambda x: struct_spwd(*x),
            }.get(f, lambda x: x)(results)
        return _


class YaybuFakeChroot(FakeChroot):

    """
    I provide a very simple COW userspace environment in which to test configuration

    I am used for some of Yaybu's internal tests.
    """

    Exception = SkipTest


class TestCase(BaseTestCase):

    FakeChroot = YaybuFakeChroot
    location = os.path.join(os.path.dirname(__file__), "..", "..", "..")
    Transport = None

    def setUp(self):
        self.path = inspect.getfile(self.__class__).rsplit(".", 1)[0] + ".json"

        if os.environ.get("YAYBU_RECORD_FIXTURES", "") == "YES":
            self._setUp_for_recording()
        else:
            self._setUp_for_playback()

        self.transport = self.Transport(None, 5, False)

        self.Transport.path = self.path
        self.Transport.id = self.id()

        from yaybu.provisioner import Provision
        Provision.Transport = self.Transport

    def _setUp_for_recording(self):
        self.chroot = self.FakeChroot(self.location)
        self.addCleanup(self.chroot.cleanUp)
        self.chroot.setUp()

        from yaybu.provisioner.transports import FakechrootTransport
        FakechrootTransport.env = self.chroot.get_env()
        FakechrootTransport.chroot_path = self.chroot.chroot_path
        FakechrootTransport.overlay_dir = self.chroot.overlay_dir

        TransportRecorder.results = self.results = []
        TransportRecorder.Transport = FakechrootTransport

        def cleanup():
            existing = {}
            if os.path.exists(self.path):
                existing = json.load(open(self.path))
            existing[self.id()] = self.results
            with open(self.path, "w") as fp:
                json.dump(existing, fp)

        self.addCleanup(cleanup)
        self.Transport = TransportRecorder

    def _setUp_for_playback(self):
        t = self.Transport = TransportPlayback
        payload = pkgutil.get_data("yaybu.tests", os.path.basename(self.path))
        if payload:
            all_results = json.loads(payload)
        else:
            all_results = {}
        t.results = all_results.get(self.id(), [])

    def failUnlessExists(self, path):
        assert self.transport.exists(path), "%s doesnt exist" % path

    def failIfExists(self, path):
        assert not self.transport.exists(path), "%s does exist" % path

    def _config(self, contents):
        path = super(TestCase, self)._config(contents)
        path2 = super(TestCase, self)._config(
            """
            include r"%s"
            main:
                new Provisioner:
                    server:
                        fqdn: fakechroot:///
                    resources: {{ resources }}
            """ % path)
        return path2

    # FIXME: Methods beyond this point are deprecated

    def apply(self, contents, *args):
        return self._up(contents, *args)

    def check_apply(self, contents, *args, **kwargs):
        try:
            return self.up(contents, *args)
        except RuntimeError:
            raise ChangeStillOutstanding()
