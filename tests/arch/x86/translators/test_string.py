# Copyright (c) 2014, Fundacion Dr. Manuel Sadosky
# All rights reserved.

# Redistribution and use in source and binary forms, with or without
# modification, are permitted provided that the following conditions are met:

# 1. Redistributions of source code must retain the above copyright notice, this
# list of conditions and the following disclaimer.

# 2. Redistributions in binary form must reproduce the above copyright notice,
# this list of conditions and the following disclaimer in the documentation
# and/or other materials provided with the distribution.

# THIS SOFTWARE IS PROVIDED BY THE COPYRIGHT HOLDERS AND CONTRIBUTORS "AS IS"
# AND ANY EXPRESS OR IMPLIED WARRANTIES, INCLUDING, BUT NOT LIMITED TO, THE
# IMPLIED WARRANTIES OF MERCHANTABILITY AND FITNESS FOR A PARTICULAR PURPOSE ARE
# DISCLAIMED. IN NO EVENT SHALL THE COPYRIGHT HOLDER OR CONTRIBUTORS BE LIABLE
# FOR ANY DIRECT, INDIRECT, INCIDENTAL, SPECIAL, EXEMPLARY, OR CONSEQUENTIAL
# DAMAGES (INCLUDING, BUT NOT LIMITED TO, PROCUREMENT OF SUBSTITUTE GOODS OR
# SERVICES; LOSS OF USE, DATA, OR PROFITS; OR BUSINESS INTERRUPTION) HOWEVER
# CAUSED AND ON ANY THEORY OF LIABILITY, WHETHER IN CONTRACT, STRICT LIABILITY,
# OR TORT (INCLUDING NEGLIGENCE OR OTHERWISE) ARISING IN ANY WAY OUT OF THE USE
# OF THIS SOFTWARE, EVEN IF ADVISED OF THE POSSIBILITY OF SUCH DAMAGE.

from __future__ import absolute_import

import platform
import unittest

from .x86translator import X86TranslationTestCase


@unittest.skipUnless(platform.machine().lower() == 'x86_64',
                     'Not running on an x86_64 system')
class X86TranslationStringTests(X86TranslationTestCase):

    def test_cmpsb(self):
        # TODO: Implement.
        pass

    def test_cmpsd(self):
        # TODO: Implement.
        pass

    def test_cmpsw(self):
        # TODO: Implement.
        pass

    def test_cmpsq(self):
        # TODO: Implement.
        pass

    def test_lods(self):
        # TODO: Implement.
        pass

    def test_lodsb(self):
        # TODO: Implement.
        pass

    def test_lodsw(self):
        # TODO: Implement.
        pass

    def test_lodsd(self):
        # TODO: Implement.
        pass

    def test_lodsq(self):
        # TODO: Implement.
        pass

    def test_movs(self):
        # TODO: Implement.
        pass

    def test_movsb(self):
        # TODO: Implement.
        pass

    def test_movsw(self):
        # TODO: Implement.
        pass

    def test_movsd(self):
        # TODO: Implement.
        pass

    def test_movsq(self):
        # TODO: Implement.
        pass

    def test_scas(self):
        # TODO: Implement.
        pass

    def test_scasb(self):
        # TODO: Implement.
        pass

    def test_scasw(self):
        # TODO: Implement.
        pass

    def test_scasd(self):
        # TODO: Implement.
        pass

    def test_scasq(self):
        # TODO: Implement.
        pass

    def test_stos(self):
        # TODO: Implement.
        pass

    def test_stosb(self):
        # TODO: Implement.
        pass

    def test_stosw(self):
        # TODO: Implement.
        pass

    def test_stosd(self):
        # TODO: Implement.
        pass

    def test_stosq(self):
        # TODO: Implement.
        pass
