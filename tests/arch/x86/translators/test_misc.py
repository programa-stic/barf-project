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
class X86TranslationMiscTests(X86TranslationTestCase):

    # "Enter and Leave Instructions"
    # ============================================================================ #
    def test_leave(self):
        # TODO: Implement.
        pass

    # "Miscellaneous Instructions"
    # ============================================================================ #
    def test_hlt(self):
        # TODO: Implement.
        pass

    def test_lea(self):
        asm = ["lea eax, [ebx + 0x100]"]

        ctx_init = self._init_context()

        x86_ctx_out, reil_ctx_out = self._run_code(asm, 0xdeadbeef, ctx_init)

        cmp_result = self._compare_contexts(ctx_init, x86_ctx_out, reil_ctx_out)

        if not cmp_result:
            self._save_failing_context(ctx_init)

        self.assertTrue(cmp_result, self._print_contexts(ctx_init, x86_ctx_out, reil_ctx_out))

    def test_nop(self):
        asm = ["nop"]

        ctx_init = self._init_context()

        x86_ctx_out, reil_ctx_out = self._run_code(asm, 0xdeadbeef, ctx_init)

        cmp_result = self._compare_contexts(ctx_init, x86_ctx_out, reil_ctx_out)

        if not cmp_result:
            self._save_failing_context(ctx_init)

        self.assertTrue(cmp_result, self._print_contexts(ctx_init, x86_ctx_out, reil_ctx_out))
