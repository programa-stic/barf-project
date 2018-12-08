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
class X86TranslationFlagTests(X86TranslationTestCase):

    def test_clc(self):
        asm = ["clc"]

        ctx_init = self._init_context()

        x86_ctx_out, reil_ctx_out = self._run_code(asm, 0xdeadbeef, ctx_init)

        cmp_result = self._compare_contexts(ctx_init, x86_ctx_out, reil_ctx_out)

        if not cmp_result:
            self._save_failing_context(ctx_init)

        self.assertTrue(cmp_result, self._print_contexts(ctx_init, x86_ctx_out, reil_ctx_out))

    def test_cld(self):
        asm = ["cld"]

        ctx_init = self._init_context()

        x86_ctx_out, reil_ctx_out = self._run_code(asm, 0xdeadbeef, ctx_init)

        cmp_result = self._compare_contexts(ctx_init, x86_ctx_out, reil_ctx_out)

        if not cmp_result:
            self._save_failing_context(ctx_init)

        self.assertTrue(cmp_result, self._print_contexts(ctx_init, x86_ctx_out, reil_ctx_out))

    def test_lahf(self):
        asm = ["lahf"]

        ctx_init = self._init_context()

        # Clear all flags in AH
        ctx_init['rax'] = 0xffffffffffff00ff

        # Set all flags in RFLAGS
        flags_mapper = {
             0: "cf",  # bit 0
             2: "pf",  # bit 2
             4: "af",  # bit 4
             6: "zf",  # bit 6
             7: "sf",  # bit 7
        }

        ctx_init['rflags'] = 0x202

        for bit, _ in flags_mapper.items():
            ctx_init['rflags'] = ctx_init['rflags'] | (2**bit)

        x86_ctx_out, reil_ctx_out = self._run_code(asm, 0xdeadbeef, ctx_init)

        cmp_result = self._compare_contexts(ctx_init, x86_ctx_out, reil_ctx_out)

        if not cmp_result:
            self._save_failing_context(ctx_init)

        self.assertTrue(cmp_result, self._print_contexts(ctx_init, x86_ctx_out, reil_ctx_out))

    def test_popf(self):
        # TODO: Implement.
        pass

    def test_popfd(self):
        # TODO: Implement.
        pass

    def test_popfq(self):
        # TODO: Implement.
        pass

    def test_pushf(self):
        # TODO: Implement.
        pass

    def test_pushfd(self):
        # TODO: Implement.
        pass

    def test_pushfq(self):
        # TODO: Implement.
        pass

    def test_sahf(self):
        asm = ["sahf"]

        ctx_init = self._init_context()

        # Set all flags in AH
        ctx_init['rax'] = 0xff00

        # Clear all flags in RFLAGS
        flags_mapper = {
             0: "cf",  # bit 0
             2: "pf",  # bit 2
             4: "af",  # bit 4
             6: "zf",  # bit 6
             7: "sf",  # bit 7
        }

        for bit, _ in flags_mapper.items():
            ctx_init['rflags'] = ctx_init['rflags'] & ((~2**bit) & 2**64-1)

        x86_ctx_out, reil_ctx_out = self._run_code(asm, 0xdeadbeef, ctx_init)

        cmp_result = self._compare_contexts(ctx_init, x86_ctx_out, reil_ctx_out)

        if not cmp_result:
            self._save_failing_context(ctx_init)

        self.assertTrue(cmp_result, self._print_contexts(ctx_init, x86_ctx_out, reil_ctx_out))

    def test_stc(self):
        asm = ["stc"]

        ctx_init = self._init_context()

        x86_ctx_out, reil_ctx_out = self._run_code(asm, 0xdeadbeef, ctx_init)

        cmp_result = self._compare_contexts(ctx_init, x86_ctx_out, reil_ctx_out)

        if not cmp_result:
            self._save_failing_context(ctx_init)

        self.assertTrue(cmp_result, self._print_contexts(ctx_init, x86_ctx_out, reil_ctx_out))

    def test_std(self):
        # TODO: Implement.
        pass
