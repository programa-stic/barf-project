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
class X86TranslationArithmeticTests(X86TranslationTestCase):

    def test_adc(self):
        asm = ["adc eax, ebx"]

        ctx_init = self._init_context()

        x86_ctx_out, reil_ctx_out = self._run_code(asm, 0xdeadbeef, ctx_init)

        cmp_result = self._compare_contexts(ctx_init, x86_ctx_out, reil_ctx_out)

        if not cmp_result:
            self._save_failing_context(ctx_init)

        self.assertTrue(cmp_result, self._print_contexts(ctx_init, x86_ctx_out, reil_ctx_out))

    def test_add(self):
        asm = ["add eax, ebx"]

        ctx_init = self._init_context()

        x86_ctx_out, reil_ctx_out = self._run_code(asm, 0xdeadbeef, ctx_init)

        cmp_result = self._compare_contexts(ctx_init, x86_ctx_out, reil_ctx_out)

        if not cmp_result:
            self._save_failing_context(ctx_init)

        self.assertTrue(cmp_result, self._print_contexts(ctx_init, x86_ctx_out, reil_ctx_out))

    def test_cmp(self):
        asm = ["cmp eax, ebx"]

        ctx_init = self._init_context()

        x86_ctx_out, reil_ctx_out = self._run_code(asm, 0xdeadbeef, ctx_init)

        cmp_result = self._compare_contexts(ctx_init, x86_ctx_out, reil_ctx_out)

        if not cmp_result:
            self._save_failing_context(ctx_init)

        self.assertTrue(cmp_result, self._print_contexts(ctx_init, x86_ctx_out, reil_ctx_out))

    def test_dec(self):
        asm = ["dec eax"]

        ctx_init = self._init_context()

        x86_ctx_out, reil_ctx_out = self._run_code(asm, 0xdeadbeef, ctx_init)

        cmp_result = self._compare_contexts(ctx_init, x86_ctx_out, reil_ctx_out)

        if not cmp_result:
            self._save_failing_context(ctx_init)

        self.assertTrue(cmp_result, self._print_contexts(ctx_init, x86_ctx_out, reil_ctx_out))

    def test_div_1(self):
        asm = ["div ebx"]

        ctx_init = {
            'rax':    0x10,
            'rbx':    0x2,
            'rdx':    0x0,
            'rflags': 0x202,
        }

        x86_ctx_out, reil_ctx_out = self._run_code(asm, 0xdeadbeef, ctx_init)

        # Undefined flags...
        reil_ctx_out = self._fix_reil_flag(reil_ctx_out, x86_ctx_out, "cf")
        reil_ctx_out = self._fix_reil_flag(reil_ctx_out, x86_ctx_out, "of")
        reil_ctx_out = self._fix_reil_flag(reil_ctx_out, x86_ctx_out, "sf")
        reil_ctx_out = self._fix_reil_flag(reil_ctx_out, x86_ctx_out, "zf")
        reil_ctx_out = self._fix_reil_flag(reil_ctx_out, x86_ctx_out, "af")
        reil_ctx_out = self._fix_reil_flag(reil_ctx_out, x86_ctx_out, "pf")

        cmp_result = self._compare_contexts(ctx_init, x86_ctx_out, reil_ctx_out)

        if not cmp_result:
            self._save_failing_context(ctx_init)

        self.assertTrue(cmp_result, self._print_contexts(ctx_init, x86_ctx_out, reil_ctx_out))

    def test_div_2(self):
        asm = ["div ebx"]

        ctx_init = {
            'rax':    0xFFFFFFFFFFFFFFFF,
            'rbx':    0x2,
            'rdx':    0x0000000000000000,
            'rflags': 0x202,
        }

        x86_ctx_out, reil_ctx_out = self._run_code(asm, 0xdeadbeef, ctx_init)

        # Undefined flags...
        reil_ctx_out = self._fix_reil_flag(reil_ctx_out, x86_ctx_out, "cf")
        reil_ctx_out = self._fix_reil_flag(reil_ctx_out, x86_ctx_out, "of")
        reil_ctx_out = self._fix_reil_flag(reil_ctx_out, x86_ctx_out, "sf")
        reil_ctx_out = self._fix_reil_flag(reil_ctx_out, x86_ctx_out, "zf")
        reil_ctx_out = self._fix_reil_flag(reil_ctx_out, x86_ctx_out, "af")
        reil_ctx_out = self._fix_reil_flag(reil_ctx_out, x86_ctx_out, "pf")

        cmp_result = self._compare_contexts(ctx_init, x86_ctx_out, reil_ctx_out)

        if not cmp_result:
            self._save_failing_context(ctx_init)

        self.assertTrue(cmp_result, self._print_contexts(ctx_init, x86_ctx_out, reil_ctx_out))

    def test_div_3(self):
        asm = ["div ebx"]

        ctx_init = {
            'rax':    0xFFFFFFFFFFFFFFFF,
            'rbx':    0x2,
            'rdx':    0x0000000000000001,
            'rflags': 0x202,
        }

        x86_ctx_out, reil_ctx_out = self._run_code(asm, 0xdeadbeef, ctx_init)

        # Undefined flags...
        reil_ctx_out = self._fix_reil_flag(reil_ctx_out, x86_ctx_out, "cf")
        reil_ctx_out = self._fix_reil_flag(reil_ctx_out, x86_ctx_out, "of")
        reil_ctx_out = self._fix_reil_flag(reil_ctx_out, x86_ctx_out, "sf")
        reil_ctx_out = self._fix_reil_flag(reil_ctx_out, x86_ctx_out, "zf")
        reil_ctx_out = self._fix_reil_flag(reil_ctx_out, x86_ctx_out, "af")
        reil_ctx_out = self._fix_reil_flag(reil_ctx_out, x86_ctx_out, "pf")

        cmp_result = self._compare_contexts(ctx_init, x86_ctx_out, reil_ctx_out)

        if not cmp_result:
            self._save_failing_context(ctx_init)

        self.assertTrue(cmp_result, self._print_contexts(ctx_init, x86_ctx_out, reil_ctx_out))

    def test_div_4(self):
        asm = ["div ebx"]

        ctx_init = {
            'rax':    0xFFFFFFFFFFFFFFFF,
            'rbx':    0x4,
            'rdx':    0x0000000000000002,
            'rflags': 0x202,
        }

        x86_ctx_out, reil_ctx_out = self._run_code(asm, 0xdeadbeef, ctx_init)

        # Undefined flags...
        reil_ctx_out = self._fix_reil_flag(reil_ctx_out, x86_ctx_out, "cf")
        reil_ctx_out = self._fix_reil_flag(reil_ctx_out, x86_ctx_out, "of")
        reil_ctx_out = self._fix_reil_flag(reil_ctx_out, x86_ctx_out, "sf")
        reil_ctx_out = self._fix_reil_flag(reil_ctx_out, x86_ctx_out, "zf")
        reil_ctx_out = self._fix_reil_flag(reil_ctx_out, x86_ctx_out, "af")
        reil_ctx_out = self._fix_reil_flag(reil_ctx_out, x86_ctx_out, "pf")

        cmp_result = self._compare_contexts(ctx_init, x86_ctx_out, reil_ctx_out)

        if not cmp_result:
            self._save_failing_context(ctx_init)

        self.assertTrue(cmp_result, self._print_contexts(ctx_init, x86_ctx_out, reil_ctx_out))

    def test_div_5(self):
        asm = ["idiv ebx"]

        ctx_init = {
            'rax':    0x0000000000000005,
            'rbx':    0x0000000000000003,
            'rdx':    0x0000000000000000,
            'rflags': 0x202,
        }

        x86_ctx_out, reil_ctx_out = self._run_code(asm, 0xdeadbeef, ctx_init)

        # Undefined flags...
        reil_ctx_out = self._fix_reil_flag(reil_ctx_out, x86_ctx_out, "cf")
        reil_ctx_out = self._fix_reil_flag(reil_ctx_out, x86_ctx_out, "of")
        reil_ctx_out = self._fix_reil_flag(reil_ctx_out, x86_ctx_out, "sf")
        reil_ctx_out = self._fix_reil_flag(reil_ctx_out, x86_ctx_out, "zf")
        reil_ctx_out = self._fix_reil_flag(reil_ctx_out, x86_ctx_out, "af")
        reil_ctx_out = self._fix_reil_flag(reil_ctx_out, x86_ctx_out, "pf")

        cmp_result = self._compare_contexts(ctx_init, x86_ctx_out, reil_ctx_out)

        if not cmp_result:
            self._save_failing_context(ctx_init)

        self.assertTrue(cmp_result, self._print_contexts(ctx_init, x86_ctx_out, reil_ctx_out))

    def test_idiv_1(self):
        asm = ["idiv ebx"]

        ctx_init = {
            'rax':    0x10,
            'rbx':    0x2,
            'rdx':    0x0,
            'rflags': 0x202,
        }

        x86_ctx_out, reil_ctx_out = self._run_code(asm, 0xdeadbeef, ctx_init)

        # Undefined flags...
        reil_ctx_out = self._fix_reil_flag(reil_ctx_out, x86_ctx_out, "cf")
        reil_ctx_out = self._fix_reil_flag(reil_ctx_out, x86_ctx_out, "of")
        reil_ctx_out = self._fix_reil_flag(reil_ctx_out, x86_ctx_out, "sf")
        reil_ctx_out = self._fix_reil_flag(reil_ctx_out, x86_ctx_out, "zf")
        reil_ctx_out = self._fix_reil_flag(reil_ctx_out, x86_ctx_out, "af")
        reil_ctx_out = self._fix_reil_flag(reil_ctx_out, x86_ctx_out, "pf")

        cmp_result = self._compare_contexts(ctx_init, x86_ctx_out, reil_ctx_out)

        if not cmp_result:
            self._save_failing_context(ctx_init)

        self.assertTrue(cmp_result, self._print_contexts(ctx_init, x86_ctx_out, reil_ctx_out))

    def test_idiv_2(self):
        asm = ["idiv ebx"]

        ctx_init = {
            'rax':    0xFFFFFFFFFFFFFFFF,
            'rbx':    0x0000000000000001,
            'rdx':    0xFFFFFFFFFFFFFFFF,
            'rflags': 0x202,
        }

        x86_ctx_out, reil_ctx_out = self._run_code(asm, 0xdeadbeef, ctx_init)

        # Undefined flags...
        reil_ctx_out = self._fix_reil_flag(reil_ctx_out, x86_ctx_out, "cf")
        reil_ctx_out = self._fix_reil_flag(reil_ctx_out, x86_ctx_out, "of")
        reil_ctx_out = self._fix_reil_flag(reil_ctx_out, x86_ctx_out, "sf")
        reil_ctx_out = self._fix_reil_flag(reil_ctx_out, x86_ctx_out, "zf")
        reil_ctx_out = self._fix_reil_flag(reil_ctx_out, x86_ctx_out, "af")
        reil_ctx_out = self._fix_reil_flag(reil_ctx_out, x86_ctx_out, "pf")

        cmp_result = self._compare_contexts(ctx_init, x86_ctx_out, reil_ctx_out)

        if not cmp_result:
            self._save_failing_context(ctx_init)

        self.assertTrue(cmp_result, self._print_contexts(ctx_init, x86_ctx_out, reil_ctx_out))

    def test_idiv_3(self):
        asm = ["idiv ebx"]

        ctx_init = {
            'rax':    0xFFFFFFFFFFFFFFFE,
            'rbx':    0xFFFFFFFFFFFFFFFF,
            'rdx':    0xFFFFFFFFFFFFFFFF,
            'rflags': 0x202,
        }

        x86_ctx_out, reil_ctx_out = self._run_code(asm, 0xdeadbeef, ctx_init)

        # Undefined flags...
        reil_ctx_out = self._fix_reil_flag(reil_ctx_out, x86_ctx_out, "cf")
        reil_ctx_out = self._fix_reil_flag(reil_ctx_out, x86_ctx_out, "of")
        reil_ctx_out = self._fix_reil_flag(reil_ctx_out, x86_ctx_out, "sf")
        reil_ctx_out = self._fix_reil_flag(reil_ctx_out, x86_ctx_out, "zf")
        reil_ctx_out = self._fix_reil_flag(reil_ctx_out, x86_ctx_out, "af")
        reil_ctx_out = self._fix_reil_flag(reil_ctx_out, x86_ctx_out, "pf")

        cmp_result = self._compare_contexts(ctx_init, x86_ctx_out, reil_ctx_out)

        if not cmp_result:
            self._save_failing_context(ctx_init)

        self.assertTrue(cmp_result, self._print_contexts(ctx_init, x86_ctx_out, reil_ctx_out))

    def test_idiv_4(self):
        asm = ["idiv ebx"]

        ctx_init = {
            'rax':    0xFFFFFFFFFFFFFFFB,  # -5
            'rbx':    0x0000000000000003,
            'rdx':    0xFFFFFFFFFFFFFFFF,
            'rflags': 0x202,
        }

        x86_ctx_out, reil_ctx_out = self._run_code(asm, 0xdeadbeef, ctx_init)

        # Undefined flags...
        reil_ctx_out = self._fix_reil_flag(reil_ctx_out, x86_ctx_out, "cf")
        reil_ctx_out = self._fix_reil_flag(reil_ctx_out, x86_ctx_out, "of")
        reil_ctx_out = self._fix_reil_flag(reil_ctx_out, x86_ctx_out, "sf")
        reil_ctx_out = self._fix_reil_flag(reil_ctx_out, x86_ctx_out, "zf")
        reil_ctx_out = self._fix_reil_flag(reil_ctx_out, x86_ctx_out, "af")
        reil_ctx_out = self._fix_reil_flag(reil_ctx_out, x86_ctx_out, "pf")

        cmp_result = self._compare_contexts(ctx_init, x86_ctx_out, reil_ctx_out)

        if not cmp_result:
            self._save_failing_context(ctx_init)

        self.assertTrue(cmp_result, self._print_contexts(ctx_init, x86_ctx_out, reil_ctx_out))

    def test_idiv_5(self):
        asm = ["idiv ebx"]

        ctx_init = {
            'rax':    0x0000000000000005,  # 5
            'rbx':    0xFFFFFFFFFFFFFFFD,  # -3
            'rdx':    0x0000000000000000,
            'rflags': 0x202,
        }

        x86_ctx_out, reil_ctx_out = self._run_code(asm, 0xdeadbeef, ctx_init)

        # Undefined flags...
        reil_ctx_out = self._fix_reil_flag(reil_ctx_out, x86_ctx_out, "cf")
        reil_ctx_out = self._fix_reil_flag(reil_ctx_out, x86_ctx_out, "of")
        reil_ctx_out = self._fix_reil_flag(reil_ctx_out, x86_ctx_out, "sf")
        reil_ctx_out = self._fix_reil_flag(reil_ctx_out, x86_ctx_out, "zf")
        reil_ctx_out = self._fix_reil_flag(reil_ctx_out, x86_ctx_out, "af")
        reil_ctx_out = self._fix_reil_flag(reil_ctx_out, x86_ctx_out, "pf")

        cmp_result = self._compare_contexts(ctx_init, x86_ctx_out, reil_ctx_out)

        if not cmp_result:
            self._save_failing_context(ctx_init)

        self.assertTrue(cmp_result, self._print_contexts(ctx_init, x86_ctx_out, reil_ctx_out))

    def test_imul_1(self):
        asm = ["imul eax"]

        ctx_init = self._init_context()

        x86_ctx_out, reil_ctx_out = self._run_code(asm, 0xdeadbeef, ctx_init)

        # FIX: Remove this once OF and CF are implemented.
        reil_ctx_out = self._fix_reil_flag(reil_ctx_out, x86_ctx_out, "of")
        reil_ctx_out = self._fix_reil_flag(reil_ctx_out, x86_ctx_out, "cf")

        # Undefined flags...
        reil_ctx_out = self._fix_reil_flag(reil_ctx_out, x86_ctx_out, "sf")
        reil_ctx_out = self._fix_reil_flag(reil_ctx_out, x86_ctx_out, "zf")
        reil_ctx_out = self._fix_reil_flag(reil_ctx_out, x86_ctx_out, "af")
        reil_ctx_out = self._fix_reil_flag(reil_ctx_out, x86_ctx_out, "pf")

        cmp_result = self._compare_contexts(ctx_init, x86_ctx_out, reil_ctx_out)

        if not cmp_result:
            self._save_failing_context(ctx_init)

        self.assertTrue(cmp_result, self._print_contexts(ctx_init, x86_ctx_out, reil_ctx_out))

    def test_imul_2(self):
        asm = ["imul eax, ebx"]

        ctx_init = self._init_context()

        x86_ctx_out, reil_ctx_out = self._run_code(asm, 0xdeadbeef, ctx_init)

        # FIX: Remove this once OF and CF are implemented.
        reil_ctx_out = self._fix_reil_flag(reil_ctx_out, x86_ctx_out, "of")
        reil_ctx_out = self._fix_reil_flag(reil_ctx_out, x86_ctx_out, "cf")

        # Undefined flags...
        reil_ctx_out = self._fix_reil_flag(reil_ctx_out, x86_ctx_out, "sf")
        reil_ctx_out = self._fix_reil_flag(reil_ctx_out, x86_ctx_out, "zf")
        reil_ctx_out = self._fix_reil_flag(reil_ctx_out, x86_ctx_out, "af")
        reil_ctx_out = self._fix_reil_flag(reil_ctx_out, x86_ctx_out, "pf")

        cmp_result = self._compare_contexts(ctx_init, x86_ctx_out, reil_ctx_out)

        if not cmp_result:
            self._save_failing_context(ctx_init)

        self.assertTrue(cmp_result, self._print_contexts(ctx_init, x86_ctx_out, reil_ctx_out))

    def test_imul_3(self):
        asm = ["imul eax, ebx, 0x20"]

        ctx_init = self._init_context()

        x86_ctx_out, reil_ctx_out = self._run_code(asm, 0xdeadbeef, ctx_init)

        # FIX: Remove this once OF and CF are implemented.
        reil_ctx_out = self._fix_reil_flag(reil_ctx_out, x86_ctx_out, "of")
        reil_ctx_out = self._fix_reil_flag(reil_ctx_out, x86_ctx_out, "cf")

        # Undefined flags...
        reil_ctx_out = self._fix_reil_flag(reil_ctx_out, x86_ctx_out, "sf")
        reil_ctx_out = self._fix_reil_flag(reil_ctx_out, x86_ctx_out, "zf")
        reil_ctx_out = self._fix_reil_flag(reil_ctx_out, x86_ctx_out, "af")
        reil_ctx_out = self._fix_reil_flag(reil_ctx_out, x86_ctx_out, "pf")

        cmp_result = self._compare_contexts(ctx_init, x86_ctx_out, reil_ctx_out)

        if not cmp_result:
            self._save_failing_context(ctx_init)

        self.assertTrue(cmp_result, self._print_contexts(ctx_init, x86_ctx_out, reil_ctx_out))

    def test_imul_4(self):
        asm = ["imul eax, ebx, 0xffffffff"]

        ctx_init = self._init_context()

        x86_ctx_out, reil_ctx_out = self._run_code(asm, 0xdeadbeef, ctx_init)

        # FIX: Remove this once OF and CF are implemented.
        reil_ctx_out = self._fix_reil_flag(reil_ctx_out, x86_ctx_out, "of")
        reil_ctx_out = self._fix_reil_flag(reil_ctx_out, x86_ctx_out, "cf")

        # Undefined flags...
        reil_ctx_out = self._fix_reil_flag(reil_ctx_out, x86_ctx_out, "sf")
        reil_ctx_out = self._fix_reil_flag(reil_ctx_out, x86_ctx_out, "zf")
        reil_ctx_out = self._fix_reil_flag(reil_ctx_out, x86_ctx_out, "af")
        reil_ctx_out = self._fix_reil_flag(reil_ctx_out, x86_ctx_out, "pf")

        cmp_result = self._compare_contexts(ctx_init, x86_ctx_out, reil_ctx_out)

        if not cmp_result:
            self._save_failing_context(ctx_init)

        self.assertTrue(cmp_result, self._print_contexts(ctx_init, x86_ctx_out, reil_ctx_out))

    def test_imul_5(self):
        asm = ["imul ebx"]

        ctx_init = {
            'rax':    0x0000000000000005,  # 5
            'rbx':    0xFFFFFFFFFFFFFFFD,  # -3
            'rdx':    0x0000000000000000,
            'rflags': 0x202,
        }

        x86_ctx_out, reil_ctx_out = self._run_code(asm, 0xdeadbeef, ctx_init)

        # Undefined flags...
        reil_ctx_out = self._fix_reil_flag(reil_ctx_out, x86_ctx_out, "cf")
        reil_ctx_out = self._fix_reil_flag(reil_ctx_out, x86_ctx_out, "of")
        reil_ctx_out = self._fix_reil_flag(reil_ctx_out, x86_ctx_out, "sf")
        reil_ctx_out = self._fix_reil_flag(reil_ctx_out, x86_ctx_out, "zf")
        reil_ctx_out = self._fix_reil_flag(reil_ctx_out, x86_ctx_out, "af")
        reil_ctx_out = self._fix_reil_flag(reil_ctx_out, x86_ctx_out, "pf")

        cmp_result = self._compare_contexts(ctx_init, x86_ctx_out, reil_ctx_out)

        if not cmp_result:
            self._save_failing_context(ctx_init)

        self.assertTrue(cmp_result, self._print_contexts(ctx_init, x86_ctx_out, reil_ctx_out))

    def test_inc(self):
        asm = ["inc eax"]

        ctx_init = self._init_context()

        x86_ctx_out, reil_ctx_out = self._run_code(asm, 0xdeadbeef, ctx_init)

        cmp_result = self._compare_contexts(ctx_init, x86_ctx_out, reil_ctx_out)

        if not cmp_result:
            self._save_failing_context(ctx_init)

        self.assertTrue(cmp_result, self._print_contexts(ctx_init, x86_ctx_out, reil_ctx_out))

    def test_mul(self):
        asm = ["mul ebx"]

        ctx_init = self._init_context()

        x86_ctx_out, reil_ctx_out = self._run_code(asm, 0xdeadbeef, ctx_init)

        # Undefined flags...
        reil_ctx_out = self._fix_reil_flag(reil_ctx_out, x86_ctx_out, "sf")
        reil_ctx_out = self._fix_reil_flag(reil_ctx_out, x86_ctx_out, "zf")
        reil_ctx_out = self._fix_reil_flag(reil_ctx_out, x86_ctx_out, "af")
        reil_ctx_out = self._fix_reil_flag(reil_ctx_out, x86_ctx_out, "pf")

        cmp_result = self._compare_contexts(ctx_init, x86_ctx_out, reil_ctx_out)

        if not cmp_result:
            self._save_failing_context(ctx_init)

        self.assertTrue(cmp_result, self._print_contexts(ctx_init, x86_ctx_out, reil_ctx_out))

    def test_neg(self):
        asm = ["neg eax"]

        ctx_init = self._init_context()

        x86_ctx_out, reil_ctx_out = self._run_code(asm, 0xdeadbeef, ctx_init)

        cmp_result = self._compare_contexts(ctx_init, x86_ctx_out, reil_ctx_out)

        if not cmp_result:
            self._save_failing_context(ctx_init)

        self.assertTrue(cmp_result, self._print_contexts(ctx_init, x86_ctx_out, reil_ctx_out))

    def test_sbb(self):
        asm = ["sbb eax, ebx"]

        ctx_init = self._init_context()

        x86_ctx_out, reil_ctx_out = self._run_code(asm, 0xdeadbeef, ctx_init)

        cmp_result = self._compare_contexts(ctx_init, x86_ctx_out, reil_ctx_out)

        if not cmp_result:
            self._save_failing_context(ctx_init)

        self.assertTrue(cmp_result, self._print_contexts(ctx_init, x86_ctx_out, reil_ctx_out))

    def test_sub(self):
        asm = ["sub eax, ebx"]

        ctx_init = self._init_context()

        x86_ctx_out, reil_ctx_out = self._run_code(asm, 0xdeadbeef, ctx_init)

        cmp_result = self._compare_contexts(ctx_init, x86_ctx_out, reil_ctx_out)

        if not cmp_result:
            self._save_failing_context(ctx_init)

        self.assertTrue(cmp_result, self._print_contexts(ctx_init, x86_ctx_out, reil_ctx_out))
