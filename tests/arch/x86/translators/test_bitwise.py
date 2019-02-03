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
class X86TranslationBitwiseTests(X86TranslationTestCase):

    # "Bit and Byte Instructions"
    # ============================================================================ #
    def test_bsf_1(self):
        asm = ["bsf rax, rbx"]

        ctx_init = self._init_context()

        x86_ctx_out, reil_ctx_out = self._run_code(asm, 0xdeadbeef, ctx_init)

        # NOTE: The CF, OF, SF, AF, and PF flags are undefined.
        reil_ctx_out = self._fix_reil_flag(reil_ctx_out, x86_ctx_out, "cf")
        reil_ctx_out = self._fix_reil_flag(reil_ctx_out, x86_ctx_out, "of")
        reil_ctx_out = self._fix_reil_flag(reil_ctx_out, x86_ctx_out, "sf")
        reil_ctx_out = self._fix_reil_flag(reil_ctx_out, x86_ctx_out, "af")
        reil_ctx_out = self._fix_reil_flag(reil_ctx_out, x86_ctx_out, "pf")

        cmp_result = self._compare_contexts(ctx_init, x86_ctx_out, reil_ctx_out)

        if not cmp_result:
            self._save_failing_context(ctx_init)

        self.assertTrue(cmp_result, self._print_contexts(ctx_init, x86_ctx_out, reil_ctx_out))

    def test_bsf_2(self):
        asm = ["bsf rax, rbx"]

        ctx_init = self._init_context()

        ctx_init["rbx"] = 0x0

        x86_ctx_out, reil_ctx_out = self._run_code(asm, 0xdeadbeef, ctx_init)

        # NOTE: The CF, OF, SF, AF, and PF flags are undefined.
        reil_ctx_out = self._fix_reil_flag(reil_ctx_out, x86_ctx_out, "cf")
        reil_ctx_out = self._fix_reil_flag(reil_ctx_out, x86_ctx_out, "of")
        reil_ctx_out = self._fix_reil_flag(reil_ctx_out, x86_ctx_out, "sf")
        reil_ctx_out = self._fix_reil_flag(reil_ctx_out, x86_ctx_out, "af")
        reil_ctx_out = self._fix_reil_flag(reil_ctx_out, x86_ctx_out, "pf")

        cmp_result = self._compare_contexts(ctx_init, x86_ctx_out, reil_ctx_out)

        if not cmp_result:
            self._save_failing_context(ctx_init)

        self.assertTrue(cmp_result, self._print_contexts(ctx_init, x86_ctx_out, reil_ctx_out))

    def test_bt(self):
        asm = ["bt eax, ebx"]

        ctx_init = self._init_context()

        x86_ctx_out, reil_ctx_out = self._run_code(asm, 0xdeadbeef, ctx_init)

        # NOTE: The OF, SF, AF, and PF flags are undefined.
        reil_ctx_out = self._fix_reil_flag(reil_ctx_out, x86_ctx_out, "of")
        reil_ctx_out = self._fix_reil_flag(reil_ctx_out, x86_ctx_out, "sf")
        reil_ctx_out = self._fix_reil_flag(reil_ctx_out, x86_ctx_out, "af")
        reil_ctx_out = self._fix_reil_flag(reil_ctx_out, x86_ctx_out, "pf")

        cmp_result = self._compare_contexts(ctx_init, x86_ctx_out, reil_ctx_out)

        if not cmp_result:
            self._save_failing_context(ctx_init)

        self.assertTrue(cmp_result, self._print_contexts(ctx_init, x86_ctx_out, reil_ctx_out))

    def test_bts_1(self):
        asm = ["bts rdx, rsi"]

        ctx_init = self._init_context()

        x86_ctx_out, reil_ctx_out = self._run_code(asm, 0xdeadbeef, ctx_init)

        # NOTE: The OF, SF, AF, and PF flags are undefined.
        reil_ctx_out = self._fix_reil_flag(reil_ctx_out, x86_ctx_out, "of")
        reil_ctx_out = self._fix_reil_flag(reil_ctx_out, x86_ctx_out, "sf")
        reil_ctx_out = self._fix_reil_flag(reil_ctx_out, x86_ctx_out, "af")
        reil_ctx_out = self._fix_reil_flag(reil_ctx_out, x86_ctx_out, "pf")

        cmp_result = self._compare_contexts(ctx_init, x86_ctx_out, reil_ctx_out)

        if not cmp_result:
            self._save_failing_context(ctx_init)

        self.assertTrue(cmp_result, self._print_contexts(ctx_init, x86_ctx_out, reil_ctx_out))

    def test_bts_2(self):
        asm = ["bts rdx, r11"]

        ctx_init = self._init_context()

        ctx_init["rdx"] = 0x4000040010001
        ctx_init["r11"] = 0x07fffe4519001

        x86_ctx_out, reil_ctx_out = self._run_code(asm, 0xdeadbeef, ctx_init)

        # NOTE: The OF, SF, AF, and PF flags are undefined.
        reil_ctx_out = self._fix_reil_flag(reil_ctx_out, x86_ctx_out, "of")
        reil_ctx_out = self._fix_reil_flag(reil_ctx_out, x86_ctx_out, "sf")
        reil_ctx_out = self._fix_reil_flag(reil_ctx_out, x86_ctx_out, "af")
        reil_ctx_out = self._fix_reil_flag(reil_ctx_out, x86_ctx_out, "pf")

        cmp_result = self._compare_contexts(ctx_init, x86_ctx_out, reil_ctx_out)

        if not cmp_result:
            self._save_failing_context(ctx_init)

        self.assertTrue(cmp_result, self._print_contexts(ctx_init, x86_ctx_out, reil_ctx_out))

    def test_test(self):
        asm = ["test eax, ebx"]

        ctx_init = self._init_context()

        x86_ctx_out, reil_ctx_out = self._run_code(asm, 0xdeadbeef, ctx_init)

        # Undefined flags...
        reil_ctx_out = self._fix_reil_flag(reil_ctx_out, x86_ctx_out, "af")

        cmp_result = self._compare_contexts(ctx_init, x86_ctx_out, reil_ctx_out)

        if not cmp_result:
            self._save_failing_context(ctx_init)

        self.assertTrue(cmp_result, self._print_contexts(ctx_init, x86_ctx_out, reil_ctx_out))

    # "Shift and Rotate Instructions"
    # ============================================================================ #
    def test_rcl(self):
        asm = ["rcl eax, 8"]

        ctx_init = self._init_context()

        # set carry flag
        ctx_init['rflags'] = ctx_init['rflags'] | 0x1

        x86_ctx_out, reil_ctx_out = self._run_code(asm, 0xdeadbeef, ctx_init)

        # NOTE: OF and CF can be left undefined in some cases. They are
        # not cover by this test.
        reil_ctx_out = self._fix_reil_flag(reil_ctx_out, x86_ctx_out, "cf")
        reil_ctx_out = self._fix_reil_flag(reil_ctx_out, x86_ctx_out, "of")

        cmp_result = self._compare_contexts(ctx_init, x86_ctx_out, reil_ctx_out)

        if not cmp_result:
            self._save_failing_context(ctx_init)

        self.assertTrue(cmp_result, self._print_contexts(ctx_init, x86_ctx_out, reil_ctx_out))

    def test_rcr(self):
        asm = ["rcr eax, 3"]

        ctx_init = self._init_context()

        # set carry flag
        ctx_init['rflags'] = ctx_init['rflags'] | 0x1

        x86_ctx_out, reil_ctx_out = self._run_code(asm, 0xdeadbeef, ctx_init)

        # NOTE: OF and CF can be left undefined in some cases. They are
        # not cover by this test.
        reil_ctx_out = self._fix_reil_flag(reil_ctx_out, x86_ctx_out, "cf")
        reil_ctx_out = self._fix_reil_flag(reil_ctx_out, x86_ctx_out, "of")

        cmp_result = self._compare_contexts(ctx_init, x86_ctx_out, reil_ctx_out)

        if not cmp_result:
            self._save_failing_context(ctx_init)

        self.assertTrue(cmp_result, self._print_contexts(ctx_init, x86_ctx_out, reil_ctx_out))

    def test_rol(self):
        asm = ["rol eax, 8"]

        ctx_init = self._init_context()

        x86_ctx_out, reil_ctx_out = self._run_code(asm, 0xdeadbeef, ctx_init)

        # NOTE: OF and CF can be left undefined in some cases. They are
        # not cover by this test.
        reil_ctx_out = self._fix_reil_flag(reil_ctx_out, x86_ctx_out, "cf")
        reil_ctx_out = self._fix_reil_flag(reil_ctx_out, x86_ctx_out, "of")

        cmp_result = self._compare_contexts(ctx_init, x86_ctx_out, reil_ctx_out)

        if not cmp_result:
            self._save_failing_context(ctx_init)

        self.assertTrue(cmp_result, self._print_contexts(ctx_init, x86_ctx_out, reil_ctx_out))

    def test_ror(self):
        asm = ["ror eax, 8"]

        ctx_init = self._init_context()

        x86_ctx_out, reil_ctx_out = self._run_code(asm, 0xdeadbeef, ctx_init)

        # NOTE: OF and CF can be left undefined in some cases. They are
        # not cover by this test.
        reil_ctx_out = self._fix_reil_flag(reil_ctx_out, x86_ctx_out, "cf")
        reil_ctx_out = self._fix_reil_flag(reil_ctx_out, x86_ctx_out, "of")

        cmp_result = self._compare_contexts(ctx_init, x86_ctx_out, reil_ctx_out)

        if not cmp_result:
            self._save_failing_context(ctx_init)

        self.assertTrue(cmp_result, self._print_contexts(ctx_init, x86_ctx_out, reil_ctx_out))

    def test_sal(self):
        asm = ["sal eax, 3"]

        ctx_init = self._init_context()

        x86_ctx_out, reil_ctx_out = self._run_code(asm, 0xdeadbeef, ctx_init)

        # Undefined flags...
        reil_ctx_out = self._fix_reil_flag(reil_ctx_out, x86_ctx_out, "af")

        # NOTE: OF and CF can be left undefined in some cases. They are
        # not cover by this test.
        reil_ctx_out = self._fix_reil_flag(reil_ctx_out, x86_ctx_out, "cf")
        reil_ctx_out = self._fix_reil_flag(reil_ctx_out, x86_ctx_out, "of")

        cmp_result = self._compare_contexts(ctx_init, x86_ctx_out, reil_ctx_out)

        if not cmp_result:
            self._save_failing_context(ctx_init)

        self.assertTrue(cmp_result, self._print_contexts(ctx_init, x86_ctx_out, reil_ctx_out))

    def test_sar_1(self):
        asm = ["sar eax, 3"]

        ctx_init = self._init_context()

        x86_ctx_out, reil_ctx_out = self._run_code(asm, 0xdeadbeef, ctx_init)

        # Undefined flags...
        reil_ctx_out = self._fix_reil_flag(reil_ctx_out, x86_ctx_out, "af")

        # NOTE: OF and CF can be left undefined in some cases. They are
        # not cover by this test.
        reil_ctx_out = self._fix_reil_flag(reil_ctx_out, x86_ctx_out, "cf")
        reil_ctx_out = self._fix_reil_flag(reil_ctx_out, x86_ctx_out, "of")

        cmp_result = self._compare_contexts(ctx_init, x86_ctx_out, reil_ctx_out)

        if not cmp_result:
            self._save_failing_context(ctx_init)

        self.assertTrue(cmp_result, self._print_contexts(ctx_init, x86_ctx_out, reil_ctx_out))

    def test_sar_2(self):
        asm = ["sar rdx, cl"]

        ctx_init = self._init_context()

        ctx_init["rdx"] = 0x404010000402
        ctx_init["rcx"] = 0x0

        x86_ctx_out, reil_ctx_out = self._run_code(asm, 0xdeadbeef, ctx_init)

        # Undefined flags...
        reil_ctx_out = self._fix_reil_flag(reil_ctx_out, x86_ctx_out, "af")

        # NOTE: OF and CF can be left undefined in some cases. They are
        # not cover by this test.
        reil_ctx_out = self._fix_reil_flag(reil_ctx_out, x86_ctx_out, "cf")
        reil_ctx_out = self._fix_reil_flag(reil_ctx_out, x86_ctx_out, "of")

        cmp_result = self._compare_contexts(ctx_init, x86_ctx_out, reil_ctx_out)

        if not cmp_result:
            self._save_failing_context(ctx_init)

        self.assertTrue(cmp_result, self._print_contexts(ctx_init, x86_ctx_out, reil_ctx_out))

    def test_shl_1(self):
        asm = ["shl eax, 3"]

        ctx_init = self._init_context()

        x86_ctx_out, reil_ctx_out = self._run_code(asm, 0xdeadbeef, ctx_init)

        # Undefined flags...
        reil_ctx_out = self._fix_reil_flag(reil_ctx_out, x86_ctx_out, "af")

        # NOTE: OF and CF can be left undefined in some cases. They are
        # not cover by this test.
        reil_ctx_out = self._fix_reil_flag(reil_ctx_out, x86_ctx_out, "cf")
        reil_ctx_out = self._fix_reil_flag(reil_ctx_out, x86_ctx_out, "of")

        cmp_result = self._compare_contexts(ctx_init, x86_ctx_out, reil_ctx_out)

        if not cmp_result:
            self._save_failing_context(ctx_init)

        self.assertTrue(cmp_result, self._print_contexts(ctx_init, x86_ctx_out, reil_ctx_out))

    def test_shl_2(self):
        asm = ["shl eax, cl"]

        ctx_init = self._init_context()

        ctx_init["rax"] = 0x01
        ctx_init["rcx"] = 0x32

        x86_ctx_out, reil_ctx_out = self._run_code(asm, 0xdeadbeef, ctx_init)

        # Undefined flags...
        reil_ctx_out = self._fix_reil_flag(reil_ctx_out, x86_ctx_out, "af")

        # NOTE: OF and CF can be left undefined in some cases. They are
        # not cover by this test.
        reil_ctx_out = self._fix_reil_flag(reil_ctx_out, x86_ctx_out, "cf")
        reil_ctx_out = self._fix_reil_flag(reil_ctx_out, x86_ctx_out, "of")

        cmp_result = self._compare_contexts(ctx_init, x86_ctx_out, reil_ctx_out)

        if not cmp_result:
            self._save_failing_context(ctx_init)

        self.assertTrue(cmp_result, self._print_contexts(ctx_init, x86_ctx_out, reil_ctx_out))

    def test_shld_1(self):
        asm = ["shld eax, esi, 3"]

        ctx_init = self._init_context()

        x86_ctx_out, reil_ctx_out = self._run_code(asm, 0xdeadbeef, ctx_init)

        # Undefined flags...
        reil_ctx_out = self._fix_reil_flag(reil_ctx_out, x86_ctx_out, "af")

        # NOTE: OF and CF can be left undefined in some cases. They are
        # not cover by this test.
        reil_ctx_out = self._fix_reil_flag(reil_ctx_out, x86_ctx_out, "cf")
        reil_ctx_out = self._fix_reil_flag(reil_ctx_out, x86_ctx_out, "of")

        cmp_result = self._compare_contexts(ctx_init, x86_ctx_out, reil_ctx_out)

        if not cmp_result:
            self._save_failing_context(ctx_init)

        self.assertTrue(cmp_result, self._print_contexts(ctx_init, x86_ctx_out, reil_ctx_out))

    def test_shr_1(self):
        asm = ["shr eax, 3"]

        ctx_init = self._init_context()

        x86_ctx_out, reil_ctx_out = self._run_code(asm, 0xdeadbeef, ctx_init)

        # Undefined flags...
        reil_ctx_out = self._fix_reil_flag(reil_ctx_out, x86_ctx_out, "af")

        # NOTE: OF and CF can be left undefined in some cases. They are
        # not cover by this test.
        reil_ctx_out = self._fix_reil_flag(reil_ctx_out, x86_ctx_out, "cf")
        reil_ctx_out = self._fix_reil_flag(reil_ctx_out, x86_ctx_out, "of")

        cmp_result = self._compare_contexts(ctx_init, x86_ctx_out, reil_ctx_out)

        if not cmp_result:
            self._save_failing_context(ctx_init)

        self.assertTrue(cmp_result, self._print_contexts(ctx_init, x86_ctx_out, reil_ctx_out))

    def test_shr_2(self):
        asm = ["shr eax, cl"]

        ctx_init = self._init_context()

        ctx_init["rax"] = 0x10000
        ctx_init["rcx"] = 0x32

        x86_ctx_out, reil_ctx_out = self._run_code(asm, 0xdeadbeef, ctx_init)

        # Undefined flags...
        reil_ctx_out = self._fix_reil_flag(reil_ctx_out, x86_ctx_out, "af")

        # NOTE: OF and CF can be left undefined in some cases. They are
        # not cover by this test.
        reil_ctx_out = self._fix_reil_flag(reil_ctx_out, x86_ctx_out, "cf")
        reil_ctx_out = self._fix_reil_flag(reil_ctx_out, x86_ctx_out, "of")

        cmp_result = self._compare_contexts(ctx_init, x86_ctx_out, reil_ctx_out)

        if not cmp_result:
            self._save_failing_context(ctx_init)

        self.assertTrue(cmp_result, self._print_contexts(ctx_init, x86_ctx_out, reil_ctx_out))

    def test_shrd_1(self):
        asm = ["shrd eax, ebx, 3"]

        ctx_init = self._init_context()

        x86_ctx_out, reil_ctx_out = self._run_code(asm, 0xdeadbeef, ctx_init)

        # NOTE: AF and OF can be left undefined in some cases. They are not
        # cover by this test.
        reil_ctx_out = self._fix_reil_flag(reil_ctx_out, x86_ctx_out, "of")
        reil_ctx_out = self._fix_reil_flag(reil_ctx_out, x86_ctx_out, "af")

        cmp_result = self._compare_contexts(ctx_init, x86_ctx_out, reil_ctx_out)

        if not cmp_result:
            self._save_failing_context(ctx_init)

        self.assertTrue(cmp_result, self._print_contexts(ctx_init, x86_ctx_out, reil_ctx_out))
