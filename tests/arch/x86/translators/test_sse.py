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
class X86TranslationSseTests(X86TranslationTestCase):

    def test_lddqu(self):
        # TODO: Implement.
        pass

    def test_movaps(self):
        asm = ["movaps xmm0, xmm1"]

        ctx_init = self._init_context()

        ctx_init["xmm0"] = 0x12345678123456781234567812345678
        ctx_init["xmm1"] = 0x87654321876543218765432187654321

        res = ctx_init["xmm1"]

        x86_ctx_out, reil_ctx_out = self._run_code(asm, 0xdeadbeef, ctx_init)

        # TODO: Compare mm/xmm registers when comparing contexts.
        # cmp_result = self._compare_contexts(ctx_init, x86_ctx_out, reil_ctx_out)

        # if not cmp_result:
        #     self._save_failing_context(ctx_init)

        # self.assertTrue(cmp_result, self._print_contexts(ctx_init, x86_ctx_out, reil_ctx_out))

        self.assertEquals(reil_ctx_out["xmm0"], res)
        self.assertEquals(reil_ctx_out["xmm1"], ctx_init["xmm1"])

    def test_movd_1(self):
        # MOVD mm, r/m32
        asm = ["movd mm0, eax"]

        ctx_init = self._init_context()

        ctx_init["mm0"] = 0x1234567812345678
        ctx_init["rax"] = 0xffffffff87654321

        res = 0x0000000087654321

        x86_ctx_out, reil_ctx_out = self._run_code(asm, 0xdeadbeef, ctx_init)

        # TODO: Compare mm/xmm registers when comparing contexts.
        # cmp_result = self._compare_contexts(ctx_init, x86_ctx_out, reil_ctx_out)

        # if not cmp_result:
        #     self._save_failing_context(ctx_init)

        # self.assertTrue(cmp_result, self._print_contexts(ctx_init, x86_ctx_out, reil_ctx_out))

        self.assertEquals(reil_ctx_out["mm0"], res)
        self.assertEquals(reil_ctx_out["rax"], ctx_init["rax"])

    def test_movd_2(self):
        # MOVD r/m32, mm
        asm = ["movd eax, mm0"]

        ctx_init = self._init_context()

        ctx_init["mm0"] = 0x1234567812345678
        ctx_init["rax"] = 0xffffffff87654321

        res = 0x0000000012345678

        x86_ctx_out, reil_ctx_out = self._run_code(asm, 0xdeadbeef, ctx_init)

        # TODO: Compare mm/xmm registers when comparing contexts.
        # cmp_result = self._compare_contexts(ctx_init, x86_ctx_out, reil_ctx_out)

        # if not cmp_result:
        #     self._save_failing_context(ctx_init)

        # self.assertTrue(cmp_result, self._print_contexts(ctx_init, x86_ctx_out, reil_ctx_out))

        self.assertEquals(reil_ctx_out["rax"], res)
        self.assertEquals(reil_ctx_out["mm0"], ctx_init["mm0"])

    def test_movd_3(self):
        # MOVD xmm, r/m32
        asm = ["movd xmm0, eax"]

        ctx_init = self._init_context()

        ctx_init["xmm0"] = 0x12345678123456781234567812345678
        ctx_init["rax"] = 0xffffffff87654321

        res = 0x00000000000000000000000087654321

        x86_ctx_out, reil_ctx_out = self._run_code(asm, 0xdeadbeef, ctx_init)

        # TODO: Compare mm/xmm registers when comparing contexts.
        # cmp_result = self._compare_contexts(ctx_init, x86_ctx_out, reil_ctx_out)

        # if not cmp_result:
        #     self._save_failing_context(ctx_init)

        # self.assertTrue(cmp_result, self._print_contexts(ctx_init, x86_ctx_out, reil_ctx_out))

        self.assertEquals(reil_ctx_out["xmm0"], res)
        self.assertEquals(reil_ctx_out["rax"], ctx_init["rax"])

    def test_movd_4(self):
        # MOVD r/m32, xmm
        asm = ["movd eax, xmm0"]

        ctx_init = self._init_context()

        ctx_init["xmm0"] = 0x12345678123456781234567812345678
        ctx_init["rax"] = 0xffffffff87654321

        res = 0x0000000012345678

        x86_ctx_out, reil_ctx_out = self._run_code(asm, 0xdeadbeef, ctx_init)

        # TODO: Compare mm/xmm registers when comparing contexts.
        # cmp_result = self._compare_contexts(ctx_init, x86_ctx_out, reil_ctx_out)

        # if not cmp_result:
        #     self._save_failing_context(ctx_init)

        # self.assertTrue(cmp_result, self._print_contexts(ctx_init, x86_ctx_out, reil_ctx_out))

        self.assertEquals(reil_ctx_out["rax"], res)
        self.assertEquals(reil_ctx_out["xmm0"], ctx_init["xmm0"])

    def test_movdqa(self):
        # TODO: Implement.
        pass

    def test_movdqu(self):
        # TODO: Implement.
        pass

    def test_movhpd(self):
        asm = ["movhpd xmm0, xmm1"]

        ctx_init = self._init_context()

        ctx_init["xmm0"] = 0x12345678123456781234567812345678
        ctx_init["xmm1"] = 0x87654321876543218765432187654321

        res = 0x87654321876543211234567812345678

        # x86_ctx_out, reil_ctx_out = self._run_code(asm, 0xdeadbeef, ctx_init)

        # NOTE Hack to be able to test this instr (src oprnd should be a memory
        # operand instead of a xmm register).
        # -------------------------------------------------------------------- #
        address = 0xdeadbeef
        reil_instrs = self._asm_to_reil(asm, address)
        reil_ctx_out, _ = self.reil_emulator.execute(reil_instrs, start=address << 8, registers=ctx_init)
        # -------------------------------------------------------------------- #

        # TODO: Compare mm/xmm registers when comparing contexts.
        # cmp_result = self._compare_contexts(ctx_init, x86_ctx_out, reil_ctx_out)

        # if not cmp_result:
        #     self._save_failing_context(ctx_init)

        # self.assertTrue(cmp_result, self._print_contexts(ctx_init, x86_ctx_out, reil_ctx_out))

        self.assertEquals(reil_ctx_out["xmm0"], res)
        self.assertEquals(reil_ctx_out["xmm1"], ctx_init["xmm1"])

    def test_movlpd(self):
        asm = ["movlpd xmm0, xmm1"]

        ctx_init = self._init_context()

        ctx_init["xmm0"] = 0x12345678123456781234567812345678
        ctx_init["xmm1"] = 0x87654321876543218765432187654321

        res = 0x12345678123456788765432187654321

        # x86_ctx_out, reil_ctx_out = self._run_code(asm, 0xdeadbeef, ctx_init)

        # NOTE Hack to be able to test this instr (src oprnd should be a memory
        # operand instead of a xmm register).
        # -------------------------------------------------------------------- #
        address = 0xdeadbeef
        reil_instrs = self._asm_to_reil(asm, address)
        reil_ctx_out, _ = self.reil_emulator.execute(reil_instrs, start=address << 8, registers=ctx_init)
        # -------------------------------------------------------------------- #

        # TODO: Compare mm/xmm registers when comparing contexts.
        # cmp_result = self._compare_contexts(ctx_init, x86_ctx_out, reil_ctx_out)

        # if not cmp_result:
        #     self._save_failing_context(ctx_init)

        # self.assertTrue(cmp_result, self._print_contexts(ctx_init, x86_ctx_out, reil_ctx_out))

        self.assertEquals(reil_ctx_out["xmm0"], res)
        self.assertEquals(reil_ctx_out["xmm1"], ctx_init["xmm1"])

    def test_movq_1(self):
        # MOVQ mm, r/m64
        asm = ["movq mm0, rax"]

        ctx_init = self._init_context()

        ctx_init["mm0"] = 0x1234567812345678
        ctx_init["rax"] = 0x8765432187654321

        res = 0x8765432187654321

        x86_ctx_out, reil_ctx_out = self._run_code(asm, 0xdeadbeef, ctx_init)

        # TODO: Compare mm/xmm registers when comparing contexts.
        # cmp_result = self._compare_contexts(ctx_init, x86_ctx_out, reil_ctx_out)

        # if not cmp_result:
        #     self._save_failing_context(ctx_init)

        # self.assertTrue(cmp_result, self._print_contexts(ctx_init, x86_ctx_out, reil_ctx_out))

        self.assertEquals(reil_ctx_out["mm0"], res)
        self.assertEquals(reil_ctx_out["rax"], ctx_init["rax"])

    def test_movq_2(self):
        # MOVQ r/m64, mm
        asm = ["movq rax, mm0"]

        ctx_init = self._init_context()

        ctx_init["mm0"] = 0x1234567812345678
        ctx_init["rax"] = 0x8765432187654321

        res = 0x1234567812345678

        x86_ctx_out, reil_ctx_out = self._run_code(asm, 0xdeadbeef, ctx_init)

        # TODO: Compare mm/xmm registers when comparing contexts.
        # cmp_result = self._compare_contexts(ctx_init, x86_ctx_out, reil_ctx_out)

        # if not cmp_result:
        #     self._save_failing_context(ctx_init)

        # self.assertTrue(cmp_result, self._print_contexts(ctx_init, x86_ctx_out, reil_ctx_out))

        self.assertEquals(reil_ctx_out["rax"], res)
        self.assertEquals(reil_ctx_out["mm0"], ctx_init["mm0"])

    def test_movq_3(self):
        # MOVQ xmm, r/m64
        asm = ["movq xmm0, rax"]

        ctx_init = self._init_context()

        ctx_init["xmm0"] = 0x12345678123456781234567812345678
        ctx_init["rax"] = 0x8765432187654321

        res = 0x00000000000000008765432187654321

        x86_ctx_out, reil_ctx_out = self._run_code(asm, 0xdeadbeef, ctx_init)

        # TODO: Compare mm/xmm registers when comparing contexts.
        # cmp_result = self._compare_contexts(ctx_init, x86_ctx_out, reil_ctx_out)

        # if not cmp_result:
        #     self._save_failing_context(ctx_init)

        # self.assertTrue(cmp_result, self._print_contexts(ctx_init, x86_ctx_out, reil_ctx_out))

        self.assertEquals(reil_ctx_out["xmm0"], res)
        self.assertEquals(reil_ctx_out["rax"], ctx_init["rax"])

    def test_movq_4(self):
        # MOVQ r/m64, xmm
        asm = ["movq rax, xmm0"]

        ctx_init = self._init_context()

        ctx_init["xmm0"] = 0x12345678123456781234567812345678
        ctx_init["rax"] = 0x8765432187654321

        res = 0x1234567812345678

        x86_ctx_out, reil_ctx_out = self._run_code(asm, 0xdeadbeef, ctx_init)

        # TODO: Compare mm/xmm registers when comparing contexts.
        # cmp_result = self._compare_contexts(ctx_init, x86_ctx_out, reil_ctx_out)

        # if not cmp_result:
        #     self._save_failing_context(ctx_init)

        # self.assertTrue(cmp_result, self._print_contexts(ctx_init, x86_ctx_out, reil_ctx_out))

        self.assertEquals(reil_ctx_out["rax"], res)
        self.assertEquals(reil_ctx_out["xmm0"], ctx_init["xmm0"])

    def test_movsd_sse(self):
        # TODO: Implement.
        pass

    def test_pcmpeqb(self):
        asm = ["pcmpeqb xmm0, xmm1"]

        ctx_init = self._init_context()

        ctx_init["xmm0"] = 0x11145178113156181231517111345618
        ctx_init["xmm1"] = 0x12345678123456781234567812345678

        res = 0x000000ff0000ff00ff00000000ffff00

        x86_ctx_out, reil_ctx_out = self._run_code(asm, 0xdeadbeef, ctx_init)

        # TODO: Compare mm/xmm registers when comparing contexts.
        # cmp_result = self._compare_contexts(ctx_init, x86_ctx_out, reil_ctx_out)

        # if not cmp_result:
        #     self._save_failing_context(ctx_init)

        # self.assertTrue(cmp_result, self._print_contexts(ctx_init, x86_ctx_out, reil_ctx_out))

        self.assertEquals(reil_ctx_out["xmm0"], res)
        self.assertEquals(reil_ctx_out["xmm1"], ctx_init["xmm1"])

    def test_pminub(self):
        asm = ["pminub xmm0, xmm1"]

        ctx_init = self._init_context()

        ctx_init["xmm0"] = 0x88776655443322118877665544332211
        ctx_init["xmm1"] = 0x992277aa113311FF992277aa113311FF
        res = 0x88226655113311118822665511331111

        x86_ctx_out, reil_ctx_out = self._run_code(asm, 0xdeadbeef, ctx_init)

        # # NOTE Hack to be able to test this instr (src oprnd should be a memory
        # # operand instead of a xmm register).
        # # -------------------------------------------------------------------- #
        # address = 0xdeadbeef
        # reil_instrs = self._asm_to_reil(asm, address)
        # reil_ctx_out, _ = self.reil_emulator.execute(reil_instrs, start=address << 8, registers=ctx_init)
        # # -------------------------------------------------------------------- #

        # TODO: Compare mm/xmm registers when comparing contexts.
        # cmp_result = self._compare_contexts(ctx_init, x86_ctx_out, reil_ctx_out)

        # if not cmp_result:
        #     self._save_failing_context(ctx_init)

        # self.assertTrue(cmp_result, self._print_contexts(ctx_init, x86_ctx_out, reil_ctx_out))

        self.assertEquals(reil_ctx_out["xmm0"], res)
        self.assertEquals(reil_ctx_out["xmm1"], ctx_init["xmm1"])

    def test_pmovmskb(self):
        asm = ["pmovmskb eax, xmm0"]

        ctx_init = self._init_context()

        ctx_init["xmm0"] = 0x12345678123456781274861892345698

        res = 0x29  # 00101001b

        x86_ctx_out, reil_ctx_out = self._run_code(asm, 0xdeadbeef, ctx_init)

        # TODO: Compare mm/xmm registers when comparing contexts.
        # cmp_result = self._compare_contexts(ctx_init, x86_ctx_out, reil_ctx_out)

        # if not cmp_result:
        #     self._save_failing_context(ctx_init)

        # self.assertTrue(cmp_result, self._print_contexts(ctx_init, x86_ctx_out, reil_ctx_out))

        self.assertEquals(reil_ctx_out["rax"] & 0xffffffff, res)

    def test_por_1(self):
        asm = ["por mm0, mm1"]

        ctx_init = self._init_context()

        ctx_init["mm0"] = 0x1234567812345678
        ctx_init["mm1"] = 0x8765432187654321

        res = ctx_init["mm0"] | ctx_init["mm1"]

        x86_ctx_out, reil_ctx_out = self._run_code(asm, 0xdeadbeef, ctx_init)

        # TODO: Compare mm/xmm registers when comparing contexts.
        # cmp_result = self._compare_contexts(ctx_init, x86_ctx_out, reil_ctx_out)

        # if not cmp_result:
        #     self._save_failing_context(ctx_init)

        # self.assertTrue(cmp_result, self._print_contexts(ctx_init, x86_ctx_out, reil_ctx_out))

        self.assertEquals(reil_ctx_out["mm0"], res)
        self.assertEquals(reil_ctx_out["mm1"], ctx_init["mm1"])

    def test_por_2(self):
        asm = ["por xmm0, xmm1"]

        ctx_init = self._init_context()

        ctx_init["xmm0"] = 0x12345678123456781234567812345678
        ctx_init["xmm1"] = 0x87654321876543218765432187654321

        res = ctx_init["xmm0"] | ctx_init["xmm1"]

        x86_ctx_out, reil_ctx_out = self._run_code(asm, 0xdeadbeef, ctx_init)

        # TODO: Compare mm/xmm registers when comparing contexts.
        # cmp_result = self._compare_contexts(ctx_init, x86_ctx_out, reil_ctx_out)

        # if not cmp_result:
        #     self._save_failing_context(ctx_init)

        # self.assertTrue(cmp_result, self._print_contexts(ctx_init, x86_ctx_out, reil_ctx_out))

        self.assertEquals(reil_ctx_out["xmm0"], res)
        self.assertEquals(reil_ctx_out["xmm1"], ctx_init["xmm1"])

    def test_pshufd(self):
        asm = ["pshufd xmm0, xmm1, 0x93"]

        # 10010011
        ctx_init = self._init_context()

        ctx_init["xmm0"] = 0x00000000000000000000000000000000
        ctx_init["xmm1"] = 0x44444444333333332222222211111111

        res = 0x33333333222222221111111144444444

        x86_ctx_out, reil_ctx_out = self._run_code(asm, 0xdeadbeef, ctx_init)

        # # NOTE Hack to be able to test this instr (src oprnd should be a memory
        # # operand instead of a xmm register).
        # # -------------------------------------------------------------------- #
        # address = 0xdeadbeef
        # reil_instrs = self._asm_to_reil(asm, address)
        # reil_ctx_out, _ = self.reil_emulator.execute(reil_instrs, start=address << 8, registers=ctx_init)
        # # -------------------------------------------------------------------- #

        # TODO: Compare mm/xmm registers when comparing contexts.
        # cmp_result = self._compare_contexts(ctx_init, x86_ctx_out, reil_ctx_out)

        # if not cmp_result:
        #     self._save_failing_context(ctx_init)

        # self.assertTrue(cmp_result, self._print_contexts(ctx_init, x86_ctx_out, reil_ctx_out))

        self.assertEquals(reil_ctx_out["xmm0"], res)
        self.assertEquals(reil_ctx_out["xmm1"], ctx_init["xmm1"])

    def test_pslldq_1(self):
        asm = ["pslldq xmm0, 7"]

        ctx_init = self._init_context()

        ctx_init["xmm0"] = 0x12345678123456781274861892345698

        res = 0x78127486189234569800000000000000

        x86_ctx_out, reil_ctx_out = self._run_code(asm, 0xdeadbeef, ctx_init)

        # TODO: Compare mm/xmm registers when comparing contexts.
        # cmp_result = self._compare_contexts(ctx_init, x86_ctx_out, reil_ctx_out)

        # if not cmp_result:
        #     self._save_failing_context(ctx_init)

        # self.assertTrue(cmp_result, self._print_contexts(ctx_init, x86_ctx_out, reil_ctx_out))

        self.assertEquals(reil_ctx_out["xmm0"], res)

    def test_pslldq_2(self):
        asm = ["pslldq xmm0, 16"]

        ctx_init = self._init_context()

        ctx_init["xmm0"] = 0x12345678123456781274861892345698

        res = 0x00000000000000000000000000000000

        x86_ctx_out, reil_ctx_out = self._run_code(asm, 0xdeadbeef, ctx_init)

        # TODO: Compare mm/xmm registers when comparing contexts.
        # cmp_result = self._compare_contexts(ctx_init, x86_ctx_out, reil_ctx_out)

        # if not cmp_result:
        #     self._save_failing_context(ctx_init)

        # self.assertTrue(cmp_result, self._print_contexts(ctx_init, x86_ctx_out, reil_ctx_out))

        self.assertEquals(reil_ctx_out["xmm0"], res)

    def test_psrldq_1(self):
        asm = ["psrldq xmm0, 7"]

        ctx_init = self._init_context()

        ctx_init["xmm0"] = 0x12345678123456781234567812345678

        res = 0x00000000000000123456781234567812

        x86_ctx_out, reil_ctx_out = self._run_code(asm, 0xdeadbeef, ctx_init)

        # TODO: Compare mm/xmm registers when comparing contexts.
        # cmp_result = self._compare_contexts(ctx_init, x86_ctx_out, reil_ctx_out)

        # if not cmp_result:
        #     self._save_failing_context(ctx_init)

        # self.assertTrue(cmp_result, self._print_contexts(ctx_init, x86_ctx_out, reil_ctx_out))

        self.assertEquals(reil_ctx_out["xmm0"], res)

    def test_psrldq_2(self):
        asm = ["psrldq xmm0, 16"]

        ctx_init = self._init_context()

        ctx_init["xmm0"] = 0x12345678123456781274861892345698

        res = 0x00000000000000000000000000000000

        x86_ctx_out, reil_ctx_out = self._run_code(asm, 0xdeadbeef, ctx_init)

        # TODO: Compare mm/xmm registers when comparing contexts.
        # cmp_result = self._compare_contexts(ctx_init, x86_ctx_out, reil_ctx_out)

        # if not cmp_result:
        #     self._save_failing_context(ctx_init)

        # self.assertTrue(cmp_result, self._print_contexts(ctx_init, x86_ctx_out, reil_ctx_out))

        self.assertEquals(reil_ctx_out["xmm0"], res)

    def test_psubb(self):
        asm = ["psubb xmm0, xmm1"]

        ctx_init = self._init_context()

        ctx_init["xmm0"] = 0x11145178113156181231517111345618
        ctx_init["xmm1"] = 0x12345678123456781234567812345678
        res = 0xffe0fb00fffd00a000fdfbf9ff0000a0

        x86_ctx_out, reil_ctx_out = self._run_code(asm, 0xdeadbeef, ctx_init)

        # TODO: Compare mm/xmm registers when comparing contexts.
        # cmp_result = self._compare_contexts(ctx_init, x86_ctx_out, reil_ctx_out)

        # if not cmp_result:
        #     self._save_failing_context(ctx_init)

        # self.assertTrue(cmp_result, self._print_contexts(ctx_init, x86_ctx_out, reil_ctx_out))

        self.assertEquals(reil_ctx_out["xmm0"], res)
        self.assertEquals(reil_ctx_out["xmm1"], ctx_init["xmm1"])

    def test_punpcklbw(self):
        asm = ["punpcklbw xmm0, xmm1"]

        ctx_init = self._init_context()

        ctx_init["xmm0"] = 0x88776655443322118877665544332211
        ctx_init["xmm1"] = 0xffeeddccbbaa9988ffeeddccbbaa9988

        res = 0xff88ee77dd66cc55bb44aa3399228811

        x86_ctx_out, reil_ctx_out = self._run_code(asm, 0xdeadbeef, ctx_init)

        # # NOTE Hack to be able to test this instr (src oprnd should be a memory
        # # operand instead of a xmm register).
        # # -------------------------------------------------------------------- #
        # address = 0xdeadbeef
        # reil_instrs = self._asm_to_reil(asm, address)
        # reil_ctx_out, _ = self.reil_emulator.execute(reil_instrs, start=address << 8, registers=ctx_init)
        # # -------------------------------------------------------------------- #

        # TODO: Compare mm/xmm registers when comparing contexts.
        # cmp_result = self._compare_contexts(ctx_init, x86_ctx_out, reil_ctx_out)

        # if not cmp_result:
        #     self._save_failing_context(ctx_init)

        # self.assertTrue(cmp_result, self._print_contexts(ctx_init, x86_ctx_out, reil_ctx_out))

        self.assertEquals(reil_ctx_out["xmm0"], res)
        self.assertEquals(reil_ctx_out["xmm1"], ctx_init["xmm1"])

    def test_punpcklqdq(self):
        asm = ["punpcklqdq xmm0, xmm1"]

        ctx_init = self._init_context()

        ctx_init["xmm0"] = 0x55555555555555551111111111111111
        ctx_init["xmm1"] = 0x44444444444444448888888888888888

        res = 0x88888888888888881111111111111111

        x86_ctx_out, reil_ctx_out = self._run_code(asm, 0xdeadbeef, ctx_init)

        # # NOTE Hack to be able to test this instr (src oprnd should be a memory
        # # operand instead of a xmm register).
        # # -------------------------------------------------------------------- #
        # address = 0xdeadbeef
        # reil_instrs = self._asm_to_reil(asm, address)
        # reil_ctx_out, _ = self.reil_emulator.execute(reil_instrs, start=address << 8, registers=ctx_init)
        # # -------------------------------------------------------------------- #

        # TODO: Compare mm/xmm registers when comparing contexts.
        # cmp_result = self._compare_contexts(ctx_init, x86_ctx_out, reil_ctx_out)

        # if not cmp_result:
        #     self._save_failing_context(ctx_init)

        # self.assertTrue(cmp_result, self._print_contexts(ctx_init, x86_ctx_out, reil_ctx_out))

        self.assertEquals(reil_ctx_out["xmm0"], res)
        self.assertEquals(reil_ctx_out["xmm1"], ctx_init["xmm1"])

    def test_punpcklwd(self):
        asm = ["punpcklwd xmm0, xmm1"]

        ctx_init = self._init_context()

        ctx_init["xmm0"] = 0x88887777666655554444333322221111
        ctx_init["xmm1"] = 0x11112222333344445555666677778888

        res = 0x55554444666633337777222288881111

        x86_ctx_out, reil_ctx_out = self._run_code(asm, 0xdeadbeef, ctx_init)

        # # NOTE Hack to be able to test this instr (src oprnd should be a memory
        # # operand instead of a xmm register).
        # # -------------------------------------------------------------------- #
        # address = 0xdeadbeef
        # reil_instrs = self._asm_to_reil(asm, address)
        # reil_ctx_out, _ = self.reil_emulator.execute(reil_instrs, start=address << 8, registers=ctx_init)
        # # -------------------------------------------------------------------- #

        # TODO: Compare mm/xmm registers when comparing contexts.
        # cmp_result = self._compare_contexts(ctx_init, x86_ctx_out, reil_ctx_out)

        # if not cmp_result:
        #     self._save_failing_context(ctx_init)

        # self.assertTrue(cmp_result, self._print_contexts(ctx_init, x86_ctx_out, reil_ctx_out))

        self.assertEquals(reil_ctx_out["xmm0"], res)
        self.assertEquals(reil_ctx_out["xmm1"], ctx_init["xmm1"])

    def test_pxor(self):
        # TODO: Implement.
        pass

    def test_vmovdqa(self):
        # TODO: Implement.
        pass
