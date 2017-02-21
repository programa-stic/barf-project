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

import os
import pickle
import platform
import random
import unittest

import pyasmjit

from barf.arch import ARCH_X86_MODE_64
from barf.arch.x86.x86base import X86ArchitectureInformation
from barf.arch.x86.x86parser import X86Parser
from barf.arch.x86.x86translator import FULL_TRANSLATION
from barf.arch.x86.x86translator import X86Translator
from barf.core.reil import ReilContainer
from barf.core.reil import ReilEmulator
from barf.core.reil import ReilSequence


@unittest.skipUnless(platform.machine().lower() == 'x86_64',
                     'Not running on an x86_64 system')
class X86TranslationTests(unittest.TestCase):

    def setUp(self):
        self.arch_mode = ARCH_X86_MODE_64

        self.arch_info = X86ArchitectureInformation(self.arch_mode)

        self.x86_parser = X86Parser(self.arch_mode)
        self.x86_translator = X86Translator(self.arch_mode, FULL_TRANSLATION)
        self.reil_emulator = ReilEmulator(self.arch_info)

        self.context_filename = "failing_context.data"

    def test_movq_1(self):
        # MOVQ mm, r/m64
        asm = ["movq mm0, rax"]

        ctx_init = self.__init_context()

        ctx_init["mm0"] = 0x1234567812345678
        ctx_init["rax"] = 0x8765432187654321

        res = 0x8765432187654321

        x86_ctx_out, reil_ctx_out = self.__run_code(asm, 0xdeadbeef, ctx_init)

        # TODO Fix.
        # cmp_result = self.__compare_contexts(ctx_init, x86_ctx_out, reil_ctx_out)

        # if not cmp_result:
        #     self.__save_failing_context(ctx_init)

        # self.assertTrue(cmp_result, self.__print_contexts(ctx_init, x86_ctx_out, reil_ctx_out))

        self.assertEquals(reil_ctx_out["mm0"], res)
        self.assertEquals(reil_ctx_out["rax"], ctx_init["rax"])

    def test_movq_2(self):
        # MOVQ r/m64, mm
        asm = ["movq rax, mm0"]

        ctx_init = self.__init_context()

        ctx_init["mm0"] = 0x1234567812345678
        ctx_init["rax"] = 0x8765432187654321

        res = 0x1234567812345678

        x86_ctx_out, reil_ctx_out = self.__run_code(asm, 0xdeadbeef, ctx_init)

        # TODO Fix.
        # cmp_result = self.__compare_contexts(ctx_init, x86_ctx_out, reil_ctx_out)

        # if not cmp_result:
        #     self.__save_failing_context(ctx_init)

        # self.assertTrue(cmp_result, self.__print_contexts(ctx_init, x86_ctx_out, reil_ctx_out))

        self.assertEquals(reil_ctx_out["rax"], res)
        self.assertEquals(reil_ctx_out["mm0"], ctx_init["mm0"])

    def test_movq_3(self):
        # MOVQ xmm, r/m64
        asm = ["movq xmm0, rax"]

        ctx_init = self.__init_context()

        ctx_init["xmm0"] = 0x12345678123456781234567812345678
        ctx_init["rax"] = 0x8765432187654321

        res = 0x00000000000000008765432187654321

        x86_ctx_out, reil_ctx_out = self.__run_code(asm, 0xdeadbeef, ctx_init)

        # TODO Fix.
        # cmp_result = self.__compare_contexts(ctx_init, x86_ctx_out, reil_ctx_out)

        # if not cmp_result:
        #     self.__save_failing_context(ctx_init)

        # self.assertTrue(cmp_result, self.__print_contexts(ctx_init, x86_ctx_out, reil_ctx_out))

        self.assertEquals(reil_ctx_out["xmm0"], res)
        self.assertEquals(reil_ctx_out["rax"], ctx_init["rax"])

    def test_movq_4(self):
        # MOVQ r/m64, xmm
        asm = ["movq rax, xmm0"]

        ctx_init = self.__init_context()

        ctx_init["xmm0"] = 0x12345678123456781234567812345678
        ctx_init["rax"] = 0x8765432187654321

        res = 0x1234567812345678

        x86_ctx_out, reil_ctx_out = self.__run_code(asm, 0xdeadbeef, ctx_init)

        # TODO Fix.
        # cmp_result = self.__compare_contexts(ctx_init, x86_ctx_out, reil_ctx_out)

        # if not cmp_result:
        #     self.__save_failing_context(ctx_init)

        # self.assertTrue(cmp_result, self.__print_contexts(ctx_init, x86_ctx_out, reil_ctx_out))

        self.assertEquals(reil_ctx_out["rax"], res)
        self.assertEquals(reil_ctx_out["xmm0"], ctx_init["xmm0"])

    def test_movd_1(self):
        # MOVD mm, r/m32
        asm = ["movd mm0, eax"]

        ctx_init = self.__init_context()

        ctx_init["mm0"] = 0x1234567812345678
        ctx_init["rax"] = 0xffffffff87654321

        res = 0x0000000087654321

        x86_ctx_out, reil_ctx_out = self.__run_code(asm, 0xdeadbeef, ctx_init)

        # TODO Fix.
        # cmp_result = self.__compare_contexts(ctx_init, x86_ctx_out, reil_ctx_out)

        # if not cmp_result:
        #     self.__save_failing_context(ctx_init)

        # self.assertTrue(cmp_result, self.__print_contexts(ctx_init, x86_ctx_out, reil_ctx_out))

        self.assertEquals(reil_ctx_out["mm0"], res)
        self.assertEquals(reil_ctx_out["rax"], ctx_init["rax"])

    def test_movd_2(self):
        # MOVD r/m32, mm
        asm = ["movd eax, mm0"]

        ctx_init = self.__init_context()

        ctx_init["mm0"] = 0x1234567812345678
        ctx_init["rax"] = 0xffffffff87654321

        res = 0x0000000012345678

        x86_ctx_out, reil_ctx_out = self.__run_code(asm, 0xdeadbeef, ctx_init)

        # TODO Fix.
        # cmp_result = self.__compare_contexts(ctx_init, x86_ctx_out, reil_ctx_out)

        # if not cmp_result:
        #     self.__save_failing_context(ctx_init)

        # self.assertTrue(cmp_result, self.__print_contexts(ctx_init, x86_ctx_out, reil_ctx_out))

        self.assertEquals(reil_ctx_out["rax"], res)
        self.assertEquals(reil_ctx_out["mm0"], ctx_init["mm0"])

    def test_movd_3(self):
        # MOVD xmm, r/m32
        asm = ["movd xmm0, eax"]

        ctx_init = self.__init_context()

        ctx_init["xmm0"] = 0x12345678123456781234567812345678
        ctx_init["rax"] = 0xffffffff87654321

        res = 0x00000000000000000000000087654321

        x86_ctx_out, reil_ctx_out = self.__run_code(asm, 0xdeadbeef, ctx_init)

        # TODO Fix.
        # cmp_result = self.__compare_contexts(ctx_init, x86_ctx_out, reil_ctx_out)

        # if not cmp_result:
        #     self.__save_failing_context(ctx_init)

        # self.assertTrue(cmp_result, self.__print_contexts(ctx_init, x86_ctx_out, reil_ctx_out))

        self.assertEquals(reil_ctx_out["xmm0"], res)
        self.assertEquals(reil_ctx_out["rax"], ctx_init["rax"])

    def test_movd_4(self):
        # MOVD r/m32, xmm
        asm = ["movd eax, xmm0"]

        ctx_init = self.__init_context()

        ctx_init["xmm0"] = 0x12345678123456781234567812345678
        ctx_init["rax"] = 0xffffffff87654321

        res = 0x0000000012345678

        x86_ctx_out, reil_ctx_out = self.__run_code(asm, 0xdeadbeef, ctx_init)

        # TODO Fix.
        # cmp_result = self.__compare_contexts(ctx_init, x86_ctx_out, reil_ctx_out)

        # if not cmp_result:
        #     self.__save_failing_context(ctx_init)

        # self.assertTrue(cmp_result, self.__print_contexts(ctx_init, x86_ctx_out, reil_ctx_out))

        self.assertEquals(reil_ctx_out["rax"], res)
        self.assertEquals(reil_ctx_out["xmm0"], ctx_init["xmm0"])

    def test_por_1(self):
        asm = ["por mm0, mm1"]

        ctx_init = self.__init_context()

        ctx_init["mm0"] = 0x1234567812345678
        ctx_init["mm1"] = 0x8765432187654321

        res = ctx_init["mm0"] | ctx_init["mm1"]

        x86_ctx_out, reil_ctx_out = self.__run_code(asm, 0xdeadbeef, ctx_init)

        # TODO Fix.
        # cmp_result = self.__compare_contexts(ctx_init, x86_ctx_out, reil_ctx_out)

        # if not cmp_result:
        #     self.__save_failing_context(ctx_init)

        # self.assertTrue(cmp_result, self.__print_contexts(ctx_init, x86_ctx_out, reil_ctx_out))

        self.assertEquals(reil_ctx_out["mm0"], res)
        self.assertEquals(reil_ctx_out["mm1"], ctx_init["mm1"])

    def test_por_2(self):
        asm = ["por xmm0, xmm1"]

        ctx_init = self.__init_context()

        ctx_init["xmm0"] = 0x12345678123456781234567812345678
        ctx_init["xmm1"] = 0x87654321876543218765432187654321

        res = ctx_init["xmm0"] | ctx_init["xmm1"]

        x86_ctx_out, reil_ctx_out = self.__run_code(asm, 0xdeadbeef, ctx_init)

        # TODO Fix.
        # cmp_result = self.__compare_contexts(ctx_init, x86_ctx_out, reil_ctx_out)

        # if not cmp_result:
        #     self.__save_failing_context(ctx_init)

        # self.assertTrue(cmp_result, self.__print_contexts(ctx_init, x86_ctx_out, reil_ctx_out))

        self.assertEquals(reil_ctx_out["xmm0"], res)
        self.assertEquals(reil_ctx_out["xmm1"], ctx_init["xmm1"])

    def test_psubb(self):
        asm = ["psubb xmm0, xmm1"]

        ctx_init = self.__init_context()

        ctx_init["xmm0"] = 0x11145178113156181231517111345618
        ctx_init["xmm1"] = 0x12345678123456781234567812345678
        res = 0xffe0fb00fffd00a000fdfbf9ff0000a0

        x86_ctx_out, reil_ctx_out = self.__run_code(asm, 0xdeadbeef, ctx_init)

        # TODO Fix.
        # cmp_result = self.__compare_contexts(ctx_init, x86_ctx_out, reil_ctx_out)

        # if not cmp_result:
        #     self.__save_failing_context(ctx_init)

        # self.assertTrue(cmp_result, self.__print_contexts(ctx_init, x86_ctx_out, reil_ctx_out))

        self.assertEquals(reil_ctx_out["xmm0"], res)
        self.assertEquals(reil_ctx_out["xmm1"], ctx_init["xmm1"])

    def test_pslldq_1(self):
        asm = ["pslldq xmm0, 7"]

        ctx_init = self.__init_context()

        ctx_init["xmm0"] = 0x12345678123456781274861892345698

        res = 0x78127486189234569800000000000000

        x86_ctx_out, reil_ctx_out = self.__run_code(asm, 0xdeadbeef, ctx_init)

        # TODO Fix.
        # cmp_result = self.__compare_contexts(ctx_init, x86_ctx_out, reil_ctx_out)

        # if not cmp_result:
        #     self.__save_failing_context(ctx_init)

        # self.assertTrue(cmp_result, self.__print_contexts(ctx_init, x86_ctx_out, reil_ctx_out))

        self.assertEquals(reil_ctx_out["xmm0"], res)

    def test_pslldq_2(self):
        asm = ["pslldq xmm0, 16"]

        ctx_init = self.__init_context()

        ctx_init["xmm0"] = 0x12345678123456781274861892345698

        res = 0x00000000000000000000000000000000

        x86_ctx_out, reil_ctx_out = self.__run_code(asm, 0xdeadbeef, ctx_init)

        # TODO Fix.
        # cmp_result = self.__compare_contexts(ctx_init, x86_ctx_out, reil_ctx_out)

        # if not cmp_result:
        #     self.__save_failing_context(ctx_init)

        # self.assertTrue(cmp_result, self.__print_contexts(ctx_init, x86_ctx_out, reil_ctx_out))

        self.assertEquals(reil_ctx_out["xmm0"], res)

    def test_psrldq_1(self):
        asm = ["psrldq xmm0, 7"]

        ctx_init = self.__init_context()

        ctx_init["xmm0"] = 0x12345678123456781234567812345678

        res = 0x00000000000000123456781234567812

        x86_ctx_out, reil_ctx_out = self.__run_code(asm, 0xdeadbeef, ctx_init)

        # TODO Fix.
        # cmp_result = self.__compare_contexts(ctx_init, x86_ctx_out, reil_ctx_out)

        # if not cmp_result:
        #     self.__save_failing_context(ctx_init)

        # self.assertTrue(cmp_result, self.__print_contexts(ctx_init, x86_ctx_out, reil_ctx_out))

        self.assertEquals(reil_ctx_out["xmm0"], res)

    def test_psrldq_2(self):
        asm = ["psrldq xmm0, 16"]

        ctx_init = self.__init_context()

        ctx_init["xmm0"] = 0x12345678123456781274861892345698

        res = 0x00000000000000000000000000000000

        x86_ctx_out, reil_ctx_out = self.__run_code(asm, 0xdeadbeef, ctx_init)

        # TODO Fix.
        # cmp_result = self.__compare_contexts(ctx_init, x86_ctx_out, reil_ctx_out)

        # if not cmp_result:
        #     self.__save_failing_context(ctx_init)

        # self.assertTrue(cmp_result, self.__print_contexts(ctx_init, x86_ctx_out, reil_ctx_out))

        self.assertEquals(reil_ctx_out["xmm0"], res)

    def test_movhpd(self):
        asm = ["movhpd xmm0, xmm1"]

        ctx_init = self.__init_context()

        ctx_init["xmm0"] = 0x12345678123456781234567812345678
        ctx_init["xmm1"] = 0x87654321876543218765432187654321

        res = 0x87654321876543211234567812345678

        # x86_ctx_out, reil_ctx_out = self.__run_code(asm, 0xdeadbeef, ctx_init)

        # NOTE Hack to be able to test this instr (src oprnd should be a memory
        # operand instead of a xmm register).
        # -------------------------------------------------------------------- #
        address = 0xdeadbeef
        reil_instrs = self.__asm_to_reil(asm, address)
        reil_ctx_out, _ = self.reil_emulator.execute(reil_instrs, start=address << 8, registers=ctx_init)
        # -------------------------------------------------------------------- #

        # TODO Fix.
        # cmp_result = self.__compare_contexts(ctx_init, x86_ctx_out, reil_ctx_out)

        # if not cmp_result:
        #     self.__save_failing_context(ctx_init)

        # self.assertTrue(cmp_result, self.__print_contexts(ctx_init, x86_ctx_out, reil_ctx_out))

        self.assertEquals(reil_ctx_out["xmm0"], res)
        self.assertEquals(reil_ctx_out["xmm1"], ctx_init["xmm1"])

    def test_movlpd(self):
        asm = ["movlpd xmm0, xmm1"]

        ctx_init = self.__init_context()

        ctx_init["xmm0"] = 0x12345678123456781234567812345678
        ctx_init["xmm1"] = 0x87654321876543218765432187654321

        res = 0x12345678123456788765432187654321

        # x86_ctx_out, reil_ctx_out = self.__run_code(asm, 0xdeadbeef, ctx_init)

        # NOTE Hack to be able to test this instr (src oprnd should be a memory
        # operand instead of a xmm register).
        # -------------------------------------------------------------------- #
        address = 0xdeadbeef
        reil_instrs = self.__asm_to_reil(asm, address)
        reil_ctx_out, _ = self.reil_emulator.execute(reil_instrs, start=address << 8, registers=ctx_init)
        # -------------------------------------------------------------------- #

        # TODO Fix.
        # cmp_result = self.__compare_contexts(ctx_init, x86_ctx_out, reil_ctx_out)

        # if not cmp_result:
        #     self.__save_failing_context(ctx_init)

        # self.assertTrue(cmp_result, self.__print_contexts(ctx_init, x86_ctx_out, reil_ctx_out))

        self.assertEquals(reil_ctx_out["xmm0"], res)
        self.assertEquals(reil_ctx_out["xmm1"], ctx_init["xmm1"])

    def test_punpcklbw(self):
        asm = ["punpcklbw xmm0, xmm1"]

        ctx_init = self.__init_context()

        ctx_init["xmm0"] = 0x88776655443322118877665544332211
        ctx_init["xmm1"] = 0xffeeddccbbaa9988ffeeddccbbaa9988

        res = 0xff88ee77dd66cc55bb44aa3399228811

        x86_ctx_out, reil_ctx_out = self.__run_code(asm, 0xdeadbeef, ctx_init)

        # # NOTE Hack to be able to test this instr (src oprnd should be a memory
        # # operand instead of a xmm register).
        # # -------------------------------------------------------------------- #
        # address = 0xdeadbeef
        # reil_instrs = self.__asm_to_reil(asm, address)
        # reil_ctx_out, _ = self.reil_emulator.execute(reil_instrs, start=address << 8, registers=ctx_init)
        # # -------------------------------------------------------------------- #

        # TODO Fix.
        # cmp_result = self.__compare_contexts(ctx_init, x86_ctx_out, reil_ctx_out)

        # if not cmp_result:
        #     self.__save_failing_context(ctx_init)

        # self.assertTrue(cmp_result, self.__print_contexts(ctx_init, x86_ctx_out, reil_ctx_out))

        self.assertEquals(reil_ctx_out["xmm0"], res)
        self.assertEquals(reil_ctx_out["xmm1"], ctx_init["xmm1"])

    def test_punpcklwd(self):
        asm = ["punpcklwd xmm0, xmm1"]

        ctx_init = self.__init_context()

        ctx_init["xmm0"] = 0x88887777666655554444333322221111
        ctx_init["xmm1"] = 0x11112222333344445555666677778888

        res = 0x55554444666633337777222288881111

        x86_ctx_out, reil_ctx_out = self.__run_code(asm, 0xdeadbeef, ctx_init)

        # # NOTE Hack to be able to test this instr (src oprnd should be a memory
        # # operand instead of a xmm register).
        # # -------------------------------------------------------------------- #
        # address = 0xdeadbeef
        # reil_instrs = self.__asm_to_reil(asm, address)
        # reil_ctx_out, _ = self.reil_emulator.execute(reil_instrs, start=address << 8, registers=ctx_init)
        # # -------------------------------------------------------------------- #

        # TODO Fix.
        # cmp_result = self.__compare_contexts(ctx_init, x86_ctx_out, reil_ctx_out)

        # if not cmp_result:
        #     self.__save_failing_context(ctx_init)

        # self.assertTrue(cmp_result, self.__print_contexts(ctx_init, x86_ctx_out, reil_ctx_out))

        self.assertEquals(reil_ctx_out["xmm0"], res)
        self.assertEquals(reil_ctx_out["xmm1"], ctx_init["xmm1"])

    def test_pshufd(self):
        asm = ["pshufd xmm0, xmm1, 0x93"]

        # 10010011
        ctx_init = self.__init_context()

        ctx_init["xmm0"] = 0x00000000000000000000000000000000
        ctx_init["xmm1"] = 0x44444444333333332222222211111111

        res = 0x33333333222222221111111144444444

        x86_ctx_out, reil_ctx_out = self.__run_code(asm, 0xdeadbeef, ctx_init)

        # # NOTE Hack to be able to test this instr (src oprnd should be a memory
        # # operand instead of a xmm register).
        # # -------------------------------------------------------------------- #
        # address = 0xdeadbeef
        # reil_instrs = self.__asm_to_reil(asm, address)
        # reil_ctx_out, _ = self.reil_emulator.execute(reil_instrs, start=address << 8, registers=ctx_init)
        # # -------------------------------------------------------------------- #

        # TODO Fix.
        # cmp_result = self.__compare_contexts(ctx_init, x86_ctx_out, reil_ctx_out)

        # if not cmp_result:
        #     self.__save_failing_context(ctx_init)

        # self.assertTrue(cmp_result, self.__print_contexts(ctx_init, x86_ctx_out, reil_ctx_out))

        self.assertEquals(reil_ctx_out["xmm0"], res)
        self.assertEquals(reil_ctx_out["xmm1"], ctx_init["xmm1"])

    def test_pminub(self):
        asm = ["pminub xmm0, xmm1"]

        ctx_init = self.__init_context()

        ctx_init["xmm0"] = 0x88776655443322118877665544332211
        ctx_init["xmm1"] = 0x992277aa113311FF992277aa113311FF
        res              = 0x88226655113311118822665511331111

        x86_ctx_out, reil_ctx_out = self.__run_code(asm, 0xdeadbeef, ctx_init)

        # # NOTE Hack to be able to test this instr (src oprnd should be a memory
        # # operand instead of a xmm register).
        # # -------------------------------------------------------------------- #
        # address = 0xdeadbeef
        # reil_instrs = self.__asm_to_reil(asm, address)
        # reil_ctx_out, _ = self.reil_emulator.execute(reil_instrs, start=address << 8, registers=ctx_init)
        # # -------------------------------------------------------------------- #

        # TODO Fix.
        # cmp_result = self.__compare_contexts(ctx_init, x86_ctx_out, reil_ctx_out)

        # if not cmp_result:
        #     self.__save_failing_context(ctx_init)

        # self.assertTrue(cmp_result, self.__print_contexts(ctx_init, x86_ctx_out, reil_ctx_out))

        self.assertEquals(reil_ctx_out["xmm0"], res)
        self.assertEquals(reil_ctx_out["xmm1"], ctx_init["xmm1"])

    def test_pmovmskb(self):
        asm = ["pmovmskb eax, xmm0"]

        ctx_init = self.__init_context()

        ctx_init["xmm0"] = 0x12345678123456781274861892345698

        res = 0x29 # 00101001b

        x86_ctx_out, reil_ctx_out = self.__run_code(asm, 0xdeadbeef, ctx_init)

        # TODO Fix.
        # cmp_result = self.__compare_contexts(ctx_init, x86_ctx_out, reil_ctx_out)

        # if not cmp_result:
        #     self.__save_failing_context(ctx_init)

        # self.assertTrue(cmp_result, self.__print_contexts(ctx_init, x86_ctx_out, reil_ctx_out))

        self.assertEquals(reil_ctx_out["rax"] & 0xffffffff, res)

    def test_pcmpeqb(self):
        asm = ["pcmpeqb xmm0, xmm1"]

        ctx_init = self.__init_context()

        ctx_init["xmm0"] = 0x11145178113156181231517111345618
        ctx_init["xmm1"] = 0x12345678123456781234567812345678

        res = 0x000000ff0000ff00ff00000000ffff00

        x86_ctx_out, reil_ctx_out = self.__run_code(asm, 0xdeadbeef, ctx_init)

        # TODO Fix.
        # cmp_result = self.__compare_contexts(ctx_init, x86_ctx_out, reil_ctx_out)

        # if not cmp_result:
        #     self.__save_failing_context(ctx_init)

        # self.assertTrue(cmp_result, self.__print_contexts(ctx_init, x86_ctx_out, reil_ctx_out))

        self.assertEquals(reil_ctx_out["xmm0"], res)
        self.assertEquals(reil_ctx_out["xmm1"], ctx_init["xmm1"])

    def test_bsf_1(self):
        asm = ["bsf rax, rbx"]

        ctx_init = self.__init_context()

        x86_ctx_out, reil_ctx_out = self.__run_code(asm, 0xdeadbeef, ctx_init)

        cmp_result = self.__compare_contexts(ctx_init, x86_ctx_out, reil_ctx_out)

        if not cmp_result:
            self.__save_failing_context(ctx_init)

        self.assertTrue(cmp_result, self.__print_contexts(ctx_init, x86_ctx_out, reil_ctx_out))

    def test_bsf_2(self):
        asm = ["bsf rax, rbx"]

        ctx_init = self.__init_context()

        ctx_init["rbx"] = 0x0

        x86_ctx_out, reil_ctx_out = self.__run_code(asm, 0xdeadbeef, ctx_init)

        cmp_result = self.__compare_contexts(ctx_init, x86_ctx_out, reil_ctx_out)

        if not cmp_result:
            self.__save_failing_context(ctx_init)

        self.assertTrue(cmp_result, self.__print_contexts(ctx_init, x86_ctx_out, reil_ctx_out))

    def test_bswap_1(self):
        asm = ["bswap eax"]

        ctx_init = self.__init_context()

        x86_ctx_out, reil_ctx_out = self.__run_code(asm, 0xdeadbeef, ctx_init)

        cmp_result = self.__compare_contexts(ctx_init, x86_ctx_out, reil_ctx_out)

        if not cmp_result:
            self.__save_failing_context(ctx_init)

        self.assertTrue(cmp_result, self.__print_contexts(ctx_init, x86_ctx_out, reil_ctx_out))

    def test_bswap_2(self):
        asm = ["bswap rax"]

        ctx_init = self.__init_context()

        x86_ctx_out, reil_ctx_out = self.__run_code(asm, 0xdeadbeef, ctx_init)

        cmp_result = self.__compare_contexts(ctx_init, x86_ctx_out, reil_ctx_out)

        if not cmp_result:
            self.__save_failing_context(ctx_init)

        self.assertTrue(cmp_result, self.__print_contexts(ctx_init, x86_ctx_out, reil_ctx_out))

    def test_cdq(self):
        asm = ["cdq"]

        ctx_init = self.__init_context()

        x86_ctx_out, reil_ctx_out = self.__run_code(asm, 0xdeadbeef, ctx_init)

        cmp_result = self.__compare_contexts(ctx_init, x86_ctx_out, reil_ctx_out)

        if not cmp_result:
            self.__save_failing_context(ctx_init)

        self.assertTrue(cmp_result, self.__print_contexts(ctx_init, x86_ctx_out, reil_ctx_out))

    def test_cdqe(self):
        asm = ["cdqe"]

        ctx_init = self.__init_context()

        x86_ctx_out, reil_ctx_out = self.__run_code(asm, 0xdeadbeef, ctx_init)

        cmp_result = self.__compare_contexts(ctx_init, x86_ctx_out, reil_ctx_out)

        if not cmp_result:
            self.__save_failing_context(ctx_init)

        self.assertTrue(cmp_result, self.__print_contexts(ctx_init, x86_ctx_out, reil_ctx_out))

    def test_lea(self):
        asm = ["lea eax, [ebx + 0x100]"]

        ctx_init = self.__init_context()

        x86_ctx_out, reil_ctx_out = self.__run_code(asm, 0xdeadbeef, ctx_init)

        cmp_result = self.__compare_contexts(ctx_init, x86_ctx_out, reil_ctx_out)

        if not cmp_result:
            self.__save_failing_context(ctx_init)

        self.assertTrue(cmp_result, self.__print_contexts(ctx_init, x86_ctx_out, reil_ctx_out))

    def test_cld(self):
        asm = ["cld"]

        ctx_init = self.__init_context()

        x86_ctx_out, reil_ctx_out = self.__run_code(asm, 0xdeadbeef, ctx_init)

        cmp_result = self.__compare_contexts(ctx_init, x86_ctx_out, reil_ctx_out)

        if not cmp_result:
            self.__save_failing_context(ctx_init)

        self.assertTrue(cmp_result, self.__print_contexts(ctx_init, x86_ctx_out, reil_ctx_out))

    def test_clc(self):
        asm = ["clc"]

        ctx_init = self.__init_context()

        x86_ctx_out, reil_ctx_out = self.__run_code(asm, 0xdeadbeef, ctx_init)

        cmp_result = self.__compare_contexts(ctx_init, x86_ctx_out, reil_ctx_out)

        if not cmp_result:
            self.__save_failing_context(ctx_init)

        self.assertTrue(cmp_result, self.__print_contexts(ctx_init, x86_ctx_out, reil_ctx_out))

    def test_nop(self):
        asm = ["nop"]

        ctx_init = self.__init_context()

        x86_ctx_out, reil_ctx_out = self.__run_code(asm, 0xdeadbeef, ctx_init)

        cmp_result = self.__compare_contexts(ctx_init, x86_ctx_out, reil_ctx_out)

        if not cmp_result:
            self.__save_failing_context(ctx_init)

        self.assertTrue(cmp_result, self.__print_contexts(ctx_init, x86_ctx_out, reil_ctx_out))

    def test_test(self):
        asm = ["test eax, ebx"]

        ctx_init = self.__init_context()

        x86_ctx_out, reil_ctx_out = self.__run_code(asm, 0xdeadbeef, ctx_init)

        # Undefined flags...
        reil_ctx_out = self.__fix_reil_flag(reil_ctx_out, x86_ctx_out, "af")

        cmp_result = self.__compare_contexts(ctx_init, x86_ctx_out, reil_ctx_out)

        if not cmp_result:
            self.__save_failing_context(ctx_init)

        self.assertTrue(cmp_result, self.__print_contexts(ctx_init, x86_ctx_out, reil_ctx_out))

    def test_not(self):
        asm = ["not eax"]

        ctx_init = self.__init_context()

        x86_ctx_out, reil_ctx_out = self.__run_code(asm, 0xdeadbeef, ctx_init)

        cmp_result = self.__compare_contexts(ctx_init, x86_ctx_out, reil_ctx_out)

        if not cmp_result:
            self.__save_failing_context(ctx_init)

        self.assertTrue(cmp_result, self.__print_contexts(ctx_init, x86_ctx_out, reil_ctx_out))

    def test_xor(self):
        asm = ["xor eax, ebx"]

        ctx_init = self.__init_context()

        x86_ctx_out, reil_ctx_out = self.__run_code(asm, 0xdeadbeef, ctx_init)

        # Undefined flags...
        reil_ctx_out = self.__fix_reil_flag(reil_ctx_out, x86_ctx_out, "af")

        cmp_result = self.__compare_contexts(ctx_init, x86_ctx_out, reil_ctx_out)

        if not cmp_result:
            self.__save_failing_context(ctx_init)

        self.assertTrue(cmp_result, self.__print_contexts(ctx_init, x86_ctx_out, reil_ctx_out))

    def test_or(self):
        asm = ["or eax, ebx"]

        ctx_init = self.__init_context()

        x86_ctx_out, reil_ctx_out = self.__run_code(asm, 0xdeadbeef, ctx_init)

        # Undefined flags...
        reil_ctx_out = self.__fix_reil_flag(reil_ctx_out, x86_ctx_out, "af")

        cmp_result = self.__compare_contexts(ctx_init, x86_ctx_out, reil_ctx_out)

        if not cmp_result:
            self.__save_failing_context(ctx_init)

        self.assertTrue(cmp_result, self.__print_contexts(ctx_init, x86_ctx_out, reil_ctx_out))

    def test_and(self):
        asm = ["and eax, ebx"]

        ctx_init = self.__init_context()

        x86_ctx_out, reil_ctx_out = self.__run_code(asm, 0xdeadbeef, ctx_init)

        # Undefined flags...
        reil_ctx_out = self.__fix_reil_flag(reil_ctx_out, x86_ctx_out, "af")

        cmp_result = self.__compare_contexts(ctx_init, x86_ctx_out, reil_ctx_out)

        if not cmp_result:
            self.__save_failing_context(ctx_init)

        self.assertTrue(cmp_result, self.__print_contexts(ctx_init, x86_ctx_out, reil_ctx_out))

    def test_cmp(self):
        asm = ["cmp eax, ebx"]

        ctx_init = self.__init_context()

        x86_ctx_out, reil_ctx_out = self.__run_code(asm, 0xdeadbeef, ctx_init)

        cmp_result = self.__compare_contexts(ctx_init, x86_ctx_out, reil_ctx_out)

        if not cmp_result:
            self.__save_failing_context(ctx_init)

        self.assertTrue(cmp_result, self.__print_contexts(ctx_init, x86_ctx_out, reil_ctx_out))

    def test_neg(self):
        asm = ["neg eax"]

        ctx_init = self.__init_context()

        x86_ctx_out, reil_ctx_out = self.__run_code(asm, 0xdeadbeef, ctx_init)

        cmp_result = self.__compare_contexts(ctx_init, x86_ctx_out, reil_ctx_out)

        if not cmp_result:
            self.__save_failing_context(ctx_init)

        self.assertTrue(cmp_result, self.__print_contexts(ctx_init, x86_ctx_out, reil_ctx_out))

    def test_dec(self):
        asm = ["dec eax"]

        ctx_init = self.__init_context()

        x86_ctx_out, reil_ctx_out = self.__run_code(asm, 0xdeadbeef, ctx_init)

        cmp_result = self.__compare_contexts(ctx_init, x86_ctx_out, reil_ctx_out)

        if not cmp_result:
            self.__save_failing_context(ctx_init)

        self.assertTrue(cmp_result, self.__print_contexts(ctx_init, x86_ctx_out, reil_ctx_out))

    def test_inc(self):
        asm = ["inc eax"]

        ctx_init = self.__init_context()

        x86_ctx_out, reil_ctx_out = self.__run_code(asm, 0xdeadbeef, ctx_init)

        cmp_result = self.__compare_contexts(ctx_init, x86_ctx_out, reil_ctx_out)

        if not cmp_result:
            self.__save_failing_context(ctx_init)

        self.assertTrue(cmp_result, self.__print_contexts(ctx_init, x86_ctx_out, reil_ctx_out))

    def test_div_1(self):
        asm = ["div ebx"]

        ctx_init = {
            'rax'    : 0x10,
            'rbx'    : 0x2,
            'rdx'    : 0x0,
            'rflags' : 0x202,
        }

        x86_ctx_out, reil_ctx_out = self.__run_code(asm, 0xdeadbeef, ctx_init)

        # Undefined flags...
        reil_ctx_out = self.__fix_reil_flag(reil_ctx_out, x86_ctx_out, "cf")
        reil_ctx_out = self.__fix_reil_flag(reil_ctx_out, x86_ctx_out, "of")
        reil_ctx_out = self.__fix_reil_flag(reil_ctx_out, x86_ctx_out, "sf")
        reil_ctx_out = self.__fix_reil_flag(reil_ctx_out, x86_ctx_out, "zf")
        reil_ctx_out = self.__fix_reil_flag(reil_ctx_out, x86_ctx_out, "af")
        reil_ctx_out = self.__fix_reil_flag(reil_ctx_out, x86_ctx_out, "pf")

        cmp_result = self.__compare_contexts(ctx_init, x86_ctx_out, reil_ctx_out)

        if not cmp_result:
            self.__save_failing_context(ctx_init)

        self.assertTrue(cmp_result, self.__print_contexts(ctx_init, x86_ctx_out, reil_ctx_out))

    def test_div_2(self):
        asm = ["div ebx"]

        ctx_init = {
            'rax'    : 0xFFFFFFFFFFFFFFFF,
            'rbx'    : 0x2,
            'rdx'    : 0x0000000000000000,
            'rflags' : 0x202,
        }

        x86_ctx_out, reil_ctx_out = self.__run_code(asm, 0xdeadbeef, ctx_init)

        # Undefined flags...
        reil_ctx_out = self.__fix_reil_flag(reil_ctx_out, x86_ctx_out, "cf")
        reil_ctx_out = self.__fix_reil_flag(reil_ctx_out, x86_ctx_out, "of")
        reil_ctx_out = self.__fix_reil_flag(reil_ctx_out, x86_ctx_out, "sf")
        reil_ctx_out = self.__fix_reil_flag(reil_ctx_out, x86_ctx_out, "zf")
        reil_ctx_out = self.__fix_reil_flag(reil_ctx_out, x86_ctx_out, "af")
        reil_ctx_out = self.__fix_reil_flag(reil_ctx_out, x86_ctx_out, "pf")

        cmp_result = self.__compare_contexts(ctx_init, x86_ctx_out, reil_ctx_out)

        if not cmp_result:
            self.__save_failing_context(ctx_init)

        self.assertTrue(cmp_result, self.__print_contexts(ctx_init, x86_ctx_out, reil_ctx_out))

    def test_div_3(self):
        asm = ["div ebx"]

        ctx_init = {
            'rax'    : 0xFFFFFFFFFFFFFFFF,
            'rbx'    : 0x2,
            'rdx'    : 0x0000000000000001,
            'rflags' : 0x202,
        }

        x86_ctx_out, reil_ctx_out = self.__run_code(asm, 0xdeadbeef, ctx_init)

        # Undefined flags...
        reil_ctx_out = self.__fix_reil_flag(reil_ctx_out, x86_ctx_out, "cf")
        reil_ctx_out = self.__fix_reil_flag(reil_ctx_out, x86_ctx_out, "of")
        reil_ctx_out = self.__fix_reil_flag(reil_ctx_out, x86_ctx_out, "sf")
        reil_ctx_out = self.__fix_reil_flag(reil_ctx_out, x86_ctx_out, "zf")
        reil_ctx_out = self.__fix_reil_flag(reil_ctx_out, x86_ctx_out, "af")
        reil_ctx_out = self.__fix_reil_flag(reil_ctx_out, x86_ctx_out, "pf")

        cmp_result = self.__compare_contexts(ctx_init, x86_ctx_out, reil_ctx_out)

        if not cmp_result:
            self.__save_failing_context(ctx_init)

        self.assertTrue(cmp_result, self.__print_contexts(ctx_init, x86_ctx_out, reil_ctx_out))

    def test_div_4(self):
        asm = ["div ebx"]

        ctx_init = {
            'rax'    : 0xFFFFFFFFFFFFFFFF,
            'rbx'    : 0x4,
            'rdx'    : 0x0000000000000002,
            'rflags' : 0x202,
        }

        x86_ctx_out, reil_ctx_out = self.__run_code(asm, 0xdeadbeef, ctx_init)

        # Undefined flags...
        reil_ctx_out = self.__fix_reil_flag(reil_ctx_out, x86_ctx_out, "cf")
        reil_ctx_out = self.__fix_reil_flag(reil_ctx_out, x86_ctx_out, "of")
        reil_ctx_out = self.__fix_reil_flag(reil_ctx_out, x86_ctx_out, "sf")
        reil_ctx_out = self.__fix_reil_flag(reil_ctx_out, x86_ctx_out, "zf")
        reil_ctx_out = self.__fix_reil_flag(reil_ctx_out, x86_ctx_out, "af")
        reil_ctx_out = self.__fix_reil_flag(reil_ctx_out, x86_ctx_out, "pf")

        cmp_result = self.__compare_contexts(ctx_init, x86_ctx_out, reil_ctx_out)

        if not cmp_result:
            self.__save_failing_context(ctx_init)

        self.assertTrue(cmp_result, self.__print_contexts(ctx_init, x86_ctx_out, reil_ctx_out))

    def test_div_5(self):
        asm = ["idiv ebx"]

        ctx_init = {
            'rax'    : 0x0000000000000005,
            'rbx'    : 0x0000000000000003,
            'rdx'    : 0x0000000000000000,
            'rflags' : 0x202,
        }

        x86_ctx_out, reil_ctx_out = self.__run_code(asm, 0xdeadbeef, ctx_init)

        # Undefined flags...
        reil_ctx_out = self.__fix_reil_flag(reil_ctx_out, x86_ctx_out, "cf")
        reil_ctx_out = self.__fix_reil_flag(reil_ctx_out, x86_ctx_out, "of")
        reil_ctx_out = self.__fix_reil_flag(reil_ctx_out, x86_ctx_out, "sf")
        reil_ctx_out = self.__fix_reil_flag(reil_ctx_out, x86_ctx_out, "zf")
        reil_ctx_out = self.__fix_reil_flag(reil_ctx_out, x86_ctx_out, "af")
        reil_ctx_out = self.__fix_reil_flag(reil_ctx_out, x86_ctx_out, "pf")

        cmp_result = self.__compare_contexts(ctx_init, x86_ctx_out, reil_ctx_out)

        if not cmp_result:
            self.__save_failing_context(ctx_init)

        self.assertTrue(cmp_result, self.__print_contexts(ctx_init, x86_ctx_out, reil_ctx_out))

    def test_idiv_1(self):
        asm = ["idiv ebx"]

        ctx_init = {
            'rax'    : 0x10,
            'rbx'    : 0x2,
            'rdx'    : 0x0,
            'rflags' : 0x202,
        }

        x86_ctx_out, reil_ctx_out = self.__run_code(asm, 0xdeadbeef, ctx_init)

        # Undefined flags...
        reil_ctx_out = self.__fix_reil_flag(reil_ctx_out, x86_ctx_out, "cf")
        reil_ctx_out = self.__fix_reil_flag(reil_ctx_out, x86_ctx_out, "of")
        reil_ctx_out = self.__fix_reil_flag(reil_ctx_out, x86_ctx_out, "sf")
        reil_ctx_out = self.__fix_reil_flag(reil_ctx_out, x86_ctx_out, "zf")
        reil_ctx_out = self.__fix_reil_flag(reil_ctx_out, x86_ctx_out, "af")
        reil_ctx_out = self.__fix_reil_flag(reil_ctx_out, x86_ctx_out, "pf")

        cmp_result = self.__compare_contexts(ctx_init, x86_ctx_out, reil_ctx_out)

        if not cmp_result:
            self.__save_failing_context(ctx_init)

        self.assertTrue(cmp_result, self.__print_contexts(ctx_init, x86_ctx_out, reil_ctx_out))

    def test_idiv_2(self):
        asm = ["idiv ebx"]

        ctx_init = {
            'rax'    : 0xFFFFFFFFFFFFFFFF,
            'rbx'    : 0x0000000000000001,
            'rdx'    : 0xFFFFFFFFFFFFFFFF,
            'rflags' : 0x202,
        }

        x86_ctx_out, reil_ctx_out = self.__run_code(asm, 0xdeadbeef, ctx_init)

        # Undefined flags...
        reil_ctx_out = self.__fix_reil_flag(reil_ctx_out, x86_ctx_out, "cf")
        reil_ctx_out = self.__fix_reil_flag(reil_ctx_out, x86_ctx_out, "of")
        reil_ctx_out = self.__fix_reil_flag(reil_ctx_out, x86_ctx_out, "sf")
        reil_ctx_out = self.__fix_reil_flag(reil_ctx_out, x86_ctx_out, "zf")
        reil_ctx_out = self.__fix_reil_flag(reil_ctx_out, x86_ctx_out, "af")
        reil_ctx_out = self.__fix_reil_flag(reil_ctx_out, x86_ctx_out, "pf")

        cmp_result = self.__compare_contexts(ctx_init, x86_ctx_out, reil_ctx_out)

        if not cmp_result:
            self.__save_failing_context(ctx_init)

        self.assertTrue(cmp_result, self.__print_contexts(ctx_init, x86_ctx_out, reil_ctx_out))

    def test_idiv_3(self):
        asm = ["idiv ebx"]

        ctx_init = {
            'rax'    : 0xFFFFFFFFFFFFFFFE,
            'rbx'    : 0xFFFFFFFFFFFFFFFF,
            'rdx'    : 0xFFFFFFFFFFFFFFFF,
            'rflags' : 0x202,
        }

        x86_ctx_out, reil_ctx_out = self.__run_code(asm, 0xdeadbeef, ctx_init)

        # Undefined flags...
        reil_ctx_out = self.__fix_reil_flag(reil_ctx_out, x86_ctx_out, "cf")
        reil_ctx_out = self.__fix_reil_flag(reil_ctx_out, x86_ctx_out, "of")
        reil_ctx_out = self.__fix_reil_flag(reil_ctx_out, x86_ctx_out, "sf")
        reil_ctx_out = self.__fix_reil_flag(reil_ctx_out, x86_ctx_out, "zf")
        reil_ctx_out = self.__fix_reil_flag(reil_ctx_out, x86_ctx_out, "af")
        reil_ctx_out = self.__fix_reil_flag(reil_ctx_out, x86_ctx_out, "pf")

        cmp_result = self.__compare_contexts(ctx_init, x86_ctx_out, reil_ctx_out)

        if not cmp_result:
            self.__save_failing_context(ctx_init)

        self.assertTrue(cmp_result, self.__print_contexts(ctx_init, x86_ctx_out, reil_ctx_out))

    def test_idiv_3(self):
        asm = ["idiv ebx"]

        ctx_init = {
            'rax'    : 0xFFFFFFFFFFFFFFFE,
            'rbx'    : 0xFFFFFFFFFFFFFFFF,
            'rdx'    : 0xFFFFFFFFFFFFFFFF,
            'rflags' : 0x202,
        }

        x86_ctx_out, reil_ctx_out = self.__run_code(asm, 0xdeadbeef, ctx_init)

        # Undefined flags...
        reil_ctx_out = self.__fix_reil_flag(reil_ctx_out, x86_ctx_out, "cf")
        reil_ctx_out = self.__fix_reil_flag(reil_ctx_out, x86_ctx_out, "of")
        reil_ctx_out = self.__fix_reil_flag(reil_ctx_out, x86_ctx_out, "sf")
        reil_ctx_out = self.__fix_reil_flag(reil_ctx_out, x86_ctx_out, "zf")
        reil_ctx_out = self.__fix_reil_flag(reil_ctx_out, x86_ctx_out, "af")
        reil_ctx_out = self.__fix_reil_flag(reil_ctx_out, x86_ctx_out, "pf")

        cmp_result = self.__compare_contexts(ctx_init, x86_ctx_out, reil_ctx_out)

        if not cmp_result:
            self.__save_failing_context(ctx_init)

        self.assertTrue(cmp_result, self.__print_contexts(ctx_init, x86_ctx_out, reil_ctx_out))

    def test_idiv_4(self):
        asm = ["idiv ebx"]

        ctx_init = {
            'rax'    : 0xFFFFFFFFFFFFFFFB, # -5
            'rbx'    : 0x0000000000000003,
            'rdx'    : 0xFFFFFFFFFFFFFFFF,
            'rflags' : 0x202,
        }

        x86_ctx_out, reil_ctx_out = self.__run_code(asm, 0xdeadbeef, ctx_init)

        # Undefined flags...
        reil_ctx_out = self.__fix_reil_flag(reil_ctx_out, x86_ctx_out, "cf")
        reil_ctx_out = self.__fix_reil_flag(reil_ctx_out, x86_ctx_out, "of")
        reil_ctx_out = self.__fix_reil_flag(reil_ctx_out, x86_ctx_out, "sf")
        reil_ctx_out = self.__fix_reil_flag(reil_ctx_out, x86_ctx_out, "zf")
        reil_ctx_out = self.__fix_reil_flag(reil_ctx_out, x86_ctx_out, "af")
        reil_ctx_out = self.__fix_reil_flag(reil_ctx_out, x86_ctx_out, "pf")

        cmp_result = self.__compare_contexts(ctx_init, x86_ctx_out, reil_ctx_out)

        if not cmp_result:
            self.__save_failing_context(ctx_init)

        self.assertTrue(cmp_result, self.__print_contexts(ctx_init, x86_ctx_out, reil_ctx_out))

    def test_idiv_5(self):
        asm = ["idiv ebx"]

        ctx_init = {
            'rax'    : 0x0000000000000005, #  5
            'rbx'    : 0xFFFFFFFFFFFFFFFD, # -3
            'rdx'    : 0x0000000000000000,
            'rflags' : 0x202,
        }

        x86_ctx_out, reil_ctx_out = self.__run_code(asm, 0xdeadbeef, ctx_init)

        # Undefined flags...
        reil_ctx_out = self.__fix_reil_flag(reil_ctx_out, x86_ctx_out, "cf")
        reil_ctx_out = self.__fix_reil_flag(reil_ctx_out, x86_ctx_out, "of")
        reil_ctx_out = self.__fix_reil_flag(reil_ctx_out, x86_ctx_out, "sf")
        reil_ctx_out = self.__fix_reil_flag(reil_ctx_out, x86_ctx_out, "zf")
        reil_ctx_out = self.__fix_reil_flag(reil_ctx_out, x86_ctx_out, "af")
        reil_ctx_out = self.__fix_reil_flag(reil_ctx_out, x86_ctx_out, "pf")

        cmp_result = self.__compare_contexts(ctx_init, x86_ctx_out, reil_ctx_out)

        if not cmp_result:
            self.__save_failing_context(ctx_init)

        self.assertTrue(cmp_result, self.__print_contexts(ctx_init, x86_ctx_out, reil_ctx_out))


    # # TODO: Uncomment once imul translation gets fixed.
    # def test_imul(self):
    #     asm = ["imul eax, ebx"]

    #     ctx_init = self.__init_context()

    #     x86_ctx_out, reil_ctx_out = self.__run_code(asm, 0xdeadbeef, ctx_init)

    #     # Undefined flags...
    #     reil_ctx_out = self.__fix_reil_flag(reil_ctx_out, x86_ctx_out, "sf")
    #     reil_ctx_out = self.__fix_reil_flag(reil_ctx_out, x86_ctx_out, "zf")
    #     reil_ctx_out = self.__fix_reil_flag(reil_ctx_out, x86_ctx_out, "af")
    #     reil_ctx_out = self.__fix_reil_flag(reil_ctx_out, x86_ctx_out, "pf")

    #     cmp_result = self.__compare_contexts(ctx_init, x86_ctx_out, reil_ctx_out)

    #     if not cmp_result:
    #         self.__save_failing_context(ctx_init)

    #     self.assertTrue(cmp_result, self.__print_contexts(ctx_init, x86_ctx_out, reil_ctx_out))

    def test_mul(self):
        asm = ["mul ebx"]

        ctx_init = self.__init_context()

        x86_ctx_out, reil_ctx_out = self.__run_code(asm, 0xdeadbeef, ctx_init)

        # Undefined flags...
        reil_ctx_out = self.__fix_reil_flag(reil_ctx_out, x86_ctx_out, "sf")
        reil_ctx_out = self.__fix_reil_flag(reil_ctx_out, x86_ctx_out, "zf")
        reil_ctx_out = self.__fix_reil_flag(reil_ctx_out, x86_ctx_out, "af")
        reil_ctx_out = self.__fix_reil_flag(reil_ctx_out, x86_ctx_out, "pf")

        cmp_result = self.__compare_contexts(ctx_init, x86_ctx_out, reil_ctx_out)

        if not cmp_result:
            self.__save_failing_context(ctx_init)

        self.assertTrue(cmp_result, self.__print_contexts(ctx_init, x86_ctx_out, reil_ctx_out))

    def test_sbb(self):
        asm = ["sbb eax, ebx"]

        ctx_init = self.__init_context()

        x86_ctx_out, reil_ctx_out = self.__run_code(asm, 0xdeadbeef, ctx_init)

        # FIX: Remove this once the sbb translation gets fixed.
        reil_ctx_out = self.__fix_reil_flag(reil_ctx_out, x86_ctx_out, "of")

        cmp_result = self.__compare_contexts(ctx_init, x86_ctx_out, reil_ctx_out)

        if not cmp_result:
            self.__save_failing_context(ctx_init)

        self.assertTrue(cmp_result, self.__print_contexts(ctx_init, x86_ctx_out, reil_ctx_out))

    def test_sub(self):
        asm = ["sub eax, ebx"]

        ctx_init = self.__init_context()

        x86_ctx_out, reil_ctx_out = self.__run_code(asm, 0xdeadbeef, ctx_init)

        cmp_result = self.__compare_contexts(ctx_init, x86_ctx_out, reil_ctx_out)

        if not cmp_result:
            self.__save_failing_context(ctx_init)

        self.assertTrue(cmp_result, self.__print_contexts(ctx_init, x86_ctx_out, reil_ctx_out))

    def test_adc(self):
        asm = ["adc eax, ebx"]

        ctx_init = self.__init_context()

        x86_ctx_out, reil_ctx_out = self.__run_code(asm, 0xdeadbeef, ctx_init)

        cmp_result = self.__compare_contexts(ctx_init, x86_ctx_out, reil_ctx_out)

        if not cmp_result:
            self.__save_failing_context(ctx_init)

        self.assertTrue(cmp_result, self.__print_contexts(ctx_init, x86_ctx_out, reil_ctx_out))

    def test_add(self):
        asm = ["add eax, ebx"]

        ctx_init = self.__init_context()

        x86_ctx_out, reil_ctx_out = self.__run_code(asm, 0xdeadbeef, ctx_init)

        cmp_result = self.__compare_contexts(ctx_init, x86_ctx_out, reil_ctx_out)

        if not cmp_result:
            self.__save_failing_context(ctx_init)

        self.assertTrue(cmp_result, self.__print_contexts(ctx_init, x86_ctx_out, reil_ctx_out))

    def test_xchg(self):
        asm = ["xchg eax, ebx"]

        ctx_init = self.__init_context()

        x86_ctx_out, reil_ctx_out = self.__run_code(asm, 0xdeadbeef, ctx_init)

        cmp_result = self.__compare_contexts(ctx_init, x86_ctx_out, reil_ctx_out)

        if not cmp_result:
            self.__save_failing_context(ctx_init)

        self.assertTrue(cmp_result, self.__print_contexts(ctx_init, x86_ctx_out, reil_ctx_out))

    def test_movzx_1(self):
        asm = ["movzx eax, bx"]

        ctx_init = self.__init_context()

        x86_ctx_out, reil_ctx_out = self.__run_code(asm, 0xdeadbeef, ctx_init)

        cmp_result = self.__compare_contexts(ctx_init, x86_ctx_out, reil_ctx_out)

        if not cmp_result:
            self.__save_failing_context(ctx_init)

        self.assertTrue(cmp_result, self.__print_contexts(ctx_init, x86_ctx_out, reil_ctx_out))

    def test_movzx_2(self):
        asm = ["movzx eax, al"]

        ctx_init = self.__init_context()

        ctx_init["rax"] = 0x1

        x86_ctx_out, reil_ctx_out = self.__run_code(asm, 0xdeadbeef, ctx_init)

        cmp_result = self.__compare_contexts(ctx_init, x86_ctx_out, reil_ctx_out)

        if not cmp_result:
            self.__save_failing_context(ctx_init)

        self.assertTrue(cmp_result, self.__print_contexts(ctx_init, x86_ctx_out, reil_ctx_out))

    def test_mov_1(self):
        asm = ["mov eax, ebx"]

        ctx_init = self.__init_context()

        x86_ctx_out, reil_ctx_out = self.__run_code(asm, 0xdeadbeef, ctx_init)

        cmp_result = self.__compare_contexts(ctx_init, x86_ctx_out, reil_ctx_out)

        if not cmp_result:
            self.__save_failing_context(ctx_init)

        self.assertTrue(cmp_result, self.__print_contexts(ctx_init, x86_ctx_out, reil_ctx_out))

    def test_mov_2(self):
        asm = ["mov eax, eax"]

        ctx_init = self.__init_context()

        x86_ctx_out, reil_ctx_out = self.__run_code(asm, 0xdeadbeef, ctx_init)

        cmp_result = self.__compare_contexts(ctx_init, x86_ctx_out, reil_ctx_out)

        if not cmp_result:
            self.__save_failing_context(ctx_init)

        self.assertTrue(cmp_result, self.__print_contexts(ctx_init, x86_ctx_out, reil_ctx_out))

    def test_cmova(self):
        asm = ["cmova eax, ebx"]

        ctx_init = self.__init_context()

        x86_ctx_out, reil_ctx_out = self.__run_code(asm, 0xdeadbeef, ctx_init)

        cmp_result = self.__compare_contexts(ctx_init, x86_ctx_out, reil_ctx_out)

        if not cmp_result:
            self.__save_failing_context(ctx_init)

        self.assertTrue(cmp_result, self.__print_contexts(ctx_init, x86_ctx_out, reil_ctx_out))

    def test_cmovae(self):
        asm = ["cmovae eax, ebx"]

        ctx_init = self.__init_context()

        x86_ctx_out, reil_ctx_out = self.__run_code(asm, 0xdeadbeef, ctx_init)

        cmp_result = self.__compare_contexts(ctx_init, x86_ctx_out, reil_ctx_out)

        if not cmp_result:
            self.__save_failing_context(ctx_init)

        self.assertTrue(cmp_result, self.__print_contexts(ctx_init, x86_ctx_out, reil_ctx_out))

    def test_cmovb(self):
        asm = ["cmovb eax, ebx"]

        ctx_init = self.__init_context()

        x86_ctx_out, reil_ctx_out = self.__run_code(asm, 0xdeadbeef, ctx_init)

        cmp_result = self.__compare_contexts(ctx_init, x86_ctx_out, reil_ctx_out)

        if not cmp_result:
            self.__save_failing_context(ctx_init)

        self.assertTrue(cmp_result, self.__print_contexts(ctx_init, x86_ctx_out, reil_ctx_out))

    def test_cmovbe(self):
        asm = ["cmovbe eax, ebx"]

        ctx_init = self.__init_context()

        x86_ctx_out, reil_ctx_out = self.__run_code(asm, 0xdeadbeef, ctx_init)

        cmp_result = self.__compare_contexts(ctx_init, x86_ctx_out, reil_ctx_out)

        if not cmp_result:
            self.__save_failing_context(ctx_init)

        self.assertTrue(cmp_result, self.__print_contexts(ctx_init, x86_ctx_out, reil_ctx_out))

    def test_cmovc(self):
        asm = ["cmovc eax, ebx"]

        ctx_init = self.__init_context()

        x86_ctx_out, reil_ctx_out = self.__run_code(asm, 0xdeadbeef, ctx_init)

        cmp_result = self.__compare_contexts(ctx_init, x86_ctx_out, reil_ctx_out)

        if not cmp_result:
            self.__save_failing_context(ctx_init)

        self.assertTrue(cmp_result, self.__print_contexts(ctx_init, x86_ctx_out, reil_ctx_out))

    def test_cmove(self):
        asm = ["cmove eax, ebx"]

        ctx_init = self.__init_context()

        x86_ctx_out, reil_ctx_out = self.__run_code(asm, 0xdeadbeef, ctx_init)

        cmp_result = self.__compare_contexts(ctx_init, x86_ctx_out, reil_ctx_out)

        if not cmp_result:
            self.__save_failing_context(ctx_init)

        self.assertTrue(cmp_result, self.__print_contexts(ctx_init, x86_ctx_out, reil_ctx_out))

    def test_cmovg(self):
        asm = ["cmovg eax, ebx"]

        ctx_init = self.__init_context()

        x86_ctx_out, reil_ctx_out = self.__run_code(asm, 0xdeadbeef, ctx_init)

        cmp_result = self.__compare_contexts(ctx_init, x86_ctx_out, reil_ctx_out)

        if not cmp_result:
            self.__save_failing_context(ctx_init)

        self.assertTrue(cmp_result, self.__print_contexts(ctx_init, x86_ctx_out, reil_ctx_out))

    def test_cmovge(self):
        asm = ["cmovge eax, ebx"]

        ctx_init = self.__init_context()

        x86_ctx_out, reil_ctx_out = self.__run_code(asm, 0xdeadbeef, ctx_init)

        cmp_result = self.__compare_contexts(ctx_init, x86_ctx_out, reil_ctx_out)

        if not cmp_result:
            self.__save_failing_context(ctx_init)

        self.assertTrue(cmp_result, self.__print_contexts(ctx_init, x86_ctx_out, reil_ctx_out))

    def test_cmovl(self):
        asm = ["cmovl eax, ebx"]

        ctx_init = self.__init_context()

        x86_ctx_out, reil_ctx_out = self.__run_code(asm, 0xdeadbeef, ctx_init)

        cmp_result = self.__compare_contexts(ctx_init, x86_ctx_out, reil_ctx_out)

        if not cmp_result:
            self.__save_failing_context(ctx_init)

        self.assertTrue(cmp_result, self.__print_contexts(ctx_init, x86_ctx_out, reil_ctx_out))

    def test_cmovle(self):
        asm = ["cmovle eax, ebx"]

        ctx_init = self.__init_context()

        x86_ctx_out, reil_ctx_out = self.__run_code(asm, 0xdeadbeef, ctx_init)

        cmp_result = self.__compare_contexts(ctx_init, x86_ctx_out, reil_ctx_out)

        if not cmp_result:
            self.__save_failing_context(ctx_init)

        self.assertTrue(cmp_result, self.__print_contexts(ctx_init, x86_ctx_out, reil_ctx_out))

    def test_cmovna(self):
        asm = ["cmovna eax, ebx"]

        ctx_init = self.__init_context()

        x86_ctx_out, reil_ctx_out = self.__run_code(asm, 0xdeadbeef, ctx_init)

        cmp_result = self.__compare_contexts(ctx_init, x86_ctx_out, reil_ctx_out)

        if not cmp_result:
            self.__save_failing_context(ctx_init)

        self.assertTrue(cmp_result, self.__print_contexts(ctx_init, x86_ctx_out, reil_ctx_out))

    def test_cmovnae(self):
        asm = ["cmovnae eax, ebx"]

        ctx_init = self.__init_context()

        x86_ctx_out, reil_ctx_out = self.__run_code(asm, 0xdeadbeef, ctx_init)

        cmp_result = self.__compare_contexts(ctx_init, x86_ctx_out, reil_ctx_out)

        if not cmp_result:
            self.__save_failing_context(ctx_init)

        self.assertTrue(cmp_result, self.__print_contexts(ctx_init, x86_ctx_out, reil_ctx_out))

    def test_cmovnb(self):
        asm = ["cmovnb eax, ebx"]

        ctx_init = self.__init_context()

        x86_ctx_out, reil_ctx_out = self.__run_code(asm, 0xdeadbeef, ctx_init)

        cmp_result = self.__compare_contexts(ctx_init, x86_ctx_out, reil_ctx_out)

        if not cmp_result:
            self.__save_failing_context(ctx_init)

        self.assertTrue(cmp_result, self.__print_contexts(ctx_init, x86_ctx_out, reil_ctx_out))

    def test_cmovnbe(self):
        asm = ["cmovnbe eax, ebx"]

        ctx_init = self.__init_context()

        x86_ctx_out, reil_ctx_out = self.__run_code(asm, 0xdeadbeef, ctx_init)

        cmp_result = self.__compare_contexts(ctx_init, x86_ctx_out, reil_ctx_out)

        if not cmp_result:
            self.__save_failing_context(ctx_init)

        self.assertTrue(cmp_result, self.__print_contexts(ctx_init, x86_ctx_out, reil_ctx_out))

    def test_cmovnc(self):
        asm = ["cmovnc eax, ebx"]

        ctx_init = self.__init_context()

        x86_ctx_out, reil_ctx_out = self.__run_code(asm, 0xdeadbeef, ctx_init)

        cmp_result = self.__compare_contexts(ctx_init, x86_ctx_out, reil_ctx_out)

        if not cmp_result:
            self.__save_failing_context(ctx_init)

        self.assertTrue(cmp_result, self.__print_contexts(ctx_init, x86_ctx_out, reil_ctx_out))

    def test_cmovne(self):
        asm = ["cmovne eax, ebx"]

        ctx_init = self.__init_context()

        x86_ctx_out, reil_ctx_out = self.__run_code(asm, 0xdeadbeef, ctx_init)

        cmp_result = self.__compare_contexts(ctx_init, x86_ctx_out, reil_ctx_out)

        if not cmp_result:
            self.__save_failing_context(ctx_init)

        self.assertTrue(cmp_result, self.__print_contexts(ctx_init, x86_ctx_out, reil_ctx_out))

    def test_cmovng(self):
        asm = ["cmovng eax, ebx"]

        ctx_init = self.__init_context()

        x86_ctx_out, reil_ctx_out = self.__run_code(asm, 0xdeadbeef, ctx_init)

        cmp_result = self.__compare_contexts(ctx_init, x86_ctx_out, reil_ctx_out)

        if not cmp_result:
            self.__save_failing_context(ctx_init)

        self.assertTrue(cmp_result, self.__print_contexts(ctx_init, x86_ctx_out, reil_ctx_out))

    def test_cmovnge(self):
        asm = ["cmovnge eax, ebx"]

        ctx_init = self.__init_context()

        x86_ctx_out, reil_ctx_out = self.__run_code(asm, 0xdeadbeef, ctx_init)

        cmp_result = self.__compare_contexts(ctx_init, x86_ctx_out, reil_ctx_out)

        if not cmp_result:
            self.__save_failing_context(ctx_init)

        self.assertTrue(cmp_result, self.__print_contexts(ctx_init, x86_ctx_out, reil_ctx_out))

    def test_cmovnl(self):
        asm = ["cmovnl eax, ebx"]

        ctx_init = self.__init_context()

        x86_ctx_out, reil_ctx_out = self.__run_code(asm, 0xdeadbeef, ctx_init)

        cmp_result = self.__compare_contexts(ctx_init, x86_ctx_out, reil_ctx_out)

        if not cmp_result:
            self.__save_failing_context(ctx_init)

        self.assertTrue(cmp_result, self.__print_contexts(ctx_init, x86_ctx_out, reil_ctx_out))

    def test_cmovnle(self):
        asm = ["cmovnle eax, ebx"]

        ctx_init = self.__init_context()

        x86_ctx_out, reil_ctx_out = self.__run_code(asm, 0xdeadbeef, ctx_init)

        cmp_result = self.__compare_contexts(ctx_init, x86_ctx_out, reil_ctx_out)

        if not cmp_result:
            self.__save_failing_context(ctx_init)

        self.assertTrue(cmp_result, self.__print_contexts(ctx_init, x86_ctx_out, reil_ctx_out))

    def test_cmovno(self):
        asm = ["cmovno eax, ebx"]

        ctx_init = self.__init_context()

        x86_ctx_out, reil_ctx_out = self.__run_code(asm, 0xdeadbeef, ctx_init)

        cmp_result = self.__compare_contexts(ctx_init, x86_ctx_out, reil_ctx_out)

        if not cmp_result:
            self.__save_failing_context(ctx_init)

        self.assertTrue(cmp_result, self.__print_contexts(ctx_init, x86_ctx_out, reil_ctx_out))

    def test_cmovnp(self):
        asm = ["cmovnp eax, ebx"]

        ctx_init = self.__init_context()

        x86_ctx_out, reil_ctx_out = self.__run_code(asm, 0xdeadbeef, ctx_init)

        cmp_result = self.__compare_contexts(ctx_init, x86_ctx_out, reil_ctx_out)

        if not cmp_result:
            self.__save_failing_context(ctx_init)

        self.assertTrue(cmp_result, self.__print_contexts(ctx_init, x86_ctx_out, reil_ctx_out))

    def test_cmovns(self):
        asm = ["cmovns eax, ebx"]

        ctx_init = self.__init_context()

        x86_ctx_out, reil_ctx_out = self.__run_code(asm, 0xdeadbeef, ctx_init)

        cmp_result = self.__compare_contexts(ctx_init, x86_ctx_out, reil_ctx_out)

        if not cmp_result:
            self.__save_failing_context(ctx_init)

        self.assertTrue(cmp_result, self.__print_contexts(ctx_init, x86_ctx_out, reil_ctx_out))

    def test_cmovnz(self):
        asm = ["cmovnz eax, ebx"]

        ctx_init = self.__init_context()

        x86_ctx_out, reil_ctx_out = self.__run_code(asm, 0xdeadbeef, ctx_init)

        cmp_result = self.__compare_contexts(ctx_init, x86_ctx_out, reil_ctx_out)

        if not cmp_result:
            self.__save_failing_context(ctx_init)

        self.assertTrue(cmp_result, self.__print_contexts(ctx_init, x86_ctx_out, reil_ctx_out))

    def test_cmovo(self):
        asm = ["cmovo eax, ebx"]

        ctx_init = self.__init_context()

        x86_ctx_out, reil_ctx_out = self.__run_code(asm, 0xdeadbeef, ctx_init)

        cmp_result = self.__compare_contexts(ctx_init, x86_ctx_out, reil_ctx_out)

        if not cmp_result:
            self.__save_failing_context(ctx_init)

        self.assertTrue(cmp_result, self.__print_contexts(ctx_init, x86_ctx_out, reil_ctx_out))

    def test_cmovp(self):
        asm = ["cmovp eax, ebx"]

        ctx_init = self.__init_context()

        x86_ctx_out, reil_ctx_out = self.__run_code(asm, 0xdeadbeef, ctx_init)

        cmp_result = self.__compare_contexts(ctx_init, x86_ctx_out, reil_ctx_out)

        if not cmp_result:
            self.__save_failing_context(ctx_init)

        self.assertTrue(cmp_result, self.__print_contexts(ctx_init, x86_ctx_out, reil_ctx_out))

    def test_cmovpe(self):
        asm = ["cmovpe eax, ebx"]

        ctx_init = self.__init_context()

        x86_ctx_out, reil_ctx_out = self.__run_code(asm, 0xdeadbeef, ctx_init)

        cmp_result = self.__compare_contexts(ctx_init, x86_ctx_out, reil_ctx_out)

        if not cmp_result:
            self.__save_failing_context(ctx_init)

        self.assertTrue(cmp_result, self.__print_contexts(ctx_init, x86_ctx_out, reil_ctx_out))

    def test_cmovpo(self):
        asm = ["cmovpo eax, ebx"]

        ctx_init = self.__init_context()

        x86_ctx_out, reil_ctx_out = self.__run_code(asm, 0xdeadbeef, ctx_init)

        cmp_result = self.__compare_contexts(ctx_init, x86_ctx_out, reil_ctx_out)

        if not cmp_result:
            self.__save_failing_context(ctx_init)

        self.assertTrue(cmp_result, self.__print_contexts(ctx_init, x86_ctx_out, reil_ctx_out))

    def test_cmovs(self):
        asm = ["cmovs eax, ebx"]

        ctx_init = self.__init_context()

        x86_ctx_out, reil_ctx_out = self.__run_code(asm, 0xdeadbeef, ctx_init)

        cmp_result = self.__compare_contexts(ctx_init, x86_ctx_out, reil_ctx_out)

        if not cmp_result:
            self.__save_failing_context(ctx_init)

        self.assertTrue(cmp_result, self.__print_contexts(ctx_init, x86_ctx_out, reil_ctx_out))

    def test_cmovz(self):
        asm = ["cmovz eax, ebx"]

        ctx_init = self.__init_context()

        x86_ctx_out, reil_ctx_out = self.__run_code(asm, 0xdeadbeef, ctx_init)

        cmp_result = self.__compare_contexts(ctx_init, x86_ctx_out, reil_ctx_out)

        if not cmp_result:
            self.__save_failing_context(ctx_init)

        self.assertTrue(cmp_result, self.__print_contexts(ctx_init, x86_ctx_out, reil_ctx_out))

    def test_seta(self):
        asm = ["seta al"]

        ctx_init = self.__init_context()

        x86_ctx_out, reil_ctx_out = self.__run_code(asm, 0xdeadbeef, ctx_init)

        cmp_result = self.__compare_contexts(ctx_init, x86_ctx_out, reil_ctx_out)

        if not cmp_result:
            self.__save_failing_context(ctx_init)

        self.assertTrue(cmp_result, self.__print_contexts(ctx_init, x86_ctx_out, reil_ctx_out))

    def test_setae(self):
        asm = ["setae al"]

        ctx_init = self.__init_context()

        x86_ctx_out, reil_ctx_out = self.__run_code(asm, 0xdeadbeef, ctx_init)

        cmp_result = self.__compare_contexts(ctx_init, x86_ctx_out, reil_ctx_out)

        if not cmp_result:
            self.__save_failing_context(ctx_init)

        self.assertTrue(cmp_result, self.__print_contexts(ctx_init, x86_ctx_out, reil_ctx_out))

    def test_setb(self):
        asm = ["setb al"]

        ctx_init = self.__init_context()

        x86_ctx_out, reil_ctx_out = self.__run_code(asm, 0xdeadbeef, ctx_init)

        cmp_result = self.__compare_contexts(ctx_init, x86_ctx_out, reil_ctx_out)

        if not cmp_result:
            self.__save_failing_context(ctx_init)

        self.assertTrue(cmp_result, self.__print_contexts(ctx_init, x86_ctx_out, reil_ctx_out))

    def test_setbe(self):
        asm = ["setbe al"]

        ctx_init = self.__init_context()

        x86_ctx_out, reil_ctx_out = self.__run_code(asm, 0xdeadbeef, ctx_init)

        cmp_result = self.__compare_contexts(ctx_init, x86_ctx_out, reil_ctx_out)

        if not cmp_result:
            self.__save_failing_context(ctx_init)

        self.assertTrue(cmp_result, self.__print_contexts(ctx_init, x86_ctx_out, reil_ctx_out))

    def test_setc(self):
        asm = ["setc al"]

        ctx_init = self.__init_context()

        x86_ctx_out, reil_ctx_out = self.__run_code(asm, 0xdeadbeef, ctx_init)

        cmp_result = self.__compare_contexts(ctx_init, x86_ctx_out, reil_ctx_out)

        if not cmp_result:
            self.__save_failing_context(ctx_init)

        self.assertTrue(cmp_result, self.__print_contexts(ctx_init, x86_ctx_out, reil_ctx_out))

    def test_sete(self):
        asm = ["sete al"]

        ctx_init = self.__init_context()

        x86_ctx_out, reil_ctx_out = self.__run_code(asm, 0xdeadbeef, ctx_init)

        cmp_result = self.__compare_contexts(ctx_init, x86_ctx_out, reil_ctx_out)

        if not cmp_result:
            self.__save_failing_context(ctx_init)

        self.assertTrue(cmp_result, self.__print_contexts(ctx_init, x86_ctx_out, reil_ctx_out))

    def test_setg(self):
        asm = ["setg al"]

        ctx_init = self.__init_context()

        x86_ctx_out, reil_ctx_out = self.__run_code(asm, 0xdeadbeef, ctx_init)

        cmp_result = self.__compare_contexts(ctx_init, x86_ctx_out, reil_ctx_out)

        if not cmp_result:
            self.__save_failing_context(ctx_init)

        self.assertTrue(cmp_result, self.__print_contexts(ctx_init, x86_ctx_out, reil_ctx_out))

    def test_setge(self):
        asm = ["setge al"]

        ctx_init = self.__init_context()

        x86_ctx_out, reil_ctx_out = self.__run_code(asm, 0xdeadbeef, ctx_init)

        cmp_result = self.__compare_contexts(ctx_init, x86_ctx_out, reil_ctx_out)

        if not cmp_result:
            self.__save_failing_context(ctx_init)

        self.assertTrue(cmp_result, self.__print_contexts(ctx_init, x86_ctx_out, reil_ctx_out))

    def test_setl(self):
        asm = ["setl al"]

        ctx_init = self.__init_context()

        x86_ctx_out, reil_ctx_out = self.__run_code(asm, 0xdeadbeef, ctx_init)

        cmp_result = self.__compare_contexts(ctx_init, x86_ctx_out, reil_ctx_out)

        if not cmp_result:
            self.__save_failing_context(ctx_init)

        self.assertTrue(cmp_result, self.__print_contexts(ctx_init, x86_ctx_out, reil_ctx_out))

    def test_setle(self):
        asm = ["setle al"]

        ctx_init = self.__init_context()

        x86_ctx_out, reil_ctx_out = self.__run_code(asm, 0xdeadbeef, ctx_init)

        cmp_result = self.__compare_contexts(ctx_init, x86_ctx_out, reil_ctx_out)

        if not cmp_result:
            self.__save_failing_context(ctx_init)

        self.assertTrue(cmp_result, self.__print_contexts(ctx_init, x86_ctx_out, reil_ctx_out))

    def test_setna(self):
        asm = ["setna al"]

        ctx_init = self.__init_context()

        x86_ctx_out, reil_ctx_out = self.__run_code(asm, 0xdeadbeef, ctx_init)

        cmp_result = self.__compare_contexts(ctx_init, x86_ctx_out, reil_ctx_out)

        if not cmp_result:
            self.__save_failing_context(ctx_init)

        self.assertTrue(cmp_result, self.__print_contexts(ctx_init, x86_ctx_out, reil_ctx_out))

    def test_setnae(self):
        asm = ["setnae al"]

        ctx_init = self.__init_context()

        x86_ctx_out, reil_ctx_out = self.__run_code(asm, 0xdeadbeef, ctx_init)

        cmp_result = self.__compare_contexts(ctx_init, x86_ctx_out, reil_ctx_out)

        if not cmp_result:
            self.__save_failing_context(ctx_init)

        self.assertTrue(cmp_result, self.__print_contexts(ctx_init, x86_ctx_out, reil_ctx_out))

    def test_setnb(self):
        asm = ["setnb al"]

        ctx_init = self.__init_context()

        x86_ctx_out, reil_ctx_out = self.__run_code(asm, 0xdeadbeef, ctx_init)

        cmp_result = self.__compare_contexts(ctx_init, x86_ctx_out, reil_ctx_out)

        if not cmp_result:
            self.__save_failing_context(ctx_init)

        self.assertTrue(cmp_result, self.__print_contexts(ctx_init, x86_ctx_out, reil_ctx_out))

    def test_setnbe(self):
        asm = ["setnbe al"]

        ctx_init = self.__init_context()

        x86_ctx_out, reil_ctx_out = self.__run_code(asm, 0xdeadbeef, ctx_init)

        cmp_result = self.__compare_contexts(ctx_init, x86_ctx_out, reil_ctx_out)

        if not cmp_result:
            self.__save_failing_context(ctx_init)

        self.assertTrue(cmp_result, self.__print_contexts(ctx_init, x86_ctx_out, reil_ctx_out))

    def test_setnc(self):
        asm = ["setnc al"]

        ctx_init = self.__init_context()

        x86_ctx_out, reil_ctx_out = self.__run_code(asm, 0xdeadbeef, ctx_init)

        cmp_result = self.__compare_contexts(ctx_init, x86_ctx_out, reil_ctx_out)

        if not cmp_result:
            self.__save_failing_context(ctx_init)

        self.assertTrue(cmp_result, self.__print_contexts(ctx_init, x86_ctx_out, reil_ctx_out))

    def test_setne(self):
        asm = ["setne al"]

        ctx_init = self.__init_context()

        x86_ctx_out, reil_ctx_out = self.__run_code(asm, 0xdeadbeef, ctx_init)

        cmp_result = self.__compare_contexts(ctx_init, x86_ctx_out, reil_ctx_out)

        if not cmp_result:
            self.__save_failing_context(ctx_init)

        self.assertTrue(cmp_result, self.__print_contexts(ctx_init, x86_ctx_out, reil_ctx_out))

    def test_setng(self):
        asm = ["setng al"]

        ctx_init = self.__init_context()

        x86_ctx_out, reil_ctx_out = self.__run_code(asm, 0xdeadbeef, ctx_init)

        cmp_result = self.__compare_contexts(ctx_init, x86_ctx_out, reil_ctx_out)

        if not cmp_result:
            self.__save_failing_context(ctx_init)

        self.assertTrue(cmp_result, self.__print_contexts(ctx_init, x86_ctx_out, reil_ctx_out))

    def test_setnge(self):
        asm = ["setnge al"]

        ctx_init = self.__init_context()

        x86_ctx_out, reil_ctx_out = self.__run_code(asm, 0xdeadbeef, ctx_init)

        cmp_result = self.__compare_contexts(ctx_init, x86_ctx_out, reil_ctx_out)

        if not cmp_result:
            self.__save_failing_context(ctx_init)

        self.assertTrue(cmp_result, self.__print_contexts(ctx_init, x86_ctx_out, reil_ctx_out))

    def test_setnl(self):
        asm = ["setnl al"]

        ctx_init = self.__init_context()

        x86_ctx_out, reil_ctx_out = self.__run_code(asm, 0xdeadbeef, ctx_init)

        cmp_result = self.__compare_contexts(ctx_init, x86_ctx_out, reil_ctx_out)

        if not cmp_result:
            self.__save_failing_context(ctx_init)

        self.assertTrue(cmp_result, self.__print_contexts(ctx_init, x86_ctx_out, reil_ctx_out))

    def test_setnle(self):
        asm = ["setnle al"]

        ctx_init = self.__init_context()

        x86_ctx_out, reil_ctx_out = self.__run_code(asm, 0xdeadbeef, ctx_init)

        cmp_result = self.__compare_contexts(ctx_init, x86_ctx_out, reil_ctx_out)

        if not cmp_result:
            self.__save_failing_context(ctx_init)

        self.assertTrue(cmp_result, self.__print_contexts(ctx_init, x86_ctx_out, reil_ctx_out))

    def test_setno(self):
        asm = ["setno al"]

        ctx_init = self.__init_context()

        x86_ctx_out, reil_ctx_out = self.__run_code(asm, 0xdeadbeef, ctx_init)

        cmp_result = self.__compare_contexts(ctx_init, x86_ctx_out, reil_ctx_out)

        if not cmp_result:
            self.__save_failing_context(ctx_init)

        self.assertTrue(cmp_result, self.__print_contexts(ctx_init, x86_ctx_out, reil_ctx_out))

    def test_setnp(self):
        asm = ["setnp al"]

        ctx_init = self.__init_context()

        x86_ctx_out, reil_ctx_out = self.__run_code(asm, 0xdeadbeef, ctx_init)

        cmp_result = self.__compare_contexts(ctx_init, x86_ctx_out, reil_ctx_out)

        if not cmp_result:
            self.__save_failing_context(ctx_init)

        self.assertTrue(cmp_result, self.__print_contexts(ctx_init, x86_ctx_out, reil_ctx_out))

    def test_setns(self):
        asm = ["setns al"]

        ctx_init = self.__init_context()

        x86_ctx_out, reil_ctx_out = self.__run_code(asm, 0xdeadbeef, ctx_init)

        cmp_result = self.__compare_contexts(ctx_init, x86_ctx_out, reil_ctx_out)

        if not cmp_result:
            self.__save_failing_context(ctx_init)

        self.assertTrue(cmp_result, self.__print_contexts(ctx_init, x86_ctx_out, reil_ctx_out))

    def test_setnz(self):
        asm = ["setnz al"]

        ctx_init = self.__init_context()

        x86_ctx_out, reil_ctx_out = self.__run_code(asm, 0xdeadbeef, ctx_init)

        cmp_result = self.__compare_contexts(ctx_init, x86_ctx_out, reil_ctx_out)

        if not cmp_result:
            self.__save_failing_context(ctx_init)

        self.assertTrue(cmp_result, self.__print_contexts(ctx_init, x86_ctx_out, reil_ctx_out))

    def test_seto(self):
        asm = ["seto al"]

        ctx_init = self.__init_context()

        x86_ctx_out, reil_ctx_out = self.__run_code(asm, 0xdeadbeef, ctx_init)

        cmp_result = self.__compare_contexts(ctx_init, x86_ctx_out, reil_ctx_out)

        if not cmp_result:
            self.__save_failing_context(ctx_init)

        self.assertTrue(cmp_result, self.__print_contexts(ctx_init, x86_ctx_out, reil_ctx_out))

    def test_setp(self):
        asm = ["setp al"]

        ctx_init = self.__init_context()

        x86_ctx_out, reil_ctx_out = self.__run_code(asm, 0xdeadbeef, ctx_init)

        cmp_result = self.__compare_contexts(ctx_init, x86_ctx_out, reil_ctx_out)

        if not cmp_result:
            self.__save_failing_context(ctx_init)

        self.assertTrue(cmp_result, self.__print_contexts(ctx_init, x86_ctx_out, reil_ctx_out))

    def test_setpe(self):
        asm = ["setpe al"]

        ctx_init = self.__init_context()

        x86_ctx_out, reil_ctx_out = self.__run_code(asm, 0xdeadbeef, ctx_init)

        cmp_result = self.__compare_contexts(ctx_init, x86_ctx_out, reil_ctx_out)

        if not cmp_result:
            self.__save_failing_context(ctx_init)

        self.assertTrue(cmp_result, self.__print_contexts(ctx_init, x86_ctx_out, reil_ctx_out))

    def test_setpo(self):
        asm = ["setpo al"]

        ctx_init = self.__init_context()

        x86_ctx_out, reil_ctx_out = self.__run_code(asm, 0xdeadbeef, ctx_init)

        cmp_result = self.__compare_contexts(ctx_init, x86_ctx_out, reil_ctx_out)

        if not cmp_result:
            self.__save_failing_context(ctx_init)

        self.assertTrue(cmp_result, self.__print_contexts(ctx_init, x86_ctx_out, reil_ctx_out))

    def test_sets(self):
        asm = ["sets al"]

        ctx_init = self.__init_context()

        x86_ctx_out, reil_ctx_out = self.__run_code(asm, 0xdeadbeef, ctx_init)

        cmp_result = self.__compare_contexts(ctx_init, x86_ctx_out, reil_ctx_out)

        if not cmp_result:
            self.__save_failing_context(ctx_init)

        self.assertTrue(cmp_result, self.__print_contexts(ctx_init, x86_ctx_out, reil_ctx_out))

    def test_setz(self):
        asm = ["setz al"]

        ctx_init = self.__init_context()

        x86_ctx_out, reil_ctx_out = self.__run_code(asm, 0xdeadbeef, ctx_init)

        cmp_result = self.__compare_contexts(ctx_init, x86_ctx_out, reil_ctx_out)

        if not cmp_result:
            self.__save_failing_context(ctx_init)

        self.assertTrue(cmp_result, self.__print_contexts(ctx_init, x86_ctx_out, reil_ctx_out))

    def test_all_jcc(self):
        conds = [
            'a', 'ae', 'b', 'be', 'c', 'e', 'g', 'ge', 'l', 'le', 'na', 'nae',
            'nb', 'nbe', 'nc', 'ne', 'ng', 'nge', 'nl', 'nle', 'no', 'np', 'ns',
            'nz', 'o', 'p', 'pe', 'po', 's', 'z'
        ]

        for c in conds:
            self.__test_jcc(c)

    def __test_jcc(self, jmp_cond):
        untouched_value = 0x45454545
        touched_value = 0x31313131

        asm = [
            "mov rax, 0x{:x}".format(untouched_value),
           "j" + jmp_cond + " {:s}",
           "mov rax, 0x{:x}".format(touched_value),
           "xchg rax, rax",
        ]

        asm_reil = list(asm)
        asm_reil[1] = asm_reil[1].format(str(0xdeadbeef + 0x3))

        asm_pyasmjit = list(asm)
        asm_pyasmjit[1] = asm_pyasmjit[1].format("$+0x07")

        reil_instrs = self.__asm_to_reil(asm_reil, 0xdeadbeef)

        ctx_init = self.__init_context()

        _, x86_ctx_out = pyasmjit.x86_64_execute("\n".join(asm_pyasmjit), ctx_init)
        reil_ctx_out, _ = self.reil_emulator.execute(
            reil_instrs,
            start=0xdeadbeef << 8,
            registers=ctx_init
        )
        reil_ctx_out = self.__fix_reil_flags(reil_ctx_out, x86_ctx_out)

        cmp_result = self.__compare_contexts(ctx_init, x86_ctx_out, reil_ctx_out)

        if not cmp_result:
            self.__save_failing_context(ctx_init)

        self.assertTrue(cmp_result, self.__print_contexts(ctx_init, x86_ctx_out, reil_ctx_out))

    def test_shrd_1(self):
        asm = ["shrd eax, ebx, 3"]

        ctx_init = self.__init_context()

        x86_ctx_out, reil_ctx_out = self.__run_code(asm, 0xdeadbeef, ctx_init)

        # TODO Test flags.

        cmp_result = self.__compare_contexts(ctx_init, x86_ctx_out, reil_ctx_out)

        if not cmp_result:
            self.__save_failing_context(ctx_init)

        self.assertTrue(cmp_result, self.__print_contexts(ctx_init, x86_ctx_out, reil_ctx_out))

    def test_shr_1(self):
        asm = ["shr eax, 3"]

        ctx_init = self.__init_context()

        x86_ctx_out, reil_ctx_out = self.__run_code(asm, 0xdeadbeef, ctx_init)

        # Undefined flags...
        reil_ctx_out = self.__fix_reil_flag(reil_ctx_out, x86_ctx_out, "af")

        # NOTE: OF and CF can be left undefined in some cases. They are
        # not cover by this test.
        reil_ctx_out = self.__fix_reil_flag(reil_ctx_out, x86_ctx_out, "cf")
        reil_ctx_out = self.__fix_reil_flag(reil_ctx_out, x86_ctx_out, "of")

        cmp_result = self.__compare_contexts(ctx_init, x86_ctx_out, reil_ctx_out)

        if not cmp_result:
            self.__save_failing_context(ctx_init)

        self.assertTrue(cmp_result, self.__print_contexts(ctx_init, x86_ctx_out, reil_ctx_out))

    def test_shr_2(self):
        asm = ["shr eax, cl"]

        ctx_init = self.__init_context()

        ctx_init["rax"] = 0x10000
        ctx_init["rcx"] = 0x32

        x86_ctx_out, reil_ctx_out = self.__run_code(asm, 0xdeadbeef, ctx_init)

        # Undefined flags...
        reil_ctx_out = self.__fix_reil_flag(reil_ctx_out, x86_ctx_out, "af")

        # NOTE: OF and CF can be left undefined in some cases. They are
        # not cover by this test.
        reil_ctx_out = self.__fix_reil_flag(reil_ctx_out, x86_ctx_out, "cf")
        reil_ctx_out = self.__fix_reil_flag(reil_ctx_out, x86_ctx_out, "of")

        cmp_result = self.__compare_contexts(ctx_init, x86_ctx_out, reil_ctx_out)

        if not cmp_result:
            self.__save_failing_context(ctx_init)

        self.assertTrue(cmp_result, self.__print_contexts(ctx_init, x86_ctx_out, reil_ctx_out))

    def test_shl_1(self):
        asm = ["shl eax, 3"]

        ctx_init = self.__init_context()

        x86_ctx_out, reil_ctx_out = self.__run_code(asm, 0xdeadbeef, ctx_init)

        # Undefined flags...
        reil_ctx_out = self.__fix_reil_flag(reil_ctx_out, x86_ctx_out, "af")

        # NOTE: OF and CF can be left undefined in some cases. They are
        # not cover by this test.
        reil_ctx_out = self.__fix_reil_flag(reil_ctx_out, x86_ctx_out, "cf")
        reil_ctx_out = self.__fix_reil_flag(reil_ctx_out, x86_ctx_out, "of")

        cmp_result = self.__compare_contexts(ctx_init, x86_ctx_out, reil_ctx_out)

        if not cmp_result:
            self.__save_failing_context(ctx_init)

        self.assertTrue(cmp_result, self.__print_contexts(ctx_init, x86_ctx_out, reil_ctx_out))

    def test_shl_2(self):
        asm = ["shl eax, cl"]

        ctx_init = self.__init_context()

        ctx_init["rax"] = 0x01
        ctx_init["rcx"] = 0x32

        x86_ctx_out, reil_ctx_out = self.__run_code(asm, 0xdeadbeef, ctx_init)

        # Undefined flags...
        reil_ctx_out = self.__fix_reil_flag(reil_ctx_out, x86_ctx_out, "af")

        # NOTE: OF and CF can be left undefined in some cases. They are
        # not cover by this test.
        reil_ctx_out = self.__fix_reil_flag(reil_ctx_out, x86_ctx_out, "cf")
        reil_ctx_out = self.__fix_reil_flag(reil_ctx_out, x86_ctx_out, "of")

        cmp_result = self.__compare_contexts(ctx_init, x86_ctx_out, reil_ctx_out)

        if not cmp_result:
            self.__save_failing_context(ctx_init)

        self.assertTrue(cmp_result, self.__print_contexts(ctx_init, x86_ctx_out, reil_ctx_out))

    def test_sal(self):
        asm = ["sal eax, 3"]

        ctx_init = self.__init_context()

        x86_ctx_out, reil_ctx_out = self.__run_code(asm, 0xdeadbeef, ctx_init)

        # Undefined flags...
        reil_ctx_out = self.__fix_reil_flag(reil_ctx_out, x86_ctx_out, "af")

        # NOTE: OF and CF can be left undefined in some cases. They are
        # not cover by this test.
        reil_ctx_out = self.__fix_reil_flag(reil_ctx_out, x86_ctx_out, "cf")
        reil_ctx_out = self.__fix_reil_flag(reil_ctx_out, x86_ctx_out, "of")

        cmp_result = self.__compare_contexts(ctx_init, x86_ctx_out, reil_ctx_out)

        if not cmp_result:
            self.__save_failing_context(ctx_init)

        self.assertTrue(cmp_result, self.__print_contexts(ctx_init, x86_ctx_out, reil_ctx_out))

    def test_sar(self):
        asm = ["sar eax, 3"]

        ctx_init = self.__init_context()

        x86_ctx_out, reil_ctx_out = self.__run_code(asm, 0xdeadbeef, ctx_init)

        # Undefined flags...
        reil_ctx_out = self.__fix_reil_flag(reil_ctx_out, x86_ctx_out, "af")

        # NOTE: OF and CF can be left undefined in some cases. They are
        # not cover by this test.
        reil_ctx_out = self.__fix_reil_flag(reil_ctx_out, x86_ctx_out, "cf")
        reil_ctx_out = self.__fix_reil_flag(reil_ctx_out, x86_ctx_out, "of")

        cmp_result = self.__compare_contexts(ctx_init, x86_ctx_out, reil_ctx_out)

        if not cmp_result:
            self.__save_failing_context(ctx_init)

        self.assertTrue(cmp_result, self.__print_contexts(ctx_init, x86_ctx_out, reil_ctx_out))

    def test_stc(self):
        asm = ["stc"]

        ctx_init = self.__init_context()

        x86_ctx_out, reil_ctx_out = self.__run_code(asm, 0xdeadbeef, ctx_init)

        cmp_result = self.__compare_contexts(ctx_init, x86_ctx_out, reil_ctx_out)

        if not cmp_result:
            self.__save_failing_context(ctx_init)

        self.assertTrue(cmp_result, self.__print_contexts(ctx_init, x86_ctx_out, reil_ctx_out))

    def test_rol(self):
        asm = ["rol eax, 8"]

        ctx_init = self.__init_context()

        x86_ctx_out, reil_ctx_out = self.__run_code(asm, 0xdeadbeef, ctx_init)

        # NOTE: OF and CF can be left undefined in some cases. They are
        # not cover by this test.
        reil_ctx_out = self.__fix_reil_flag(reil_ctx_out, x86_ctx_out, "cf")
        reil_ctx_out = self.__fix_reil_flag(reil_ctx_out, x86_ctx_out, "of")

        cmp_result = self.__compare_contexts(ctx_init, x86_ctx_out, reil_ctx_out)

        if not cmp_result:
            self.__save_failing_context(ctx_init)

        self.assertTrue(cmp_result, self.__print_contexts(ctx_init, x86_ctx_out, reil_ctx_out))

    def test_ror(self):
        asm = ["ror eax, 8"]

        ctx_init = self.__init_context()

        x86_ctx_out, reil_ctx_out = self.__run_code(asm, 0xdeadbeef, ctx_init)

        # NOTE: OF and CF can be left undefined in some cases. They are
        # not cover by this test.
        reil_ctx_out = self.__fix_reil_flag(reil_ctx_out, x86_ctx_out, "cf")
        reil_ctx_out = self.__fix_reil_flag(reil_ctx_out, x86_ctx_out, "of")

        cmp_result = self.__compare_contexts(ctx_init, x86_ctx_out, reil_ctx_out)

        if not cmp_result:
            self.__save_failing_context(ctx_init)

        self.assertTrue(cmp_result, self.__print_contexts(ctx_init, x86_ctx_out, reil_ctx_out))

    def test_rcl(self):
        asm = ["rcl eax, 8"]

        ctx_init = self.__init_context()

        # set carry flag
        ctx_init['rflags'] = ctx_init['rflags'] | 0x1

        x86_ctx_out, reil_ctx_out = self.__run_code(asm, 0xdeadbeef, ctx_init)

        # NOTE: OF and CF can be left undefined in some cases. They are
        # not cover by this test.
        reil_ctx_out = self.__fix_reil_flag(reil_ctx_out, x86_ctx_out, "cf")
        reil_ctx_out = self.__fix_reil_flag(reil_ctx_out, x86_ctx_out, "of")

        cmp_result = self.__compare_contexts(ctx_init, x86_ctx_out, reil_ctx_out)

        if not cmp_result:
            self.__save_failing_context(ctx_init)

        self.assertTrue(cmp_result, self.__print_contexts(ctx_init, x86_ctx_out, reil_ctx_out))

    def test_rcr(self):
        asm = ["rcr eax, 3"]

        ctx_init = self.__init_context()

        # set carry flag
        ctx_init['rflags'] = ctx_init['rflags'] | 0x1

        x86_ctx_out, reil_ctx_out = self.__run_code(asm, 0xdeadbeef, ctx_init)

        # NOTE: OF and CF can be left undefined in some cases. They are
        # not cover by this test.
        reil_ctx_out = self.__fix_reil_flag(reil_ctx_out, x86_ctx_out, "cf")
        reil_ctx_out = self.__fix_reil_flag(reil_ctx_out, x86_ctx_out, "of")

        cmp_result = self.__compare_contexts(ctx_init, x86_ctx_out, reil_ctx_out)

        if not cmp_result:
            self.__save_failing_context(ctx_init)

        self.assertTrue(cmp_result, self.__print_contexts(ctx_init, x86_ctx_out, reil_ctx_out))

    def test_bt(self):
        asm = ["bt eax, ebx"]

        ctx_init = self.__init_context()

        x86_ctx_out, reil_ctx_out = self.__run_code(asm, 0xdeadbeef, ctx_init)

        # NOTE: The OF, SF, AF, and PF flags are undefined.
        reil_ctx_out = self.__fix_reil_flag(reil_ctx_out, x86_ctx_out, "of")
        reil_ctx_out = self.__fix_reil_flag(reil_ctx_out, x86_ctx_out, "sf")
        reil_ctx_out = self.__fix_reil_flag(reil_ctx_out, x86_ctx_out, "af")
        reil_ctx_out = self.__fix_reil_flag(reil_ctx_out, x86_ctx_out, "pf")

        cmp_result = self.__compare_contexts(ctx_init, x86_ctx_out, reil_ctx_out)

        if not cmp_result:
            self.__save_failing_context(ctx_init)

        self.assertTrue(cmp_result, self.__print_contexts(ctx_init, x86_ctx_out, reil_ctx_out))

    def test_bts_1(self):
        asm = ["bts rdx, rsi"]

        ctx_init = self.__init_context()

        x86_ctx_out, reil_ctx_out = self.__run_code(asm, 0xdeadbeef, ctx_init)

        # NOTE: The OF, SF, AF, and PF flags are undefined.
        reil_ctx_out = self.__fix_reil_flag(reil_ctx_out, x86_ctx_out, "of")
        reil_ctx_out = self.__fix_reil_flag(reil_ctx_out, x86_ctx_out, "sf")
        reil_ctx_out = self.__fix_reil_flag(reil_ctx_out, x86_ctx_out, "af")
        reil_ctx_out = self.__fix_reil_flag(reil_ctx_out, x86_ctx_out, "pf")

        cmp_result = self.__compare_contexts(ctx_init, x86_ctx_out, reil_ctx_out)

        if not cmp_result:
            self.__save_failing_context(ctx_init)

        self.assertTrue(cmp_result, self.__print_contexts(ctx_init, x86_ctx_out, reil_ctx_out))

    def test_bts_2(self):
        asm = ["bts rdx, r11"]

        ctx_init = self.__init_context()

        ctx_init["rdx"] = 0x4000040010001
        ctx_init["r11"] = 0x07fffe4519001

        x86_ctx_out, reil_ctx_out = self.__run_code(asm, 0xdeadbeef, ctx_init)

        # NOTE: The OF, SF, AF, and PF flags are undefined.
        reil_ctx_out = self.__fix_reil_flag(reil_ctx_out, x86_ctx_out, "of")
        reil_ctx_out = self.__fix_reil_flag(reil_ctx_out, x86_ctx_out, "sf")
        reil_ctx_out = self.__fix_reil_flag(reil_ctx_out, x86_ctx_out, "af")
        reil_ctx_out = self.__fix_reil_flag(reil_ctx_out, x86_ctx_out, "pf")

        cmp_result = self.__compare_contexts(ctx_init, x86_ctx_out, reil_ctx_out)

        if not cmp_result:
            self.__save_failing_context(ctx_init)

        self.assertTrue(cmp_result, self.__print_contexts(ctx_init, x86_ctx_out, reil_ctx_out))

    def test_cmpxchg(self):
        asm = ["cmpxchg ebx, ecx"]

        ctx_init = self.__init_context()

        _, x86_ctx_out = pyasmjit.x86_64_execute("\n".join(asm), ctx_init)
        reil_ctx_out, _ = self.reil_emulator.execute(
            self.__asm_to_reil(asm, 0xdeadbeef),
            start=0xdeadbeef << 8,
            end=(0xdeadbeef + 0x1) << 8,
            registers=ctx_init
        )
        reil_ctx_out = self.__fix_reil_flags(reil_ctx_out, x86_ctx_out)

        cmp_result = self.__compare_contexts(ctx_init, x86_ctx_out, reil_ctx_out)

        if not cmp_result:
            self.__save_failing_context(ctx_init)

        self.assertTrue(cmp_result, self.__print_contexts(ctx_init, x86_ctx_out, reil_ctx_out))

    def test_movsx(self):
        asm = ["movsx eax, bx"]

        ctx_init = self.__init_context()

        x86_ctx_out, reil_ctx_out = self.__run_code(asm, 0xdeadbeef, ctx_init)

        cmp_result = self.__compare_contexts(ctx_init, x86_ctx_out, reil_ctx_out)

        if not cmp_result:
            self.__save_failing_context(ctx_init)

        self.assertTrue(cmp_result, self.__print_contexts(ctx_init, x86_ctx_out, reil_ctx_out))

    def test_sahf(self):
        asm = ["sahf"]

        ctx_init = self.__init_context()

        # Set all flags in AH
        ctx_init['rax'] = 0xff00

        # Clear all flags in RFLAGS
        flags_mapper = {
             0 : "cf",  # bit 0
             2 : "pf",  # bit 2
             4 : "af",  # bit 4
             6 : "zf",  # bit 6
             7 : "sf",  # bit 7
        }

        for bit, _ in flags_mapper.items():
            ctx_init['rflags'] = ctx_init['rflags'] & ((~2**bit) & 2**64-1)

        x86_ctx_out, reil_ctx_out = self.__run_code(asm, 0xdeadbeef, ctx_init)

        cmp_result = self.__compare_contexts(ctx_init, x86_ctx_out, reil_ctx_out)

        if not cmp_result:
            self.__save_failing_context(ctx_init)

        self.assertTrue(cmp_result, self.__print_contexts(ctx_init, x86_ctx_out, reil_ctx_out))

    # Auxiliary methods
    # ======================================================================== #
    def __init_context(self):
        """Initialize register with random values.
        """
        if os.path.isfile(self.context_filename):
            context = self.__load_failing_context()
        else:
            context = self.__create_random_context()

        return context

    def __create_random_context(self):
        context = {}

        for reg in self.arch_info.registers_gp_base:
            if reg not in ['rsp', 'rip', 'rbp']:
                min_value, max_value = 0, 2**self.arch_info.operand_size - 1
                context[reg] = random.randint(min_value, max_value)

        context['rflags'] = self.__create_random_flags()

        return context

    def __create_random_flags(self):
        # TODO: Check why PyAsmJIT throws an exception when DF flag is
        # set.
        flags_mapper = {
             0 : "cf",  # bit 0
             2 : "pf",  # bit 2
             4 : "af",  # bit 4
             6 : "zf",  # bit 6
             7 : "sf",  # bit 7
            # 10 : "df",  # bit 10
            11 : "of",  # bit 11
        }

        # Set 'mandatory' flags.
        flags = 0x202

        for bit, _ in flags_mapper.items():
            flags = flags | (2**bit * random.randint(0, 1))

        return flags

    def __load_failing_context(self):
        f = open(self.context_filename, "rb")
        context = pickle.load(f)
        f.close()

        return context

    def __save_failing_context(self, context):
        f = open(self.context_filename, "wb")
        pickle.dump(context, f)
        f.close()

    def __compare_contexts(self, context_init, x86_context, reil_context):
        match = True
        mask = 2**64-1

        for reg in sorted(context_init.keys()):
            if (x86_context[reg] & mask) != (reil_context[reg] & mask):
                match = False
                break

        return match

    def __print_contexts(self, context_init, x86_context, reil_context):
        out = "Contexts don't match!\n\n"

        header_fmt = " {0:^8s} : {1:^16s} | {2:>16s} ?= {3:<16s}\n"
        header = header_fmt.format("Register", "Initial", "x86", "REIL")
        ruler = "-" * len(header) + "\n"

        out += header
        out += ruler

        fmt = " {0:>8s} : {1:016x} | {2:016x} {eq} {3:016x} {marker}\n"

        mask = 2**64-1

        for reg in sorted(context_init.keys()):
            if (x86_context[reg] & mask) != (reil_context[reg] & mask):
                eq, marker = "!=", "<"
            else:
                eq, marker = "==", ""

            out += fmt.format(
                reg,
                context_init[reg] & mask,
                x86_context[reg] & mask,
                reil_context[reg] & mask,
                eq=eq,
                marker=marker
            )

        # Pretty print flags.
        reg = "rflags"
        fmt = "{0:s} ({1:>7s}) : {2:016x} ({3:s})"

        init_value = context_init[reg] & mask
        x86_value = x86_context[reg] & mask
        reil_value = reil_context[reg] & mask

        init_flags_str = self.__print_flags(context_init[reg])
        x86_flags_str = self.__print_flags(x86_context[reg])
        reil_flags_str = self.__print_flags(reil_context[reg])

        out += "\n"
        out += fmt.format(reg, "initial", init_value, init_flags_str) + "\n"
        out += fmt.format(reg, "x86", x86_value, x86_flags_str) + "\n"
        out += fmt.format(reg, "reil", reil_value, reil_flags_str)

        return out

    def __print_registers(self, registers):
        out = ""

        header_fmt = " {0:^8s} : {1:^16s}\n"
        header = header_fmt.format("Register", "Value")
        ruler = "-" * len(header) + "\n"

        out += header
        out += ruler

        fmt = " {0:>8s} : {1:016x}\n"

        for reg in sorted(registers.keys()):
            out += fmt.format(reg, registers[reg])

        print(out)

    def __print_flags(self, flags):
        # flags
        flags_mapper = {
             0 : "cf",  # bit 0
             2 : "pf",  # bit 2
             4 : "af",  # bit 4
             6 : "zf",  # bit 6
             7 : "sf",  # bit 7
            10 : "df",  # bit 10
            11 : "of",  # bit 11
        }

        out = ""

        for bit, flag in flags_mapper.items():
            flag_str = flag.upper() if flags & 2**bit else flag.lower()
            out += flag_str + " "

        return out[:-1]

    def __fix_reil_flag(self, reil_context, x86_context, flag):
        reil_context_out = dict(reil_context)

        flags_reg = 'eflags' if 'eflags' in reil_context_out else 'rflags'

        _, bit = self.arch_info.alias_mapper[flag]

        # Clean flag.
        reil_context_out[flags_reg] &= ~(2**bit) & (2**32-1)

        # Copy flag.
        reil_context_out[flags_reg] |= (x86_context[flags_reg] & 2**bit)

        return reil_context_out

    def __fix_reil_flags(self, reil_context, x86_context):
        reil_context_out = dict(reil_context)

        # Remove this when AF and PF are implemented.
        reil_context_out = self.__fix_reil_flag(reil_context_out, x86_context, "af")
        reil_context_out = self.__fix_reil_flag(reil_context_out, x86_context, "pf")

        return reil_context_out

    def __set_address(self, address, x86_instrs):
        addr = address

        for x86_instr in x86_instrs:
            x86_instr.address = addr
            x86_instr.size = 1
            addr += 1

    def __translate(self, asm_instrs):
        instr_container = ReilContainer()

        asm_instr_last = None
        instr_seq_prev = None

        for asm_instr in asm_instrs:
            instr_seq = ReilSequence()

            for reil_instr in self.x86_translator.translate(asm_instr):
                instr_seq.append(reil_instr)

            if instr_seq_prev:
                instr_seq_prev.next_sequence_address = instr_seq.address

            instr_container.add(instr_seq)

            instr_seq_prev = instr_seq

        if instr_seq_prev:
            if asm_instr_last:
                instr_seq_prev.next_sequence_address = (asm_instr_last.address + asm_instr_last.size) << 8

        return instr_container

    def __asm_to_reil(self, asm_list, address):
        x86_instrs = [self.x86_parser.parse(asm) for asm in asm_list]

        self.__set_address(address, x86_instrs)

        reil_instrs = self.__translate(x86_instrs)

        return reil_instrs

    def __run_code(self, asm_list, address, ctx_init):
        reil_instrs = self.__asm_to_reil(asm_list, address)

        _, x86_ctx_out = pyasmjit.x86_64_execute("\n".join(asm_list), ctx_init)
        reil_ctx_out, _ = self.reil_emulator.execute(reil_instrs, start=address << 8, registers=ctx_init)

        # Fix AF and PF.
        reil_ctx_out = self.__fix_reil_flags(reil_ctx_out, x86_ctx_out)

        return x86_ctx_out, reil_ctx_out


def main():
    unittest.main()


if __name__ == '__main__':
    main()
