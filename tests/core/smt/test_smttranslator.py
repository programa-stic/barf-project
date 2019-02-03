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

import unittest

from barf.arch.x86 import X86ArchitectureInformation
from barf.arch import ARCH_X86_MODE_32
from barf.core.reil.parser import ReilParser
from barf.core.smt.smtsolver import Z3Solver as SmtSolver
# from barf.core.smt.smtsolver import CVC4Solver as SmtSolver
from barf.core.smt.smttranslator import SmtTranslator


class SmtTranslatorTests(unittest.TestCase):

    def setUp(self):
        self._address_size = 32
        self._parser = ReilParser()
        self._solver = SmtSolver()
        self._translator = SmtTranslator(self._solver, self._address_size)

        self._arch_info = X86ArchitectureInformation(ARCH_X86_MODE_32)

        self._translator.set_arch_alias_mapper(self._arch_info.alias_mapper)
        self._translator.set_arch_registers_size(self._arch_info.registers_size)

    # Arithmetic Instructions
    def test_translate_add_1(self):
        # Same size operands.
        instr = self._parser.parse(["add [BYTE t0, BYTE t1, BYTE t2]"])[0]
        form = self._translator.translate(instr)

        self.assertEqual(len(form), 1)
        self.assertEqual(form[0].value, "(= t2_1 (bvadd t0_0 t1_0))")

    def test_translate_add_2(self):
        # Destination operand larger than source operands.
        instr = self._parser.parse(["add [BYTE t0, BYTE t1, WORD t2]"])[0]
        form = self._translator.translate(instr)

        self.assertEqual(len(form), 1)
        self.assertEqual(form[0].value, "(= t2_1 (bvadd ((_ zero_extend 8) t0_0) ((_ zero_extend 8) t1_0)))")

    def test_translate_add_3(self):
        # Destination operand smaller than source operands.
        instr = self._parser.parse(["add [WORD t0, WORD t1, BYTE t2]"])[0]
        form = self._translator.translate(instr)

        self.assertEqual(len(form), 1)
        self.assertEqual(form[0].value, "(= t2_1 ((_ extract 7 0) (bvadd t0_0 t1_0)))")

    def test_translate_add_4(self):
        # Mixed source operands.
        instr = self._parser.parse(["add [BYTE t0, BYTE 0x12, WORD t2]"])[0]
        form = self._translator.translate(instr)

        self.assertEqual(len(form), 1)
        self.assertEqual(form[0].value, "(= t2_1 (bvadd ((_ zero_extend 8) t0_0) ((_ zero_extend 8) #x12)))")

    def test_translate_sub(self):
        instr = self._parser.parse(["sub [BYTE t0, BYTE t1, BYTE t2]"])[0]
        form = self._translator.translate(instr)

        self.assertEqual(len(form), 1)
        self.assertEqual(form[0].value, "(= t2_1 (bvsub t0_0 t1_0))")

    def test_translate_mul(self):
        instr = self._parser.parse(["mul [BYTE t0, BYTE t1, BYTE t2]"])[0]
        form = self._translator.translate(instr)

        self.assertEqual(len(form), 1)
        self.assertEqual(form[0].value, "(= t2_1 (bvmul t0_0 t1_0))")

    def test_translate_div(self):
        instr = self._parser.parse(["div [BYTE t0, BYTE t1, BYTE t2]"])[0]
        form = self._translator.translate(instr)

        self.assertEqual(len(form), 1)
        self.assertEqual(form[0].value, "(= t2_1 (bvudiv t0_0 t1_0))")

    def test_translate_mod(self):
        instr = self._parser.parse(["mod [BYTE t0, BYTE t1, BYTE t2]"])[0]
        form = self._translator.translate(instr)

        self.assertEqual(len(form), 1)
        self.assertEqual(form[0].value, "(= t2_1 (bvurem t0_0 t1_0))")

    def test_translate_bsh(self):
        instr = self._parser.parse(["bsh [DWORD t0, DWORD t1, DWORD t2]"])[0]
        form = self._translator.translate(instr)

        self.assertEqual(len(form), 1)
        self.assertEqual(form[0].value, "(= t2_1 (ite (bvsge t1_0 #x00000000) (bvshl t0_0 t1_0) (bvlshr t0_0 (bvneg t1_0))))")

    # Bitwise Instructions
    def test_translate_and(self):
        instr = self._parser.parse(["and [BYTE t0, BYTE t1, BYTE t2]"])[0]
        form = self._translator.translate(instr)

        self.assertEqual(len(form), 1)
        self.assertEqual(form[0].value, "(= t2_1 (bvand t0_0 t1_0))")

    def test_translate_or(self):
        instr = self._parser.parse(["or [BYTE t0, BYTE t1, BYTE t2]"])[0]
        form = self._translator.translate(instr)

        self.assertEqual(len(form), 1)
        self.assertEqual(form[0].value, "(= t2_1 (bvor t0_0 t1_0))")

    def test_translate_xor(self):
        instr = self._parser.parse(["xor [BYTE t0, BYTE t1, BYTE t2]"])[0]
        form = self._translator.translate(instr)

        self.assertEqual(len(form), 1)
        self.assertEqual(form[0].value, "(= t2_1 (bvxor t0_0 t1_0))")

    # Data Transfer Instructions
    def test_translate_ldm(self):
        instr = self._parser.parse(["ldm [DWORD t0, empty, BYTE t2]"])[0]
        form = self._translator.translate(instr)

        self.assertEqual(len(form), 1)
        self.assertEqual(form[0].value, "(= (select MEM_0 (bvadd t0_0 #x00000000)) t2_1)")

    def test_translate_stm(self):
        instr = self._parser.parse(["stm [BYTE t0, empty, DWORD t2]"])[0]
        form = self._translator.translate(instr)

        self.assertEqual(len(form), 1)
        self.assertEqual(form[0].value, "(= MEM_1 (store MEM_0 (bvadd t2_0 #x00000000) t0_0))")

    def test_translate_str(self):
        instr = self._parser.parse(["str [BYTE t0, empty, BYTE t2]"])[0]
        form = self._translator.translate(instr)

        self.assertEqual(len(form), 1)
        self.assertEqual(form[0].value, "(= t2_1 t0_0)")

    # Conditional Instructions
    def test_translate_bisz(self):
        instr = self._parser.parse(["bisz [DWORD t0, empty, DWORD t2]"])[0]
        form = self._translator.translate(instr)

        self.assertEqual(len(form), 1)
        self.assertEqual(form[0].value, "(= t2_1 (ite (= t0_0 #x00000000) #x00000001 #x00000000))")

    def test_translate_jcc(self):
        instr = self._parser.parse(["jcc [BIT t0, empty, DWORD t2]"])[0]
        form = self._translator.translate(instr)

        self.assertEqual(len(form), 1)
        self.assertEqual(form[0].value, "(not (= t0_0 #b0))")

    # Other Instructions
    def test_translate_undef(self):
        instr = self._parser.parse(["undef [empty, empty, DWORD t2]"])[0]

        with self.assertRaises(Exception) as context:
            self._translator.translate(instr)

            self.assertTrue("Unsupported instruction : UNDEF" in context.exception)

    def test_translate_unkn(self):
        instr = self._parser.parse(["unkn [empty, empty, empty]"])[0]

        with self.assertRaises(Exception) as context:
            self._translator.translate(instr)

            self.assertTrue("Unsupported instruction : UNKN" in context.exception)

    def test_translate_nop(self):
        instr = self._parser.parse(["nop [empty, empty, empty]"])[0]
        form = self._translator.translate(instr)

        self.assertEqual(len(form), 0)

    # Extensions
    def test_translate_sext(self):
        instr = self._parser.parse(["sext [BYTE t0, empty, WORD t2]"])[0]
        form = self._translator.translate(instr)

        self.assertEqual(len(form), 1)
        self.assertEqual(form[0].value, "(= t2_1 ((_ sign_extend 8) t0_0))")

    def test_translate_sdiv(self):
        instr = self._parser.parse(["sdiv [BYTE t0, BYTE t1, BYTE t2]"])[0]
        form = self._translator.translate(instr)

        self.assertEqual(len(form), 1)
        self.assertEqual(form[0].value, "(= t2_1 (bvsdiv t0_0 t1_0))")

    def test_translate_smod(self):
        instr = self._parser.parse(["smod [BYTE t0, BYTE t1, BYTE t2]"])[0]
        form = self._translator.translate(instr)

        self.assertEqual(len(form), 1)
        self.assertEqual(form[0].value, "(= t2_1 (bvsmod t0_0 t1_0))")


def main():
    unittest.main()


if __name__ == '__main__':
    main()
