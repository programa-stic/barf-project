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

import unittest

from barf.analysis.codeanalyzer import CodeAnalyzer
from barf.analysis.gadget.gadget import GadgetType
from barf.analysis.gadget.gadgetclassifier import GadgetClassifier
from barf.analysis.gadget.gadgetfinder import GadgetFinder
from barf.analysis.gadget.gadgetverifier import GadgetVerifier
from barf.arch import ARCH_X86
from barf.arch import ARCH_X86_MODE_32
from barf.arch import ARCH_X86_MODE_64
from barf.arch.x86.x86base import X86ArchitectureInformation
from barf.arch.x86.x86disassembler import X86Disassembler
from barf.arch.x86.x86translator import LITE_TRANSLATION
from barf.arch.x86.x86translator import X86Translator
from barf.core.reil import ReilEmptyOperand
from barf.core.reil import ReilEmulator
from barf.core.reil import ReilImmediateOperand
from barf.core.reil import ReilRegisterOperand
from barf.core.smt.smtlibv2 import Z3Solver as SmtSolver
from barf.core.smt.smttranslator import SmtTranslator


class GadgetClassifierTests(unittest.TestCase):

    def setUp(self):
        self._arch_info = X86ArchitectureInformation(ARCH_X86_MODE_32)

        self._ir_emulator = ReilEmulator(self._arch_info)

        self._g_classifier = GadgetClassifier(self._ir_emulator, self._arch_info)

    # FIXME: Don't take into account esp modification because of RET instruction.
    # def test_nop_1(self):
    #     # testing : nop
    #     binary  = "\x90"                     # 0x00 : (1) nop
    #     binary += "\xc3"                     # 0x00 : (1) ret

    #     g_finder = GadgetFinder(X86Disassembler(), binary, X86Translator(translation_mode=LITE_TRANSLATION), ARCH_X86, ARCH_X86_MODE_32)

    #     g_candidates = g_finder.find(0x00000000, 0x00000001)
    #     g_classified = self._g_classifier.classify(g_candidates[0])

    #     # self.print_candidates(g_candidates)
    #     # self.print_classified(g_classified)

    #     self.assertEquals(len(g_candidates), 1)
    #     self.assertEquals(len(g_classified), 1)

    #     self.assertEquals(g_classified[0].type, GadgetType.NoOperation)
    #     self.assertEquals(g_classified[0].sources, [])
    #     self.assertEquals(g_classified[0].destination, [])

    #     self.assertEquals(len(g_classified[0].modified_registers), 0)

    # FIXME: Don't take into account esp modification because of RET instruction.
    # def test_nop_2(self):
    #     # testing : nop
    #     binary  = "\x89\xc0"                 # 0X00 : (2) mov eax, eax
    #     binary += "\xc3"                     # 0X02 : (1) ret

    #     g_finder = GadgetFinder(X86Disassembler(), binary, X86Translator(translation_mode=LITE_TRANSLATION), ARCH_X86, ARCH_X86_MODE_32)

    #     g_candidates = g_finder.find(0x00000000, 0x00000002)
    #     g_classified = self._g_classifier.classify(g_candidates[0])

    #     self.assertEquals(len(g_candidates), 1)
    #     self.assertEquals(len(g_classified), 1)

    #     # self.print_candidates(g_candidates)
    #     # self.print_classified(g_classified)

    #     self.assertEquals(g_classified[0].type, GadgetType.NoOperation)
    #     self.assertEquals(g_classified[0].sources, [])
    #     self.assertEquals(g_classified[0].destination, [])

    #     self.assertEquals(len(g_classified[0].modified_registers), 0)

    #     self.assertFalse(ReilRegisterOperand("eax", 32) in g_classified[0].modified_registers)

    def test_move_register_1(self):
        # testing : dst_reg <- src_reg
        binary  = "\x89\xd8"                 # 0x00 : (2) mov eax, ebx
        binary += "\xc3"                     # 0x02 : (1) ret

        g_finder = GadgetFinder(X86Disassembler(), binary, X86Translator(translation_mode=LITE_TRANSLATION), ARCH_X86, ARCH_X86_MODE_32)

        g_candidates = g_finder.find(0x00000000, 0x00000002)
        g_classified = self._g_classifier.classify(g_candidates[0])

        # self.print_candidates(g_candidates)
        # self.print_classified(g_classified)

        self.assertEquals(len(g_candidates), 1)
        self.assertEquals(len(g_classified), 1)

        self.assertEquals(g_classified[0].type, GadgetType.MoveRegister)
        self.assertEquals(g_classified[0].sources, [ReilRegisterOperand("ebx", 32)])
        self.assertEquals(g_classified[0].destination, [ReilRegisterOperand("eax", 32)])

        self.assertEquals(len(g_classified[0].modified_registers), 1)

        self.assertFalse(ReilRegisterOperand("eax", 32) in g_classified[0].modified_registers)
        self.assertTrue(ReilRegisterOperand("esp", 32) in g_classified[0].modified_registers)

    def test_move_register_2(self):
        # testing : dst_reg <- src_reg
        binary  = "\x8d\x03"                 # 0x00 : (2) lea eax, [ebx]
        binary += "\xc3"                     # 0x02 : (1) ret

        g_finder = GadgetFinder(X86Disassembler(), binary, X86Translator(translation_mode=LITE_TRANSLATION), ARCH_X86, ARCH_X86_MODE_32)

        g_candidates = g_finder.find(0x00000000, 0x00000002)
        g_classified = self._g_classifier.classify(g_candidates[0])

        # self.print_candidates(g_candidates)
        # self.print_classified(g_classified)

        self.assertEquals(len(g_candidates), 1)
        self.assertEquals(len(g_classified), 1)

        self.assertEquals(g_classified[0].type, GadgetType.MoveRegister)
        self.assertEquals(g_classified[0].sources, [ReilRegisterOperand("ebx", 32)])
        self.assertEquals(g_classified[0].destination, [ReilRegisterOperand("eax", 32)])

        self.assertEquals(len(g_classified[0].modified_registers), 1)

        self.assertFalse(ReilRegisterOperand("eax", 32) in g_classified[0].modified_registers)
        self.assertTrue(ReilRegisterOperand("esp", 32) in g_classified[0].modified_registers)

    def test_move_register_3(self):
        # testing : dst_reg <- src_reg
        binary  = "\x93"                     # 0x00 : (1) xchg ebx, eax
        binary += "\xc3"                     # 0x01 : (1) ret

        g_finder = GadgetFinder(X86Disassembler(), binary, X86Translator(translation_mode=LITE_TRANSLATION), ARCH_X86, ARCH_X86_MODE_32)

        g_candidates = g_finder.find(0x00000000, 0x00000001)
        g_classified = self._g_classifier.classify(g_candidates[0])

        # self.print_candidates(g_candidates)
        # self.print_classified(g_classified)

        self.assertEquals(len(g_candidates), 1)
        self.assertEquals(len(g_classified), 2)

        self.assertEquals(g_classified[0].type, GadgetType.MoveRegister)
        self.assertEquals(g_classified[0].sources, [ReilRegisterOperand("eax", 32)])
        self.assertEquals(g_classified[0].destination, [ReilRegisterOperand("ebx", 32)])

        self.assertEquals(len(g_classified[0].modified_registers), 2)

        self.assertTrue(ReilRegisterOperand("eax", 32) in g_classified[0].modified_registers)
        self.assertFalse(ReilRegisterOperand("ebx", 32) in g_classified[0].modified_registers)
        self.assertTrue(ReilRegisterOperand("esp", 32) in g_classified[0].modified_registers)

    def test_move_register_4(self):
        # testing : dst_reg <- src_reg
        binary  = "\x93"                     # 0x00 : (1) xchg ebx, eax
        binary += "\xc3"                     # 0x01 : (1) ret

        g_finder = GadgetFinder(X86Disassembler(), binary, X86Translator(translation_mode=LITE_TRANSLATION), ARCH_X86, ARCH_X86_MODE_32)

        g_candidates = g_finder.find(0x00000000, 0x00000001)
        g_classified = self._g_classifier.classify(g_candidates[0])

        # self.print_candidates(g_candidates)
        # self.print_classified(g_classified)

        self.assertEquals(len(g_candidates), 1)
        self.assertEquals(len(g_classified), 2)

        self.assertEquals(g_classified[1].type, GadgetType.MoveRegister)
        self.assertEquals(g_classified[1].sources, [ReilRegisterOperand("ebx", 32)])
        self.assertEquals(g_classified[1].destination, [ReilRegisterOperand("eax", 32)])

        self.assertEquals(len(g_classified[1].modified_registers), 2)

        self.assertFalse(ReilRegisterOperand("eax", 32) in g_classified[1].modified_registers)
        self.assertTrue(ReilRegisterOperand("ebx", 32) in g_classified[1].modified_registers)
        self.assertTrue(ReilRegisterOperand("esp", 32) in g_classified[1].modified_registers)

    def test_move_register_5(self):
        # testing : dst_reg <- src_reg
        binary  = "\x6b\xc3\x01"             # 0x00 : (3) imul eax, ebx, 0x1
        binary += "\xc3"                     # 0x03 : (1) ret

        g_finder = GadgetFinder(X86Disassembler(), binary, X86Translator(translation_mode=LITE_TRANSLATION), ARCH_X86, ARCH_X86_MODE_32)

        g_candidates = g_finder.find(0x00000000, 0x00000003)
        g_classified = self._g_classifier.classify(g_candidates[0])

        # self.print_candidates(g_candidates)
        # self.print_classified(g_classified)

        self.assertEquals(len(g_candidates), 1)
        self.assertEquals(len(g_classified), 1)

        self.assertEquals(g_classified[0].type, GadgetType.MoveRegister)
        self.assertEquals(g_classified[0].sources, [ReilRegisterOperand("ebx", 32)])
        self.assertEquals(g_classified[0].destination, [ReilRegisterOperand("eax", 32)])

        self.assertEquals(len(g_classified[0].modified_registers), 1)

        self.assertFalse(ReilRegisterOperand("eax", 32) in g_classified[0].modified_registers)
        self.assertTrue(ReilRegisterOperand("esp", 32) in g_classified[0].modified_registers)

    def test_load_constant_1(self):
        # testing : dst_reg <- constant
        binary  = "\xb8\x00\x00\x00\x00"     # 0x00 : (5) mov eax, 0x0
        binary += "\xc3"                     # 0x05 : (1) ret

        g_finder = GadgetFinder(X86Disassembler(), binary, X86Translator(translation_mode=LITE_TRANSLATION), ARCH_X86, ARCH_X86_MODE_32)

        g_candidates = g_finder.find(0x00000000, 0x00000005)
        g_classified = self._g_classifier.classify(g_candidates[1])

        # self.print_candidates(g_candidates)
        # self.print_classified(g_classified)

        self.assertEquals(len(g_candidates), 2)
        self.assertEquals(len(g_classified), 1)

        self.assertEquals(g_classified[0].type, GadgetType.LoadConstant)
        self.assertEquals(g_classified[0].sources, [ReilImmediateOperand(0x0, 32)])
        self.assertEquals(g_classified[0].destination, [ReilRegisterOperand("eax", 32)])

        self.assertEquals(len(g_classified[0].modified_registers), 1)

        self.assertFalse(ReilRegisterOperand("eax", 32) in g_classified[0].modified_registers)
        self.assertTrue(ReilRegisterOperand("esp", 32) in g_classified[0].modified_registers)

    def test_load_constant_2(self):
        # testing : dst_reg <- constant
        binary  = "\x29\xc0"                # 0x00 : (2) sub eax, eax
        binary += "\xc3"                    # 0x02 : (1) ret

        g_finder = GadgetFinder(X86Disassembler(), binary, X86Translator(translation_mode=LITE_TRANSLATION), ARCH_X86, ARCH_X86_MODE_32)

        g_candidates = g_finder.find(0x00000000, 0x00000002)
        g_classified = self._g_classifier.classify(g_candidates[0])

        # self.print_candidates(g_candidates)
        # self.print_classified(g_classified)

        self.assertEquals(len(g_candidates), 1)
        self.assertEquals(len(g_classified), 1)

        self.assertEquals(g_classified[0].type, GadgetType.LoadConstant)
        self.assertEquals(g_classified[0].sources, [ReilImmediateOperand(0x0, 32)])
        self.assertEquals(g_classified[0].destination, [ReilRegisterOperand("eax", 32)])

        self.assertEquals(len(g_classified[0].modified_registers), 1)

        self.assertFalse(ReilRegisterOperand("eax", 32) in g_classified[0].modified_registers)
        self.assertTrue(ReilRegisterOperand("esp", 32) in g_classified[0].modified_registers)

    def test_arithmetic_add_1(self):
        # testing : dst_reg <- src1_reg + src2_reg
        binary  = "\x01\xc1"                 # 0x00 : (2) add ecx, eax
        binary += "\xc3"                     # 0x02 : (1) ret

        g_finder = GadgetFinder(X86Disassembler(), binary, X86Translator(translation_mode=LITE_TRANSLATION), ARCH_X86, ARCH_X86_MODE_32)

        g_candidates = g_finder.find(0x00000000, 0x00000002)
        g_classified = self._g_classifier.classify(g_candidates[0])

        # self.print_candidates(g_candidates)
        # self.print_classified(g_classified)

        self.assertEquals(len(g_candidates), 1)
        self.assertEquals(len(g_classified), 1)

        self.assertEquals(g_classified[0].type, GadgetType.Arithmetic)
        self.assertEquals(g_classified[0].sources, [ReilRegisterOperand("eax", 32), ReilRegisterOperand("ecx", 32)])
        self.assertEquals(g_classified[0].destination, [ReilRegisterOperand("ecx", 32)])
        self.assertEquals(g_classified[0].operation, "+")

        self.assertEquals(len(g_classified[0].modified_registers), 1)

        self.assertFalse(ReilRegisterOperand("ecx", 32) in g_classified[0].modified_registers)
        self.assertTrue(ReilRegisterOperand("esp", 32) in g_classified[0].modified_registers)

    def test_arithmetic_add_2(self):
        # testing : dst_reg <- src1_reg + src2_reg
        binary  = "\x23\x00"                  # 0x00 : (2) and eax, dword [eax]
        binary += "\x00\xc9"                  # 0x02 : (2) add cl, cl
        binary += "\xc3"                      # 0x04 : (1) ret

        g_finder = GadgetFinder(X86Disassembler(), binary, X86Translator(translation_mode=LITE_TRANSLATION), ARCH_X86, ARCH_X86_MODE_32)

        g_candidates = g_finder.find(0x00000000, 0x00000004)
        g_classified = self._g_classifier.classify(g_candidates[1])

        # self.print_candidates(g_candidates)
        # self.print_classified(g_classified)

        self.assertEquals(len(g_candidates), 2)
        self.assertEquals(len(g_classified), 2)

        self.assertEquals(g_classified[0].type, GadgetType.Arithmetic)
        self.assertEquals(g_classified[0].sources, [ReilRegisterOperand("cl", 8), ReilRegisterOperand("cl", 8)])
        self.assertEquals(g_classified[0].destination, [ReilRegisterOperand("cl", 8)])
        self.assertEquals(g_classified[0].operation, "+")

        self.assertEquals(len(g_classified[0].modified_registers), 3)

        self.assertTrue(ReilRegisterOperand("eax", 32) in g_classified[0].modified_registers)
        self.assertTrue(ReilRegisterOperand("ecx", 32) in g_classified[0].modified_registers)
        self.assertTrue(ReilRegisterOperand("esp", 32) in g_classified[0].modified_registers)

    def test_arithmetic_add_3(self):
        # testing : dst_reg <- src1_reg + src2_reg
        binary  = "\x00\xC3"                   # 0x00 : (2) add bl,al
        binary += "\x50"                       # 0x02 : (1) push eax
        binary += "\xC3"                       # 0x03 : (1) ret

        g_finder = GadgetFinder(X86Disassembler(), binary, X86Translator(translation_mode=LITE_TRANSLATION), ARCH_X86, ARCH_X86_MODE_32)

        g_candidates = g_finder.find(0x00000000, 0x00000003)
        g_classified = self._g_classifier.classify(g_candidates[0])

        # self.print_candidates(g_candidates)
        # self.print_classified(g_classified)

        self.assertEquals(len(g_candidates), 1)
        self.assertEquals(len(g_classified), 4)

        self.assertEquals(g_classified[0].type, GadgetType.Arithmetic)
        self.assertEquals(g_classified[0].sources, [ReilRegisterOperand("al", 8), ReilRegisterOperand("bl", 8)])
        self.assertEquals(g_classified[0].destination, [ReilRegisterOperand("bl", 8)])
        self.assertEquals(g_classified[0].operation, "+")

        self.assertEquals(len(g_classified[0].modified_registers), 1)

        self.assertTrue(ReilRegisterOperand("ebx", 32) in g_classified[0].modified_registers)

    def test_arithmetic_sub(self):
        # testing : dst_reg <- src1_reg - src2_reg
        binary  = "\x29\xd1"                 # 0x00 : (2) sub ecx, edx
        binary += "\xc3"                     # 0x02 : (1) ret

        g_finder = GadgetFinder(X86Disassembler(), binary, X86Translator(translation_mode=LITE_TRANSLATION), ARCH_X86, ARCH_X86_MODE_32)

        g_candidates = g_finder.find(0x00000000, 0x00000002)
        g_classified = self._g_classifier.classify(g_candidates[0])

        # self.print_candidates(g_candidates)
        # self.print_classified(g_classified)

        self.assertEquals(len(g_candidates), 1)
        self.assertEquals(len(g_classified), 1)

        self.assertEquals(g_classified[0].type, GadgetType.Arithmetic)
        self.assertEquals(g_classified[0].sources, [ReilRegisterOperand("ecx", 32), ReilRegisterOperand("edx", 32)])
        self.assertEquals(g_classified[0].destination, [ReilRegisterOperand("ecx", 32)])
        self.assertEquals(g_classified[0].operation, "-")

        self.assertEquals(len(g_classified[0].modified_registers), 1)

        self.assertFalse(ReilRegisterOperand("ecx", 32) in g_classified[0].modified_registers)
        self.assertTrue(ReilRegisterOperand("esp", 32) in g_classified[0].modified_registers)

    def test_load_memory_1(self):
        # testing : dst_reg <- m[src_reg]
        binary  = "\x8b\x03"                 # 0x00 : (2) mov eax, dword ptr [ebx]
        binary += "\xc3"                     # 0x02 : (1) ret

        g_finder = GadgetFinder(X86Disassembler(), binary, X86Translator(translation_mode=LITE_TRANSLATION), ARCH_X86, ARCH_X86_MODE_32)

        g_candidates = g_finder.find(0x00000000, 0x00000002)
        g_classified = self._g_classifier.classify(g_candidates[0])

        # self.print_candidates(g_candidates)
        # self.print_classified(g_classified)

        self.assertEquals(len(g_candidates), 1)
        self.assertEquals(len(g_classified), 1)

        self.assertEquals(g_classified[0].type, GadgetType.LoadMemory)
        self.assertEquals(g_classified[0].sources, [ReilRegisterOperand("ebx", 32), ReilImmediateOperand(0x0, 32)])
        self.assertEquals(g_classified[0].destination, [ReilRegisterOperand("eax", 32)])

        self.assertEquals(len(g_classified[0].modified_registers), 1)

        self.assertFalse(ReilRegisterOperand("eax", 32) in g_classified[0].modified_registers)
        self.assertTrue(ReilRegisterOperand("esp", 32) in g_classified[0].modified_registers)

    def test_load_memory_2(self):
        # testing : dst_reg <- m[offset]
        binary  = "\x8b\x0d\xef\xbe\xad\xde" # 0x00 : (6) mov ecx, dword ptr [0xdeadbeef]
        binary += "\xc3"                     # 0x06 : (1) ret

        g_finder = GadgetFinder(X86Disassembler(), binary, X86Translator(translation_mode=LITE_TRANSLATION), ARCH_X86, ARCH_X86_MODE_32)

        g_candidates = g_finder.find(0x00000000, 0x00000006)
        g_classified = self._g_classifier.classify(g_candidates[1])

        # self.print_candidates(g_candidates)
        # self.print_classified(g_classified)

        self.assertEquals(len(g_candidates), 2)
        self.assertEquals(len(g_classified), 1)

        self.assertEquals(g_classified[0].type, GadgetType.LoadMemory)
        self.assertEquals(g_classified[0].sources, [ReilEmptyOperand(), ReilImmediateOperand(0xdeadbeef, 32)])
        self.assertEquals(g_classified[0].destination, [ReilRegisterOperand("ecx", 32)])

        self.assertEquals(len(g_classified[0].modified_registers), 1)

        self.assertFalse(ReilRegisterOperand("ecx", 32) in g_classified[0].modified_registers)
        self.assertTrue(ReilRegisterOperand("esp", 32) in g_classified[0].modified_registers)

    def test_load_memory_3(self):
        # testing : dst_reg <- m[src_reg + offset]
        binary  = "\x8b\x88\x00\x01\x00\x00" # 0x00 : (6) mov ecx, dword ptr [eax+0x100]
        binary += "\xc3"                     # 0x06 : (1) ret

        g_finder = GadgetFinder(X86Disassembler(), binary, X86Translator(translation_mode=LITE_TRANSLATION), ARCH_X86, ARCH_X86_MODE_32)

        g_candidates = g_finder.find(0x00000000, 0x00000006)
        g_classified = self._g_classifier.classify(g_candidates[1])

        # self.print_candidates(g_candidates)
        # self.print_classified(g_classified)

        self.assertEquals(len(g_candidates), 2)
        self.assertEquals(len(g_classified), 1)

        self.assertEquals(g_classified[0].type, GadgetType.LoadMemory)
        self.assertEquals(g_classified[0].sources, [ReilRegisterOperand("eax", 32), ReilImmediateOperand(0x100, 32)])
        self.assertEquals(g_classified[0].destination, [ReilRegisterOperand("ecx", 32)])

        self.assertEquals(len(g_classified[0].modified_registers), 1)

        self.assertFalse(ReilRegisterOperand("ecx", 32) in g_classified[0].modified_registers)
        self.assertTrue(ReilRegisterOperand("esp", 32) in g_classified[0].modified_registers)

    def test_load_memory_4(self):
        # testing : dst_reg <- m[dst_reg]
        binary  = "\x8b\x09"                 # 0x00 : (2) mov ecx, dword ptr [ecx]
        binary += "\xc3"                     # 0x02 : (1) ret

        g_finder = GadgetFinder(X86Disassembler(), binary, X86Translator(translation_mode=LITE_TRANSLATION), ARCH_X86, ARCH_X86_MODE_32)

        g_candidates = g_finder.find(0x00000000, 0x00000002)
        g_classified = self._g_classifier.classify(g_candidates[0])

        # self.print_candidates(g_candidates)
        # self.print_classified(g_classified)

        self.assertEquals(len(g_candidates), 1)
        self.assertEquals(len(g_classified), 1)

        self.assertEquals(g_classified[0].type, GadgetType.LoadMemory)
        self.assertEquals(g_classified[0].sources, [ReilRegisterOperand("ecx", 32), ReilImmediateOperand(0x0, 32)])
        self.assertEquals(g_classified[0].destination, [ReilRegisterOperand("ecx", 32)])

        self.assertEquals(len(g_classified[0].modified_registers), 1)

        self.assertFalse(ReilRegisterOperand("ecx", 32) in g_classified[0].modified_registers)
        self.assertTrue(ReilRegisterOperand("esp", 32) in g_classified[0].modified_registers)

    def test_load_memory_5(self):
        # testing : dst_reg <- m[dst_reg + offset]
        binary  = "\x8b\x89\x00\x01\x00\x00"  # 0x00 : (6) mov ecx, dword ptr [ecx+0x100]
        binary += "\xc3"                      # 0x06 : (1) ret

        g_finder = GadgetFinder(X86Disassembler(), binary, X86Translator(translation_mode=LITE_TRANSLATION), ARCH_X86, ARCH_X86_MODE_32)

        g_candidates = g_finder.find(0x00000000, 0x00000006)
        g_classified = self._g_classifier.classify(g_candidates[1])

        # self.print_candidates(g_candidates)
        # self.print_classified(g_classified)

        self.assertEquals(len(g_candidates), 2)
        self.assertEquals(len(g_classified), 1)

        self.assertEquals(g_classified[0].type, GadgetType.LoadMemory)
        self.assertEquals(g_classified[0].sources, [ReilRegisterOperand("ecx", 32), ReilImmediateOperand(0x100, 32)])
        self.assertEquals(g_classified[0].destination, [ReilRegisterOperand("ecx", 32)])

        self.assertEquals(len(g_classified[0].modified_registers), 1)

        self.assertFalse(ReilRegisterOperand("ecx", 32) in g_classified[0].modified_registers)
        self.assertTrue(ReilRegisterOperand("esp", 32) in g_classified[0].modified_registers)

    # def test_load_memory_6(self):
    #     # FIXME:
    #     # testing : dst_reg <- m[dst_reg + offset]
    #     binary  = "\x5c\xc3" # pop esp ; ret

    #     # binary  = "\x8b\x89\x00\x01\x00\x00"  # 0x00 : (6) mov ecx, dword ptr [ecx+0x100]
    #     # binary += "\xc3"                      # 0x06 : (1) ret

    #     g_finder = GadgetFinder(X86Disassembler(), binary, X86Translator(translation_mode=LITE_TRANSLATION), ARCH_X86, ARCH_X86_MODE_32)

    #     g_candidates = g_finder.find(0x00000000, 0x00000001)
    #     g_classified = self._g_classifier.classify(g_candidates[0])

    #     self.print_candidates(g_candidates)
    #     self.print_classified(g_classified)

    #     self.assertEquals(len(g_candidates), 2)
    #     self.assertEquals(len(g_classified), 1)

    #     self.assertEquals(g_classified[0].type, GadgetType.LoadMemory)
    #     self.assertEquals(g_classified[0].sources, [ReilRegisterOperand("ecx", 32), ReilImmediateOperand(0x100, 32)])
    #     self.assertEquals(g_classified[0].destination, [ReilRegisterOperand("ecx", 32)])

    #     self.assertEquals(len(g_classified[0].modified_registers), 0)

    #     self.assertFalse(ReilRegisterOperand("ecx", 32) in g_classified[0].modified_registers)

    def test_store_memory_1(self):
        # testing : m[dst_reg] <- src_reg
        binary  = "\x89\x18"                 # 0x00 : (2) mov dword ptr [eax], ebx
        binary += "\xc3"                     # 0x02 : (1) ret

        g_finder = GadgetFinder(X86Disassembler(), binary, X86Translator(translation_mode=LITE_TRANSLATION), ARCH_X86, ARCH_X86_MODE_32)

        g_candidates = g_finder.find(0x00000000, 0x00000002)
        g_classified = self._g_classifier.classify(g_candidates[0])

        # self.print_candidates(g_candidates)
        # self.print_classified(g_classified)

        self.assertEquals(len(g_candidates), 1)
        self.assertEquals(len(g_classified), 1)

        self.assertEquals(g_classified[0].type, GadgetType.StoreMemory)
        self.assertEquals(g_classified[0].sources, [ReilRegisterOperand("ebx", 32)])
        self.assertEquals(g_classified[0].destination, [ReilRegisterOperand("eax", 32), ReilImmediateOperand(0x0, 32)])

        self.assertEquals(len(g_classified[0].modified_registers), 1)

        self.assertTrue(ReilRegisterOperand("esp", 32) in g_classified[0].modified_registers)

    def test_store_memory_2(self):
        # testing : m[offset] <- src_reg
        binary  = "\x89\x0d\xef\xbe\xad\xde" # 0x00 : (6) mov dword ptr [0xdeadbeef], ecx
        binary += "\xc3"                     # 0x06 : (1) ret

        g_finder = GadgetFinder(X86Disassembler(), binary, X86Translator(translation_mode=LITE_TRANSLATION), ARCH_X86, ARCH_X86_MODE_32)

        g_candidates = g_finder.find(0x00000000, 0x00000006)
        g_classified = self._g_classifier.classify(g_candidates[1])

        # self.print_candidates(g_candidates)
        # self.print_classified(g_classified)

        self.assertEquals(len(g_candidates), 2)
        self.assertEquals(len(g_classified), 1)

        self.assertEquals(g_classified[0].type, GadgetType.StoreMemory)
        self.assertEquals(g_classified[0].sources, [ReilRegisterOperand("ecx", 32)])
        self.assertEquals(g_classified[0].destination, [ReilEmptyOperand(), ReilImmediateOperand(0xdeadbeef, 32)])

        self.assertEquals(len(g_classified[0].modified_registers), 1)

        self.assertTrue(ReilRegisterOperand("esp", 32) in g_classified[0].modified_registers)

    def test_store_memory_3(self):
        # testing : m[dst_reg + offset] <- src_reg
        binary  = "\x89\x88\x00\x01\x00\x00" # 0x00 : (6) mov dword ptr [eax+0x100], ecx
        binary += "\xc3"                     # 0x06 : (1) ret

        g_finder = GadgetFinder(X86Disassembler(), binary, X86Translator(translation_mode=LITE_TRANSLATION), ARCH_X86, ARCH_X86_MODE_32)

        g_candidates = g_finder.find(0x00000000, 0x00000006)
        g_classified = self._g_classifier.classify(g_candidates[1])

        # self.print_candidates(g_candidates)
        # self.print_classified(g_classified)

        self.assertEquals(len(g_candidates), 2)
        self.assertEquals(len(g_classified), 1)

        self.assertEquals(g_classified[0].type, GadgetType.StoreMemory)
        self.assertEquals(g_classified[0].sources, [ReilRegisterOperand("ecx", 32)])
        self.assertEquals(g_classified[0].destination, [ReilRegisterOperand("eax", 32), ReilImmediateOperand(0x100, 32)])

        self.assertEquals(len(g_classified[0].modified_registers), 1)

        self.assertTrue(ReilRegisterOperand("esp", 32) in g_classified[0].modified_registers)

    def test_store_memory_4(self):
        # testing : m[dst_reg] <- dst_reg
        binary  = "\x89\x09"                 # 0x00 : (2) mov dword ptr [ecx], ecx
        binary += "\xc3"                     # 0x02 : (1) ret

        g_finder = GadgetFinder(X86Disassembler(), binary, X86Translator(translation_mode=LITE_TRANSLATION), ARCH_X86, ARCH_X86_MODE_32)

        g_candidates = g_finder.find(0x00000000, 0x00000002)
        g_classified = self._g_classifier.classify(g_candidates[0])

        # self.print_candidates(g_candidates)
        # self.print_classified(g_classified)

        self.assertEquals(len(g_candidates), 1)
        self.assertEquals(len(g_classified), 1)

        self.assertEquals(g_classified[0].type, GadgetType.StoreMemory)
        self.assertEquals(g_classified[0].sources, [ReilRegisterOperand("ecx", 32)])
        self.assertEquals(g_classified[0].destination, [ReilRegisterOperand("ecx", 32), ReilImmediateOperand(0x0, 32)])

        self.assertEquals(len(g_classified[0].modified_registers), 1)

        self.assertTrue(ReilRegisterOperand("esp", 32) in g_classified[0].modified_registers)

    def test_store_memory_5(self):
        # testing : m[dst_reg + offset] <- dst_reg
        binary  = "\x89\x89\x00\x01\x00\x00" # 0x00 : (6) mov dword ptr [ecx+0x100], ecx
        binary += "\xc3"                     # 0x06 : (1) ret

        g_finder = GadgetFinder(X86Disassembler(), binary, X86Translator(translation_mode=LITE_TRANSLATION), ARCH_X86, ARCH_X86_MODE_32)

        g_candidates = g_finder.find(0x00000000, 0x00000006)
        g_classified = self._g_classifier.classify(g_candidates[1])

        # self.print_candidates(g_candidates)
        # self.print_classified(g_classified)

        self.assertEquals(len(g_candidates), 2)
        self.assertEquals(len(g_classified), 1)

        self.assertEquals(g_classified[0].type, GadgetType.StoreMemory)
        self.assertEquals(g_classified[0].sources, [ReilRegisterOperand("ecx", 32)])
        self.assertEquals(g_classified[0].destination, [ReilRegisterOperand("ecx", 32), ReilImmediateOperand(0x100, 32)])

        self.assertEquals(len(g_classified[0].modified_registers), 1)

        self.assertTrue(ReilRegisterOperand("esp", 32) in g_classified[0].modified_registers)

    def test_store_memory_6(self):
        # testing : m[dst_reg + offset] <- dst_reg
        binary  = "\x00\x00"                # 0x00 : (2) add byte ptr [eax], al
        binary += "\xc3"                    # 0x02 : (1) ret

        g_finder = GadgetFinder(X86Disassembler(), binary, X86Translator(translation_mode=LITE_TRANSLATION), ARCH_X86, ARCH_X86_MODE_32)

        g_candidates = g_finder.find(0x00000000, 0x00000002)
        g_classified = self._g_classifier.classify(g_candidates[0])

        # self.print_candidates(g_candidates)
        # self.print_classified(g_classified)

        self.assertEquals(len(g_candidates), 1)
        self.assertEquals(len(g_classified), 1)

        self.assertEquals(g_classified[0].type, GadgetType.ArithmeticStore)
        self.assertEquals(g_classified[0].sources, [ReilRegisterOperand("eax", 32), ReilImmediateOperand(0x0, 32), ReilRegisterOperand("al", 8)])
        self.assertEquals(g_classified[0].destination, [ReilRegisterOperand("eax", 32), ReilImmediateOperand(0x0, 32)])

        # self.assertFalse(ReilRegisterOperand("eax", 32) in g_classified[0].modified_registers)

    def test_arithmetic_load_add_1(self):
        # testing : dst_reg <- dst_reg + mem[src_reg]
        binary  = "\x03\x03"                 # 0x00 : (2) add eax, dword ptr [ebx]
        binary += "\xc3"                     # 0x00 : (1) ret

        g_finder = GadgetFinder(X86Disassembler(), binary, X86Translator(translation_mode=LITE_TRANSLATION), ARCH_X86, ARCH_X86_MODE_32)

        g_candidates = g_finder.find(0x00000000, 0x00000002)
        g_classified = self._g_classifier.classify(g_candidates[0])

        # self.print_candidates(g_candidates)
        # self.print_classified(g_classified)

        self.assertEquals(len(g_candidates), 1)
        self.assertEquals(len(g_classified), 1)

        self.assertEquals(g_classified[0].type, GadgetType.ArithmeticLoad)
        self.assertEquals(g_classified[0].sources, [ReilRegisterOperand("eax", 32), ReilRegisterOperand("ebx", 32), ReilImmediateOperand(0x0, 32)])
        self.assertEquals(g_classified[0].destination, [ReilRegisterOperand("eax", 32)])
        self.assertEquals(g_classified[0].operation, "+")

        self.assertEquals(len(g_classified[0].modified_registers), 1)

        self.assertFalse(ReilRegisterOperand("eax", 32) in g_classified[0].modified_registers)
        self.assertTrue(ReilRegisterOperand("esp", 32) in g_classified[0].modified_registers)

    def test_arithmetic_load_add_2(self):
        # testing : dst_reg <- dst_reg + mem[offset]
        binary  = "\x03\x05\xef\xbe\xad\xde" # 0x00 : (6) add eax, dword ptr [0xdeadbeef]
        binary += "\xc3"                     # 0x01 : (1) ret

        g_finder = GadgetFinder(X86Disassembler(), binary, X86Translator(translation_mode=LITE_TRANSLATION), ARCH_X86, ARCH_X86_MODE_32)

        g_candidates = g_finder.find(0x00000000, 0x00000006)
        g_classified = self._g_classifier.classify(g_candidates[1])

        # self.print_candidates(g_candidates)
        # self.print_classified(g_classified)

        self.assertEquals(len(g_candidates), 2)
        self.assertEquals(len(g_classified), 1)

        self.assertEquals(g_classified[0].type, GadgetType.ArithmeticLoad)
        self.assertEquals(g_classified[0].sources, [ReilRegisterOperand("eax", 32), ReilEmptyOperand(), ReilImmediateOperand(0xdeadbeef, 32)])
        self.assertEquals(g_classified[0].destination, [ReilRegisterOperand("eax", 32)])
        self.assertEquals(g_classified[0].operation, "+")

        self.assertEquals(len(g_classified[0].modified_registers), 1)

        self.assertFalse(ReilRegisterOperand("eax", 32) in g_classified[0].modified_registers)
        self.assertTrue(ReilRegisterOperand("esp", 32) in g_classified[0].modified_registers)

    def test_arithmetic_load_add_3(self):
        # testing : dst_reg <- dst_reg + mem[src_reg + offset]
        binary  = "\x03\x83\x00\x01\x00\x00" # 0x00 : (6) add eax, dword ptr [ebx+0x100]
        binary += "\xc3"                     # 0x06 : (1) ret

        g_finder = GadgetFinder(X86Disassembler(), binary, X86Translator(translation_mode=LITE_TRANSLATION), ARCH_X86, ARCH_X86_MODE_32)

        g_candidates = g_finder.find(0x00000000, 0x00000006)
        g_classified = self._g_classifier.classify(g_candidates[2])

        # self.print_candidates(g_candidates)
        # self.print_classified(g_classified)

        self.assertEquals(len(g_candidates), 3)
        self.assertEquals(len(g_classified), 1)

        self.assertEquals(g_classified[0].type, GadgetType.ArithmeticLoad)
        self.assertEquals(g_classified[0].sources, [ReilRegisterOperand("eax", 32), ReilRegisterOperand("ebx", 32), ReilImmediateOperand(0x100, 32)])
        self.assertEquals(g_classified[0].destination, [ReilRegisterOperand("eax", 32)])
        self.assertEquals(g_classified[0].operation, "+")

        self.assertEquals(len(g_classified[0].modified_registers), 1)

        self.assertFalse(ReilRegisterOperand("eax", 32) in g_classified[0].modified_registers)
        self.assertTrue(ReilRegisterOperand("esp", 32) in g_classified[0].modified_registers)

    def test_arithmetic_load_add_4(self):
        # testing : dst_reg <- dst_reg + mem[dst_reg]
        binary  = "\x03\x09"                 # 0x00 : (2) add ecx, dword ptr [ecx]
        binary += "\xc3"                     # 0x02 : (1) ret

        g_finder = GadgetFinder(X86Disassembler(), binary, X86Translator(translation_mode=LITE_TRANSLATION), ARCH_X86, ARCH_X86_MODE_32)

        g_candidates = g_finder.find(0x00000000, 0x00000002)
        g_classified = self._g_classifier.classify(g_candidates[0])

        # self.print_candidates(g_candidates)
        # self.print_classified(g_classified)

        self.assertEquals(len(g_candidates), 1)
        self.assertEquals(len(g_classified), 1)

        self.assertEquals(g_classified[0].type, GadgetType.ArithmeticLoad)
        self.assertEquals(g_classified[0].sources, [ReilRegisterOperand("ecx", 32), ReilRegisterOperand("ecx", 32), ReilImmediateOperand(0x0, 32)])
        self.assertEquals(g_classified[0].destination, [ReilRegisterOperand("ecx", 32)])
        self.assertEquals(g_classified[0].operation, "+")

        self.assertEquals(len(g_classified[0].modified_registers), 1)

        self.assertFalse(ReilRegisterOperand("ecx", 32) in g_classified[0].modified_registers)
        self.assertTrue(ReilRegisterOperand("esp", 32) in g_classified[0].modified_registers)

    def test_arithmetic_load_add_5(self):
        # testing : dst_reg <- dst_reg + mem[dst_reg + offset]
        binary  = "\x03\x89\x00\x01\x00\x00" # 0x00 : (6) add ecx, dword ptr [ecx+0x100]
        binary += "\xc3"                     # 0x06 : (1) ret

        g_finder = GadgetFinder(X86Disassembler(), binary, X86Translator(translation_mode=LITE_TRANSLATION), ARCH_X86, ARCH_X86_MODE_32)

        g_candidates = g_finder.find(0x00000000, 0x00000006)
        g_classified = self._g_classifier.classify(g_candidates[1])

        # self.print_candidates(g_candidates)
        # self.print_classified(g_classified)

        self.assertEquals(len(g_candidates), 2)
        self.assertEquals(len(g_classified), 1)

        self.assertEquals(g_classified[0].type, GadgetType.ArithmeticLoad)
        self.assertEquals(g_classified[0].sources, [ReilRegisterOperand("ecx", 32), ReilRegisterOperand("ecx", 32), ReilImmediateOperand(0x100, 32)])
        self.assertEquals(g_classified[0].destination, [ReilRegisterOperand("ecx", 32)])
        self.assertEquals(g_classified[0].operation, "+")

        self.assertEquals(len(g_classified[0].modified_registers), 1)

        self.assertFalse(ReilRegisterOperand("ecx", 32) in g_classified[0].modified_registers)
        self.assertTrue(ReilRegisterOperand("esp", 32) in g_classified[0].modified_registers)

    def test_arithmetic_store_add_1(self):
        # testing : m[dst_reg] <- m[dst_reg] + src_reg
        binary  = "\x01\x18"                 # 0x02 : (2) add dword ptr [eax], ebx
        binary += "\xc3"                     # 0x02 : (2) ret

        g_finder = GadgetFinder(X86Disassembler(), binary, X86Translator(translation_mode=LITE_TRANSLATION), ARCH_X86, ARCH_X86_MODE_32)

        g_candidates = g_finder.find(0x00000000, 0x00000002)
        g_classified = self._g_classifier.classify(g_candidates[0])

        # self.print_candidates(g_candidates)
        # self.print_classified(g_classified)

        self.assertEquals(len(g_candidates), 1)
        self.assertEquals(len(g_classified), 1)

        self.assertEquals(g_classified[0].type, GadgetType.ArithmeticStore)
        self.assertEquals(g_classified[0].sources, [ReilRegisterOperand("eax", 32), ReilImmediateOperand(0x0, 32), ReilRegisterOperand("ebx", 32)])
        self.assertEquals(g_classified[0].destination, [ReilRegisterOperand("eax", 32), ReilImmediateOperand(0x0, 32)])
        self.assertEquals(g_classified[0].operation, "+")

        self.assertEquals(len(g_classified[0].modified_registers), 1)

        self.assertTrue(ReilRegisterOperand("esp", 32) in g_classified[0].modified_registers)

    def test_arithmetic_store_add_2(self):
        # testing : m[offset] <- m[offset] + src_reg
        binary  = "\x01\x0d\xef\xbe\xad\xde" # 0x00 : (6) add dword ptr [0xdeadbeef], ecx
        binary += "\xc3"                     # 0x06 : (1) ret

        g_finder = GadgetFinder(X86Disassembler(), binary, X86Translator(translation_mode=LITE_TRANSLATION), ARCH_X86, ARCH_X86_MODE_32)

        g_candidates = g_finder.find(0x00000000, 0x00000006)
        g_classified = self._g_classifier.classify(g_candidates[1])

        # self.print_candidates(g_candidates)
        # self.print_classified(g_classified)

        self.assertEquals(len(g_candidates), 2)
        self.assertEquals(len(g_classified), 1)

        self.assertEquals(g_classified[0].type, GadgetType.ArithmeticStore)
        self.assertEquals(g_classified[0].sources, [ReilEmptyOperand(), ReilImmediateOperand(0xdeadbeef, 32), ReilRegisterOperand("ecx", 32)])
        self.assertEquals(g_classified[0].destination, [ReilEmptyOperand(), ReilImmediateOperand(0xdeadbeef, 32)])
        self.assertEquals(g_classified[0].operation, "+")

        self.assertEquals(len(g_classified[0].modified_registers), 1)

        self.assertTrue(ReilRegisterOperand("esp", 32) in g_classified[0].modified_registers)

    def test_arithmetic_store_add_3(self):
        # testing : m[dst_reg + offset] <- m[dst_reg + offset] + src_reg
        binary  = "\x01\x88\x00\x01\x00\x00" # 0x00 : (6) add dword ptr [eax+0x100], ecx
        binary += "\xc3"                     # 0x06 : (1) ret

        g_finder = GadgetFinder(X86Disassembler(), binary, X86Translator(translation_mode=LITE_TRANSLATION), ARCH_X86, ARCH_X86_MODE_32)

        g_candidates = g_finder.find(0x00000000, 0x00000006)
        g_classified = self._g_classifier.classify(g_candidates[1])

        # self.print_candidates(g_candidates)
        # self.print_classified(g_classified)

        self.assertEquals(len(g_candidates), 2)
        self.assertEquals(len(g_classified), 1)

        self.assertEquals(g_classified[0].type, GadgetType.ArithmeticStore)
        self.assertEquals(g_classified[0].sources, [ReilRegisterOperand("eax", 32), ReilImmediateOperand(0x100, 32), ReilRegisterOperand("ecx", 32)])
        self.assertEquals(g_classified[0].destination, [ReilRegisterOperand("eax", 32), ReilImmediateOperand(0x100, 32)])
        self.assertEquals(g_classified[0].operation, "+")

        self.assertEquals(len(g_classified[0].modified_registers), 1)

        self.assertTrue(ReilRegisterOperand("esp", 32) in g_classified[0].modified_registers)

    def test_arithmetic_store_add_4(self):
        # testing : m[dst_reg] <- m[dst_reg] + dst_reg
        binary  = "\x01\x09"                 # 0x00 : (2) add dword ptr [ecx], ecx
        binary += "\xc3"                     # 0x02 : (1) ret

        g_finder = GadgetFinder(X86Disassembler(), binary, X86Translator(translation_mode=LITE_TRANSLATION), ARCH_X86, ARCH_X86_MODE_32)

        g_candidates = g_finder.find(0x00000000, 0x00000002)
        g_classified = self._g_classifier.classify(g_candidates[0])

        # self.print_candidates(g_candidates)
        # self.print_classified(g_classified)

        self.assertEquals(len(g_candidates), 1)
        self.assertEquals(len(g_classified), 1)

        self.assertEquals(g_classified[0].type, GadgetType.ArithmeticStore)
        self.assertEquals(g_classified[0].sources, [ReilRegisterOperand("ecx", 32), ReilImmediateOperand(0x0, 32), ReilRegisterOperand("ecx", 32)])
        self.assertEquals(g_classified[0].destination, [ReilRegisterOperand("ecx", 32), ReilImmediateOperand(0x0, 32)])
        self.assertEquals(g_classified[0].operation, "+")

        self.assertEquals(len(g_classified[0].modified_registers), 1)

        self.assertTrue(ReilRegisterOperand("esp", 32) in g_classified[0].modified_registers)

    def test_arithmetic_store_add_5(self):
        # testing : m[dst_reg + offset] <- m[dst_reg + offset] + dst_reg
        binary  = "\x01\x89\x00\x01\x00\x00" # 0x00 : (6) add dword ptr [ecx+0x100], ecx
        binary += "\xc3"                     # 0x06 : (1) ret

        g_finder = GadgetFinder(X86Disassembler(), binary, X86Translator(translation_mode=LITE_TRANSLATION), ARCH_X86, ARCH_X86_MODE_32)

        g_candidates = g_finder.find(0x00000000, 0x00000006)
        g_classified = self._g_classifier.classify(g_candidates[1])

        # self.print_candidates(g_candidates)
        # self.print_classified(g_classified)

        self.assertEquals(len(g_candidates), 2)
        self.assertEquals(len(g_classified), 1)

        self.assertEquals(g_classified[0].type, GadgetType.ArithmeticStore)
        self.assertEquals(g_classified[0].sources, [ReilRegisterOperand("ecx", 32), ReilImmediateOperand(0x100, 32), ReilRegisterOperand("ecx", 32)])
        self.assertEquals(g_classified[0].destination, [ReilRegisterOperand("ecx", 32), ReilImmediateOperand(0x100, 32)])
        self.assertEquals(g_classified[0].operation, "+")

        self.assertEquals(len(g_classified[0].modified_registers), 1)

        self.assertTrue(ReilRegisterOperand("esp", 32) in g_classified[0].modified_registers)

    def test_no_classification_1(self):
        binary  = "\xc7\x40\x24\x00\x00\x00\x00" # 0x00 : (7) mov dword ptr [eax+0x24], 0x0
        binary += "\xc7\x40\x20\x00\x00\x00\x00" # 0x07 : (7) mov dword ptr [eax+0x20], 0x0
        binary += "\xc3"                         # 0x0e : (1) ret

        g_finder = GadgetFinder(X86Disassembler(), binary, X86Translator(translation_mode=LITE_TRANSLATION), ARCH_X86, ARCH_X86_MODE_32)

        g_candidates = g_finder.find(0x00000000, 0x0000000e)
        g_classified = self._g_classifier.classify(g_candidates[2])

        # self.print_candidates(g_candidates)
        # self.print_classified(g_classified)

        self.assertEquals(len(g_candidates), 3)
        self.assertEquals(len(g_classified), 0)

    def print_candidates(self, candidates):
        print "Candidates :"

        for gadget in candidates:
            print gadget
            print "-" * 10

    def print_classified(self, classified):
        print "Classified :"

        for gadget in classified:
            print gadget
            print gadget.type
            print "-" * 10


class GadgetVerifierTests(unittest.TestCase):

    def setUp(self):
        self._arch_info = X86ArchitectureInformation(ARCH_X86_MODE_32)
        self._smt_solver = SmtSolver()
        self._smt_translator = SmtTranslator(self._smt_solver, self._arch_info.address_size)

        self._ir_emulator = ReilEmulator(self._arch_info)

        self._smt_translator.set_arch_alias_mapper(self._arch_info.alias_mapper)
        self._smt_translator.set_arch_registers_size(self._arch_info.registers_size)

        self._code_analyzer = CodeAnalyzer(self._smt_solver, self._smt_translator, self._arch_info)

        self._g_classifier = GadgetClassifier(self._ir_emulator, self._arch_info)
        self._g_verifier = GadgetVerifier(self._code_analyzer, self._arch_info)

    # FIXME: Don't take into account esp modification because of RET instruction.
    # def test_nop_1(self):
    #     # testing : nop
    #     binary  = "\x90"                     # 0x00 : (1) nop
    #     binary += "\xc3"                     # 0x00 : (1) ret

    #     g_finder = GadgetFinder(X86Disassembler(), binary, X86Translator(translation_mode=LITE_TRANSLATION), ARCH_X86, ARCH_X86_MODE_32)

    #     g_candidates = g_finder.find(0x00000000, 0x00000001)
    #     g_classified = self._g_classifier.classify(g_candidates[0])

    #     # self.print_candidates(g_candidates)
    #     # self.print_classified(g_classified)

    #     verified = self._g_verifier.verify(g_classified[0])

    #     self.assertEquals(len(g_candidates), 1)
    #     self.assertEquals(len(g_classified), 1)

    #     self.assertTrue(verified)

    #     self.assertEquals(g_classified[0].type, GadgetType.NoOperation)
    #     self.assertEquals(g_classified[0].sources, [])
    #     self.assertEquals(g_classified[0].destination, [])

    #     self.assertEquals(len(g_classified[0].modified_registers), 0)

    # FIXME: Don't take into account esp modification because of RET instruction.
    # def test_nop_2(self):
    #     # testing : nop
    #     binary  = "\x39\xd8"                    # 0x00 : (2) cmp eax, ebx
    #     binary += "\xc3"                        # 0x02 : (1) ret

    #     g_finder = GadgetFinder(X86Disassembler(), binary, X86Translator(translation_mode=LITE_TRANSLATION), ARCH_X86, ARCH_X86_MODE_32)

    #     g_candidates = g_finder.find(0x00000000, 0x00000002)

    #     g_classified = self._g_classifier.classify(g_candidates[0])

    #     # self.print_candidates(g_candidates)
    #     # self.print_classified(g_classified)

    #     verified = self._g_verifier.verify(g_classified[0])

    #     self.assertEquals(len(g_candidates), 1)
    #     self.assertEquals(len(g_classified), 1)

    #     self.assertFalse(verified)

    #     self.assertEquals(g_classified[0].type, GadgetType.NoOperation)
    #     self.assertEquals(g_classified[0].sources, [])
    #     self.assertEquals(g_classified[0].destination, [])

    #     self.assertEquals(len(g_classified[0].modified_registers), 0)

    # FIXME: Don't take into account esp modification because of RET instruction.
    # def test_nop_3(self):
    #     # testing : nop

    #     binary  = "\x08\xc9"                    # 0x00 : (2) or cl, cl
    #     binary += "\xc3"                        # 0x02 : (1) ret

    #     g_finder = GadgetFinder(X86Disassembler(), binary, X86Translator(translation_mode=LITE_TRANSLATION), ARCH_X86, ARCH_X86_MODE_32)

    #     g_candidates = g_finder.find(0x00000000, 0x00000002)

    #     g_classified = self._g_classifier.classify(g_candidates[1])

    #     # self.print_candidates(g_candidates)
    #     # self.print_classified(g_classified)

    #     verified = self._g_verifier.verify(g_classified[0])

    #     self.assertEquals(len(g_candidates), 2)
    #     self.assertEquals(len(g_classified), 1)

    #     self.assertTrue(verified)

    #     self.assertEquals(g_classified[0].type, GadgetType.NoOperation)
    #     self.assertEquals(g_classified[0].sources, [])
    #     self.assertEquals(g_classified[0].destination, [])

    #     self.assertEquals(len(g_classified[0].modified_registers), 0)

    def test_move_register(self):
        binary  = "\x89\xd8"                  # 0x00 : (2) mov eax, ebx
        binary += "\xc3"                      # 0x02 : (1) ret

        g_finder = GadgetFinder(X86Disassembler(), binary, X86Translator(translation_mode=LITE_TRANSLATION), ARCH_X86, ARCH_X86_MODE_32)

        g_candidates = g_finder.find(0x00000000, 0x00000002)
        g_classified = self._g_classifier.classify(g_candidates[0])

        # self.print_candidates(g_candidates)
        # self.print_classified(g_classified)

        verified = self._g_verifier.verify(g_classified[0])

        self.assertEquals(len(g_candidates), 1)
        self.assertEquals(len(g_classified), 1)

        self.assertTrue(verified)

        self.assertEquals(g_classified[0].type, GadgetType.MoveRegister)
        self.assertEquals(g_classified[0].sources, [ReilRegisterOperand("ebx", 32)])
        self.assertEquals(g_classified[0].destination, [ReilRegisterOperand("eax", 32)])

        self.assertEquals(len(g_classified[0].modified_registers), 1)

        self.assertFalse(ReilRegisterOperand("eax", 32) in g_classified[0].modified_registers)
        self.assertTrue(ReilRegisterOperand("esp", 32) in g_classified[0].modified_registers)

    def test_load_memory_two_accesses_1(self):
        # testing : dst_reg <- m[dst_reg + offset]
        binary  = "\x58"                      # 0x00 : (1) pop eax
        binary += "\x5b"                      # 0x01 : (1) pop ebx
        binary += "\xc3"                      # 0x02 : (1) ret

        g_finder = GadgetFinder(X86Disassembler(), binary, X86Translator(translation_mode=LITE_TRANSLATION), ARCH_X86, ARCH_X86_MODE_32)

        g_candidates = g_finder.find(0x00000000, 0x00000002)
        g_classified = self._g_classifier.classify(g_candidates[0])

        # self.print_candidates(g_candidates)
        # self.print_classified(g_classified)

        verified = self._g_verifier.verify(g_classified[1])

        self.assertEquals(len(g_candidates), 1)
        self.assertEquals(len(g_classified), 2)

        self.assertTrue(verified)

        self.assertEquals(g_classified[1].type, GadgetType.LoadMemory)
        self.assertEquals(g_classified[1].sources, [ReilRegisterOperand("esp", 32), ReilImmediateOperand(0x0, 32)])
        self.assertEquals(g_classified[1].destination, [ReilRegisterOperand("eax", 32)])

        self.assertEquals(len(g_classified[1].modified_registers), 2)

        self.assertTrue(ReilRegisterOperand("ebx", 32) in g_classified[1].modified_registers)
        self.assertTrue(ReilRegisterOperand("esp", 32) in g_classified[1].modified_registers)

    def test_load_memory_two_accesses_2(self):
        # testing : dst_reg <- m[dst_reg + offset]
        binary  = "\x8b\x09"                  # 0x00 : (2) mov ecx, dword ptr [ecx]
        binary += "\x03\x03"                  # 0x02 : (2) add eax, dword ptr [ebx]
        binary += "\xc3"                      # 0x04 : (1) ret

        g_finder = GadgetFinder(X86Disassembler(), binary, X86Translator(translation_mode=LITE_TRANSLATION), ARCH_X86, ARCH_X86_MODE_32)

        g_candidates = g_finder.find(0x00000000, 0x00000004)
        g_classified = self._g_classifier.classify(g_candidates[0])

        # self.print_candidates(g_candidates)
        # self.print_classified(g_classified)

        verified = self._g_verifier.verify(g_classified[0])

        self.assertEquals(len(g_candidates), 1)
        self.assertEquals(len(g_classified), 2)

        self.assertTrue(verified)

        self.assertEquals(g_classified[0].type, GadgetType.LoadMemory)
        self.assertEquals(g_classified[0].sources, [ReilRegisterOperand("ecx", 32), ReilImmediateOperand(0x0, 32)])
        self.assertEquals(g_classified[0].destination, [ReilRegisterOperand("ecx", 32)])

        self.assertEquals(len(g_classified[0].modified_registers), 2)

        self.assertTrue(ReilRegisterOperand("eax", 32) in g_classified[0].modified_registers)
        self.assertTrue(ReilRegisterOperand("esp", 32) in g_classified[0].modified_registers)

    def test_store_memory_two_accesses_1(self):
        # testing : m[dst_reg + offset] <- dst_reg
        binary  = "\x50"                      # 0x00 : (1) push eax
        binary += "\x53"                      # 0x01 : (1) push ebx
        binary += "\xc3"                      # 0x02 : (1) ret

        g_finder = GadgetFinder(X86Disassembler(), binary, X86Translator(translation_mode=LITE_TRANSLATION), ARCH_X86, ARCH_X86_MODE_32)

        g_candidates = g_finder.find(0x00000000, 0x00000002)
        g_classified = self._g_classifier.classify(g_candidates[0])

        # self.print_candidates(g_candidates)
        # self.print_classified(g_classified)

        verified = self._g_verifier.verify(g_classified[1])

        self.assertEquals(len(g_candidates), 1)
        self.assertEquals(len(g_classified), 2)

        self.assertTrue(verified)

        self.assertEquals(g_classified[1].type, GadgetType.StoreMemory)
        self.assertEquals(g_classified[1].sources, [ReilRegisterOperand("eax", 32)])
        self.assertEquals(g_classified[1].destination, [ReilRegisterOperand("esp", 32), ReilImmediateOperand(0xfffffffc, 32)])

        self.assertEquals(len(g_classified[1].modified_registers), 1)

        self.assertTrue(ReilRegisterOperand("esp", 32) in g_classified[1].modified_registers)

    def test_arithmetic_load_memory_two_accesses_1(self):
        # testing : dst_reg <- dst_reg + m[dst_reg + offset]
        binary  = "\x8b\x09"                  # 0x00 : (2) mov ecx, dword ptr [ecx]
        binary += "\x03\x03"                  # 0x02 : (2) add eax, dword ptr [ebx]
        binary += "\xc3"                      # 0x04 : (1) ret

        g_finder = GadgetFinder(X86Disassembler(), binary, X86Translator(translation_mode=LITE_TRANSLATION), ARCH_X86, ARCH_X86_MODE_32)

        g_candidates = g_finder.find(0x00000000, 0x00000004)
        g_classified = self._g_classifier.classify(g_candidates[0])

        # self.print_candidates(g_candidates)
        # self.print_classified(g_classified)

        verified = self._g_verifier.verify(g_classified[1])

        self.assertEquals(len(g_candidates), 1)
        self.assertEquals(len(g_classified), 2)

        self.assertTrue(verified)

        self.assertEquals(g_classified[1].type, GadgetType.ArithmeticLoad)
        self.assertEquals(g_classified[1].sources, [ReilRegisterOperand("eax", 32), ReilRegisterOperand("ebx", 32), ReilImmediateOperand(0x0, 32)])
        self.assertEquals(g_classified[1].destination, [ReilRegisterOperand("eax", 32)])

        self.assertEquals(len(g_classified[1].modified_registers), 2)

        self.assertTrue(ReilRegisterOperand("ecx", 32) in g_classified[1].modified_registers)
        self.assertTrue(ReilRegisterOperand("esp", 32) in g_classified[1].modified_registers)

    def test_arithmetic_load_add_1(self):
        # testing : dst_reg <- src1_reg + src2_reg
        binary  = "\x23\x00"                    # 0x02 : (2) and eax, dword ptr [eax]
        binary += "\x00\xc9"                    # 0x02 : (2) add cl, cl
        binary += "\xc3"                        # 0x05 : (1) ret

        g_finder = GadgetFinder(X86Disassembler(), binary, X86Translator(translation_mode=LITE_TRANSLATION), ARCH_X86, ARCH_X86_MODE_32)

        g_candidates = g_finder.find(0x00000000, 0x00000004)
        g_classified = self._g_classifier.classify(g_candidates[1])

        # self.print_candidates(g_candidates)
        # self.print_classified(g_classified)

        verified = self._g_verifier.verify(g_classified[0])

        self.assertEquals(len(g_candidates), 2)
        self.assertEquals(len(g_classified), 2)

        self.assertTrue(verified)

        self.assertEquals(g_classified[0].type, GadgetType.Arithmetic)
        self.assertEquals(g_classified[0].sources, [ReilRegisterOperand("cl", 8), ReilRegisterOperand("cl", 8)])
        self.assertEquals(g_classified[0].destination, [ReilRegisterOperand("cl", 8)])
        self.assertEquals(g_classified[0].operation, "+")

        self.assertEquals(len(g_classified[0].modified_registers), 3)

        self.assertTrue(ReilRegisterOperand("eax", 32) in g_classified[0].modified_registers)
        self.assertTrue(ReilRegisterOperand("ecx", 32) in g_classified[0].modified_registers)
        self.assertTrue(ReilRegisterOperand("esp", 32) in g_classified[1].modified_registers)

    def test_arithmetic_load_and_1(self):
        # testing : dst_reg <- src1_reg + src2_reg
        binary  = "\x23\x00"                    # 0x02 : (2) and eax, dword ptr [eax]
        binary += "\x00\xc9"                    # 0x02 : (2) add cl, cl
        binary += "\xc3"                        # 0x05 : (1) ret

        g_finder = GadgetFinder(X86Disassembler(), binary, X86Translator(translation_mode=LITE_TRANSLATION), ARCH_X86, ARCH_X86_MODE_32)

        g_candidates = g_finder.find(0x00000000, 0x00000004)
        g_classified = self._g_classifier.classify(g_candidates[1])

        # self.print_candidates(g_candidates)
        # self.print_classified(g_classified)

        verified = self._g_verifier.verify(g_classified[1])

        self.assertEquals(len(g_candidates), 2)
        self.assertEquals(len(g_classified), 2)

        self.assertTrue(verified)

        self.assertEquals(g_classified[1].type, GadgetType.ArithmeticLoad)
        self.assertEquals(g_classified[1].sources, [ReilRegisterOperand("eax", 32), ReilRegisterOperand("eax", 32), ReilImmediateOperand(0x0, 32)])
        self.assertEquals(g_classified[1].destination, [ReilRegisterOperand("eax", 32)])
        self.assertEquals(g_classified[1].operation, "&")

        self.assertEquals(len(g_classified[1].modified_registers), 2)

        self.assertTrue(ReilRegisterOperand("ecx", 32) in g_classified[1].modified_registers)
        self.assertTrue(ReilRegisterOperand("esp", 32) in g_classified[1].modified_registers)

    def test_arithmetic_add_1(self):
        # testing : dst_reg <- src1_reg + src2_reg
        binary  = "\x00\xc3"                   # 0x00 : (2) add bl, al
        binary += "\x50"                       # 0x02 : (1) push eax
        binary += "\xc3"                       # 0x03 : (1) ret

        g_finder = GadgetFinder(X86Disassembler(), binary, X86Translator(translation_mode=LITE_TRANSLATION), ARCH_X86, ARCH_X86_MODE_32)

        g_candidates = g_finder.find(0x00000000, 0x00000003)
        g_classified = self._g_classifier.classify(g_candidates[0])

        # self.print_candidates(g_candidates)
        # self.print_classified(g_classified)

        verified = self._g_verifier.verify(g_classified[0])

        self.assertEquals(len(g_candidates), 1)
        self.assertEquals(len(g_classified), 4)

        self.assertTrue(verified)

        self.assertEquals(g_classified[0].type, GadgetType.Arithmetic)
        self.assertEquals(g_classified[0].sources, [ReilRegisterOperand("al", 8), ReilRegisterOperand("bl", 8)])
        self.assertEquals(g_classified[0].destination, [ReilRegisterOperand("bl", 8)])
        self.assertEquals(g_classified[0].operation, "+")

        self.assertEquals(len(g_classified[0].modified_registers), 1)

        self.assertTrue(ReilRegisterOperand("ebx", 32) in g_classified[0].modified_registers)

    def test_load_memory_1(self):
        # testing : dst_reg <- mem[offset]
        binary  = "\x8b\x45\x08"               # 0x00 : (3) mov eax, dword ptr [ebp+0x8]
        binary += "\x5d"                       # 0x03 : (1) pop ebp
        binary += "\xc3"                       # 0x04 : (1) ret

        g_finder = GadgetFinder(X86Disassembler(), binary, X86Translator(translation_mode=LITE_TRANSLATION), ARCH_X86, ARCH_X86_MODE_32)

        g_candidates = g_finder.find(0x00000000, 0x00000004)
        g_classified = self._g_classifier.classify(g_candidates[0])

        # self.print_candidates(g_candidates)
        # self.print_classified(g_classified)

        verified = self._g_verifier.verify(g_classified[1])

        self.assertEquals(len(g_candidates), 1)
        self.assertEquals(len(g_classified), 2)

        self.assertTrue(verified)

        self.assertEquals(g_classified[1].type, GadgetType.LoadMemory)
        self.assertEquals(g_classified[1].sources, [ReilRegisterOperand("ebp", 32), ReilImmediateOperand(0x8, 32)])
        self.assertEquals(g_classified[1].destination, [ReilRegisterOperand("eax", 32)])

        self.assertEquals(len(g_classified[1].modified_registers), 2)

        self.assertTrue(ReilRegisterOperand("esp", 32) in g_classified[1].modified_registers)
        self.assertTrue(ReilRegisterOperand("ebp", 32) in g_classified[1].modified_registers)

    def test_load_memory_2(self):
        # testing : dst_reg <- mem[offset]
        binary  = "\x08\xa3\xa0\x31\x05\x08"            # 0x00 : (6) or [ebx+0x80531a0], ah
        binary += "\xc9"                                # 0x06 : (1) leave
        binary += "\xc3"                                # 0x07 : (1) ret

        g_finder = GadgetFinder(X86Disassembler(), binary, X86Translator(translation_mode=LITE_TRANSLATION), ARCH_X86, ARCH_X86_MODE_32)

        g_candidates = g_finder.find(0x00000000, 0x00000007)
        g_classified = self._g_classifier.classify(g_candidates[1])

        # self.print_candidates(g_candidates)
        # self.print_classified(g_classified)

        verified = self._g_verifier.verify(g_classified[0])

        self.assertEquals(len(g_candidates), 4)
        self.assertEquals(len(g_classified), 2)

        self.assertTrue(verified)

        self.assertEquals(g_classified[0].type, GadgetType.LoadMemory)
        self.assertEquals(g_classified[0].sources, [ReilRegisterOperand("ebp", 32), ReilImmediateOperand(0x0, 32)])
        self.assertEquals(g_classified[0].destination, [ReilRegisterOperand("ebp", 32)])

        self.assertEquals(len(g_classified[0].modified_registers), 1)

        self.assertTrue(ReilRegisterOperand("esp", 32) in g_classified[0].modified_registers)

    def test_arithmetic_store_add_1(self):
        # testing : m[dst_reg] <- m[dst_reg] + src_reg
        binary  = "\x01\x18"                 # 0x00 : (2) add dword ptr [eax], ebx
        binary += "\xc3"                     # 0x02 : (1) ret

        g_finder = GadgetFinder(X86Disassembler(), binary, X86Translator(translation_mode=LITE_TRANSLATION), ARCH_X86, ARCH_X86_MODE_32)

        g_candidates = g_finder.find(0x00000000, 0x00000002)
        g_classified = self._g_classifier.classify(g_candidates[0])

        # self.print_candidates(g_candidates)
        # self.print_classified(g_classified)

        verified = self._g_verifier.verify(g_classified[0])

        self.assertEquals(len(g_candidates), 1)
        self.assertEquals(len(g_classified), 1)

        self.assertTrue(verified)

        self.assertEquals(g_classified[0].type, GadgetType.ArithmeticStore)
        self.assertEquals(g_classified[0].sources, [ReilRegisterOperand("eax", 32), ReilImmediateOperand(0x0, 32), ReilRegisterOperand("ebx", 32)])
        self.assertEquals(g_classified[0].destination, [ReilRegisterOperand("eax", 32), ReilImmediateOperand(0x0, 32)])
        self.assertEquals(g_classified[0].operation, "+")

        self.assertEquals(len(g_classified[0].modified_registers), 1)

        self.assertTrue(ReilRegisterOperand("esp", 32) in g_classified[0].modified_registers)

    def test_arithmetic_store_xor_1(self):
        # testing : m[dst_reg] <- m[dst_reg] + src_reg

        binary = "\x31\x05\x08\x8b\x00\x5d\xc3" # xor dword ptr [0x5d008b08], eax ; ret

        g_finder = GadgetFinder(X86Disassembler(), binary, X86Translator(translation_mode=LITE_TRANSLATION), ARCH_X86, ARCH_X86_MODE_32)

        g_candidates = g_finder.find(0x00000000, 0x00000006)
        g_classified = self._g_classifier.classify(g_candidates[2])

        # self.print_candidates(g_candidates)
        # self.print_classified(g_classified)

        verified = self._g_verifier.verify(g_classified[0])

        self.assertEquals(len(g_candidates), 3)
        self.assertEquals(len(g_classified), 1)

        self.assertTrue(verified)

        self.assertEquals(g_classified[0].type, GadgetType.ArithmeticStore)
        self.assertEquals(g_classified[0].sources, [ReilEmptyOperand(), ReilImmediateOperand(0x5d008b08, 32), ReilRegisterOperand("eax", 32)])
        self.assertEquals(g_classified[0].destination, [ReilEmptyOperand(), ReilImmediateOperand(0x5d008b08, 32)])
        self.assertEquals(g_classified[0].operation, "^")

        self.assertEquals(len(g_classified[0].modified_registers), 1)

        self.assertTrue(ReilRegisterOperand("esp", 32) in g_classified[0].modified_registers)

    def test_arithmetic_store_or_1(self):
        # testing : m[dst_reg] <- m[dst_reg] OP src_reg
        binary  = "\x08\xa3\xa0\x31\x05\x08"            # 0x00 : (6) or [ebx+0x80531a0], ah
        binary += "\xc9"                                # 0x06 : (1) leave
        binary += "\xc3"                                # 0x07 : (1) ret

        g_finder = GadgetFinder(X86Disassembler(), binary, X86Translator(translation_mode=LITE_TRANSLATION), ARCH_X86, ARCH_X86_MODE_32)

        g_candidates = g_finder.find(0x00000000, 0x00000007)
        g_classified = self._g_classifier.classify(g_candidates[1])

        # self.print_candidates(g_candidates)
        # self.print_classified(g_classified)

        verified = self._g_verifier.verify(g_classified[1])

        self.assertEquals(len(g_candidates), 4)
        self.assertEquals(len(g_classified), 2)

        self.assertTrue(verified)

        self.assertEquals(g_classified[1].type, GadgetType.ArithmeticStore)
        self.assertEquals(g_classified[1].sources, [ReilRegisterOperand("ebx", 32), ReilImmediateOperand(0x80531a0, 32), ReilRegisterOperand("ah", 8)])
        self.assertEquals(g_classified[1].destination, [ReilRegisterOperand("ebx", 32), ReilImmediateOperand(0x80531a0, 32)])

        self.assertEquals(len(g_classified[1].modified_registers), 2)

        self.assertTrue(ReilRegisterOperand("esp", 32) in g_classified[1].modified_registers)
        self.assertTrue(ReilRegisterOperand("ebp", 32) in g_classified[1].modified_registers)

    def test_load_constant_1(self):
        # testing : reg <- constant
        binary  = "\x00\x0f"                            # 0x00 : (2) add [edi],cl
        binary += "\xb6\x55"                            # 0x02 : (2) mov dh,0x55
        binary += "\xc3"                                # 0x04 : (1) ret

        g_finder = GadgetFinder(X86Disassembler(), binary, X86Translator(translation_mode=LITE_TRANSLATION), ARCH_X86, ARCH_X86_MODE_32)

        g_candidates = g_finder.find(0x00000000, 0x00000004)
        g_classified = self._g_classifier.classify(g_candidates[1])

        # self.print_candidates(g_candidates)
        # self.print_classified(g_classified)

        verified = self._g_verifier.verify(g_classified[1])

        self.assertEquals(len(g_candidates), 2)
        self.assertEquals(len(g_classified), 2)

        self.assertTrue(verified)

        self.assertEquals(g_classified[0].type, GadgetType.LoadConstant)
        self.assertEquals(g_classified[0].sources, [ReilImmediateOperand(0x55, 8)])
        self.assertEquals(g_classified[0].destination, [ReilRegisterOperand("dh", 8)])

        self.assertEquals(len(g_classified[0].modified_registers), 2)

        self.assertTrue(ReilRegisterOperand("edx", 32) in g_classified[0].modified_registers)
        self.assertTrue(ReilRegisterOperand("esp", 32) in g_classified[0].modified_registers)

    def print_candidates(self, candidates):
        print "Candidates :"

        for gadget in candidates:
            print gadget
            print "-" * 10

    def print_classified(self, classified):
        print "Classified :"

        for gadget in classified:
            print gadget
            print gadget.type
            print "-" * 10


class GadgetVerifierTests64(unittest.TestCase):

    def setUp(self):
        self._arch_info = X86ArchitectureInformation(ARCH_X86_MODE_64)
        self._smt_solver = SmtSolver()
        self._smt_translator = SmtTranslator(self._smt_solver, self._arch_info.address_size)
        self._ir_emulator = ReilEmulator(self._arch_info)

        self._smt_translator.set_arch_alias_mapper(self._arch_info.alias_mapper)
        self._smt_translator.set_arch_registers_size(self._arch_info.registers_size)

        self._code_analyzer = CodeAnalyzer(self._smt_solver, self._smt_translator, self._arch_info)

        self._g_classifier = GadgetClassifier(self._ir_emulator, self._arch_info)
        self._g_verifier = GadgetVerifier(self._code_analyzer, self._arch_info)

    def test_store_memory_1(self):
        # testing : m[dst_reg + offset] <- src_reg

        # mov dword ptr [rax], esi ; ret
        binary  = "\x89\x30"                # 0x00 : (2) mov [rax], esi
        binary += "\xC3"                    # 0x02 : (1) ret

        disassembler = X86Disassembler(architecture_mode=ARCH_X86_MODE_64)
        translator = X86Translator(architecture_mode=ARCH_X86_MODE_64,
                               translation_mode=LITE_TRANSLATION)

        g_finder = GadgetFinder(disassembler, binary, translator, ARCH_X86, ARCH_X86_MODE_64)

        g_candidates = g_finder.find(0x00000000, 0x00000002)
        g_classified = self._g_classifier.classify(g_candidates[0])

        # self.print_candidates(g_candidates)
        # self.print_classified(g_classified)

        verified = self._g_verifier.verify(g_classified[0])

        self.assertEquals(len(g_candidates), 1)
        self.assertEquals(len(g_classified), 1)

        self.assertEquals(g_classified[0].type, GadgetType.StoreMemory)
        self.assertEquals(g_classified[0].sources, [ReilRegisterOperand("esi", 32)])
        self.assertEquals(g_classified[0].destination, [ReilRegisterOperand("rax", 64), ReilImmediateOperand(0x0, 64)])

    def print_candidates(self, candidates):
        print "Candidates :"

        for gadget in candidates:
            print gadget
            print "-" * 10

    def print_classified(self, classified):
        print "Classified :"

        for gadget in classified:
            print gadget
            print gadget.type
            print "-" * 10


def main():
    unittest.main()


if __name__ == '__main__':
    main()
