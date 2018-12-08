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

from barf.arch import ARCH_X86_MODE_32
from barf.arch.x86 import X86ArchitectureInformation
from barf.arch.x86.parser import X86Parser
from barf.arch.x86.translator import X86Translator
from barf.core.reil.emulator import ReilEmulator


class ReilEmulatorTaintTests(unittest.TestCase):

    def setUp(self):
        self._arch_info = X86ArchitectureInformation(ARCH_X86_MODE_32)

        self._emulator = ReilEmulator(self._arch_info)

        self._asm_parser = X86Parser(ARCH_X86_MODE_32)
        self._translator = X86Translator(ARCH_X86_MODE_32)

    def test_arithmetic_1(self):
        asm_instrs  = self._asm_parser.parse("add eax, ebx")

        self.__set_address(0xdeadbeef, [asm_instrs])

        reil_instrs = self._translator.translate(asm_instrs)

        regs_initial = {
            "eax" : 0x1,
            "ebx" : 0x2,
        }

        self._emulator.set_register_taint("ebx", True)

        regs_final, _ = self._emulator.execute_lite(
            reil_instrs,
            context=regs_initial
        )

        self.assertEqual(self._emulator.get_register_taint("eax"), True)

    def test_store_reg_1(self):
        asm_instrs  = self._asm_parser.parse("mov eax, ebx")

        self.__set_address(0xdeadbeef, [asm_instrs])

        reil_instrs = self._translator.translate(asm_instrs)

        regs_initial = {
            "eax" : 0x1,
            "ebx" : 0x2,
        }

        self._emulator.set_register_taint("eax", True)

        regs_final, _ = self._emulator.execute_lite(
            reil_instrs,
            context=regs_initial
        )

        self.assertEqual(self._emulator.get_register_taint("eax"), False)

    def test_store_mem_1(self):
        asm_instrs  = self._asm_parser.parse("mov [eax], ebx")

        self.__set_address(0xdeadbeef, [asm_instrs])

        reil_instrs = self._translator.translate(asm_instrs)

        regs_initial = {
            "eax" : 0xcafecafe,
            "ebx" : 0x2,
        }

        self._emulator.set_register_taint("ebx", True)

        regs_final, _ = self._emulator.execute_lite(
            reil_instrs,
            context=regs_initial
        )

        self.assertEqual(self._emulator.get_memory_taint(regs_initial['eax'], 4), True)

    def test_store_mem_2(self):
        asm_instrs  = self._asm_parser.parse("mov [eax], ebx")

        self.__set_address(0xdeadbeef, [asm_instrs])

        reil_instrs = self._translator.translate(asm_instrs)

        regs_initial = {
            "eax" : 0xcafecafe,
            "ebx" : 0x2,
        }

        self._emulator.set_register_taint("eax", True)

        regs_final, _ = self._emulator.execute_lite(
            reil_instrs,
            context=regs_initial
        )

        self.assertEqual(self._emulator.get_memory_taint(regs_initial['eax'], 4), False)

    def test_load_mem_1(self):
        asm_instrs  = self._asm_parser.parse("mov eax, [ebx]")

        self.__set_address(0xdeadbeef, [asm_instrs])

        reil_instrs = self._translator.translate(asm_instrs)

        regs_initial = {
            "eax" : 0x2,
            "ebx" : 0xcafecafe,
        }

        self._emulator.set_memory_taint(regs_initial["ebx"], 4, True)

        regs_final, _ = self._emulator.execute_lite(
            reil_instrs,
            context=regs_initial
        )

        self.assertEqual(self._emulator.get_register_taint("eax"), True)

    def __set_address(self, address, asm_instrs):
        addr = address

        for asm_instr in asm_instrs:
            asm_instr.address = addr
            addr += 1


def main():
    unittest.main()


if __name__ == '__main__':
    main()
