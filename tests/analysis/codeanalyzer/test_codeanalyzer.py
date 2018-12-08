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

from barf.analysis.codeanalyzer import CodeAnalyzer
from barf.arch import ARCH_X86_MODE_32
from barf.arch.x86 import X86ArchitectureInformation
from barf.arch.x86.parser import X86Parser
from barf.arch.x86.translator import X86Translator
from barf.core.smt.smtsolver import Z3Solver as SmtSolver
# from barf.core.smt.smtsolver import CVC4Solver as SmtSolver
from barf.core.smt.smttranslator import SmtTranslator


class CodeAnalyzerTests(unittest.TestCase):

    def setUp(self):
        self._arch_info = X86ArchitectureInformation(ARCH_X86_MODE_32)

        self._smt_solver = SmtSolver()

        self._smt_translator = SmtTranslator(self._smt_solver, self._arch_info.address_size)
        self._smt_translator.set_arch_alias_mapper(self._arch_info.alias_mapper)
        self._smt_translator.set_arch_registers_size(self._arch_info.registers_size)

        self._x86_parser = X86Parser(ARCH_X86_MODE_32)

        self._x86_translator = X86Translator(ARCH_X86_MODE_32)

        self._code_analyzer = CodeAnalyzer(self._smt_solver, self._smt_translator, self._arch_info)

    def test_add_reg_reg(self):
        # Parser x86 instructions.
        asm_instrs = [self._x86_parser.parse(i) for i in [
            "add eax, ebx",
        ]]

        # Add REIL instruction to the analyzer.
        for reil_instr in self.__asm_to_reil(asm_instrs):
            self._code_analyzer.add_instruction(reil_instr)

        # Add constraints.
        eax_pre = self._code_analyzer.get_register_expr("eax", mode="pre")
        eax_post = self._code_analyzer.get_register_expr("eax", mode="post")

        constraints = [
            eax_pre != 42,      # Pre-condition
            eax_post == 42,     # Post-condition
        ]

        for constr in constraints:
            self._code_analyzer.add_constraint(constr)

        # Assertions.
        self.assertEqual(self._code_analyzer.check(), 'sat')
        self.assertNotEqual(self._code_analyzer.get_expr_value(eax_pre), 42)
        self.assertEqual(self._code_analyzer.get_expr_value(eax_post), 42)

    def test_add_reg_mem(self):
        # Parser x86 instructions.
        asm_instrs = [self._x86_parser.parse(i) for i in [
            "add eax, [ebx + 0x1000]",
        ]]

        # Add REIL instruction to the analyzer.
        for reil_instr in self.__asm_to_reil(asm_instrs):
            self._code_analyzer.add_instruction(reil_instr)

        # Add constraints.
        eax_pre = self._code_analyzer.get_register_expr("eax", mode="pre")
        eax_post = self._code_analyzer.get_register_expr("eax", mode="post")

        constraints = [
            eax_pre != 42,      # Pre-condition
            eax_post == 42,     # Post-condition
        ]

        for constr in constraints:
            self._code_analyzer.add_constraint(constr)

        # Assertions
        self.assertEqual(self._code_analyzer.check(), 'sat')
        self.assertNotEqual(self._code_analyzer.get_expr_value(eax_pre), 42)
        self.assertEqual(self._code_analyzer.get_expr_value(eax_post), 42)

    def test_add_mem_reg(self):
        # Parser x86 instructions.
        asm_instrs = [self._x86_parser.parse(i) for i in [
            "add [eax + 0x1000], ebx",
        ]]

        # Add REIL instruction to the analyzer.
        for reil_instr in self.__asm_to_reil(asm_instrs):
            self._code_analyzer.add_instruction(reil_instr)

        # Add constraints.
        eax_pre = self._code_analyzer.get_register_expr("eax", mode="pre")

        mem_pre = self._code_analyzer.get_memory(mode="pre")
        mem_post = self._code_analyzer.get_memory(mode="post")

        constraints = [
            mem_pre[eax_pre + 0x1000] != 42,  # Pre-condition
            mem_post[eax_pre + 0x1000] == 42,   # Post-condition
        ]

        for constr in constraints:
            self._code_analyzer.add_constraint(constr)

        # Assertions.
        self.assertEqual(self._code_analyzer.check(), 'sat')
        self.assertNotEqual(self._code_analyzer.get_expr_value(mem_pre[eax_pre + 0x1000]), 42)
        self.assertEqual(self._code_analyzer.get_expr_value(mem_post[eax_pre + 0x1000]), 42)

    def __asm_to_reil(self, instructions):
        # Set address for each instruction.
        for addr, asm_instr in enumerate(instructions):
            asm_instr.address = addr

        # Translate to REIL instructions.
        reil_instrs = [self._x86_translator.translate(i) for i in instructions]

        # Flatten list and return
        reil_instrs = [instr for instrs in reil_instrs for instr in instrs]

        return reil_instrs


def main():
    unittest.main()


if __name__ == '__main__':
    main()
