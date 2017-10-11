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

from barf.core.reil import ReilParser
from barf.core.smt.smtsymbol import BitVec
from barf.core.smt.smtsolver import Z3Solver as SmtSolver
# from barf.core.smt.smtsolver import CVC4Solver as SmtSolver
from barf.core.smt.smttranslator import SmtTranslator


class SmtSolverTests(unittest.TestCase):

    def setUp(self):
        self._address_size = 32
        self._parser = ReilParser()
        self._solver = SmtSolver()
        self._translator = SmtTranslator(self._solver, self._address_size)

    def test_mul(self):
        instrs = self._parser.parse([
            "mul [DWORD 0x0, DWORD 0x1, DWORD t0]"
        ])

        # Translate instructions to formulae
        for instr in instrs:
            for form in self._translator.translate(instr):
                self._solver.add(form)

        # Add constraints
        constraints = [
            self._translator.make_bitvec(32, self._translator.get_name_init("t0")) != 0,   # Precondition
            self._translator.make_bitvec(32, self._translator.get_name_curr("t0")) == 0,   # Postcondition
        ]

        for constr in constraints:
            self._solver.add(constr)

        # Assertions
        self.assertEqual(self._solver.check(), 'sat')

    def test_div_1(self):
        instrs = self._parser.parse([
            "div [DWORD 2, DWORD 1, DWORD t1]"
        ])

        # Translate instructions to formulae
        for instr in instrs:
            for form in self._translator.translate(instr):
                self._solver.add(form)

        # Add constraints
        constraints = [
            self._translator.make_bitvec(32, self._translator.get_name_curr("t1")) != 0x2,
        ]

        for constr in constraints:
            self._solver.add(constr)

        # Assertions
        self.assertEqual(self._solver.check(), 'unsat')

    def test_div_2(self):
        instrs = self._parser.parse([
            "div [DWORD 0xffffffff, DWORD 0x2, DWORD t1]"
        ])

        # Translate instructions to formulae
        for instr in instrs:
            for form in self._translator.translate(instr):
                self._solver.add(form)

        # Add constraints
        constraints = [
            self._translator.make_bitvec(32, self._translator.get_name_curr("t1")) != 0x7fffffff,
        ]

        for constr in constraints:
            self._solver.add(constr)

        # Assertions
        self.assertEqual(self._solver.check(), 'unsat')

    def test_sdiv_1(self):
        instrs = self._parser.parse([
            "sdiv [DWORD -2, DWORD -1, DWORD t1]"
        ])

        # Translate instructions to formulae
        for instr in instrs:
            for form in self._translator.translate(instr):
                self._solver.add(form)

        # Add constraints
        constraints = [
            self._translator.make_bitvec(32, self._translator.get_name_curr("t1")) != 0x2,
        ]

        for constr in constraints:
            self._solver.add(constr)

        # Assertions
        self.assertEqual(self._solver.check(), 'unsat')

    def test_sdiv_2(self):
        instrs = self._parser.parse([
            "sdiv [DWORD -2, DWORD 1, DWORD t1]"
        ])

        # Translate instructions to formulae
        for instr in instrs:
            for form in self._translator.translate(instr):
                self._solver.add(form)

        # Add constraints
        constraints = [
            self._translator.make_bitvec(32, self._translator.get_name_curr("t1")) != 0xfffffffe,
        ]

        for constr in constraints:
            self._solver.add(constr)

        # Assertions
        self.assertEqual(self._solver.check(), 'unsat')

    def test_smod_1(self):
        instrs = self._parser.parse([
            "smod [DWORD 5, DWORD -3, DWORD t1]"
        ])

        # Translate instructions to formulae
        for instr in instrs:
            for form in self._translator.translate(instr):
                self._solver.add(form)

        # Add constraints
        constraints = [
            self._translator.make_bitvec(32, self._translator.get_name_curr("t1")) != 0xffffffff,
        ]

        for constr in constraints:
            self._solver.add(constr)

        # Assertions
        self.assertEqual(self._solver.check(), 'unsat')

    def test_smod_2(self):
        instrs = self._parser.parse([
            "smod [DWORD -5, DWORD 3, DWORD t1]"
        ])

        # Translate instructions to formulae
        for instr in instrs:
            for form in self._translator.translate(instr):
                self._solver.add(form)

        # Add constraints
        constraints = [
            self._translator.make_bitvec(32, self._translator.get_name_curr("t1")) != 0x1,
        ]

        for constr in constraints:
            self._solver.add(constr)

        # Assertions
        self.assertEqual(self._solver.check(), 'unsat')

    def test_bsh_left_1(self):
        instrs = self._parser.parse([
            "bsh [DWORD t1, DWORD 16, QWORD t2]"
        ])

        # Translate instructions to formulae
        for instr in instrs:
            for form in self._translator.translate(instr):
                self._solver.add(form)

        # Add constraints
        constraints = [
            self._translator.make_bitvec(32, self._translator.get_name_curr("t1")) == 0xffffffff,
            self._translator.make_bitvec(64, self._translator.get_name_curr("t2")) != 0x0000ffffffff0000,
        ]

        for constr in constraints:
            self._solver.add(constr)

        # Assertions
        self.assertEqual(self._solver.check(), 'unsat')

    def test_bsh_left_2(self):
        instrs = self._parser.parse([
            "bsh [DWORD t1, DWORD 16, DWORD t2]"
        ])

        # Translate instructions to formulae
        for instr in instrs:
            for form in self._translator.translate(instr):
                self._solver.add(form)

        # Add constraints
        constraints = [
            self._translator.make_bitvec(32, self._translator.get_name_curr("t1")) == 0xffffffff,
            self._translator.make_bitvec(32, self._translator.get_name_curr("t2")) != 0xffff0000,
        ]

        for constr in constraints:
            self._solver.add(constr)

        # Assertions
        self.assertEqual(self._solver.check(), 'unsat')

    def test_bsh_left_3(self):
        instrs = self._parser.parse([
            "bsh [DWORD t1, DWORD 16, WORD t2]"
        ])

        # Translate instructions to formulae
        for instr in instrs:
            for form in self._translator.translate(instr):
                self._solver.add(form)

        # Add constraints
        constraints = [
            self._translator.make_bitvec(32, self._translator.get_name_curr("t1")) == 0xffffffff,
            self._translator.make_bitvec(16, self._translator.get_name_curr("t2")) != 0x0000,
        ]

        for constr in constraints:
            self._solver.add(constr)

        # Assertions
        self.assertEqual(self._solver.check(), 'unsat')

    def test_bsh_right_1(self):
        instrs = self._parser.parse([
            "bsh [DWORD t1, DWORD -16, QWORD t2]"
        ])

        # Translate instructions to formulae
        for instr in instrs:
            for form in self._translator.translate(instr):
                self._solver.add(form)

        # Add constraints
        constraints = [
            self._translator.make_bitvec(32, self._translator.get_name_curr("t1")) == 0xffffffff,
            self._translator.make_bitvec(64, self._translator.get_name_curr("t2")) != 0x000000000000ffff,
        ]

        for constr in constraints:
            self._solver.add(constr)

        # Assertions
        self.assertEqual(self._solver.check(), 'unsat')

    def test_bsh_right_2(self):
        instrs = self._parser.parse([
            "bsh [DWORD t1, DWORD -16, DWORD t2]"
        ])

        # Translate instructions to formulae
        for instr in instrs:
            for form in self._translator.translate(instr):
                self._solver.add(form)

        # Add constraints
        constraints = [
            self._translator.make_bitvec(32, self._translator.get_name_curr("t1")) == 0xffffffff,
            self._translator.make_bitvec(32, self._translator.get_name_curr("t2")) != 0x0000ffff,
        ]

        for constr in constraints:
            self._solver.add(constr)

        # Assertions
        self.assertEqual(self._solver.check(), 'unsat')

    def test_bsh_right_3(self):
        instrs = self._parser.parse([
            "bsh [DWORD t1, DWORD -16, WORD t2]"
        ])

        # Translate instructions to formulae
        for instr in instrs:
            for form in self._translator.translate(instr):
                self._solver.add(form)

        # Add constraints
        constraints = [
            self._translator.make_bitvec(32, self._translator.get_name_curr("t1")) == 0xffffffff,
            self._translator.make_bitvec(16, self._translator.get_name_curr("t2")) != 0xffff,
        ]

        for constr in constraints:
            self._solver.add(constr)

        # Assertions
        self.assertEqual(self._solver.check(), 'unsat')

    # Extensions
    def test_sext_1(self):
        instrs = self._parser.parse([
            "sext [WORD 0xffff, EMPTY, DWORD t1]"
        ])

        # Translate instructions to formulae
        for instr in instrs:
            for form in self._translator.translate(instr):
                self._solver.add(form)

        # Add constraints
        constraints = [
            self._translator.make_bitvec(32, self._translator.get_name_curr("t1")) != 0xffffffff,
        ]

        for constr in constraints:
            self._solver.add(constr)

        # Assertions
        self.assertEqual(self._solver.check(), 'unsat')

    def test_sext_2(self):
        instrs = self._parser.parse([
            "sext [WORD 0x7fff, EMPTY, DWORD t1]"
        ])

        # Translate instructions to formulae
        for instr in instrs:
            for form in self._translator.translate(instr):
                self._solver.add(form)

        # Add constraints
        constraints = [
            self._translator.make_bitvec(32, self._translator.get_name_curr("t1")) != 0x00007fff,
        ]

        for constr in constraints:
            self._solver.add(constr)

        # Assertions
        self.assertEqual(self._solver.check(), 'unsat')


def main():
    unittest.main()


if __name__ == '__main__':
    main()
