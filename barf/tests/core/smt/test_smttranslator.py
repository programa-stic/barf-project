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
from barf.core.smt.smtlibv2 import BitVec
from barf.core.smt.smtlibv2 import Z3Solver as SmtSolver
from barf.core.smt.smttranslator import SmtTranslator

VERBOSE = False


class SmtTranslatorTests(unittest.TestCase):

    def setUp(self):
        self._address_size = 32
        self._parser = ReilParser()
        self._solver = SmtSolver()
        self._translator = SmtTranslator(self._solver, self._address_size)

    def test_add_reg_reg(self):
        if VERBOSE:
            print "\n[+] Test: test_add_reg_reg"

        # add eax, ebx
        instrs = self._parser.parse([
            "add [eax, ebx, t0]",
            "str [t0, e, eax]",
        ])

        instrs[0].operands[0].size = 32
        instrs[0].operands[1].size = 32
        instrs[0].operands[2].size = 32

        instrs[1].operands[0].size = 32
        instrs[1].operands[2].size = 32

        self._solver.reset()

        # translate instructions to formulae
        if VERBOSE:
            print "[+] Instructions:"
            for instr in instrs:
                trans = self._translator.translate(instr)

                if trans is not None:
                    self._solver.add(trans)

                print "    %-20s -> %-20s" % (instr, trans)

        # add constrains
        constraints = [
            self._solver.mkBitVec(32, self._translator.get_curr_name("eax")) == 42,
            self._solver.mkBitVec(32, self._translator.get_init_name("eax")) != 42,
        ]

        if VERBOSE:
            print "[+] Constraints :"
            for i, constr in enumerate(constraints):
                self._solver.add(constr)

                print "    %2d : %s" % (i, constr)

        # check satisfiability
        is_sat = self._solver.check() == 'sat'

        if VERBOSE:
            print "[+] Satisfiability : %s" % str(is_sat)

            if is_sat:
                print "    eax : 0x%08x" % self._solver.getvaluebyname(self._translator.get_curr_name("eax"))
                print "    ebx : 0x%08x" % self._solver.getvaluebyname(self._translator.get_curr_name("ebx"))

            print "~" * 80

        self.assertEqual(is_sat, True)

    def test_add_reg_mem(self):
        if VERBOSE:
            print "\n[+] Test: test_add_reg_mem"

        # add eax, [ebx]
        instrs = self._parser.parse([
            "ldm [ebx, EMPTY, t0]",
            "add [eax, t0, t1]",
            "str [t1, EMPTY, eax]",
        ])

        instrs[0].operands[0].size = 32
        instrs[0].operands[2].size = 32

        instrs[1].operands[0].size = 32
        instrs[1].operands[1].size = 32
        instrs[1].operands[2].size = 32

        instrs[2].operands[0].size = 32
        instrs[2].operands[2].size = 32

        self._solver.reset()

        # translate instructions to formulae
        if VERBOSE:
            print "[+] Instructions:"
            for instr in instrs:
                trans = self._translator.translate(instr)

                if trans is not None:
                    self._solver.add(trans)

                print "    %-20s -> %-20s" % (instr, trans)

        # add constrains
        constraints = [
            self._solver.mkBitVec(32, self._translator.get_curr_name("eax")) == 42,
            self._solver.mkBitVec(32, self._translator.get_init_name("eax")) != 42,
        ]

        if VERBOSE:
            print "[+] Constraints :"
            for i, constr in enumerate(constraints):
                self._solver.add(constr)

                print "    %2d : %s" % (i, constr)

        # check satisfiability
        is_sat = self._solver.check() == 'sat'

        if VERBOSE:
            print "[+] Satisfiability : %s" % str(is_sat)

            if is_sat:
                print "    eax : 0x%08x" % self._solver.getvaluebyname(self._translator.get_curr_name("eax"))
                print "    ebx : 0x%08x" % self._solver.getvaluebyname(self._translator.get_curr_name("ebx"))

            print "~" * 80

        self.assertEqual(is_sat, True)

    def test_add_mem_reg(self):
        if VERBOSE:
            print "\n[+] Test: test_add_mem_reg"

        # add [eax], ebx
        instrs = self._parser.parse([
            "ldm [eax, EMPTY, t0]",
            "add [t0, ebx, t1]",
            "stm [t1, EMPTY, eax]",
        ])

        instrs[0].operands[0].size = 32
        instrs[0].operands[2].size = 32

        instrs[1].operands[0].size = 32
        instrs[1].operands[1].size = 32
        instrs[1].operands[2].size = 32

        instrs[2].operands[0].size = 32
        instrs[2].operands[2].size = 32

        self._solver.reset()

        # add constrains
        mem = self._translator.get_memory()
        eax = self._solver.mkBitVec(32, "eax_0")

        constraint = (mem[eax] != 42)

        if VERBOSE:
            print "constraint : %s" % constraint

        self._solver.add(constraint)

        # translate instructions to formulae
        if VERBOSE:
            print "[+] Instructions:"
            for instr in instrs:
                trans = self._translator.translate(instr)

                if trans is not None:
                    self._solver.add(trans)

                print "    %-20s -> %-20s" % (instr, trans)

        # add constrains
        constraints = [
            mem[eax] == 42,
            self._solver.mkBitVec(32, self._translator.get_init_name("t0")) != 42,
        ]

        if VERBOSE:
            print "[+] Constraints :"
            for i, constr in enumerate(constraints):
                self._solver.add(constr)

                print "    %2d : %s" % (i, constr)

        # check satisfiability
        is_sat = self._solver.check() == 'sat'

        if VERBOSE:
            print "[+] Satisfiability : %s" % str(is_sat)

            if is_sat:
                print "    eax : 0x%08x" % self._solver.getvaluebyname(self._translator.get_curr_name("eax"))
                print "    ebx : 0x%08x" % self._solver.getvaluebyname(self._translator.get_curr_name("ebx"))
                print "    t0 : 0x%08x" % self._solver.getvaluebyname(self._translator.get_curr_name("t0"))
                print "    [eax] : 0x%08x" % self._solver.getvalue(mem[eax])

            print "~" * 80

        self.assertEqual(is_sat, True)

    def test_add_mem_reg_2(self):
        if VERBOSE:
            print "\n[+] Test: test_add_mem_reg_2"

        # add [eax + 0x1000], ebx
        instrs = self._parser.parse([
            "add [eax, 0x1000, t0]",
            "ldm [t0, e, t1]",
            "add [t1, ebx, t2]",
            "stm [t2, e, t0]",
        ])

        instrs[0].operands[0].size = 32
        instrs[0].operands[1].size = 32
        instrs[0].operands[2].size = 32

        instrs[1].operands[0].size = 32
        instrs[1].operands[2].size = 32

        instrs[2].operands[0].size = 32
        instrs[2].operands[1].size = 32
        instrs[2].operands[2].size = 32

        instrs[3].operands[0].size = 32
        instrs[3].operands[2].size = 32

        self._solver.reset()

        # add constrains
        mem = self._translator.get_memory()
        eax = self._solver.mkBitVec(32, "eax_0")
        off = BitVec(32, "#x%08x" % 0x1000)

        constraint = (mem[eax + off] != 42)

        if VERBOSE:
            print "constraint : %s" % constraint

        self._solver.add(constraint)

        # translate instructions to formulae
        if VERBOSE:
            print "[+] Instructions:"
            for instr in instrs:
                trans = self._translator.translate(instr)

                if trans is not None:
                    self._solver.add(trans)

                print "    %-20s -> %-20s" % (instr, trans)

        # add constrains
        constraints = [
            mem[eax + off] == 42,
            self._solver.mkBitVec(32, self._translator.get_init_name("t1")) != 42,
        ]

        if VERBOSE:
            print "[+] Constraints :"

            for i, constr in enumerate(constraints):
                self._solver.add(constr)

                print "    %2d : %s" % (i, constr)

        # check satisfiability
        is_sat = self._solver.check() == 'sat'

        if VERBOSE:
            print "[+] Satisfiability : %s" % str(is_sat)

            if is_sat:
                print "    eax : 0x%08x" % self._solver.getvaluebyname(self._translator.get_curr_name("eax"))
                print "    ebx : 0x%08x" % self._solver.getvaluebyname(self._translator.get_curr_name("ebx"))
                print "    t0 : 0x%08x" % self._solver.getvaluebyname(self._translator.get_curr_name("t0"))
                print "    t1 : 0x%08x" % self._solver.getvaluebyname(self._translator.get_curr_name("t1"))
                print "    [eax + off] : 0x%08x" % self._solver.getvalue(mem[eax + off])

            print "~" * 80

        self.assertEqual(is_sat, True)

    def test_mul(self):
        if VERBOSE:
            print "\n[+] Test: test_mul"

        instrs = self._parser.parse([
            "mul [0x0, 0x1, t0]",
        ])

        instrs[0].operands[0].size = 32
        instrs[0].operands[1].size = 32

        # TODO: Ver esto, el tam del output deberia ser 64
        instrs[0].operands[2].size = 32

        self._solver.reset()

        # translate instructions to formulae
        if VERBOSE:
            print "[+] Instructions:"
            for instr in instrs:
                trans = self._translator.translate(instr)

                if trans is not None:
                    self._solver.add(trans)

                print "    %-20s -> %-20s" % (instr, trans)

        # add constrains
        constraints = [
            self._solver.mkBitVec(32, self._translator.get_curr_name("t0")) == 0,
            self._solver.mkBitVec(32, self._translator.get_init_name("t0")) != 0,
        ]

        if VERBOSE:
            print "[+] Constraints :"
            for i, constr in enumerate(constraints):
                self._solver.add(constr)

                print "    %2d : %s" % (i, constr)

        # check satisfiability
        is_sat = self._solver.check() == 'sat'

        if VERBOSE:
            print "[+] Satisfiability : %s" % str(is_sat)

            if is_sat:
                print "    t0 : 0x%08x" % self._solver.getvaluebyname(self._translator.get_curr_name("t0"))

            print "~" * 80

        self.assertEqual(is_sat, True)

    def test_sext_1(self):
        instr = self._parser.parse(["sext [WORD 0xffff, EMPTY, DWORD t1]"])

        self._solver.reset()

        smt_expr = self._translator.translate(instr[0])

        self._solver.add(smt_expr[0])

        # add constrains
        constraints = [
            self._solver.mkBitVec(32, self._translator.get_curr_name("t1")) != 0xffffffff,
        ]

        self._solver.add(constraints[0])

        self.assertEqual(self._solver.check(), 'unsat')

    def test_sext_2(self):
        instr = self._parser.parse(["sext [WORD 0x7fff, EMPTY, DWORD t1]"])

        self._solver.reset()

        smt_expr = self._translator.translate(instr[0])

        self._solver.add(smt_expr[0])

        # add constrains
        constraints = [
            self._solver.mkBitVec(32, self._translator.get_curr_name("t1")) != 0x00007fff,
        ]

        self._solver.add(constraints[0])

        self.assertEqual(self._solver.check(), 'unsat')

    def test_bsh_left_1(self):
        instr = self._parser.parse(["bsh [DWORD t1, DWORD 16, QWORD t2]"])

        self._solver.reset()

        smt_expr = self._translator.translate(instr[0])

        self._solver.add(smt_expr[0])

        # add constrains
        constraints = [
            self._solver.mkBitVec(32, self._translator.get_curr_name("t1")) == 0xffffffff,
            self._solver.mkBitVec(64, self._translator.get_curr_name("t2")) != 0x0000ffffffff0000,
        ]

        self._solver.add(constraints[0])
        self._solver.add(constraints[1])

        self.assertEqual(self._solver.check(), 'unsat')

    def test_bsh_left_2(self):
        instr = self._parser.parse(["bsh [DWORD t1, DWORD 16, DWORD t2]"])

        self._solver.reset()

        smt_expr = self._translator.translate(instr[0])

        self._solver.add(smt_expr[0])

        # add constrains
        constraints = [
            self._solver.mkBitVec(32, self._translator.get_curr_name("t1")) == 0xffffffff,
            self._solver.mkBitVec(32, self._translator.get_curr_name("t2")) != 0xffff0000,
        ]

        self._solver.add(constraints[0])
        self._solver.add(constraints[1])

        self.assertEqual(self._solver.check(), 'unsat')

    def test_bsh_left_3(self):
        instr = self._parser.parse(["bsh [DWORD t1, DWORD 16, WORD t2]"])

        self._solver.reset()

        smt_expr = self._translator.translate(instr[0])

        self._solver.add(smt_expr[0])

        # add constrains
        constraints = [
            self._solver.mkBitVec(32, self._translator.get_curr_name("t1")) == 0xffffffff,
            self._solver.mkBitVec(16, self._translator.get_curr_name("t2")) != 0x0000,
        ]

        self._solver.add(constraints[0])
        self._solver.add(constraints[1])

        self.assertEqual(self._solver.check(), 'unsat')

    def test_bsh_right_1(self):
        instr = self._parser.parse(["bsh [DWORD t1, DWORD -16, QWORD t2]"])

        self._solver.reset()

        smt_expr = self._translator.translate(instr[0])

        self._solver.add(smt_expr[0])

        # add constrains
        constraints = [
            self._solver.mkBitVec(32, self._translator.get_curr_name("t1")) == 0xffffffff,
            self._solver.mkBitVec(64, self._translator.get_curr_name("t2")) != 0x000000000000ffff,
        ]

        self._solver.add(constraints[0])
        self._solver.add(constraints[1])

        self.assertEqual(self._solver.check(), 'unsat')

    def test_bsh_right_2(self):
        instr = self._parser.parse(["bsh [DWORD t1, DWORD -16, DWORD t2]"])

        self._solver.reset()

        smt_expr = self._translator.translate(instr[0])

        self._solver.add(smt_expr[0])

        # add constrains
        constraints = [
            self._solver.mkBitVec(32, self._translator.get_curr_name("t1")) == 0xffffffff,
            self._solver.mkBitVec(32, self._translator.get_curr_name("t2")) != 0x0000ffff,
        ]

        self._solver.add(constraints[0])
        self._solver.add(constraints[1])

        self.assertEqual(self._solver.check(), 'unsat')

    def test_bsh_right_3(self):
        instr = self._parser.parse(["bsh [DWORD t1, DWORD -16, WORD t2]"])

        self._solver.reset()

        smt_expr = self._translator.translate(instr[0])

        self._solver.add(smt_expr[0])

        # add constrains
        constraints = [
            self._solver.mkBitVec(32, self._translator.get_curr_name("t1")) == 0xffffffff,
            self._solver.mkBitVec(16, self._translator.get_curr_name("t2")) != 0xffff,
        ]

        self._solver.add(constraints[0])
        self._solver.add(constraints[1])

        self.assertEqual(self._solver.check(), 'unsat')

    def test_div_1(self):
        instr = self._parser.parse(["div [DWORD 2, DWORD 1, DWORD t1]"])

        self._solver.reset()

        smt_expr = self._translator.translate(instr[0])

        self._solver.add(smt_expr[0])

        # add constrains
        constraints = [
            self._solver.mkBitVec(32, self._translator.get_curr_name("t1")) != 0x2,
        ]

        self._solver.add(constraints[0])

        self.assertEqual(self._solver.check(), 'unsat')

    def test_div_2(self):
        instr = self._parser.parse(["div [DWORD 0xffffffff, DWORD 0x2, DWORD t1]"])

        self._solver.reset()

        smt_expr = self._translator.translate(instr[0])

        self._solver.add(smt_expr[0])

        # add constrains
        constraints = [
            self._solver.mkBitVec(32, self._translator.get_curr_name("t1")) != 0x7fffffff,
        ]

        self._solver.add(constraints[0])

        self.assertEqual(self._solver.check(), 'unsat')

    def test_sdiv_1(self):
        instr = self._parser.parse(["sdiv [DWORD -2, DWORD -1, DWORD t1]"])

        self._solver.reset()

        smt_expr = self._translator.translate(instr[0])

        self._solver.add(smt_expr[0])

        # add constrains
        constraints = [
            self._solver.mkBitVec(32, self._translator.get_curr_name("t1")) != 0x2,
        ]

        self._solver.add(constraints[0])

        self.assertEqual(self._solver.check(), 'unsat')

    def test_sdiv_2(self):
        instr = self._parser.parse(["sdiv [DWORD -2, DWORD 1, DWORD t1]"])

        self._solver.reset()

        smt_expr = self._translator.translate(instr[0])

        self._solver.add(smt_expr[0])

        # add constrains
        constraints = [
            self._solver.mkBitVec(32, self._translator.get_curr_name("t1")) != 0xfffffffe,
        ]

        self._solver.add(constraints[0])

        self.assertEqual(self._solver.check(), 'unsat')

    def test_smod_1(self):
        instr = self._parser.parse(["smod [DWORD 5, DWORD -3, DWORD t1]"])

        self._solver.reset()

        smt_expr = self._translator.translate(instr[0])

        self._solver.add(smt_expr[0])

        # add constrains
        constraints = [
            self._solver.mkBitVec(32, self._translator.get_curr_name("t1")) != 0xffffffff,
        ]

        self._solver.add(constraints[0])

        self.assertEqual(self._solver.check(), 'unsat')

    def test_smod_2(self):
        instr = self._parser.parse(["smod [DWORD -5, DWORD 3, DWORD t1]"])

        self._solver.reset()

        smt_expr = self._translator.translate(instr[0])

        self._solver.add(smt_expr[0])

        # add constrains
        constraints = [
            self._solver.mkBitVec(32, self._translator.get_curr_name("t1")) != 0x1,
        ]

        self._solver.add(constraints[0])

        self.assertEqual(self._solver.check(), 'unsat')

def main():
    unittest.main()


if __name__ == '__main__':
    main()
