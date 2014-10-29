import unittest

from barf.core.reil import ReilEmulator
from barf.core.reil import ReilMnemonic
from barf.core.reil import ReilParser
from barf.core.smt.smtlibv2 import BitVec
from barf.core.smt.smtlibv2 import Z3Solver as SmtSolver
from barf.core.smt.smttranslator import SmtTranslator
from barf.utils.utils import VariableNamer

verbose = False

class SmtTranslatorTests(unittest.TestCase):

    def setUp(self):
        self._address_size = 32
        self._parser = ReilParser()
        self._solver = SmtSolver()
        self._translator = SmtTranslator(self._solver, self._address_size)

    def test_add_reg_reg(self):
        if verbose:
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
        if verbose:
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

        if verbose:
            print "[+] Constraints :"
            for i, constr in enumerate(constraints):
                self._solver.add(constr)

                print "    %2d : %s" % (i, constr)

        # check satisfiability
        is_sat = self._solver.check() == 'sat'

        if verbose:
            print "[+] Satisfiability : %s" % str(is_sat)

            if is_sat:
                print "    eax : 0x%08x" % self._solver.getvaluebyname(self._translator.get_curr_name("eax"))
                print "    ebx : 0x%08x" % self._solver.getvaluebyname(self._translator.get_curr_name("ebx"))

            print "~" * 80

        self.assertEqual(is_sat, True)

    def test_add_reg_mem(self):
        if verbose:
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
        if verbose:
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

        if verbose:
            print "[+] Constraints :"
            for i, constr in enumerate(constraints):
                self._solver.add(constr)

                print "    %2d : %s" % (i, constr)

        # check satisfiability
        is_sat = self._solver.check() == 'sat'

        if verbose:
            print "[+] Satisfiability : %s" % str(is_sat)

            if is_sat:
                print "    eax : 0x%08x" % self._solver.getvaluebyname(self._translator.get_curr_name("eax"))
                print "    ebx : 0x%08x" % self._solver.getvaluebyname(self._translator.get_curr_name("ebx"))

            print "~" * 80

        self.assertEqual(is_sat, True)

    def test_add_mem_reg(self):
        if verbose:
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

        if verbose:
            print "constraint : %s" % constraint

        self._solver.add(constraint)

        # translate instructions to formulae
        if verbose:
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

        if verbose:
            print "[+] Constraints :"
            for i, constr in enumerate(constraints):
                self._solver.add(constr)

                print "    %2d : %s" % (i, constr)

        # check satisfiability
        is_sat = self._solver.check() == 'sat'

        if verbose:
            print "[+] Satisfiability : %s" % str(is_sat)

            if is_sat:
                print "    eax : 0x%08x" % self._solver.getvaluebyname(self._translator.get_curr_name("eax"))
                print "    ebx : 0x%08x" % self._solver.getvaluebyname(self._translator.get_curr_name("ebx"))
                print "    t0 : 0x%08x" % self._solver.getvaluebyname(self._translator.get_curr_name("t0"))
                print "    [eax] : 0x%08x" % self._solver.getvalue(mem[eax])

            print "~" * 80

        self.assertEqual(is_sat, True)

    def test_add_mem_reg_2(self):
        if verbose:
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

        if verbose:
            print "constraint : %s" % constraint

        self._solver.add(constraint)

        # translate instructions to formulae
        if verbose:
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

        if verbose:
            print "[+] Constraints :"

            for i, constr in enumerate(constraints):
                self._solver.add(constr)

                print "    %2d : %s" % (i, constr)

        # check satisfiability
        is_sat = self._solver.check() == 'sat'

        if verbose:
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
        if verbose:
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
        if verbose:
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

        if verbose:
            print "[+] Constraints :"
            for i, constr in enumerate(constraints):
                self._solver.add(constr)

                print "    %2d : %s" % (i, constr)

        # check satisfiability
        is_sat = self._solver.check() == 'sat'

        if verbose:
            print "[+] Satisfiability : %s" % str(is_sat)

            if is_sat:
                print "    t0 : 0x%08x" % self._solver.getvaluebyname(self._translator.get_curr_name("t0"))

            print "~" * 80

        self.assertEqual(is_sat, True)


def main():
    unittest.main()


if __name__ == '__main__':
    main()
