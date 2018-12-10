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

from barf.core.reil.parser import ReilParser
from barf.core.smt.smtsymbol import BitVec
from barf.core.smt.smtsymbol import Bool
from barf.core.smt.smtsolver import Z3Solver as SmtSolver
# from barf.core.smt.smtsolver import CVC4Solver as SmtSolver


class SmtSolverBitVecTests(unittest.TestCase):

    def setUp(self):
        self._address_size = 32
        self._parser = ReilParser()
        self._solver = SmtSolver()

    # Arithmetic operations.
    def test_add(self):
        x = BitVec(32, "x")
        y = BitVec(32, "y")
        z = BitVec(32, "z")

        self._solver.declare_fun("x", x)
        self._solver.declare_fun("y", y)
        self._solver.declare_fun("z", z)

        self._solver.add(x + y == z)

        # Add constraints to avoid trivial solutions.
        self._solver.add(x > 1)
        self._solver.add(y > 1)
        self._solver.add(x != y)

        self.assertEqual(self._solver.check(), "sat")

        x_val = self._solver.get_value(x)
        y_val = self._solver.get_value(y)
        z_val = self._solver.get_value(z)

        self.assertTrue(x_val + y_val == z_val)

    def test_sub(self):
        x = BitVec(32, "x")
        y = BitVec(32, "y")
        z = BitVec(32, "z")

        self._solver.declare_fun("x", x)
        self._solver.declare_fun("y", y)
        self._solver.declare_fun("z", z)

        self._solver.add(x - y == z)

        self._solver.add(x > 1)
        self._solver.add(y > 1)
        self._solver.add(x != y)

        self.assertEqual(self._solver.check(), "sat")

        # Add constraints to avoid trivial solutions.
        x_val = self._solver.get_value(x)
        y_val = self._solver.get_value(y)
        z_val = self._solver.get_value(z)

        self.assertTrue((x_val - y_val) & 0xffffffff == z_val)

    def test_mul(self):
        x = BitVec(32, "x")
        y = BitVec(32, "y")
        z = BitVec(32, "z")

        self._solver.declare_fun("x", x)
        self._solver.declare_fun("y", y)
        self._solver.declare_fun("z", z)

        self._solver.add(x * y == z)

        # Add constraints to avoid trivial solutions.
        self._solver.add(x > 1)
        self._solver.add(y > 1)
        self._solver.add(x != y)

        self.assertEqual(self._solver.check(), "sat")

        x_val = self._solver.get_value(x)
        y_val = self._solver.get_value(y)
        z_val = self._solver.get_value(z)

        self.assertTrue((x_val * y_val) & 0xffffffff == z_val)

    def test_div(self):
        x = BitVec(32, "x")
        y = BitVec(32, "y")
        z = BitVec(32, "z")

        self._solver.declare_fun("x", x)
        self._solver.declare_fun("y", y)
        self._solver.declare_fun("z", z)

        self._solver.add(x // y == z)

        # Add constraints to avoid trivial solutions.
        self._solver.add(x > 1)
        self._solver.add(y > 1)
        self._solver.add(x != y)

        self.assertEqual(self._solver.check(), "sat")

        x_val = self._solver.get_value(x)
        y_val = self._solver.get_value(y)
        z_val = self._solver.get_value(z)

        self.assertTrue(x_val // y_val == z_val)

    def test_mod(self):
        x = BitVec(32, "x")
        y = BitVec(32, "y")
        z = BitVec(32, "z")

        self._solver.declare_fun("x", x)
        self._solver.declare_fun("y", y)
        self._solver.declare_fun("z", z)

        self._solver.add(x % y == z)

        # Add constraints to avoid trivial solutions.
        self._solver.add(x > 1)
        self._solver.add(y > 1)
        self._solver.add(x != y)

        self.assertEqual(self._solver.check(), "sat")

        x_val = self._solver.get_value(x)
        y_val = self._solver.get_value(y)
        z_val = self._solver.get_value(z)

        self.assertTrue(x_val % y_val == z_val)

    def test_neg(self):
        x = BitVec(32, "x")
        z = BitVec(32, "z")

        self._solver.declare_fun("x", x)
        self._solver.declare_fun("z", z)

        self._solver.add(-x == z)

        # Add constraints to avoid trivial solutions.
        self._solver.add(x > 1)

        self.assertEqual(self._solver.check(), "sat")

        x_val = self._solver.get_value(x)
        z_val = self._solver.get_value(z)

        self.assertTrue(-x_val & 0xffffffff == z_val)

    # Bitwise operations.
    def test_and(self):
        x = BitVec(32, "x")
        y = BitVec(32, "y")
        z = BitVec(32, "z")

        self._solver.declare_fun("x", x)
        self._solver.declare_fun("y", y)
        self._solver.declare_fun("z", z)

        self._solver.add(x & y == z)

        # Add constraints to avoid trivial solutions.
        self._solver.add(x > 1)
        self._solver.add(y > 1)
        self._solver.add(x != y)

        self.assertEqual(self._solver.check(), "sat")

        x_val = self._solver.get_value(x)
        y_val = self._solver.get_value(y)
        z_val = self._solver.get_value(z)

        self.assertTrue(x_val & y_val == z_val)

    def test_xor(self):
        x = BitVec(32, "x")
        y = BitVec(32, "y")
        z = BitVec(32, "z")

        self._solver.declare_fun("x", x)
        self._solver.declare_fun("y", y)
        self._solver.declare_fun("z", z)

        self._solver.add(x ^ y == z)

        # Add constraints to avoid trivial solutions.
        self._solver.add(x > 1)
        self._solver.add(y > 1)
        self._solver.add(x != y)

        self.assertEqual(self._solver.check(), "sat")

        x_val = self._solver.get_value(x)
        y_val = self._solver.get_value(y)
        z_val = self._solver.get_value(z)

        self.assertTrue(x_val ^ y_val == z_val)

    def test_or(self):
        x = BitVec(32, "x")
        y = BitVec(32, "y")
        z = BitVec(32, "z")

        self._solver.declare_fun("x", x)
        self._solver.declare_fun("y", y)
        self._solver.declare_fun("z", z)

        self._solver.add(x | y == z)

        # Add constraints to avoid trivial solutions.
        self._solver.add(x > 1)
        self._solver.add(y > 1)
        self._solver.add(x != y)

        self.assertEqual(self._solver.check(), "sat")

        x_val = self._solver.get_value(x)
        y_val = self._solver.get_value(y)
        z_val = self._solver.get_value(z)

        self.assertTrue(x_val | y_val == z_val)

    def test_lshift(self):
        x = BitVec(32, "x")
        y = BitVec(32, "y")
        z = BitVec(32, "z")

        self._solver.declare_fun("x", x)
        self._solver.declare_fun("y", y)
        self._solver.declare_fun("z", z)

        self._solver.add(x << y == z)

        # Add constraints to avoid trivial solutions.
        self._solver.add(x > 1)
        self._solver.add(y > 1)
        self._solver.add(x != y)

        self.assertEqual(self._solver.check(), "sat")

        x_val = self._solver.get_value(x)
        y_val = self._solver.get_value(y)
        z_val = self._solver.get_value(z)

        self.assertTrue((x_val << y_val) & 0xffffffff == z_val)

    def test_rshift(self):
        x = BitVec(32, "x")
        y = BitVec(32, "y")
        z = BitVec(32, "z")

        self._solver.declare_fun("x", x)
        self._solver.declare_fun("y", y)
        self._solver.declare_fun("z", z)

        self._solver.add(x >> y == z)

        # Add constraints to avoid trivial solutions.
        self._solver.add(x > 1)
        self._solver.add(y > 1)
        self._solver.add(x != y)

        self.assertEqual(self._solver.check(), "sat")

        x_val = self._solver.get_value(x)
        y_val = self._solver.get_value(y)
        z_val = self._solver.get_value(z)

        self.assertTrue(x_val >> y_val == z_val)

    def test_invert(self):
        x = BitVec(32, "x")
        y = BitVec(32, "y")
        z = BitVec(32, "z")

        self._solver.declare_fun("x", x)
        self._solver.declare_fun("y", y)
        self._solver.declare_fun("z", z)

        self._solver.add(~x == z)

        # Add constraints to avoid trivial solutions.
        self._solver.add(x > 1)

        self.assertEqual(self._solver.check(), "sat")

        x_val = self._solver.get_value(x)
        y_val = self._solver.get_value(y)
        z_val = self._solver.get_value(z)

        self.assertTrue(~x_val & 0xffffffff == z_val)

    # Comparison operators (signed)
    def test_lt(self):
        x = BitVec(32, "x")
        y = BitVec(32, "y")

        self._solver.declare_fun("x", x)
        self._solver.declare_fun("y", y)

        self._solver.add(x < y)

        # Add constraints to avoid trivial solutions.
        self._solver.add(x > 1)
        self._solver.add(y > 1)

        self.assertEqual(self._solver.check(), "sat")

        x_val = self._solver.get_value(x)
        y_val = self._solver.get_value(y)

        self.assertTrue(x_val < y_val)

    def test_le(self):
        x = BitVec(32, "x")
        y = BitVec(32, "y")

        self._solver.declare_fun("x", x)
        self._solver.declare_fun("y", y)

        self._solver.add(x <= y)

        # Add constraints to avoid trivial solutions.
        self._solver.add(x > 1)
        self._solver.add(y > 1)

        self.assertEqual(self._solver.check(), "sat")

        x_val = self._solver.get_value(x)
        y_val = self._solver.get_value(y)

        self.assertTrue(x_val <= y_val)

    def test_eq(self):
        x = BitVec(32, "x")
        y = BitVec(32, "y")

        self._solver.declare_fun("x", x)
        self._solver.declare_fun("y", y)

        self._solver.add(x == y)

        # Add constraints to avoid trivial solutions.
        self._solver.add(x > 1)
        self._solver.add(y > 1)

        self.assertEqual(self._solver.check(), "sat")

        x_val = self._solver.get_value(x)
        y_val = self._solver.get_value(y)

        self.assertTrue(x_val == y_val)

    def test_neq(self):
        x = BitVec(32, "x")
        y = BitVec(32, "y")

        self._solver.declare_fun("x", x)
        self._solver.declare_fun("y", y)

        self._solver.add(x != y)

        # Add constraints to avoid trivial solutions.
        self._solver.add(x > 1)
        self._solver.add(y > 1)

        self.assertEqual(self._solver.check(), "sat")

        x_val = self._solver.get_value(x)
        y_val = self._solver.get_value(y)

        self.assertTrue(x_val != y_val)

    def test_gt(self):
        x = BitVec(32, "x")
        y = BitVec(32, "y")

        self._solver.declare_fun("x", x)
        self._solver.declare_fun("y", y)

        self._solver.add(x > y)

        # Add constraints to avoid trivial solutions.
        self._solver.add(x > 1)
        self._solver.add(y > 1)

        self.assertEqual(self._solver.check(), "sat")

        x_val = self._solver.get_value(x)
        y_val = self._solver.get_value(y)

        self.assertTrue(x_val > y_val)

    def test_ge(self):
        x = BitVec(32, "x")
        y = BitVec(32, "y")

        self._solver.declare_fun("x", x)
        self._solver.declare_fun("y", y)

        self._solver.add(x >= y)

        # Add constraints to avoid trivial solutions.
        self._solver.add(x > 1)
        self._solver.add(y > 1)

        self.assertEqual(self._solver.check(), "sat")

        x_val = self._solver.get_value(x)
        y_val = self._solver.get_value(y)

        self.assertTrue(x_val >= y_val)

    # Comparison operators (unsigned)
    def test_ult(self):
        # TODO Implement.
        pass

    def test_ule(self):
        # TODO Implement.
        pass

    def test_ugt(self):
        # TODO Implement.
        pass

    def test_uge(self):
        # TODO Implement.
        pass

    # Arithmetic operators (unsigned)
    def test_udiv(self):
        # TODO Implement.
        pass

    def test_urem(self):
        # TODO Implement.
        pass


def main():
    unittest.main()


if __name__ == '__main__':
    main()
