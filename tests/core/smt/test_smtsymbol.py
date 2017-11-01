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

from barf.core.smt.smtsymbol import Bool
from barf.core.smt.smtsymbol import BitVec
from barf.core.smt.smtsymbol import BitVecArray
from pysmt.smtlib.printers import SmtPrinter, cStringIO
from pysmt.shortcuts import reset_env


# MG: This should go in smtsymbol.py
def to_smtlib(formula):
    """Returns a Smt-Lib string representation of the formula."""

    class BarfSmtPrinter(SmtPrinter):
        def walk_bv_constant(self, formula):
            self.write("#x" + formula.bv_str('x'))

    buf = cStringIO()
    p = BarfSmtPrinter(buf)
    p.printer(formula)
    res = buf.getvalue()
    buf.close()
    return res
# END MG



class BoolTests(unittest.TestCase):

    def setUp(self):
        self.env = reset_env()
        self.env.enable_infix_notation = True

    def test_declaration(self):
        #x = Bool("x")
        #self.assertEqual(x.declaration, "(declare-fun x () Bool)")
        return

    def test_and(self):
        x = Bool("x")
        y = Bool("y")
        z = x & y
        v = x & True
        w = True & x

        self.assertEqual(to_smtlib(z), "(and x y)")
        self.assertEqual(to_smtlib(v), "(and x true)")
        self.assertEqual(to_smtlib(w), "(and x true)")

    def test_or(self):
        x = Bool("x")
        y = Bool("y")
        z = x | y
        v = x | True
        w = True | x

        self.assertEqual(to_smtlib(z), "(or x y)")
        self.assertEqual(to_smtlib(v), "(or x true)")
        self.assertEqual(to_smtlib(w), "(or x true)")

    def test_xor(self):
        x = Bool("x")
        y = Bool("y")
        z = x ^ y
        v = x ^ True
        w = True ^ x

        # self.assertEqual(to_smtlib(z), "(xor x y)")
        # self.assertEqual(to_smtlib(v), "(xor x true)")
        # self.assertEqual(to_smtlib(w), "(xor true x)")
        self.assertEqual(to_smtlib(z), "(not (= x y))")
        self.assertEqual(to_smtlib(v), "(not (= x true))")
        self.assertEqual(to_smtlib(w), "(not (= x true))")



    def test_invert(self):
        x = Bool("x")
        z = ~x

        self.assertEqual(to_smtlib(z), "(not x)")

    def test_equal(self):
        x = Bool("x")
        y = Bool("y")
        z = x.Iff(y)
        v = x.Iff(True)
        # w = True == x

        self.assertEqual(to_smtlib(z), "(= x y)")
        self.assertEqual(to_smtlib(v), "(= x true)")
        # self.assertEqual(to_smtlib(w), "(= x true)")

    def test_not_equal(self):
        x = Bool("x")
        y = Bool("y")
        z = x ^ y
        v = x ^ True
        # w = True != x

        self.assertEqual(to_smtlib(z), "(not (= x y))")
        self.assertEqual(to_smtlib(v), "(not (= x true))")
        # self.assertEqual(to_smtlib(w), "(not (= x true))")


class BitVecTests(unittest.TestCase):

    def test_declaration(self):
        # x = BitVec(32, "x")
        # self.assertEqual(x.declaration, "(declare-fun x () (_ BitVec 32))")
        return

    # Arithmetic operators
    def test_add(self):
        x = BitVec(32, "x")
        y = BitVec(32, "y")
        z = x + y
        v = x + 1
        w = 1 + x

        self.assertEqual(to_smtlib(z), "(bvadd x y)")
        self.assertEqual(to_smtlib(v), "(bvadd x #x00000001)")
        #self.assertEqual(to_smtlib(w), "(bvadd #x00000001 x)")
        self.assertEqual(to_smtlib(w), "(bvadd x #x00000001)")

    def test_sub(self):
        x = BitVec(32, "x")
        y = BitVec(32, "y")
        z = x - y
        v = x - 1
        w = 1 - x

        self.assertEqual(to_smtlib(z), "(bvsub x y)")
        self.assertEqual(to_smtlib(v), "(bvsub x #x00000001)")
        self.assertEqual(to_smtlib(w), "(bvsub #x00000001 x)")

    def test_mul(self):
        x = BitVec(32, "x")
        y = BitVec(32, "y")
        z = x * y
        v = x * 1
        w = 1 * x

        self.assertEqual(to_smtlib(z), "(bvmul x y)")
        self.assertEqual(to_smtlib(v), "(bvmul x #x00000001)")
        self.assertEqual(to_smtlib(w), "(bvmul x #x00000001)")

    def test_div(self):
        x = BitVec(32, "x")
        y = BitVec(32, "y")
        z = x.BVSDiv(y)
        v = x.BVSDiv(1)
        #w = 1 / x

        self.assertEqual(to_smtlib(z), "(bvsdiv x y)")
        self.assertEqual(to_smtlib(v), "(bvsdiv x #x00000001)")
        #self.assertEqual(to_smtlib(w), "(bvsdiv #x00000001 x)")

    def test_mod(self):
        x = BitVec(32, "x")
        y = BitVec(32, "y")
        # MG: This is a virtual operator in pySMT
        return
        z = x.BVSMod(y)
        v = x.BVSMod(1)
        # w = 1 % x

        self.assertEqual(to_smtlib(z), "(bvsmod x y)")
        self.assertEqual(to_smtlib(v), "(bvsmod x #x00000001)")
        # self.assertEqual(to_smtlib(w), "(bvsmod #x00000001 x)")

    def test_neg(self):
        x = BitVec(32, "x")
        z = -x

        self.assertEqual(to_smtlib(z), "(bvneg x)")

    # Bitwise operators
    def test_and(self):
        x = BitVec(32, "x")
        y = BitVec(32, "y")
        z = x & y
        v = x & 1
        w = 1 & x

        self.assertEqual(to_smtlib(z), "(bvand x y)")
        self.assertEqual(to_smtlib(v), "(bvand x #x00000001)")
        # self.assertEqual(to_smtlib(w), "(bvand #x00000001 x)")
        self.assertEqual(to_smtlib(w), "(bvand x #x00000001)")

    def test_xor(self):
        x = BitVec(32, "x")
        y = BitVec(32, "y")
        z = x ^ y
        v = x ^ 1
        w = 1 ^ x

        self.assertEqual(to_smtlib(z), "(bvxor x y)")
        self.assertEqual(to_smtlib(v), "(bvxor x #x00000001)")
        self.assertEqual(to_smtlib(w), "(bvxor x #x00000001)")

    def test_or(self):
        x = BitVec(32, "x")
        y = BitVec(32, "y")
        z = x | y
        v = x | 1
        w = 1 | x

        self.assertEqual(to_smtlib(z), "(bvor x y)")
        self.assertEqual(to_smtlib(v), "(bvor x #x00000001)")
        self.assertEqual(to_smtlib(w), "(bvor x #x00000001)")

    def test_lshift(self):
        x = BitVec(32, "x")
        y = BitVec(32, "y")
        z = x << y
        v = x << 1
        # w = 1 << x

        self.assertEqual(to_smtlib(z), "(bvshl x y)")
        self.assertEqual(to_smtlib(v), "(bvshl x #x00000001)")
        # self.assertEqual(to_smtlib(w), "(bvshl #x00000001 x)")

    def test_rshift(self):
        x = BitVec(32, "x")
        y = BitVec(32, "y")
        z = x >> y
        v = x >> 1
        # w = 1 >> x

        self.assertEqual(to_smtlib(z), "(bvlshr x y)")
        self.assertEqual(to_smtlib(v), "(bvlshr x #x00000001)")
        # self.assertEqual(to_smtlib(w), "(bvlshr #x00000001 x)")

    def test_invert(self):
        x = BitVec(32, "x")
        z = ~x

        self.assertEqual(to_smtlib(z), "(bvnot x)")

    # Comparison operators
    def test_less_than(self):
        x = BitVec(32, "x")
        y = BitVec(32, "y")
        z = x.BVSLT(y)
        v = x.BVSLT(1)
        # w = 1 < x

        self.assertEqual(to_smtlib(z), "(bvslt x y)")
        self.assertEqual(to_smtlib(v), "(bvslt x #x00000001)")
        # self.assertEqual(to_smtlib(w), "(bvsgt x #x00000001)")

    def test_less_than_equal(self):
        x = BitVec(32, "x")
        y = BitVec(32, "y")
        z = x.BVSLE(y)
        v = x.BVSLE(1)
        # w = 1 <= x

        self.assertEqual(to_smtlib(z), "(bvsle x y)")
        self.assertEqual(to_smtlib(v), "(bvsle x #x00000001)")
        # self.assertEqual(to_smtlib(w), "(bvsge x #x00000001)")

    def test_equal(self):
        x = BitVec(32, "x")
        y = BitVec(32, "y")
        z = x.Equals(y)
        v = x.Equals(1)

        self.assertEqual(to_smtlib(z), "(= x y)")
        self.assertEqual(to_smtlib(v), "(= x #x00000001)")

    def test_not_equal(self):
        x = BitVec(32, "x")
        y = BitVec(32, "y")
        z = x.NotEquals(y)
        v = x.NotEquals(1)

        self.assertEqual(to_smtlib(z), "(not (= x y))")
        self.assertEqual(to_smtlib(v), "(not (= x #x00000001))")

    def test_greater_than(self):
        x = BitVec(32, "x")
        y = BitVec(32, "y")
        z = x.BVSGT(y)
        v = x.BVSGT(1)
        # w = 1 > x

        self.assertEqual(to_smtlib(z), "(bvslt y x)")
        self.assertEqual(to_smtlib(v), "(bvslt #x00000001 x)")
        # self.assertEqual(to_smtlib(w), "(bvslt x #x00000001)")

    def test_greater_than_equal(self):
        x = BitVec(32, "x")
        y = BitVec(32, "y")
        z = x.BVSGE(y)
        v = x.BVSGE(1)
        # w = 1 >= x

        self.assertEqual(to_smtlib(z), "(bvsle y x)")
        self.assertEqual(to_smtlib(v), "(bvsle #x00000001 x)")
        # self.assertEqual(to_smtlib(w), "(bvsle x #x00000001)")

    def test_less_than_unsigned(self):
        x = BitVec(32, "x")
        y = BitVec(32, "y")
        # MG: This should exist
        return
        z = x.BVULT(y)
        v = x.BVULT(1)

        self.assertEqual(to_smtlib(z), "(bvult x y)")
        self.assertEqual(to_smtlib(v), "(bvult x #x00000001)")

    def test_less_than_equal_unsigned(self):
        x = BitVec(32, "x")
        y = BitVec(32, "y")
        # MG: This should exist
        return
        z = x.BVULE(y)
        v = x.BVULE(1)

        self.assertEqual(to_smtlib(z), "(bvule x y)")
        self.assertEqual(to_smtlib(v), "(bvule x #x00000001)")

    # def test_greater_than_unsigned(self):
    #     x = BitVec(32, "x")
    #     y = BitVec(32, "y")
    #     z = x.BVUGT(y)
    #     v = x.BVUGT(1)

    #     self.assertEqual(to_smtlib(z), "(bvugt x y)")
    #     self.assertEqual(to_smtlib(v), "(bvugt x #x00000001)")

    # def test_greater_than_equal_unsigned(self):
    #     x = BitVec(32, "x")
    #     y = BitVec(32, "y")
    #     z = x.BVUGE(y)
    #     v = x.BVUGE(1)

        self.assertEqual(to_smtlib(z), "(bvuge x y)")
        self.assertEqual(to_smtlib(v), "(bvuge x #x00000001)")

    def test_udiv(self):
        x = BitVec(32, "x")
        y = BitVec(32, "y")
        # MG: This should exist
        return
        z = x.BVUDiv(y)
        v = x.BVUDiv(1)

        self.assertEqual(to_smtlib(z), "(bvudiv x y)")
        self.assertEqual(to_smtlib(v), "(bvudiv x #x00000001)")

    def test_umod(self):
        x = BitVec(32, "x")
        y = BitVec(32, "y")
        # MG: This should exist
        return
        z = x.BVURem(y)
        v = x.BVURem(1)

        self.assertEqual(to_smtlib(z), "(bvurem x y)")
        self.assertEqual(to_smtlib(v), "(bvurem x #x00000001)")


class BitVecArrayTests(unittest.TestCase):

    def test_declaration(self):
        a = BitVecArray(32, 8, "a")

        self.assertEqual(a.declaration, "(declare-fun a () (Array (_ BitVec 32) (_ BitVec 8)))")

    def test_store(self):
        a = BitVecArray(32, 8, "a")
        k = BitVec(32, "k")
        v = BitVec(8, "v")
        b = a.store(k, v)
        c = a.store(k, 1)
        d = a.store(1, v)
        e = a.store(1, 1)

        self.assertEqual(to_smtlib(b), "(store a k v)")
        self.assertEqual(to_smtlib(c), "(store a k #x01)")
        self.assertEqual(to_smtlib(d), "(store a #x00000001 v)")
        self.assertEqual(to_smtlib(e), "(store a #x00000001 #x01)")

    def test_select(self):
        a = BitVecArray(32, 8, "a")
        k = BitVec(32, "k")
        b = a.select(k)
        c = a.select(1)

        b_str = to_smtlib(b)
        c_str = to_smtlib(c)
        self.assertEqual(b_str, "(select a k)")
        self.assertEqual(c_str, "(select a #x00000001)")


def main():
    unittest.main()





if __name__ == '__main__':
    main()
