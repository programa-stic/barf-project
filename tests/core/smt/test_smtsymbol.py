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

from barf.core.smt.smtsymbol import Bool
from barf.core.smt.smtsymbol import BitVec
from barf.core.smt.smtsymbol import BitVecArray


class BoolTests(unittest.TestCase):

    def test_declaration(self):
        x = Bool("x")

        self.assertEqual(x.declaration, "(declare-fun x () Bool)")

    def test_and(self):
        x = Bool("x")
        y = Bool("y")
        z = x & y
        v = x & True
        w = True & x

        self.assertEqual(z.value, "(and x y)")
        self.assertEqual(v.value, "(and x true)")
        self.assertEqual(w.value, "(and true x)")

    def test_or(self):
        x = Bool("x")
        y = Bool("y")
        z = x | y
        v = x | True
        w = True | x

        self.assertEqual(z.value, "(or x y)")
        self.assertEqual(v.value, "(or x true)")
        self.assertEqual(w.value, "(or true x)")

    def test_xor(self):
        x = Bool("x")
        y = Bool("y")
        z = x ^ y
        v = x ^ True
        w = True ^ x

        self.assertEqual(z.value, "(xor x y)")
        self.assertEqual(v.value, "(xor x true)")
        self.assertEqual(w.value, "(xor true x)")

    def test_invert(self):
        x = Bool("x")
        z = ~x

        self.assertEqual(z.value, "(not x)")

    def test_equal(self):
        x = Bool("x")
        y = Bool("y")
        z = x == y
        v = x == True
        w = True == x

        self.assertEqual(z.value, "(= x y)")
        self.assertEqual(v.value, "(= x true)")
        self.assertEqual(w.value, "(= x true)")

    def test_not_equal(self):
        x = Bool("x")
        y = Bool("y")
        z = x != y
        v = x != True
        w = True != x

        self.assertEqual(z.value, "(not (= x y))")
        self.assertEqual(v.value, "(not (= x true))")
        self.assertEqual(w.value, "(not (= x true))")


class BitVecTests(unittest.TestCase):

    def test_declaration(self):
        x = BitVec(32, "x")

        self.assertEqual(x.declaration, "(declare-fun x () (_ BitVec 32))")

    # Arithmetic operators
    def test_add(self):
        x = BitVec(32, "x")
        y = BitVec(32, "y")
        z = x + y
        v = x + 1
        w = 1 + x

        self.assertEqual(z.value, "(bvadd x y)")
        self.assertEqual(v.value, "(bvadd x #x00000001)")
        self.assertEqual(w.value, "(bvadd #x00000001 x)")

    def test_sub(self):
        x = BitVec(32, "x")
        y = BitVec(32, "y")
        z = x - y
        v = x - 1
        w = 1 - x

        self.assertEqual(z.value, "(bvsub x y)")
        self.assertEqual(v.value, "(bvsub x #x00000001)")
        self.assertEqual(w.value, "(bvsub #x00000001 x)")

    def test_mul(self):
        x = BitVec(32, "x")
        y = BitVec(32, "y")
        z = x * y
        v = x * 1
        w = 1 * x

        self.assertEqual(z.value, "(bvmul x y)")
        self.assertEqual(v.value, "(bvmul x #x00000001)")
        self.assertEqual(w.value, "(bvmul #x00000001 x)")

    def test_div(self):
        x = BitVec(32, "x")
        y = BitVec(32, "y")
        z = x // y
        v = x // 1
        w = 1 // x

        self.assertEqual(z.value, "(bvsdiv x y)")
        self.assertEqual(v.value, "(bvsdiv x #x00000001)")
        self.assertEqual(w.value, "(bvsdiv #x00000001 x)")

    def test_mod(self):
        x = BitVec(32, "x")
        y = BitVec(32, "y")
        z = x % y
        v = x % 1
        w = 1 % x

        self.assertEqual(z.value, "(bvsmod x y)")
        self.assertEqual(v.value, "(bvsmod x #x00000001)")
        self.assertEqual(w.value, "(bvsmod #x00000001 x)")

    def test_neg(self):
        x = BitVec(32, "x")
        z = -x

        self.assertEqual(z.value, "(bvneg x)")

    # Bitwise operators
    def test_and(self):
        x = BitVec(32, "x")
        y = BitVec(32, "y")
        z = x & y
        v = x & 1
        w = 1 & x

        self.assertEqual(z.value, "(bvand x y)")
        self.assertEqual(v.value, "(bvand x #x00000001)")
        self.assertEqual(w.value, "(bvand #x00000001 x)")

    def test_xor(self):
        x = BitVec(32, "x")
        y = BitVec(32, "y")
        z = x ^ y
        v = x ^ 1
        w = 1 ^ x

        self.assertEqual(z.value, "(bvxor x y)")
        self.assertEqual(v.value, "(bvxor x #x00000001)")
        self.assertEqual(w.value, "(bvxor #x00000001 x)")

    def test_or(self):
        x = BitVec(32, "x")
        y = BitVec(32, "y")
        z = x | y
        v = x | 1
        w = 1 | x

        self.assertEqual(z.value, "(bvor x y)")
        self.assertEqual(v.value, "(bvor x #x00000001)")
        self.assertEqual(w.value, "(bvor #x00000001 x)")

    def test_lshift(self):
        x = BitVec(32, "x")
        y = BitVec(32, "y")
        z = x << y
        v = x << 1
        w = 1 << x

        self.assertEqual(z.value, "(bvshl x y)")
        self.assertEqual(v.value, "(bvshl x #x00000001)")
        self.assertEqual(w.value, "(bvshl #x00000001 x)")

    def test_rshift(self):
        x = BitVec(32, "x")
        y = BitVec(32, "y")
        z = x >> y
        v = x >> 1
        w = 1 >> x

        self.assertEqual(z.value, "(bvlshr x y)")
        self.assertEqual(v.value, "(bvlshr x #x00000001)")
        self.assertEqual(w.value, "(bvlshr #x00000001 x)")

    def test_invert(self):
        x = BitVec(32, "x")
        z = ~x

        self.assertEqual(z.value, "(bvnot x)")

    # Comparison operators
    def test_less_than(self):
        x = BitVec(32, "x")
        y = BitVec(32, "y")
        z = x < y
        v = x < 1
        w = 1 < x

        self.assertEqual(z.value, "(bvslt x y)")
        self.assertEqual(v.value, "(bvslt x #x00000001)")
        self.assertEqual(w.value, "(bvsgt x #x00000001)")

    def test_less_than_equal(self):
        x = BitVec(32, "x")
        y = BitVec(32, "y")
        z = x <= y
        v = x <= 1
        w = 1 <= x

        self.assertEqual(z.value, "(bvsle x y)")
        self.assertEqual(v.value, "(bvsle x #x00000001)")
        self.assertEqual(w.value, "(bvsge x #x00000001)")

    def test_equal(self):
        x = BitVec(32, "x")
        y = BitVec(32, "y")
        z = x == y
        v = x == 1
        w = 1 == x

        self.assertEqual(z.value, "(= x y)")
        self.assertEqual(v.value, "(= x #x00000001)")
        self.assertEqual(w.value, "(= x #x00000001)")

    def test_not_equal(self):
        x = BitVec(32, "x")
        y = BitVec(32, "y")
        z = x != y
        v = x != 1
        w = 1 != x

        self.assertEqual(z.value, "(not (= x y))")
        self.assertEqual(v.value, "(not (= x #x00000001))")
        self.assertEqual(w.value, "(not (= x #x00000001))")

    def test_greater_than(self):
        x = BitVec(32, "x")
        y = BitVec(32, "y")
        z = x > y
        v = x > 1
        w = 1 > x

        self.assertEqual(z.value, "(bvsgt x y)")
        self.assertEqual(v.value, "(bvsgt x #x00000001)")
        self.assertEqual(w.value, "(bvslt x #x00000001)")

    def test_greater_than_equal(self):
        x = BitVec(32, "x")
        y = BitVec(32, "y")
        z = x >= y
        v = x >= 1
        w = 1 >= x

        self.assertEqual(z.value, "(bvsge x y)")
        self.assertEqual(v.value, "(bvsge x #x00000001)")
        self.assertEqual(w.value, "(bvsle x #x00000001)")

    def test_less_than_unsigned(self):
        x = BitVec(32, "x")
        y = BitVec(32, "y")
        z = x.ult(y)
        v = x.ult(1)

        self.assertEqual(z.value, "(bvult x y)")
        self.assertEqual(v.value, "(bvult x #x00000001)")

    def test_less_than_equal_unsigned(self):
        x = BitVec(32, "x")
        y = BitVec(32, "y")
        z = x.ule(y)
        v = x.ule(1)

        self.assertEqual(z.value, "(bvule x y)")
        self.assertEqual(v.value, "(bvule x #x00000001)")

    def test_greater_than_unsigned(self):
        x = BitVec(32, "x")
        y = BitVec(32, "y")
        z = x.ugt(y)
        v = x.ugt(1)

        self.assertEqual(z.value, "(bvugt x y)")
        self.assertEqual(v.value, "(bvugt x #x00000001)")

    def test_greater_than_equal_unsigned(self):
        x = BitVec(32, "x")
        y = BitVec(32, "y")
        z = x.uge(y)
        v = x.uge(1)

        self.assertEqual(z.value, "(bvuge x y)")
        self.assertEqual(v.value, "(bvuge x #x00000001)")

    def test_udiv(self):
        x = BitVec(32, "x")
        y = BitVec(32, "y")
        z = x.udiv(y)
        v = x.udiv(1)

        self.assertEqual(z.value, "(bvudiv x y)")
        self.assertEqual(v.value, "(bvudiv x #x00000001)")

    def test_umod(self):
        x = BitVec(32, "x")
        y = BitVec(32, "y")
        z = x.umod(y)
        v = x.umod(1)

        self.assertEqual(z.value, "(bvurem x y)")
        self.assertEqual(v.value, "(bvurem x #x00000001)")


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

        self.assertEqual(b.value, "(store a k v)")
        self.assertEqual(c.value, "(store a k #x01)")
        self.assertEqual(d.value, "(store a #x00000001 v)")
        self.assertEqual(e.value, "(store a #x00000001 #x01)")

    def test_select(self):
        a = BitVecArray(32, 8, "a")
        k = BitVec(32, "k")
        b = a.select(k)
        c = a.select(1)

        self.assertEqual(b.value, "(select a k)")
        self.assertEqual(c.value, "(select a #x00000001)")


def main():
    unittest.main()


if __name__ == '__main__':
    main()
