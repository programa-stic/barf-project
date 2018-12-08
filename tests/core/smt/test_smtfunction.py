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

from barf.core.smt.smtsymbol import BitVec
from barf.core.smt.smtsymbol import Bool

from barf.core.smt.smtfunction import concat
from barf.core.smt.smtfunction import extract
from barf.core.smt.smtfunction import ite
from barf.core.smt.smtfunction import sign_extend
from barf.core.smt.smtfunction import zero_extend


class SmtFunctionTests(unittest.TestCase):

    def test_zero_extend(self):
        x = BitVec(32, "x")
        y = zero_extend(x, 64)

        self.assertEqual(y.value, "((_ zero_extend 32) x)")

    def test_sign_extend(self):
        x = BitVec(32, "x")
        y = sign_extend(x, 64)

        self.assertEqual(y.value, "((_ sign_extend 32) x)")

    def test_extract(self):
        x = BitVec(32, "x")
        x0 = extract(x, 0, 8)
        x1 = extract(x, 8, 8)
        x2 = extract(x, 16, 8)
        x3 = extract(x, 24, 8)

        self.assertEqual(x0.value, "((_ extract 7 0) x)")
        self.assertEqual(x1.value, "((_ extract 15 8) x)")
        self.assertEqual(x2.value, "((_ extract 23 16) x)")
        self.assertEqual(x3.value, "((_ extract 31 24) x)")

    def test_ite(self):
        b = Bool("b")
        x = BitVec(32, "x")
        y = BitVec(32, "y")
        z = BitVec(32, "z")
        v = ite(32, x == 0, y, z)
        w = ite(32, b, y, z)

        self.assertEqual(v.value, "(ite (= x #x00000000) y z)")
        self.assertEqual(w.value, "(ite b y z)")

    def test_concat(self):
        x = BitVec(32, "x")
        y = BitVec(32, "y")
        z = concat(32, x, y)
        v = concat(32, x)

        self.assertEqual(z.value, "(concat x y)")
        self.assertEqual(v.value, "x")


def main():
    unittest.main()


if __name__ == '__main__':
    main()
