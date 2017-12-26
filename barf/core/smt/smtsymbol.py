# Copyright (c) 2017, Fundacion Dr. Manuel Sadosky
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

from pysmt.shortcuts import Bool, BV, Symbol, Ite, Select
from pysmt.shortcuts import BVSExt, BVZExt, BVExtract, BVConcat
from pysmt.typing import BVType, ArrayType
from pysmt.smtlib.printers import SmtPrinter


class BarfSmtPrinter(SmtPrinter):
    def walk_bv_constant(self, formula):
        # Barf relies on hex printing of BV Const
        self.write("#x" + formula.bv_str(fmt='x'))


def to_smtlib(formula):
    """Returns a Smt-Lib string representation of the formula."""
    # MG: Six is used for compatibility btw python 2 and 3
    from six.moves import cStringIO
    buf = cStringIO()
    BarfSmtPrinter(buf).printer(formula)
    res = buf.getvalue()
    buf.close()
    return res


def _cast_to_bool(value):
    if type(value) is bool:
        value = Bool(str(value).lower())
    assert type(value) == Bool
    return value


def _cast_to_bitvec(value, size):
    if type(value) in (int, long):
        value = Constant(size, value)
    assert value.bv_width() == size
    return value


def Bool(value):
    return Symbol(value)


def BitVec(size, value):
    return Symbol(value, BVType(size))


def Constant(size, value):
    return BV(value, size)


def Array(key_size, value_size, value):
    return Symbol(value, ArrayType(BVType(key_size), BVType(value_size)))


def zero_extend(s, size):
    assert type(size) is int
    assert size - s.bv_width() >= 0, (size, s.bv_width())
    if size == s.bv_width():
        return s
    return BVZExt(s, size - s.bv_width())


def sign_extend(s, size):
    assert type(size) is int
    assert size - s.bv_width() >= 0
    if size == s.bv_width():
        return s
    return BVSExt(s, size - s.bv_width())


def extract(s, offset, size):
    if offset == 0 and size == s.bv_width():
        return s
    return BVExtract(s, offset, offset + size - 1)


def ite(size, cond, true, false):
    return Ite(cond, true, false)


def concat(size, *args):
    if len(args) == 1:
        return args[0]
    return BVConcat(*args)


class BitVecArray(object):

    def __init__(self, key_size, value_size, name, *children):
        self.array = Array(key_size, value_size, name, *children)
        self.name = name
        self.key_size = key_size
        self.value_size = value_size

    @property
    def declaration(self):
        return "(declare-fun {} () (Array (_ BitVec {}) (_ BitVec {})))".format(self.name, self.key_size,
                                                                                self.value_size)

    def select(self, key):
        return Select(self.array, _cast_to_bitvec(key, self.key_size))

    def store(self, key, value):
        return self.array.Store(_cast_to_bitvec(key, self.key_size),
                                _cast_to_bitvec(value, self.value_size))

    def Equals(self, other):
        return self.array.Equals(other.array)

    # Index operators
    def __getitem__(self, key):
        return self.select(key)

    def __setitem__(self, key, value):
        self.array = self.store(key, value)
