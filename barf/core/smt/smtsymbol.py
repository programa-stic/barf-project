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


def cast_to_bool(value):
    if type(value) in (int, long, bool):
        value = Bool(str(bool(value)).lower())

    assert type(value) == Bool

    return value


def cast_to_bitvec(value, size):
    if type(value) in (int, long):
        value = cast_int(value, size)
    elif type(value) is str:
        assert len(value) == 1

        value = cast_char(value, size)
    elif type(value) is BitVec:
        assert value.size == size
    else:
        raise Exception("Invalid value type.")

    assert type(value) == BitVec

    return value


def cast_int(value, size):
    if size == 1:
        return BitVec(size, '#' + bin(value & 1)[1:])
    else:
        return BitVec(size, '#x%0*x' % (size / 4, truncate_int(value, size)))


def cast_char(value, size):
    return cast_int(ord(value), size)


def truncate_int(value, size):
    return value & ((1 << size) - 1)


class Symbol(object):

    def __init__(self, value, *children):
        self._value = str(value) if len(children) == 0 else "({:s} {:s})".format(value, " ".join([str(c) for c in children]))

    @property
    def value(self):
        return self._value

    def __str__(self):
        return self._value


class Bool(Symbol):

    def __init__(self, value, *children):
        super(Bool, self).__init__(value, *children)

    @property
    def declaration(self):
        return "(declare-fun {} () Bool)".format(self.value)

    # Comparison operators
    def __eq__(self, other):
        return Bool("=", self, cast_to_bool(other))

    def __ne__(self, other):
        return Bool("not", self == other)

    # Logical operators
    def __and__(self, other):
        return Bool("and", self, cast_to_bool(other))

    def __or__(self, other):
        return Bool("or", self, cast_to_bool(other))

    def __xor__(self, other):
        return Bool("xor", self, cast_to_bool(other))

    def __invert__(self):
        return Bool("not", self)

    # Reverse logical operators
    def __rand__(self, other):
        return Bool("and", cast_to_bool(other), self)

    def __ror__(self, other):
        return Bool("or", cast_to_bool(other), self)

    def __rxor__(self, other):
        return Bool("xor", cast_to_bool(other), self)


class BitVec(Symbol):

    def __init__(self, size, value, *children):
        super(BitVec, self).__init__(value, *children)

        self.size = size

    @property
    def declaration(self):
        return "(declare-fun {} () (_ BitVec {}))".format(self.value, self.size)

    # Arithmetic operators
    def __add__(self, other):
        return BitVec(self.size, "bvadd", self, cast_to_bitvec(other, self.size))

    def __sub__(self, other):
        return BitVec(self.size, "bvsub", self, cast_to_bitvec(other, self.size))

    def __mul__(self, other):
        return BitVec(self.size, "bvmul", self, cast_to_bitvec(other, self.size))

    def __div__(self, other):
        return BitVec(self.size, "bvsdiv", self, cast_to_bitvec(other, self.size))

    def __mod__(self, other):
        return BitVec(self.size, "bvsmod", self, cast_to_bitvec(other, self.size))

    def __neg__(self):
        return BitVec(self.size, "bvneg", self)

    # Reverse arithmetic operators
    def __radd__(self, other):
        return BitVec(self.size, "bvadd", cast_to_bitvec(other, self.size), self)

    def __rsub__(self, other):
        return BitVec(self.size, "bvsub", cast_to_bitvec(other, self.size), self)

    def __rmul__(self, other):
        return BitVec(self.size, "bvmul", cast_to_bitvec(other, self.size), self)

    def __rdiv__(self, other):
        return BitVec(self.size, "bvsdiv", cast_to_bitvec(other, self.size), self)

    def __rmod__(self, other):
        return BitVec(self.size, "bvsmod", cast_to_bitvec(other, self.size), self)

    # Bitwise operators
    def __and__(self, other):
        return BitVec(self.size, "bvand", self, cast_to_bitvec(other, self.size))

    def __xor__(self, other):
        return BitVec(self.size, "bvxor", self, cast_to_bitvec(other, self.size))

    def __or__(self, other):
        return BitVec(self.size, "bvor", self, cast_to_bitvec(other, self.size))

    def __lshift__(self, other):
        return BitVec(self.size, "bvshl", self, cast_to_bitvec(other, self.size))

    def __rshift__(self, other):
        return BitVec(self.size, "bvlshr", self, cast_to_bitvec(other, self.size))

    def __invert__(self):
        return BitVec(self.size, "bvnot", self)

    # Reverse bitwise operators
    def __rand__(self, other):
        return BitVec(self.size, "bvand", cast_to_bitvec(other, self.size), self)

    def __rxor__(self, other):
        return BitVec(self.size, "bvxor", cast_to_bitvec(other, self.size), self)

    def __ror__(self, other):
        return BitVec(self.size, "bvor", cast_to_bitvec(other, self.size), self)

    def __rlshift__(self, other):
        return BitVec(self.size, "bvshl", cast_to_bitvec(other, self.size), self)

    def __rrshift__(self, other):
        return BitVec(self.size, "bvlshr", cast_to_bitvec(other, self.size), self)

    # Comparison operators (signed)
    def __lt__(self, other):
        return Bool("bvslt", self, cast_to_bitvec(other, self.size))

    def __le__(self, other):
        return Bool("bvsle", self, cast_to_bitvec(other, self.size))

    def __eq__(self, other):
        return Bool("=", self, cast_to_bitvec(other, self.size))

    def __ne__(self, other):
        return Bool("not", self == other)

    def __gt__(self, other):
        return Bool("bvsgt", self, cast_to_bitvec(other, self.size))

    def __ge__(self, other):
        return Bool("bvsge", self, cast_to_bitvec(other, self.size))

    # Comparison operators (unsigned)
    def ult(self, other):
        return Bool("bvult", self, cast_to_bitvec(other, self.size))

    def ule(self, other):
        return Bool("bvule", self, cast_to_bitvec(other, self.size))

    def ugt(self, other):
        return Bool("bvugt", self, cast_to_bitvec(other, self.size))

    def uge(self, other):
        return Bool("bvuge", self, cast_to_bitvec(other, self.size))

    # Arithmetic operators (unsigned)
    def udiv(self, other):
        return BitVec(self.size, "bvudiv", self, cast_to_bitvec(other, self.size))

    def umod(self, other):
        return BitVec(self.size, "bvumod", self, cast_to_bitvec(other, self.size))


class Array(Symbol):

    def __init__(self, key_size, value_size, value, *children):
        super(Array, self).__init__(value, *children)

        self.key_size = key_size
        self.value_size = value_size


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
        return BitVec(self.value_size, "select", self.array, cast_to_bitvec(key, self.key_size))

    def store(self, key, value):
        return Array(self.key_size, self.value_size, "(store {} {} {})".format(self.array,
                                                                               cast_to_bitvec(key, self.key_size),
                                                                               cast_to_bitvec(value, self.value_size)))

    # Index operators
    def __getitem__(self, key):
        return self.select(key)

    def __setitem__(self, key, value):
        self.array = self.store(key, value)

    # Comparison operators
    def __eq__(self, other):
        assert isinstance(other.array, Array)
        assert other.array.key_size == self.array.key_size and other.array.value_size == self.array.value_size

        return Bool("=", self.array, other.array)

    def __neq__(self, other):
        assert isinstance(other.array, Array)
        assert other.array.key_size == self.array.key_size and other.array.value_size == self.array.value_size

        return Bool("not", self.__eq__(other))
