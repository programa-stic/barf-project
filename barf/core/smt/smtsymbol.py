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

from barf.core.smt.smtlibv2 import Symbol, cast_to_bitvec, BitVec, Bool


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
