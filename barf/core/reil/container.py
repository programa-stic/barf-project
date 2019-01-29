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
from __future__ import print_function

from barf.core.reil.helpers import split_address
from barf.core.reil.helpers import to_asm_address


class ReilSequenceInvalidAddressError(Exception):
    pass


class ReilSequence(object):

    """Reil instruction sequence.
    """

    def __init__(self, assembly=None):
        self.__assembly = assembly
        self.__sequence = []
        self.__next_seq_address = None

    @property
    def assembly(self):
        return self.__assembly

    def append(self, instruction):
        self.__sequence.append(instruction)

    def fetch(self, address):
        base_addr, index = split_address(address)

        if base_addr != to_asm_address(self.address):
            raise ReilSequenceInvalidAddressError()

        return self.get(index)

    def get(self, index):
        return self.__sequence[index]

    def get_next_address(self, address):
        base_addr, index = split_address(address)

        if base_addr != to_asm_address(self.address):
            raise ReilSequenceInvalidAddressError()

        addr = address

        if index < len(self.__sequence) - 1:
            addr += 1
        else:
            raise ReilSequenceInvalidAddressError()

        return addr

    def dump(self):
        for instr in self.__sequence:
            base_addr, index = split_address(instr.address)

            print("{:08x}:{:02x}\t{}".format(base_addr, index, instr))

    @property
    def address(self):
        return self.__sequence[0].address if self.__sequence else None

    @property
    def next_sequence_address(self):
        return self.__next_seq_address

    @next_sequence_address.setter
    def next_sequence_address(self, address):
        self.__next_seq_address = address

    def __len__(self):
        return len(self.__sequence)

    def __iter__(self):
        for instr in self.__sequence:
            yield instr


class ReilContainerInvalidAddressError(Exception):
    pass


class ReilContainer(object):

    """Reil instruction container.
    """

    def __init__(self):
        self.__container = {}

    def add(self, sequence):
        base_addr, _ = split_address(sequence.address)

        if base_addr in self.__container.keys():
            raise Exception("Invalid sequence")

        self.__container[base_addr] = sequence

    def fetch(self, address):
        base_addr, index = split_address(address)

        if base_addr not in self.__container:
            raise ReilContainerInvalidAddressError()

        return self.__container[base_addr].get(index)

    def fetch_sequence(self, address):
        base_addr, index = split_address(address)

        if base_addr not in self.__container:
            raise ReilContainerInvalidAddressError()

        return self.__container[base_addr]

    def get_next_address(self, address):
        base_addr, index = split_address(address)

        if base_addr not in self.__container:
            raise Exception("Invalid address.")

        addr = address

        if index < len(self.__container[base_addr]) - 1:
            addr += 1
        else:
            addr = self.__container[base_addr].next_sequence_address

        return addr

    def dump(self):
        for base_addr in sorted(self.__container.keys()):
            self.__container[base_addr].dump()

            print("-" * 80)

    def __iter__(self):
        for addr in sorted(self.__container.keys()):
            for instr in self.__container[addr]:
                yield instr
