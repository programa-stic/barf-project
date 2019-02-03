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

import random


REIL_MEMORY_ENDIANNESS_LE = 0x0     # Little Endian
REIL_MEMORY_ENDIANNESS_BE = 0x1     # Big Endian


class ReilMemory(object):

    """A REIL memory model (byte addressable).
    """

    def __init__(self, address_size):
        # TODO: Set endianness through a parameter.
        # TODO: Check that all addresses have size address_size.
        # TODO: Use endianness parameter.

        # Memory's address size.
        self.__address_size = address_size

        # Memory's endianness.
        self.__endianness = REIL_MEMORY_ENDIANNESS_LE

        # Dictionary that implements the memory itself.
        self._memory = {}

    @property
    def address_size(self):
        return self.__address_size

    # Read methods
    # ======================================================================== #
    def read(self, address, size):
        """Read arbitrary size content from memory.
        """
        value = 0x0

        for i in range(0, size):
            value |= self._read_byte(address + i) << (i * 8)

        return value

    def _read_byte(self, address):
        """Read a byte from memory.
        """
        # Initialize memory location with a random value.
        if address not in self._memory:
            self._memory[address] = random.randint(0x00, 0xff)

        return self._memory[address]

    # Write methods
    # ======================================================================== #
    def write(self, address, size, value):
        """Write arbitrary size content to memory.
        """
        for i in range(0, size):
            self.__write_byte(address + i, (value >> (i * 8)) & 0xff)

    def __write_byte(self, address, value):
        """Write byte in memory.
        """
        self._memory[address] = value & 0xff

    # Misc methods
    # ======================================================================== #
    def reset(self):
        # Dictionary that implements the memory itself.
        self._memory = {}

    # Magic methods
    # ======================================================================== #
    def __str__(self):
        lines = []

        for addr in sorted(self._memory.keys()):
            lines += ["0x%08x : 0x%08x" % (addr, self._memory[addr])]

        return "\n".join(lines)


class ReilMemoryEx(ReilMemory):

    """Reil memory extended class"""

    def __init__(self, address_size):
        super(ReilMemoryEx, self).__init__(address_size)

        # Previous state of memory.
        self.__memory_prev = {}

        # Write operations counter.
        self.__write_count = 0

    # Read methods
    # ======================================================================== #
    def read_inverse(self, value, size):
        """Return a list of memory addresses that contain the specified
        value.

        """
        addr_candidates = [addr for addr, val in self._memory.items() if val == (value & 0xff)]
        addr_matches = []

        for addr in addr_candidates:
            match = True

            for i in range(0, size):
                byte_curr = (value >> (i * 8)) & 0xff
                try:
                    match = self._memory[addr + i] == byte_curr
                except KeyError:
                    match = False

                if not match:
                    break

            if match:
                addr_matches += [addr]

        return addr_matches

    def try_read(self, address, size):
        """Try to read memory content at specified address.

        If any location was not written before, it returns a tuple
        (False, None). Otherwise, it returns (True, memory content).

        """
        value = 0x0

        for i in range(0, size):
            addr = address + i

            if addr in self._memory:
                value |= self._read_byte(addr) << (i * 8)
            else:
                return False, None

        return True, value

    def try_read_prev(self, address, size):
        """Try to read previous memory content at specified address.

        If any location was not written before, it returns a tuple
        (False, None). Otherwise, it returns (True, memory content).

        """
        value = 0x0

        for i in range(0, size):
            addr = address + i

            if addr in self.__memory_prev:
                _, val_byte = self.__try_read_byte_prev(addr)
                value |= val_byte << (i * 8)
            else:
                return False, None

        return True, value

    def __try_read_byte_prev(self, address):
        """Read previous value for memory location.

        Return a tuple (True, Byte) in case of successful read,
        (False, None) otherwise.

        """
        # Initialize memory location with a random value
        if address not in self.__memory_prev:
            return False, None

        return True, self.__memory_prev[address]

    # Write methods
    # ======================================================================== #
    def write(self, address, size, value):
        """Write arbitrary size content to memory.
        """
        for i in range(0, size):
            self.__write_byte(address + i, (value >> (i * 8)) & 0xff)

        self.__write_count += 1

    def __write_byte(self, address, value):
        """Write byte in memory.
        """
        # Save previous address content.
        if address in self._memory:
            self.__memory_prev[address] = self._memory[address]

        self._memory[address] = value & 0xff

    # Misc methods
    # ======================================================================== #
    def reset(self):
        super(ReilMemoryEx, self).reset()

        # Previous state of memory.
        self.__memory_prev = {}

        # Write operations counter.
        self.__write_count = 0

    def get_addresses(self):
        """Get accessed addresses.
        """
        return list(self._memory.keys())

    def get_write_count(self):
        """Get number of write operations performed on the memory.
        """
        return self.__write_count
