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

from barf.core.reil.emulator import ReilMemory
from barf.core.reil.emulator import ReilMemoryEx


class ReilMemoryTests(unittest.TestCase):

    def test_write_read_byte_1(self):
        address_size = 32
        memory = ReilMemory(address_size)

        addr = 0x00001000
        write_val = 0xdeadbeef

        memory.write(addr, 32 // 8, write_val)
        read_val = memory.read(addr, 32 // 8)

        self.assertEqual(write_val, read_val)

    def test_write_read_byte_2(self):
        address_size = 32
        memory = ReilMemory(address_size)

        addr = 0x00001000
        write_val = 0xdeadbeef

        memory.write(addr, 32 // 8, write_val)
        read_val = memory.read(addr, 32 // 8)

        self.assertEqual(write_val, read_val)

        addr = 0x00001001
        write_val = 0x1234

        memory.write(addr, 16 // 8, write_val)
        read_val = memory.read(addr, 16 // 8)

        self.assertEqual(write_val, read_val)

    def test_write_read_byte_3(self):
        address_size = 32
        memory = ReilMemory(address_size)

        addr = 0x00001000
        write_val = 0xdeadbeefcafecafe

        memory.write(addr, 64 // 8, write_val)
        read_val = memory.read(addr, 64 // 8)

        self.assertEqual(write_val, read_val)

    def test_write_read_byte_4(self):
        address_size = 32
        memory = ReilMemoryEx(address_size)

        addr0 = 0x00001000
        write_val = 0xdeadbeef

        memory.write(addr0, 32 // 8, write_val)
        read_val = memory.read(addr0, 32 // 8)

        self.assertEqual(write_val, read_val)

        addr1 = 0x00004000
        write_val = 0xdeadbeef

        memory.write(addr1, 32 // 8, write_val)
        read_val = memory.read(addr1, 32 // 8)

        self.assertEqual(write_val, read_val)

        addrs = memory.read_inverse(0xdeadbeef, 32 // 8)

        self.assertEqual(addr0, addrs[0])
        self.assertEqual(addr1, addrs[1])


def main():
    unittest.main()


if __name__ == '__main__':
    main()
