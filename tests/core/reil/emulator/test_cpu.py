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

from barf.core.reil.emulator import ReilCpu
from barf.core.reil.emulator import ReilMemoryEx
from barf.core.reil.parser import ReilParser


class ReilCpuTests(unittest.TestCase):

    def setUp(self):
        self.__address_size = 32
        self.__parser = ReilParser()

    # Arithmetic Instructions
    def test_add(self):
        mem = ReilMemoryEx(self.__address_size)
        cpu = ReilCpu(mem)

        instr = self.__parser.parse(["add [DWORD t0, DWORD t1, DWORD t2]"])[0]
        instr.address = 0xcafecafe00

        t0 = 0x12345678
        t1 = 0x1234

        cpu.registers['t0'] = t0
        cpu.registers['t1'] = t1

        cpu.execute(instr)

        self.assertEquals(t0 + t1, cpu.registers['t2'])

    def test_sub(self):
        mem = ReilMemoryEx(self.__address_size)
        cpu = ReilCpu(mem)

        instr = self.__parser.parse(["sub [DWORD t0, DWORD t1, DWORD t2]"])[0]
        instr.address = 0xcafecafe00

        t0 = 0x12345678
        t1 = 0x1234

        cpu.registers['t0'] = t0
        cpu.registers['t1'] = t1

        cpu.execute(instr)

        self.assertEquals(t0 - t1, cpu.registers['t2'])

    def test_mul(self):
        mem = ReilMemoryEx(self.__address_size)
        cpu = ReilCpu(mem)

        instr = self.__parser.parse(["mul [DWORD t0, DWORD t1, DWORD t2]"])[0]
        instr.address = 0xcafecafe00

        t0 = 0x1234
        t1 = 0x1234

        cpu.registers['t0'] = t0
        cpu.registers['t1'] = t1

        cpu.execute(instr)

        self.assertEquals(t0 * t1, cpu.registers['t2'])

    def test_div(self):
        mem = ReilMemoryEx(self.__address_size)
        cpu = ReilCpu(mem)

        instr = self.__parser.parse(["div [DWORD t0, DWORD t1, DWORD t2]"])[0]
        instr.address = 0xcafecafe00

        t0 = 0x12345678
        t1 = 0x1234

        cpu.registers['t0'] = t0
        cpu.registers['t1'] = t1

        cpu.execute(instr)

        self.assertEquals(t0 // t1, cpu.registers['t2'])

    def test_mod(self):
        mem = ReilMemoryEx(self.__address_size)
        cpu = ReilCpu(mem)

        instr = self.__parser.parse(["mod [DWORD t0, DWORD t1, DWORD t2]"])[0]
        instr.address = 0xcafecafe00

        t0 = 0x12345678
        t1 = 0x1234

        cpu.registers['t0'] = t0
        cpu.registers['t1'] = t1

        cpu.execute(instr)

        self.assertEquals(t0 % t1, cpu.registers['t2'])

    def test_bsh_left(self):
        mem = ReilMemoryEx(self.__address_size)
        cpu = ReilCpu(mem)

        instr = self.__parser.parse(["bsh [DWORD t0, DWORD t1, DWORD t2]"])[0]
        instr.address = 0xcafecafe00

        t0 = 0x12345678
        t1 = 0x8

        cpu.registers['t0'] = t0
        cpu.registers['t1'] = t1

        cpu.execute(instr)

        self.assertEquals((t0 << t1) & 2**32-1, cpu.registers['t2'])

    def test_bsh_rigt(self):
        mem = ReilMemoryEx(self.__address_size)
        cpu = ReilCpu(mem)

        instr = self.__parser.parse(["bsh [DWORD t0, DWORD t1, DWORD t2]"])[0]
        instr.address = 0xcafecafe00

        t0 = 0x12345678
        t1 = 0x8

        cpu.registers['t0'] = t0
        cpu.registers['t1'] = -t1

        cpu.execute(instr)

        self.assertEquals(t0 >> t1, cpu.registers['t2'])

    # Bitwise Instructions
    def test_and(self):
        mem = ReilMemoryEx(self.__address_size)
        cpu = ReilCpu(mem)

        instr = self.__parser.parse(["and [DWORD t0, DWORD t1, DWORD t2]"])[0]
        instr.address = 0xcafecafe00

        t0 = 0x12345678
        t1 = 0x1234

        cpu.registers['t0'] = t0
        cpu.registers['t1'] = t1

        cpu.execute(instr)

        self.assertEquals(t0 & t1, cpu.registers['t2'])

    def test_or(self):
        mem = ReilMemoryEx(self.__address_size)
        cpu = ReilCpu(mem)

        instr = self.__parser.parse(["or [DWORD t0, DWORD t1, DWORD t2]"])[0]
        instr.address = 0xcafecafe00

        t0 = 0x12345678
        t1 = 0x1234

        cpu.registers['t0'] = t0
        cpu.registers['t1'] = t1

        cpu.execute(instr)

        self.assertEquals(t0 | t1, cpu.registers['t2'])

    def test_xor(self):
        mem = ReilMemoryEx(self.__address_size)
        cpu = ReilCpu(mem)

        instr = self.__parser.parse(["xor [DWORD t0, DWORD t1, DWORD t2]"])[0]
        instr.address = 0xcafecafe00

        t0 = 0x12345678
        t1 = 0x1234

        cpu.registers['t0'] = t0
        cpu.registers['t1'] = t1

        cpu.execute(instr)

        self.assertEquals(t0 ^ t1, cpu.registers['t2'])

    # Data Transfer Instructions
    def test_ldm(self):
        mem = ReilMemoryEx(self.__address_size)
        cpu = ReilCpu(mem)

        instr = self.__parser.parse(["ldm [DWORD t0, EMPTY, DWORD t1]"])[0]
        instr.address = 0xcafecafe00

        t0 = 0x12345678
        t1 = 0x1234

        cpu.registers['t0'] = t0
        cpu.memory.write(t0, 4, t1)

        cpu.execute(instr)

        self.assertEquals(t1, cpu.registers['t1'])

    def test_stm(self):
        mem = ReilMemoryEx(self.__address_size)
        cpu = ReilCpu(mem)

        instr = self.__parser.parse(["stm [DWORD t0, EMPTY, DWORD t1]"])[0]
        instr.address = 0xcafecafe00

        t0 = 0x12345678
        t1 = 0x1234

        cpu.registers['t0'] = t0
        cpu.registers['t1'] = t1

        cpu.execute(instr)

        self.assertEquals(t0, cpu.memory.read(t1, 4))

    def test_str(self):
        mem = ReilMemoryEx(self.__address_size)
        cpu = ReilCpu(mem)

        instr = self.__parser.parse(["str [DWORD t0, EMPTY, DWORD t1]"])[0]
        instr.address = 0xcafecafe00

        t0 = 0x12345678

        cpu.registers['t0'] = t0

        cpu.execute(instr)

        self.assertEquals(t0, cpu.registers['t1'])

    # Conditional Instructions
    def test_bisz(self):
        mem = ReilMemoryEx(self.__address_size)
        cpu = ReilCpu(mem)

        instr = self.__parser.parse(["BISZ [DWORD t0, EMPTY, BIT t1]"])[0]
        instr.address = 0xcafecafe00

        t0 = 0x12345678

        cpu.registers['t0'] = t0

        cpu.execute(instr)

        self.assertEquals(1 if t0 == 0 else 0, cpu.registers['t1'])

    def test_jcc(self):
        mem = ReilMemoryEx(self.__address_size)
        cpu = ReilCpu(mem)

        instr = self.__parser.parse(["jcc [BIT t0, EMPTY, POINTER t1]"])[0]
        instr.address = 0xcafecafe00

        t0 = 0x1
        t1 = 0x1234567800

        cpu.registers['t0'] = t0
        cpu.registers['t1'] = t1

        next_ip = cpu.execute(instr)

        self.assertEquals(t1, next_ip)

    # Extensions
    def test_sext(self):
        mem = ReilMemoryEx(self.__address_size)
        cpu = ReilCpu(mem)

        instr = self.__parser.parse(["sext [DWORD t0, EMPTY, QWORD t1]"])[0]
        instr.address = 0xcafecafe00

        t0 = 0x12345678

        cpu.registers['t0'] = -t0 & 2**32-1

        cpu.execute(instr)

        self.assertEquals(-t0 & 2**64-1, cpu.registers['t1'])

    def test_sdiv(self):
        mem = ReilMemoryEx(self.__address_size)
        cpu = ReilCpu(mem)

        instr = self.__parser.parse(["sdiv [DWORD t0, DWORD t1, DWORD t2]"])[0]
        instr.address = 0xcafecafe00

        t0 = -0x12345678
        t1 = -0x1234

        cpu.registers['t0'] = t0
        cpu.registers['t1'] = t1

        cpu.execute(instr)

        self.assertEquals(t0 // t1, cpu.registers['t2'])

    def test_smod(self):
        mem = ReilMemoryEx(self.__address_size)
        cpu = ReilCpu(mem)

        instr = self.__parser.parse(["smod [DWORD t0, DWORD t1, DWORD t2]"])[0]
        instr.address = 0xcafecafe00

        t0 = -0x12345678
        t1 = -0x1234

        cpu.registers['t0'] = t0
        cpu.registers['t1'] = t1

        cpu.execute(instr)

        self.assertEquals((t0 % t1) & 2**32-1, cpu.registers['t2'])
