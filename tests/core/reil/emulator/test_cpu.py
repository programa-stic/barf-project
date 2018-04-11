import unittest

from barf.core.reil.emulator import ReilCpu
from barf.core.reil.emulator import ReilMemoryEx
from barf.core.reil.parser import ReilParser


class ReilCpuTests(unittest.TestCase):

    def setUp(self):
        self.__address_size = 32

    # Arithmetic Instructions
    def test_add(self):
        mem = ReilMemoryEx(self.__address_size)
        cpu = ReilCpu(mem)

        parser = ReilParser()

        reil_instr = parser.parse(["add [DWORD t0, DWORD t1, DWORD t2]"])[0]
        reil_instr.address = 0xcafecafe

        t0 = 0x12345678
        t1 = 0x1234

        cpu.registers['t0'] = t0
        cpu.registers['t1'] = t1

        cpu.execute(reil_instr)

        self.assertEquals(t0 + t1, cpu.registers['t2'])

    def test_sub(self):
        mem = ReilMemoryEx(self.__address_size)
        cpu = ReilCpu(mem)

        parser = ReilParser()

        reil_instr = parser.parse(["sub [DWORD t0, DWORD t1, DWORD t2]"])[0]
        reil_instr.address = 0xcafecafe

        t0 = 0x12345678
        t1 = 0x1234

        cpu.registers['t0'] = t0
        cpu.registers['t1'] = t1

        cpu.execute(reil_instr)

        self.assertEquals(t0 - t1, cpu.registers['t2'])

    def test_mul(self):
        mem = ReilMemoryEx(self.__address_size)
        cpu = ReilCpu(mem)

        parser = ReilParser()

        reil_instr = parser.parse(["mul [DWORD t0, DWORD t1, DWORD t2]"])[0]
        reil_instr.address = 0xcafecafe

        t0 = 0x1234
        t1 = 0x1234

        cpu.registers['t0'] = t0
        cpu.registers['t1'] = t1

        cpu.execute(reil_instr)

        self.assertEquals(t0 * t1, cpu.registers['t2'])

    def test_div(self):
        mem = ReilMemoryEx(self.__address_size)
        cpu = ReilCpu(mem)

        parser = ReilParser()

        reil_instr = parser.parse(["div [DWORD t0, DWORD t1, DWORD t2]"])[0]
        reil_instr.address = 0xcafecafe

        t0 = 0x12345678
        t1 = 0x1234

        cpu.registers['t0'] = t0
        cpu.registers['t1'] = t1

        cpu.execute(reil_instr)

        self.assertEquals(t0 / t1, cpu.registers['t2'])

    def test_mod(self):
        mem = ReilMemoryEx(self.__address_size)
        cpu = ReilCpu(mem)

        parser = ReilParser()

        reil_instr = parser.parse(["mod [DWORD t0, DWORD t1, DWORD t2]"])[0]
        reil_instr.address = 0xcafecafe

        t0 = 0x12345678
        t1 = 0x1234

        cpu.registers['t0'] = t0
        cpu.registers['t1'] = t1

        cpu.execute(reil_instr)

        self.assertEquals(t0 % t1, cpu.registers['t2'])

    def test_bsh_left(self):
        mem = ReilMemoryEx(self.__address_size)
        cpu = ReilCpu(mem)

        parser = ReilParser()

        reil_instr = parser.parse(["bsh [DWORD t0, DWORD t1, DWORD t2]"])[0]
        reil_instr.address = 0xcafecafe

        t0 = 0x12345678
        t1 = 0x8

        cpu.registers['t0'] = t0
        cpu.registers['t1'] = t1

        cpu.execute(reil_instr)

        self.assertEquals((t0 << t1) & 2**32-1, cpu.registers['t2'])

    def test_bsh_rigt(self):
        mem = ReilMemoryEx(self.__address_size)
        cpu = ReilCpu(mem)

        parser = ReilParser()

        reil_instr = parser.parse(["bsh [DWORD t0, DWORD t1, DWORD t2]"])[0]
        reil_instr.address = 0xcafecafe

        t0 = 0x12345678
        t1 = 0x8

        cpu.registers['t0'] = t0
        cpu.registers['t1'] = -t1

        cpu.execute(reil_instr)

        self.assertEquals(t0 >> t1, cpu.registers['t2'])

    # Bitwise Instructions
    def test_and(self):
        mem = ReilMemoryEx(self.__address_size)
        cpu = ReilCpu(mem)

        parser = ReilParser()

        reil_instr = parser.parse(["and [DWORD t0, DWORD t1, DWORD t2]"])[0]
        reil_instr.address = 0xcafecafe

        t0 = 0x12345678
        t1 = 0x1234

        cpu.registers['t0'] = t0
        cpu.registers['t1'] = t1

        cpu.execute(reil_instr)

        self.assertEquals(t0 & t1, cpu.registers['t2'])

    def test_or(self):
        mem = ReilMemoryEx(self.__address_size)
        cpu = ReilCpu(mem)

        parser = ReilParser()

        reil_instr = parser.parse(["or [DWORD t0, DWORD t1, DWORD t2]"])[0]
        reil_instr.address = 0xcafecafe

        t0 = 0x12345678
        t1 = 0x1234

        cpu.registers['t0'] = t0
        cpu.registers['t1'] = t1

        cpu.execute(reil_instr)

        self.assertEquals(t0 | t1, cpu.registers['t2'])

    def test_xor(self):
        mem = ReilMemoryEx(self.__address_size)
        cpu = ReilCpu(mem)

        parser = ReilParser()

        reil_instr = parser.parse(["xor [DWORD t0, DWORD t1, DWORD t2]"])[0]
        reil_instr.address = 0xcafecafe

        t0 = 0x12345678
        t1 = 0x1234

        cpu.registers['t0'] = t0
        cpu.registers['t1'] = t1

        cpu.execute(reil_instr)

        self.assertEquals(t0 ^ t1, cpu.registers['t2'])

    # Data Transfer Instructions
    def test_ldm(self):
        mem = ReilMemoryEx(self.__address_size)
        cpu = ReilCpu(mem)

        parser = ReilParser()

        reil_instr = parser.parse(["ldm [DWORD t0, EMPTY, DWORD t1]"])[0]
        reil_instr.address = 0xcafecafe

        t0 = 0x12345678
        t1 = 0x1234

        cpu.registers['t0'] = t0
        cpu.memory.write(t0, 4, t1)

        cpu.execute(reil_instr)

        self.assertEquals(t1, cpu.registers['t1'])

    def test_stm(self):
        mem = ReilMemoryEx(self.__address_size)
        cpu = ReilCpu(mem)

        parser = ReilParser()

        reil_instr = parser.parse(["stm [DWORD t0, EMPTY, DWORD t1]"])[0]
        reil_instr.address = 0xcafecafe

        t0 = 0x12345678
        t1 = 0x1234

        cpu.registers['t0'] = t0
        cpu.registers['t1'] = t1

        cpu.execute(reil_instr)

        self.assertEquals(t0, cpu.memory.read(t1, 4))

    def test_str(self):
        mem = ReilMemoryEx(self.__address_size)
        cpu = ReilCpu(mem)

        parser = ReilParser()

        reil_instr = parser.parse(["str [DWORD t0, EMPTY, DWORD t1]"])[0]
        reil_instr.address = 0xcafecafe

        t0 = 0x12345678

        cpu.registers['t0'] = t0

        cpu.execute(reil_instr)

        self.assertEquals(t0, cpu.registers['t1'])

    # Conditional Instructions
    def test_bisz(self):
        mem = ReilMemoryEx(self.__address_size)
        cpu = ReilCpu(mem)

        parser = ReilParser()

        reil_instr = parser.parse(["BISZ [DWORD t0, EMPTY, BIT t1]"])[0]
        reil_instr.address = 0xcafecafe

        t0 = 0x12345678

        cpu.registers['t0'] = t0

        cpu.execute(reil_instr)

        self.assertEquals(1 if t0 == 0 else 0, cpu.registers['t1'])

    def test_jcc(self):
        mem = ReilMemoryEx(self.__address_size)
        cpu = ReilCpu(mem)

        parser = ReilParser()

        reil_instr = parser.parse(["jcc [BIT t0, EMPTY, POINTER t1]"])[0]
        reil_instr.address = 0xcafecafe

        t0 = 0x1
        t1 = 0x1234567800

        cpu.registers['t0'] = t0
        cpu.registers['t1'] = t1

        next_ip = cpu.execute(reil_instr)

        self.assertEquals(t1, next_ip)

    # Extensions
    def test_sext(self):
        mem = ReilMemoryEx(self.__address_size)
        cpu = ReilCpu(mem)

        parser = ReilParser()

        reil_instr = parser.parse(["sext [DWORD t0, EMPTY, QWORD t1]"])[0]
        reil_instr.address = 0xcafecafe

        t0 = 0x12345678

        cpu.registers['t0'] = -t0 & 2**32-1

        cpu.execute(reil_instr)

        self.assertEquals(-t0 & 2**64-1, cpu.registers['t1'])

    def test_sdiv(self):
        mem = ReilMemoryEx(self.__address_size)
        cpu = ReilCpu(mem)

        parser = ReilParser()

        reil_instr = parser.parse(["sdiv [DWORD t0, DWORD t1, DWORD t2]"])[0]
        reil_instr.address = 0xcafecafe

        t0 = -0x12345678
        t1 = -0x1234

        cpu.registers['t0'] = t0
        cpu.registers['t1'] = t1

        cpu.execute(reil_instr)

        self.assertEquals(t0 / t1, cpu.registers['t2'])

    def test_smod(self):
        mem = ReilMemoryEx(self.__address_size)
        cpu = ReilCpu(mem)

        parser = ReilParser()

        reil_instr = parser.parse(["smod [DWORD t0, DWORD t1, DWORD t2]"])[0]
        reil_instr.address = 0xcafecafe

        t0 = -0x12345678
        t1 = -0x1234

        cpu.registers['t0'] = t0
        cpu.registers['t1'] = t1

        cpu.execute(reil_instr)

        self.assertEquals((t0 % t1) & 2**32-1, cpu.registers['t2'])
