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

import unittest

from barf.arch import ARCH_X86_MODE_32
from barf.arch import ARCH_X86_MODE_64
from barf.arch.x86.x86parser import X86Parser


class X86Parser32BitsTests(unittest.TestCase):

    def setUp(self):
        self._parser = X86Parser(ARCH_X86_MODE_32)

    def test_two_oprnd_reg_reg(self):
        asm = self._parser.parse("add eax, ebx")

        self.assertEqual(str(asm), "add eax, ebx")

    def test_two_oprnd_reg_imm(self):
        asm = self._parser.parse("add eax, 0x12345678")

        self.assertEqual(str(asm), "add eax, 0x12345678")

    def test_two_oprnd_reg_mem(self):
        asm = self._parser.parse("add eax, [ebx + edx * 4 + 0x10]")

        self.assertEqual(str(asm), "add eax, [ebx+edx*4+0x10]")

    def test_two_oprnd_mem_reg(self):
        asm = self._parser.parse("add [ebx + edx * 4 + 0x10], eax")

        self.assertEqual(str(asm), "add [ebx+edx*4+0x10], eax")

    def test_one_oprnd_reg(self):
        asm = self._parser.parse("inc eax")

        self.assertEqual(str(asm), "inc eax")

    def test_one_oprnd_imm(self):
        asm = self._parser.parse("jmp 0x12345678")

        self.assertEqual(str(asm), "jmp 0x12345678")

    def test_one_oprnd_mem(self):
        asm = self._parser.parse("inc dword ptr [ebx+edx*4+0x10]")

        self.assertEqual(str(asm), "inc dword ptr [ebx+edx*4+0x10]")

    def test_zero_oprnd(self):
        asm = self._parser.parse("nop")

        self.assertEqual(str(asm), "nop")

    # Misc
    # ======================================================================== #
    def test_misc_1(self):
        asm = self._parser.parse("mov dword ptr [-0x21524111], ecx")

        self.assertEqual(str(asm), "mov dword ptr [-0x21524111], ecx")
        self.assertNotEqual(str(asm), "mov dword ptr [0xdeadbeef], ecx")

    def test_misc_2(self):
        asm = self._parser.parse("fucompi st(1)")

        self.assertEqual(str(asm), "fucompi st1")


class X86Parser64BitsTests(unittest.TestCase):

    def setUp(self):
        self._parser = X86Parser(ARCH_X86_MODE_64)

    def test_64_two_oprnd_reg_reg(self):
        asm = self._parser.parse("add rax, rbx")

        self.assertEqual(str(asm), "add rax, rbx")

    def test_64_two_oprnd_reg_reg_2(self):
        asm = self._parser.parse("add rax, r8")

        self.assertEqual(str(asm), "add rax, r8")

    def test_64_two_oprnd_reg_mem(self):
        asm = self._parser.parse("add rax, [rbx + r15 * 4 + 0x10]")

        self.assertEqual(str(asm), "add rax, [rbx+r15*4+0x10]")

    # Misc
    # ======================================================================== #
    def test_misc_offset_1(self):
        asm = self._parser.parse("add byte ptr [rax+0xffffff89], cl")

        self.assertEqual(str(asm), "add byte ptr [rax+0xffffff89], cl")


def main():
    unittest.main()


if __name__ == '__main__':
    main()
