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

from barf.analysis.basicblock.basicblock import BasicBlock
from barf.arch.x86.x86parser import X86Parser
from barf.arch.x86.x86translator import X86Translator
from barf.core.reil import DualInstruction


class BinDiffTests(unittest.TestCase):

    def setUp(self):
        self._parser = X86Parser()
        self._translator = X86Translator()

    def test_equality(self):
        addr = 0x0804842f

        asm = self._parser.parse("cmp DWORD PTR [esp+0x18], 0x41424344")
        asm.address = 0x08048425
        asm.size = 8

        asm1 = [asm]

        asm = self._parser.parse("jne 0x08048445")
        asm.address = 0x0804842d
        asm.size = 2

        asm1 += [asm]

        ir1  = [self._translator.translate(asm1[0])]
        ir1 += [self._translator.translate(asm1[1])]

        asm = self._parser.parse("cmp DWORD PTR [esp+0x18], 0x41424344")
        asm.address = 0x08048425
        asm.size = 8

        asm2 = [asm]

        asm = self._parser.parse("jne 0x0804844f")
        asm.address = 0x0804842d
        asm.size = 2

        asm2 += [asm]

        ir2  = [self._translator.translate(asm2[0])]
        ir2 += [self._translator.translate(asm2[1])]

        bb1 = BasicBlock()
        bb1.instrs.append(DualInstruction(addr, asm1[0], ir1[0]))
        bb1.instrs.append(DualInstruction(addr, asm1[1], ir1[1]))

        bb2 = BasicBlock()
        bb2.instrs.append(DualInstruction(addr, asm2[0], ir2[0]))
        bb2.instrs.append(DualInstruction(addr, asm2[1], ir2[1]))

        self.assertTrue(bb1 == bb1)
        self.assertTrue(bb2 == bb2)

        # It will not assert true. Read comment on BasicBlock.__eq__
        # self.assertTrue(bb1 != bb2)


def main():
    unittest.main()


if __name__ == '__main__':
    main()
