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

"""
This modules contains a x86 disassembler based on the Capstone
disassembly framework.

"""
from capstone import *

from barf.arch import ARCH_X86_MODE_32
from barf.arch import ARCH_X86_MODE_64
from barf.arch.x86.x86base import X86ArchitectureInformation
from barf.arch.x86.x86parser import X86Parser
from barf.core.disassembler import Disassembler
from barf.core.disassembler import DisassemblerError


class X86Disassembler(Disassembler):
    """X86 Disassembler.
    """

    def __init__(self, architecture_mode=ARCH_X86_MODE_32):
        super(X86Disassembler, self).__init__()

        arch_mode_map = {
            ARCH_X86_MODE_32: CS_MODE_32,
            ARCH_X86_MODE_64: CS_MODE_64
        }

        self._arch_mode = architecture_mode
        self._arch_info = X86ArchitectureInformation(architecture_mode)

        self._parser = X86Parser(architecture_mode)
        self._disassembler = Cs(CS_ARCH_X86, arch_mode_map[architecture_mode])

    def disassemble(self, data, address, architecture_mode=ARCH_X86_MODE_32):
        """Disassemble the data into an instruction.
        """
        asm, size = self._cs_disassemble_one(data, address)

        instr = self._parser.parse(asm) if asm else None

        if instr:
            instr.address = address
            instr.size = size
            instr.bytes = data[0:size]
        else:
            raise DisassemblerError()

        return instr

    def disassemble_all(self, data, address):
        """Disassemble the data into multiple instructions.
        """
        raise NotImplementedError()

    def _cs_disassemble_one(self, data, address):
        """Disassemble the data into an instruction in string form.
        """
        asm, size = "", 0

        disasm = list(self._disassembler.disasm_lite(data, address))

        if len(disasm) > 0:
            address, size, mnemonic, op_str = disasm[0]

            asm = str(mnemonic + " " + op_str).strip()

        # Quick fix for Capstone 'bug'.
        if asm in ["repne", "rep", "lock", "data16"]:
            asm, size = "", 0

        return asm, size
