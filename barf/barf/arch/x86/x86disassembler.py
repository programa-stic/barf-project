"""
This modules contains a x86 disassembler base on the XED Intel library.

"""
from capstone import *

from barf.arch import ARCH_X86_MODE_32
from barf.arch import ARCH_X86_MODE_64
from barf.arch.x86.x86parser import X86Parser
from barf.core.disassembler import Disassembler

class X86Disassembler(Disassembler):
    """X86 Disassembler.
    """

    def __init__(self, architecture_mode=ARCH_X86_MODE_32):
        super(X86Disassembler, self).__init__()

        arch_mode_map = {
            ARCH_X86_MODE_32 : CS_MODE_32,
            ARCH_X86_MODE_64 : CS_MODE_64
        }

        self.x86_parser = X86Parser(architecture_mode)
        self.md = Cs(CS_ARCH_X86, arch_mode_map[architecture_mode])

    def disassemble(self, data, address):
        """Disassemble the data into an instruction.
        """
        disasm = list(self.md.disasm_lite(data, address))

        if len(disasm) > 0:
            address, size, mnemonic, op_str = disasm[0]
        else:
            return None, 0

        bytes = data[0:size]
        asm = str((mnemonic + " " + op_str).strip())
        instr = self.x86_parser.parse(asm, address, size, bytes)

        if not instr:
            return None, 0

        return instr, size

    def disassemble_all(self, data, address):
        """Disassemble the data into multiple instructions.
        """
        raise NotImplementedError()
