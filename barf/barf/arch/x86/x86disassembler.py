"""
This modules contains a x86 disassembler based on the Capstone
disassembly framework.

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

        self._parser = X86Parser(architecture_mode)
        self._disassembler = Cs(CS_ARCH_X86, arch_mode_map[architecture_mode])

    def disassemble(self, data, address):
        """Disassemble the data into an instruction.
        """
        asm, size = self._cs_disassemble_one(data, address)

        instr = self._parser.parse(asm) if asm else None

        if instr:
            instr.address = address
            instr.size = size
            instr.bytes = data[0:size]

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