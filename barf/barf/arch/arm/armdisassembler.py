"""
This modules contains a ARM disassembler based on the Capstone
disassembly framework.

"""
from capstone import *

from barf.arch import ARCH_ARM_MODE_32
from barf.arch.arm.armparser import ArmParser
from barf.core.disassembler import Disassembler

class ArmDisassembler(Disassembler):
    """ARM Disassembler.
    """

    def __init__(self, architecture_mode=ARCH_ARM_MODE_32):
        super(ArmDisassembler, self).__init__()

        arch_mode_map = {
            ARCH_ARM_MODE_32 : CS_MODE_ARM,
        }

        self._parser = ArmParser(architecture_mode)
        self._disassembler = Cs(CS_ARCH_ARM, arch_mode_map[architecture_mode])

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

        return asm, size
