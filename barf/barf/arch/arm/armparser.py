"""
ARM Instruction Parser.
"""

import copy
import logging
import os

from pyparsing import alphanums
from pyparsing import alphas
from pyparsing import Combine
from pyparsing import Forward
from pyparsing import Literal
from pyparsing import nums
from pyparsing import Optional
from pyparsing import Or
from pyparsing import Suppress
from pyparsing import Word
from pyparsing import ZeroOrMore

from barf.arch import ARCH_ARM_MODE_32
from barf.arch.arm.armbase import ArmArchitectureInformation
from barf.arch.arm.armbase import ArmImmediateOperand
from barf.arch.arm.armbase import ArmInstruction
from barf.arch.arm.armbase import ArmMemoryOperand
from barf.arch.arm.armbase import ArmRegisterOperand
from barf.arch.arm.armbase import ArmShifterOperand

logger = logging.getLogger(__name__)

arch_info = None

# Parsing functions
# ============================================================================ #
def parse_operand(string, location, tokens):
    """Parse an ARM instruction operand.
    """

    if "immediate" in tokens:
        oprnd = ArmImmediateOperand("".join(tokens["immediate"]))

    if "register" in tokens:
        name = tokens["register"]
        size = arch_info.registers_size[tokens["register"]]

        oprnd = ArmRegisterOperand(name, size)

    if "memory" in tokens:
        segment = tokens.get("segment", None)
        base = tokens.get("base", None)
        index = tokens.get("index", None)
        scale = int(tokens.get("scale", "0x1"), 16)
        displacement = int("".join(tokens.get("displacement", "0x0")), 16)

        oprnd = ArmMemoryOperand(segment, base, index, scale, displacement)

    if "shifter_operand" in tokens:
        reg_base = tokens.get("reg_base", None)
        shift_type = tokens.get("shift_type", None)
        
        if tokens.get("shift_immediate"):
            oprnd = ArmShifterOperand(ArmRegisterOperand(reg_base), shift_type, ArmImmediateOperand(tokens.get("shift_immediate").get("value")))
        elif tokens.get("shift_register"):
            oprnd = ArmShifterOperand(ArmRegisterOperand(reg_base), shift_type, ArmRegisterOperand(tokens.get("shift_register")))
        else:
            oprnd = ArmShifterOperand(ArmRegisterOperand(reg_base), shift_type, None)
        
    return oprnd

def parse_instruction(string, location, tokens):
    """Parse an ARM instruction.
    """
    prefix = tokens.get("prefix", None)
    mnemonic = tokens.get("mnemonic")
    operands = [op for op in tokens.get("operands", [])]

    instr = ArmInstruction(
        prefix,
        mnemonic,
        operands,
        arch_info.architecture_mode
    )

    return instr

# Grammar Rules
# ============================================================================ #
mul      = Literal("*")
plus     = Literal("+")
minus    = Literal("-")
comma    = Literal(",")
lbracket = Literal("[")
rbracket = Literal("]")
hashsign = Literal("#")
exclamation    = Literal("!")

hex_num = Combine(Literal("0x") + Word("0123456789abcdef"))
dec_num = Word("0123456789")

# Operand Parsing
# ============================================================================ #
immediate = Optional(Suppress(hashsign)) + Optional(Or([plus, minus])) +  Or([hex_num, dec_num])("value")

register = Or([
    Combine(Literal("r") + Word(nums)),
    Literal("sp"),
    Literal("lr"),
    Literal("pc"),
    Literal("cpsr"),
])

shift_type = Or([
    Literal("lsl"),
    Literal("lsr"),
    Literal("asr"),
    Literal("ror"),
    Literal("rrx"),
])

shift_amount = Or([immediate("shift_immediate"), register("shift_register")])

shifter_operand = register("reg_base")  + Suppress(comma) + shift_type("shift_type") + Optional(shift_amount("shift_amount")) # opcional porque RRX no tiene shift_amount




operand = (
#     Optional(modifier)("modifier") +
#     Or([immediate("immediate"), register("register"), memory("memory")])
    Or([immediate("immediate"), register("register"), shifter_operand("shifter_operand")])
).setParseAction(parse_operand)

# Instruction Parsing
# ============================================================================ #
mnemonic = Word(alphanums)

instruction = (
#     Optional(prefix)("prefix") +
    mnemonic("mnemonic") +
#     Optional(ZeroOrMore(operand + Suppress(comma)) + operand)("operands")
#     (operand + Suppress(comma) + operand + Suppress(comma) + operand)("operands")
    Optional(ZeroOrMore(operand + Suppress(comma)) + operand)("operands")
).setParseAction(parse_instruction)

class ArmParser(object):
    """ARM Instruction Parser.
    """

    def __init__(self, architecture_mode=ARCH_ARM_MODE_32):
        global arch_info, modifier_size

        arch_info = ArmArchitectureInformation(architecture_mode)

        self._cache = {}

    def parse(self, instr):
        """Parse an ARM instruction.
        """
        # Commented to get the exception trace of a parser error.
#         try:
        instr_lower = instr.lower()

        if not instr_lower in self._cache:
            instr_asm = instruction.parseString(instr_lower)[0]

            self._cache[instr_lower] = instr_asm

        instr_asm = copy.deepcopy(self._cache[instr_lower])

            # self._check_instruction(instr_asm)
#         except Exception as e:
#             instr_asm = None
# 
#             error_msg = "Failed to parse instruction: %s"
# 
#             logger.error(error_msg, instr, exc_info=True)
#             
#             print("Failed to parse instruction: " + instr)
#             print(e)

        return instr_asm

    def _check_instruction(self, instr):
        # Check operands size.
        assert all([oprnd.size in [8, 16, 32, 64, 80, 128]
                        for oprnd in instr.operands]), \
                "Invalid operand size: %s" % instr

        # Check memory operand parameters.
        assert all([oprnd.base or oprnd.index or oprnd.displacement
                        for oprnd in instr.operands
                            if isinstance(oprnd, ArmMemoryOperand)]), \
                "Invalid memory operand parameters: %s" % instr
