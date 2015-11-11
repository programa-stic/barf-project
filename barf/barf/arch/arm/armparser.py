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
ARM Instruction Parser.
"""

import copy
import logging

from pyparsing import alphanums
from pyparsing import Combine
from pyparsing import Literal
from pyparsing import nums
from pyparsing import Optional
from pyparsing import Or
from pyparsing import Suppress
from pyparsing import Word
from pyparsing import ZeroOrMore
from pyparsing import Group
from pyparsing import LineEnd

from barf.arch import ARCH_ARM_MODE_THUMB
from barf.arch.arm.armbase import ArmArchitectureInformation
from barf.arch.arm.armbase import ArmRegisterListOperand
from barf.arch.arm.armbase import ArmImmediateOperand
from barf.arch.arm.armbase import ArmInstruction
from barf.arch.arm.armbase import ArmMemoryOperand
from barf.arch.arm.armbase import ArmRegisterOperand
from barf.arch.arm.armbase import ArmShiftedRegisterOperand
from barf.arch.arm.armbase import ARM_MEMORY_INDEX_OFFSET
from barf.arch.arm.armbase import ARM_MEMORY_INDEX_POST
from barf.arch.arm.armbase import ARM_MEMORY_INDEX_PRE
from barf.arch.arm.armbase import cc_mapper
from barf.arch.arm.armbase import ldm_stm_am_mapper

logger = logging.getLogger(__name__)

arch_info = None

# Parsing functions
# ============================================================================ #
def process_shifted_register(tokens):

    base = process_register(tokens["base"])
    sh_type = tokens["type"]
    amount = tokens.get("amount", None)

    if amount:
        if "imm" in amount:
            amount = ArmImmediateOperand("".join(amount["imm"]), arch_info.operand_size)
        elif "reg" in amount:
            amount = process_register(amount["reg"])
        else:
            raise Exception("Unknown amount type.")

    return ArmShiftedRegisterOperand(base, sh_type, amount, base.size)

def process_register(tokens):
    name = tokens["name"]
    if name in arch_info.registers_size:
        size = arch_info.registers_size[name]
    else:
        size = arch_info.architecture_size
    oprnd = ArmRegisterOperand(name, size)

    return oprnd

def parse_operand(string, location, tokens):
    """Parse an ARM instruction operand.
    """

    if "immediate_operand" in tokens:
        size = arch_info.operand_size
        oprnd = ArmImmediateOperand("".join(tokens["immediate_operand"]), size)

    if "register_operand" in tokens:
        oprnd =  process_register(tokens["register_operand"])

        # TODO: Figure out where to really store this flag, instead of in the register class
        if "wb" in tokens["register_operand"]:
            oprnd.wb = True


    if "memory_operand" in tokens:
        mem_oprnd = tokens["memory_operand"]

        if "offset" in mem_oprnd:
            index_type = ARM_MEMORY_INDEX_OFFSET
            mem_oprnd = mem_oprnd["offset"]
        elif "pre" in mem_oprnd:
            index_type = ARM_MEMORY_INDEX_PRE
            mem_oprnd = mem_oprnd["pre"]
        elif "post" in mem_oprnd:
            index_type = ARM_MEMORY_INDEX_POST
            mem_oprnd = mem_oprnd["post"]
        else:
            raise Exception("Unknown index type.")

        reg_base = process_register(mem_oprnd["base"])
        disp = mem_oprnd.get("disp", None)
        disp_minus = True if mem_oprnd.get("minus") else False

        if disp:
            if "shift" in disp:
                displacement = process_shifted_register(disp["shift"])
            elif "reg" in disp:
                displacement = process_register(disp["reg"])
            elif "imm" in disp:
                displacement = ArmImmediateOperand("".join(disp["imm"]), arch_info.operand_size)
            else:
                raise Exception("Unknown displacement type.")
        else:
            displacement = None

        size = arch_info.operand_size
        # TODO: Add sizes for LDR/STR variations (half word, byte, double word)
        oprnd = ArmMemoryOperand(reg_base, index_type, displacement, disp_minus, size)

    if "shifted_register" in tokens:
        oprnd =  process_shifted_register(tokens["shifted_register"])

    if "register_list_operand" in tokens:
        parsed_reg_list = tokens["register_list_operand"]
        reg_list = []
        for reg_range in parsed_reg_list:
            start_reg = process_register(reg_range[0])
            if len(reg_range) > 1:
                end_reg = process_register(reg_range[1])
                reg_list.append([start_reg, end_reg])
            else:
                reg_list.append([start_reg])

        oprnd = ArmRegisterListOperand(reg_list, reg_list[0][0].size)

    return oprnd

def parse_instruction(string, location, tokens):
    """Parse an ARM instruction.
    """
    mnemonic = tokens.get("mnemonic")
    operands = [op for op in tokens.get("operands", [])]

    instr = ArmInstruction(
        string,
        mnemonic["ins"],
        operands,
        arch_info.architecture_mode
    )

    if "cc" in mnemonic:
        instr.condition_code = cc_mapper[mnemonic["cc"]]

    if "uf" in mnemonic:
        instr.update_flags = True

    if "ldm_stm_addr_mode" in mnemonic:
        instr.ldm_stm_addr_mode = ldm_stm_am_mapper[mnemonic["ldm_stm_addr_mode"]]

    return instr

# Grammar Rules
# ============================================================================ #
mul      = Literal("*")
plus     = Literal("+")
minus    = Literal("-")
comma    = Literal(",")
lbracket = Literal("[")
rbracket = Literal("]")
lbrace   = Literal("{")
rbrace   = Literal("}")
hashsign = Literal("#")
exclamation    = Literal("!")
caret   = Literal("^")

hex_num = Combine(Literal("0x") + Word("0123456789abcdef"))
dec_num = Word("0123456789")

# Operand Parsing
# ============================================================================ #
sign = Optional(Or([plus, minus("minus")]))

immediate = Group(Optional(Suppress(hashsign)) + (sign +  Or([hex_num, dec_num]))("value"))

register = Group(Or([
    Combine(Literal("r") + Word(nums)("reg_num")),
    Combine(Literal("d") + Word(nums)("reg_num")),
    Combine(Literal("c") + Word(nums)("reg_num")),
    Combine(Literal("p") + Word(nums)("reg_num")),
    Literal("sp"),
    Literal("lr"),
    Literal("pc"),
    Literal("fp"),
    Literal("ip"),
    Literal("sl"),
    Literal("sb"),
    Literal("cpsr"),
    Literal("fpscr"),
    Literal("apsr"),
    Literal("cpsr_fc"),
])("name") + Optional(exclamation)("wb"))

shift_type = Or([
    Literal("lsl"),
    Literal("lsr"),
    Literal("asr"),
    Literal("ror"),
    Literal("rrx"),
])

shift_amount = Group(Or([immediate("imm"), register("reg")]))

shifted_register = Group(register("base") + Suppress(comma) + shift_type("type") + Optional(shift_amount("amount")))

displacement = Group(Or([immediate("imm"), register("reg"), shifted_register("shift")]))

offset_memory_operand = Group(
    Suppress(lbracket) +
    register("base") +
    Optional(
        Suppress(comma) +
        sign +
        displacement("disp")
    ) +
    Suppress(rbracket)
)

pre_indexed_memory_operand = Group(
    Suppress(lbracket) +
    register("base") +
    Suppress(comma) +
    sign +
    displacement("disp") +
    Suppress(rbracket) +
    Suppress(exclamation)
)

post_indexed_memory_operand = Group(
    Suppress(lbracket) +
    register("base") +
    Suppress(rbracket) +
    Suppress(comma) +
    sign +
    displacement("disp")
)

memory_operand = Group(Or([
    offset_memory_operand("offset"),
    pre_indexed_memory_operand("pre"),
    post_indexed_memory_operand("post")
]))

register_range = Group(register("start") + Optional(Suppress(minus) + register("end")))

register_list_operand = Group(
    Suppress(lbrace) +
    Optional(ZeroOrMore(register_range + Suppress(comma)) + register_range) +
    Suppress(rbrace)
)

operand = (Or([
    immediate("immediate_operand"),
    register("register_operand"),
    shifted_register("shifted_register"),
    memory_operand("memory_operand"),
    register_list_operand("register_list_operand")
])).setParseAction(parse_operand)

# Instruction Parsing
# ============================================================================ #
condition_code = Optional(Or([
    Literal("eq"),
    Literal("ne"),

    Literal("cs"), Literal("hs"),
    Literal("cc"), Literal("lo"),

    Literal("mi"),
    Literal("pl"),

    Literal("vs"),
    Literal("vc"),

    Literal("hi"),
    Literal("ls"),

    Literal("ge"),
    Literal("lt"),

    Literal("gt"),
    Literal("le"),

    Literal("al"),
]))("cc")

ldm_stm_addr_mode = Optional(Or([
    Literal("ia"),
    Literal("ib"),
    Literal("da"),
    Literal("db"),

    Literal("fd"),
    Literal("fa"),
    Literal("ed"),
    Literal("ea"),
]))("ldm_stm_addr_mode")

update_flags = Optional(Literal("s"))("uf")

cc_plus_uf = Or([
    condition_code + update_flags, # pre-UAL syntax
    update_flags + condition_code, # UAL syntax
])

mnemonic = Group(Or([
    Combine(Literal("mov")("ins") + cc_plus_uf),
    Combine(Literal("and")("ins") + cc_plus_uf),
    Combine(Literal("eor")("ins") + cc_plus_uf),
    Combine(Literal("orr")("ins") + cc_plus_uf),

    Combine(Literal("ldr")("ins") + condition_code),
    Combine(Literal("str")("ins") + condition_code),
    Combine(Literal("ldrb")("ins") + condition_code),
    Combine(Literal("strb")("ins") + condition_code),
    Combine(Literal("ldrh")("ins") + condition_code),
    Combine(Literal("strh")("ins") + condition_code),
    Combine(Literal("ldrd")("ins") + condition_code),
    Combine(Literal("strd")("ins") + condition_code),

    Combine(Literal("ldm")("ins") + condition_code + ldm_stm_addr_mode),
    Combine(Literal("stm")("ins") + condition_code + ldm_stm_addr_mode),

    Combine(Literal("add")("ins") + cc_plus_uf),
    Combine(Literal("sub")("ins") + cc_plus_uf),
    Combine(Literal("rsb")("ins") + cc_plus_uf),
    Combine(Literal("cmp")("ins") + condition_code),
    Combine(Literal("cmn")("ins") + condition_code),

    Combine(Literal("lsl")("ins") + cc_plus_uf),

    Combine(Literal("mul")("ins") + cc_plus_uf),

    Combine(Literal("b")("ins") + condition_code),
    Combine(Literal("bl")("ins") + condition_code),
    Combine(Literal("bx")("ins") + condition_code),

    Word(alphanums)("ins"),
]))

instruction = (
    mnemonic("mnemonic") +
    Optional(ZeroOrMore(operand + Suppress(comma)) + operand)("operands") +
    LineEnd()
).setParseAction(parse_instruction)

class ArmParser(object):
    """ARM Instruction Parser.
    """

    def __init__(self, architecture_mode=ARCH_ARM_MODE_THUMB):
        global arch_info

        arch_info = ArmArchitectureInformation(architecture_mode)

        self._cache = {}

    def parse(self, instr):
        """Parse an ARM instruction.
        """
        # Commented to get the exception trace of a parser error.
        try:
            instr_lower = instr.lower()

            if not instr_lower in self._cache:
                instr_asm = instruction.parseString(instr_lower)[0]

                self._cache[instr_lower] = instr_asm

            instr_asm = copy.deepcopy(self._cache[instr_lower])

            # self._check_instruction(instr_asm)
        except Exception:
            instr_asm = None
            error_msg = "Failed to parse instruction: %s"
            logger.error(error_msg, instr, exc_info=True)
#             print("Failed to parse instruction: " + instr)
#             print("Exception: " + str(e))

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
