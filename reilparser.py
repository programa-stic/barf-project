"""
Reil Instruction Parser.

Instructions
------------

    Arithmetic    : ADD, SUB, MUL, DIV, MOD, BSH
    Bitwise       : AND, OR, XOR
    Data Transfer : LDM, STM, STR
    Conditional   : BISZ, JCC
    Other         : UNDEF, UNKN, NOP

Examples
--------

    * add t0, t1, t2

    * add eax, t0, t1

    * str ebx, e, t0

    * str ebx (32), e, t0 (32)

* Note that it can also parse registers size.

"""

import copy
import logging

from pyparsing import alphanums
from pyparsing import alphas
from pyparsing import Combine
from pyparsing import Literal
from pyparsing import nums
from pyparsing import Optional
from pyparsing import Or
from pyparsing import Suppress
from pyparsing import Word

from barf.core.reil.reil import ReilEmptyOperand
from barf.core.reil.reil import ReilImmediateOperand
from barf.core.reil.reil import ReilInstructionBuilder
from barf.core.reil.reil import ReilMnemonic
from barf.core.reil.reil import ReilRegisterOperand

logger = logging.getLogger(__name__)

def parse_operand(string, location, tokens):
    """Parse instruction operand.
    """
    sizes = {
        "dqword"  : 128,
        "pointer" : 72,
        "qword"   : 64,
        "pointer" : 40,
        "dword"   : 32,
        "word"    : 16,
        "byte"    : 8,
        "bit"     : 1,
    }

    if "immediate" in tokens:
        imm_str = "".join(tokens["immediate"])
        base = 16 if imm_str.startswith("0x") or imm_str.startswith("-0x") else 10

        immediate = int(imm_str, base)

        oprnd = ReilImmediateOperand(immediate)

    if "register" in tokens:
        if tokens["register"] in ["e", "empty"]:
            oprnd = ReilEmptyOperand()

            oprnd.size = 0
        else:
            name = tokens["register"]

            oprnd = ReilRegisterOperand(name)

    if "size" in tokens:
        size = int(sizes[tokens["size"]])

        oprnd.size = size

    return [oprnd]

def parse_instruction(string, location, tokens):
    """Parse instruction.
    """
    mnemonic = ReilMnemonic.from_string(tokens["mnemonic"])

    oprnd1 = tokens["fst_operand"][0]
    oprnd2 = tokens["snd_operand"][0]
    oprnd3 = tokens["trd_operand"][0]

    ins_builder = ReilInstructionBuilder()

    return ins_builder.build(mnemonic, oprnd1, oprnd2, oprnd3)

# ============================================================================ #

comma = Literal(",")

hex_num = Combine("0x" + Word("0123456789abcdef"))
dec_num = Word("0123456789")

immediate = Optional("-") +  Or([hex_num, dec_num])
register = Word(alphanums)

mnemonic = Or([
    # Arithmetic
    Literal("add"), Literal("sub"), Literal("mul"),
    Literal("div"), Literal("mod"), Literal("bsh"),

    # Bitwise
    Literal("and"), Literal("or"), Literal("xor"),

    # Data Transfer
    Literal("ldm"), Literal("stm"), Literal("str"),

    # Conditional
    Literal("bisz"), Literal("jcc"),

    # Other
    Literal("undef"), Literal("unkn"), Literal("nop"),

    # Extra
    Literal("ret"),
])

size = Or([
    Literal("pointer"),
    Literal("dqword"),
    Literal("qword"),
    Literal("dword"),
    Literal("word"),
    Literal("byte"),
    Literal("bit"),
])("size")

operand = (Optional(size) + Or([
    immediate("immediate"),
    register("register")
])).setParseAction(parse_operand)

instruction = (
    mnemonic("mnemonic") +
    Suppress("[") +
    operand("fst_operand") + Suppress(comma) +
    operand("snd_operand") + Suppress(comma) +
    operand("trd_operand") +
    Suppress("]")
).setParseAction(parse_instruction)

class ReilParser(object):

    """Reil Instruction Parser."""

    def __init__(self):

        # A parsing cache. Each parsed instruction is cached to improve
        # performance.
        self._cache = {}

    def parse(self, instrs):
        """Parse an IR instruction.
        """
        instrs_reil = []

        try:
            for instr in instrs:
                instr_lower = instr.lower()

                # If the instruction to parsed is not in the cache,
                # parse it and add it to the cache.
                if not instr_lower in self._cache:
                    self._cache[instr_lower] = instruction.parseString(
                        instr_lower)[0]

                # Retrieve parsed instruction from the cache and clone
                # it.
                instrs_reil += [copy.deepcopy(self._cache[instr_lower])]
        except:
            instr_reil = None

            error_msg = "Failed to parse instruction: %s"

            logger.error(error_msg, instr, exc_info=True)

        return instrs_reil
