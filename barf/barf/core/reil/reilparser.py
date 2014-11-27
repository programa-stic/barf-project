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

Placeholder Registers
---------------------

It is possible to specify *placeholder registers*. For example, the
following instruction:

    add $0, $1, t0

is parsed and the first and second registers are created as
'ReilRegisterOperand' and are *tagged* as *placeholder* registers. That
means that the particular value for those registers can be set later.
This is of great help for instruction translators. For example, suppose
you need to write a translator for the x86 add instruccion, it could be
translated this way:

def translate_add():
    parser = ReilParser()

    return parser.parse("add $0, $1, #0")

This function provides a template translation of the x86 ADD
instruction. Then, each ADD instruction instance, for example, ADD eax,
ebx wil be translated using the previous template, where $0 and #0 will
be replace with eax and $1 with ebx. For a more exhaustive explanation,
refer to arhc/x86/x86translator.py

"""

import copy

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
from barf.utils.utils import VariableNamer

ins_builder = ReilInstructionBuilder()

def parse_operand(string, location, tokens):
    """Parse instruction operand.
    """
    # print tokens

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

    # Immediate operand.
    if "imm" in tokens.keys():
        if tokens["imm"].startswith("0x"):
            base = 16
        else:
            base = 10

        if "size" in tokens:
            oprnd = ReilImmediateOperand(int(tokens["imm"], base), int(sizes[tokens["size"]]))
        else:
            oprnd = ReilImmediateOperand(int(tokens["imm"], base))

        if "size" in tokens:
            oprnd.size = int(sizes[tokens["size"]])

    # Register operand.
    if "reg" in tokens.keys():
        if tokens["reg"] == "e" or tokens["reg"] == "empty":
            oprnd = ReilEmptyOperand()
            oprnd.size = 0
        else:
            oprnd = ReilRegisterOperand(tokens["reg"])

            if "size" in tokens:
                oprnd.size = int(sizes[tokens["size"]])

    # Placeholder operand.
    if "placeholder" in tokens.keys():
        oprnd = ReilRegisterOperand("")
        oprnd.tag = tokens["placeholder"]

        if "size" in tokens:
            oprnd.size = int(sizes[tokens["size"]])

            # print oprnd.tag
            # print oprnd.size

    # Temporary register operand.
    if "auto_reg" in tokens.keys():
        oprnd = ReilRegisterOperand("")
        oprnd.tag = tokens["auto_reg"]

        if "size" in tokens:
            oprnd.size = int(sizes[tokens["size"]])

    return [oprnd]

def parse_instruction(string, location, tokens):
    """Parse instruction.
    """
    mnemonic = ReilMnemonic.from_string(tokens["mnemonic"])

    oprnd1 = tokens["fst_operand"][0]
    oprnd2 = tokens["snd_operand"][0]
    oprnd3 = tokens["trd_operand"][0]

    return ins_builder.build(mnemonic, oprnd1, oprnd2, oprnd3)

# ============================================================================ #

percentage = Literal("%")
comma = Literal(",")
lparen = Literal("(")
rparen = Literal(")")

hex_num = Combine("0x" + Word("0123456789abcdef"))
dec_num = Word("0123456789")

imm = Or([hex_num, dec_num, Combine("-" + Word("0123456789"))])
reg = Word(alphanums)
placeholder = Or([Combine("$" + Word("0123456789")), Combine("#" + Word("0123456789"))])
auto_reg = Or([Combine("%" + dec_num), Combine("?" + Word(alphas) + "." + Word(nums))])

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

size1 = Or([
    # Suppress(lparen) + dec_num + Suppress(rparen),
    Literal("pointer"),
    Literal("dqword"),
    Literal("qword"),
    Literal("dword"),
    Literal("word"),
    Literal("byte"),
    Literal("bit"),
])("size")

# operand = (Or([
#     imm("imm"),
#     reg("reg"),
#     placeholder("placeholder"),
#     auto_reg("auto_reg"),
# ]) + Optional(size)).setParseAction(parse_operand)

operand = (Optional(size1) + Or([
    imm("imm"),
    reg("reg"),
    placeholder("placeholder"),
    auto_reg("auto_reg"),
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

    def parse(self, instrs, restart_reg_namer=True):
        """Parse an IR instruction.
        """
        instrs_reil = []

        try:
            for instr in instrs:
                instr_lower = instr.lower()

                # If the instruction to parsed is not in the cache, parse it and
                # add it to the cache.
                if not instr_lower in self._cache:
                    self._cache[instr_lower] = instruction.parseString(instr_lower)[0]

                # Retrieve parsed instruction from the cache and clone it.
                instrs_reil += [copy.deepcopy(self._cache[instr_lower])]
        except Exception as reason:
            print("[E] Reil parsing error :")
            print("      Reason: %s" % reason)
            print("      Instructions: %s" % map(str, instrs))

        return instrs_reil
