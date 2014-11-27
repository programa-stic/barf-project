"""
x86 Instruction Parser.


id ::= a-zA-Z

prefix ::= id

mnemonic ::= id

modifier ::=   id
             | id modifier

mem_access ::= lbracket mem_access_mode rbracket

mem_access_mode ::=   id
                    | id plus id
                    | id plus num
                    | id plus id mul num
                    | id plus id mul num plus num
                    | id plus id mul num minus num
                    | id plus id plus num
                    | id mul num
                    | id mul num plus num
                    | num

operand ::=   id
            | mem_access

instruction ::=   mnemonic modifier operand
                | mnemonic operand
                | mnemonic modifier operand comma modifier operand
                | mnemonic modifier operand comma operand
                | mnemonic operand comma modifier operand
                | mnemonic operand comma operand
                | prefix instruction

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

import barf
import barf.arch.x86.x86instruction

from barf.arch import ARCH_X86_MODE_32
from barf.arch import ARCH_X86_MODE_64
from barf.arch.x86.x86base import X86ArchitectureInformation
from barf.arch.x86.x86base import X86ImmediateOperand
from barf.arch.x86.x86base import X86InstructionBase
from barf.arch.x86.x86base import X86MemoryOperand
from barf.arch.x86.x86base import X86RegisterOperand

logger = logging.getLogger("X86Parser")

arch_info = None

modifier_size = {
    "xmmword ptr" : 128,
    "xword ptr"   : 80,
    "tword ptr"   : 80,
    "qword ptr"   : 64,
    "dword ptr"   : 32,
    "word ptr"    : 16,
    "byte ptr"    : 8,
    "ptr"         : None, # base on architecture size
    "far ptr"     : None, # base on architecture size
    "far"         : None, # base on architecture size
}

# Parsing functions
# ============================================================================ #

def infer_operands_size(operands):
    size = None

    for oprnd in operands:
        if oprnd.size:
            size = oprnd.size
            break

    if size:
        for oprnd in operands:
            if not oprnd.size:
                oprnd.size = size
    else:
        for oprnd in operands:
            if isinstance(oprnd, X86ImmediateOperand):
                oprnd.size = arch_info.architecture_size

def build_instruction(prefix, mnemonic, operands):
    """Build x86 instruction class from its mnemonic.
    """
    module = barf.arch.x86.x86instruction
    klass = mnemonic.capitalize()
    default = X86InstructionBase

    x86_class = getattr(module, klass, default)

    return x86_class(prefix, mnemonic, operands, arch_info.architecture_mode)

def build_memory_operand(dictionary):
    """Build x86 memory operand from a dictionary.
    """
    segment = dictionary.get("segment", None)
    base = dictionary.get("base", None)
    index = dictionary.get("index", None)
    scale = 0x1
    displacement = 0x0

    if "scale" in dictionary:
        scale = int(dictionary["scale"], 16)

    if "displacement" in dictionary:
        sign  = dictionary.get("displacement_signess", "+")
        value = dictionary.get("displacement")

        displacement = int(sign + value, 16)

    return X86MemoryOperand(segment, base, index, scale, displacement)

def parse_operand_modifier(string, location, tokens):
    """Parser operand modifier.
    """
    return " ".join(tokens)

def parse_operand(string, location, tokens):
    """Parse an instruction operand.
    """
    if "mem_addr" in tokens.keys():
        oprnd = build_memory_operand(tokens)

    if "imm" in tokens.keys():
        modifier = tokens.get("modifier", "")
        if modifier:
            oprnd = X86ImmediateOperand(int("".join(tokens["imm"]), 16), modifier_size[modifier])
        else:
            oprnd = X86ImmediateOperand(int("".join(tokens["imm"]), 16))

    if "reg" in tokens.keys():
        oprnd = X86RegisterOperand(tokens["reg"], arch_info.register_size[tokens["reg"]])

    oprnd.modifier = tokens.get("modifier", "")

    if not oprnd.size and oprnd.modifier:
        oprnd.size = modifier_size[oprnd.modifier]

    return [oprnd]

def parse_instruction(string, location, tokens):
    """Parse an instruction.
    """
    prefix = tokens.get("prefix", None)
    mnemonic = tokens.get("mnemonic", None)
    operands = []

    if "fst_operand" in tokens.keys():
        operands.append(tokens["fst_operand"][0])

    if "snd_operand" in tokens.keys():
        operands.append(tokens["snd_operand"][0])

    if "trd_operand" in tokens.keys():
        operands.append(tokens["trd_operand"][0])

    if "fth_operand" in tokens.keys():
        operands.append(tokens["fth_operand"][0])

    infer_operands_size(operands)

    return build_instruction(prefix, mnemonic, operands)

# Grammar Rules
# ============================================================================ #
mul      = Literal("*")
plus     = Literal("+")
minus    = Literal("-")
comma    = Literal(",")
lbracket = Literal("[")
rbracket = Literal("]")
colon    = Literal(":")

hex_num = Combine("0x" + Word("0123456789abcdef"))
dec_num = Word("0123456789")

mnemonic = Word(alphanums)

# Operand Parsing
# ============================================================================ #
modifier = Forward()
modifier << (ZeroOrMore(
    Or([
        Literal("xmmword"),
        Literal("xword"),
        Literal("tword"),
        Literal("qword"),
        Literal("dword"),
        Literal("word"),
        Literal("byte"),
        Literal("ptr"),
        Literal("far"),
    ])
)("modifier")).setParseAction(parse_operand_modifier)

reg = Or([
    Literal("cs"),
    Literal("ds"),
    Literal("ss"),
    Literal("es"),
    Literal("fs"),
    Literal("gs"),
    Word(alphas),
    Combine("r" + Word(alphanums)),
    Combine("st" + Word(nums)),
    Combine("st(" + Word(nums) + ")"),
    Combine("xmm" + Word(nums)),
    Combine("ymm" + Word(nums)),
    Combine("mm" + Word(nums)),
    Combine("dr" + Word(nums)),
    Combine("cr" + Word(nums)),
])

imm = Optional("-") +  Or([hex_num, dec_num])

seg = Or([
    Literal("cs"),
    Literal("ds"),
    Literal("ss"),
    Literal("es"),
    Literal("fs"),
    Literal("gs"),
])("segment")

base = reg("base")

scale = Or([
    Literal("1"),
    Literal("2"),
    Literal("4"),
    Literal("8"),
    Literal("0x1"),
    Literal("0x2"),
    Literal("0x4"),
    Literal("0x8")
])("scale")

index = reg("index") + Optional("*" + scale)

displacement = Or([hex_num, dec_num])("displacement")
displacement_signess = (Or([plus, minus]))("displacement_signess")

memory_addressing = (
    Optional(seg + Suppress(colon)) +
    Suppress(lbracket) +
    Or([
        base,
        index,
        displacement,
        displacement_signess + displacement,

        base + plus + index,
        base + plus + index + displacement_signess + displacement,

        base + displacement_signess + displacement,
        index + displacement_signess + displacement,
    ]) +
    Suppress(rbracket)
)

operand = (Optional(modifier) + Or([
    imm("imm"),
    reg("reg"),
    memory_addressing("mem_addr"),
])).setParseAction(parse_operand)

# Intruction Parsing
# ============================================================================ #
prefix = Or([
    Literal("lock"),
    Literal("rep"),
    Literal("repe"),
    Literal("repne"),
    Literal("repz"),
    Literal("addr16"),
    Literal("data16"),
    Literal("data32"),
])

instruction = ((Optional(prefix)("prefix")) + Or([
    mnemonic("mnemonic"),
    mnemonic("mnemonic") + operand("fst_operand"),
    mnemonic("mnemonic") + operand("fst_operand") + Suppress(comma) + operand("snd_operand"),
    mnemonic("mnemonic") + operand("fst_operand") + Suppress(comma) + operand("snd_operand") + Suppress(comma) + operand("trd_operand"),
    mnemonic("mnemonic") + operand("fst_operand") + Suppress(comma) + operand("snd_operand") + Suppress(comma) + operand("trd_operand") + Suppress(comma) + operand("fth_operand"),
])).setParseAction(parse_instruction)


class X86Parser():
    """x86 Instruction Parser.
    """

    def __init__(self, architecture_mode=ARCH_X86_MODE_32):
        global arch_info, modifier_size

        arch_info = X86ArchitectureInformation(architecture_mode)

        self._cache = {}

        modifier_size["far ptr"] = arch_info.architecture_size
        modifier_size["far"] = arch_info.architecture_size
        modifier_size["ptr"] = arch_info.architecture_size

    def parse(self, instr, address=None, size=None, bytes=None):
        """Parse an x86 instruction.
        """
        instr_parse = None

        try:
            instr_lower = instr.lower()

            if not instr_lower in self._cache:
                instr_asm = instruction.parseString(instr_lower)[0]
                instr_asm.size = size
                instr_asm.bytes = bytes

                self._cache[instr_lower] = instr_asm

            instr_asm = copy.deepcopy(self._cache[instr_lower])
            instr_asm.address = address

            assert all([oprnd.size in [8, 16, 32, 64, 80, 128] for oprnd in instr_asm.operands]), "error : %s" % (instr_asm)
            assert all([oprnd.base or oprnd.index or oprnd.displacement for oprnd in instr_asm.operands if isinstance(oprnd, X86MemoryOperand)]), "error : %s" % (instr_asm)
        except Exception, reason:
            # print "[E] x86 parsing error : '%s' (%s)" % (instr, reason)

            logger.debug("[E] x86 parsing error : '%s' (%s)" % (instr, reason))

            instr_asm = None

        return instr_asm
