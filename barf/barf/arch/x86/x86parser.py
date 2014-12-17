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

logger = logging.getLogger(__name__)

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
            if isinstance(oprnd, X86ImmediateOperand) and not oprnd.size:
                oprnd.size = arch_info.architecture_size

def parse_operand(string, location, tokens):
    """Parse an instruction operand.
    """
    # print "parse_operand: ", tokens

    modifier = " ".join(tokens.get("modifier", ""))

    if "immediate" in tokens.keys():
        value = int("".join(tokens["immediate"]), 16)
        size = modifier_size.get(modifier, None)

        oprnd = X86ImmediateOperand(value)
        oprnd.size = size

    if "register" in tokens.keys():
        name = tokens["register"]
        size = arch_info.register_size[tokens["register"]]

        oprnd = X86RegisterOperand(name, size)

    if "memory" in tokens.keys():
        segment = tokens.get("segment", None)
        base = tokens.get("base", None)
        index = tokens.get("index", None)
        scale = int(tokens.get("scale", "0x1"), 16)
        displacement = int("".join(tokens.get("displacement", "0x0")), 16)

        oprnd = X86MemoryOperand(segment, base, index, scale, displacement)

    oprnd.modifier = modifier

    if not oprnd.size and oprnd.modifier:
        oprnd.size = modifier_size[oprnd.modifier]

    return oprnd

def parse_instruction(string, location, tokens):
    """Parse an instruction.
    """
    prefix = tokens.get("prefix", None)
    mnemonic = tokens.get("mnemonic")
    operands = [op for op in tokens.get("operands", [])]

    infer_operands_size(operands)

    instr = X86InstructionBase(
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
colon    = Literal(":")

hex_num = Combine("0x" + Word("0123456789abcdef"))
dec_num = Word("0123456789")

# Operand Parsing
# ============================================================================ #
modifier = (
    Optional(Or([
        Literal("xmmword"),
        Literal("xword"),
        Literal("tword"),
        Literal("qword"),
        Literal("dword"),
        Literal("word"),
        Literal("byte"),
        Literal("far"),
    ])) +
    Optional(Literal("ptr"))
)

immediate = Optional("-") +  Or([hex_num, dec_num])

segment = Or([
    Literal("cs"),
    Literal("ds"),
    Literal("ss"),
    Literal("es"),
    Literal("fs"),
    Literal("gs"),
])("segment")

register = Or([
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

base = register("base")

scale = Or([
    Literal("1"),
    Literal("2"),
    Literal("4"),
    Literal("8"),
    Literal("0x1"),
    Literal("0x2"),
    Literal("0x4"),
    Literal("0x8"),
])

scaled_index = register("index") + Optional(mul + scale("scale"))

displacement = (
    Optional(Or([plus, minus])) + Or([hex_num, dec_num])
)("displacement")

memory = (
    Optional(segment + Suppress(colon)) +
    Suppress(lbracket) +
    Or([
        base,
        scaled_index,
        displacement,

        base + plus + scaled_index,
        base + plus + scaled_index + displacement,

        base + displacement,
        scaled_index + displacement,
    ]) +
    Suppress(rbracket)
)

operand = (
    Optional(modifier)("modifier") +
    Or([immediate("immediate"), register("register"), memory("memory")])
).setParseAction(parse_operand)

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

mnemonic = Word(alphanums)

instruction = (
    Optional(prefix)("prefix") +
    mnemonic("mnemonic") +
    Optional(ZeroOrMore(operand + Suppress(comma)) + operand)("operands")
).setParseAction(parse_instruction)


class X86Parser(object):
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

        if instr in ["repne", "rep", "lock", "data16"]:
            return None

        try:
            instr_lower = instr.lower()

            if not instr_lower in self._cache:
                instr_asm = instruction.parseString(instr_lower)[0]
                instr_asm.size = size
                instr_asm.bytes = bytes

                self._cache[instr_lower] = instr_asm

            instr_asm = copy.deepcopy(self._cache[instr_lower])
            instr_asm.address = address

            self._check_instruction(instr_asm)
        except Exception, reason:
            instr_asm = None

            self._log_parsing_exception(instr, address, size, bytes)

        return instr_asm

    def _log_parsing_exception(self, instr, address, size, bytes):
        if bytes:
            bytes_str = "".join("\\x%02x" % ord(b) for b in bytes)
        else:
            bytes_str = "???"

        logger.error(
            "Failed to parse x86 instruction: %s (%s : %s)",
            instr,
            hex(address) if address else "???",
            bytes_str,
            exc_info=True
        )

    def _check_instruction(self, instr_asm):
        assert all([oprnd.size in [8, 16, 32, 64, 80, 128] for oprnd in instr_asm.operands]), "error : %s" % (instr_asm)
        assert all([oprnd.base or oprnd.index or oprnd.displacement for oprnd in instr_asm.operands if isinstance(oprnd, X86MemoryOperand)]), "error : %s" % (instr_asm)
