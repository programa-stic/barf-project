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
x86 Instruction Parser.
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
from pyparsing import ZeroOrMore

from barf.arch import ARCH_X86_MODE_32
from barf.arch.x86.x86base import X86ArchitectureInformation
from barf.arch.x86.x86base import X86ImmediateOperand
from barf.arch.x86.x86base import X86Instruction
from barf.arch.x86.x86base import X86MemoryOperand
from barf.arch.x86.x86base import X86RegisterOperand

logger = logging.getLogger(__name__)

arch_info = None

modifier_size = {
    "ymmword ptr" : 256,
    "xmmword ptr" : 128,
    "xword ptr"   : 80,
    "tword ptr"   : 80,
    "qword ptr"   : 64,
    "dword ptr"   : 32,
    "word ptr"    : 16,
    "byte ptr"    : 8,
    "ptr"         : None,   # Based on architecture size.
    "far ptr"     : None,   # Based on architecture size.
    "far"         : None,   # Based on architecture size.
}

# Parsing functions
# ============================================================================ #
def infer_operands_size(operands):
    """Infer x86 instruction operand size based on other operands.
    """
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


def parse_immediate(string):
    if string.startswith("0x") or string.startswith("-0x"):
        immediate = int(string, 16)
    else:
        immediate = int(string, 10)

    return immediate


def parse_operand(string, location, tokens):
    """Parse an x86 instruction operand.
    """
    modifier = " ".join(tokens.get("modifier", ""))

    if "immediate" in tokens:
        immediate = parse_immediate("".join(tokens["immediate"]))
        size = modifier_size.get(modifier, None)

        oprnd = X86ImmediateOperand(immediate, size)

    if "register" in tokens:
        name = tokens["register"]
        size = arch_info.registers_size[tokens["register"]]

        oprnd = X86RegisterOperand(name, size)

    if "memory" in tokens:
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
    """Parse an x86 instruction.
    """
    prefix = tokens.get("prefix", None)
    mnemonic = tokens.get("mnemonic")
    operands = [op for op in tokens.get("operands", [])]

    infer_operands_size(operands)

    # Quick hack: Capstone returns rep instead of repe for cmps and scas
    # instructions.
    if prefix == "rep" and (mnemonic.startswith("cmps") or mnemonic.startswith("scas")):
        prefix = "repe"

    instr = X86Instruction(
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

hex_num = Combine(Literal("0x") + Word("0123456789abcdef"))
dec_num = Word("0123456789")

# Operand Parsing
# ============================================================================ #
modifier = (
    Optional(Or([
        Literal("ymmword"),
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
    segment,
    Word(alphas),
    Combine(Literal("r") + Word(alphanums)),
    Combine(Literal("st") + Word(nums)),
    Combine(Literal("st") + Suppress(Literal("(")) + Word(nums) + Suppress(Literal(")"))),
    Combine(Literal("xmm") + Word(nums)),
    Combine(Literal("ymm") + Word(nums)),
    Combine(Literal("mm") + Word(nums)),
    Combine(Literal("dr") + Word(nums)),
    Combine(Literal("cr") + Word(nums)),
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

    def parse(self, instr):
        """Parse an x86 instruction.
        """
        try:
            instr_lower = instr.lower()

            if instr_lower not in self._cache:
                instr_asm = instruction.parseString(instr_lower)[0]

                self._cache[instr_lower] = instr_asm

            instr_asm = copy.deepcopy(self._cache[instr_lower])

            # self._check_instruction(instr_asm)
        except:
            instr_asm = None

            error_msg = "Failed to parse instruction: %s"

            logger.error(error_msg, instr, exc_info=True)

        return instr_asm

    def _check_instruction(self, instr):
        # Check operands size.
        assert all([oprnd.size in [8, 16, 32, 64, 80, 128]
                        for oprnd in instr.operands]), \
                "Invalid operand size: %s" % instr

        # Check memory operand parameters.
        assert all([oprnd.base or oprnd.index or oprnd.displacement
                        for oprnd in instr.operands
                            if isinstance(oprnd, X86MemoryOperand)]), \
                "Invalid memory operand parameters: %s" % instr
