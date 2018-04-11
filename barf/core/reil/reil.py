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
This module contains all the classes that handle the intermediate
representation language. It is basically the REIL language with minor
changes. Below there is an overview of the REIL language and its
instruction format. For full details see "REIL: A platform-independent
intermediate representation of disassembled code for static code
analysis."

All algorithms within the framework are designed to operate on the
intermediate representation. This provides great flexibility when it
comes to implement a cross-platform framework.

Instruction Format
------------------

    mnemonic oprnd1, oprnd2, oprnd3

Instructions
------------

    Arithmetic    : ADD, SUB, MUL, DIV, MOD, BSH
    Bitwise       : AND, OR, XOR
    Data Transfer : LDM, STM, STR
    Conditional   : BISZ, JCC
    Other         : UNDEF, UNKN, NOP

"""

DISPLAY_SIZE = True     # Display operands size in instruction


class ReilMnemonic(object):

    """Enumeration of IR mnemonics.
    """

    # Arithmetic Instructions
    ADD   = 1
    SUB   = 2
    MUL   = 3
    DIV   = 4
    MOD   = 5
    BSH   = 6

    # Bitwise Instructions
    AND   = 7
    OR    = 8
    XOR   = 9

    # Data Transfer Instructions
    LDM   = 10
    STM   = 11
    STR   = 12

    # Conditional Instructions
    BISZ  = 13
    JCC   = 14

    # Other Instructions
    UNKN  = 15
    UNDEF = 16
    NOP   = 17

    # Extensions
    SEXT  = 18
    SDIV  = 19
    SMOD  = 20

    @staticmethod
    def to_string(mnemonic):
        """Return the string representation of the given mnemonic.
        """
        strings = {
            # Arithmetic Instructions
            ReilMnemonic.ADD: "add",
            ReilMnemonic.SUB: "sub",
            ReilMnemonic.MUL: "mul",
            ReilMnemonic.DIV: "div",
            ReilMnemonic.MOD: "mod",
            ReilMnemonic.BSH: "bsh",

            # Bitwise Instructions
            ReilMnemonic.AND: "and",
            ReilMnemonic.OR:  "or",
            ReilMnemonic.XOR: "xor",

            # Data Transfer Instructions
            ReilMnemonic.LDM: "ldm",
            ReilMnemonic.STM: "stm",
            ReilMnemonic.STR: "str",

            # Conditional Instructions
            ReilMnemonic.BISZ: "bisz",
            ReilMnemonic.JCC:  "jcc",

            # Other Instructions
            ReilMnemonic.UNKN:  "unkn",
            ReilMnemonic.UNDEF: "undef",
            ReilMnemonic.NOP:   "nop",

            # Extensions
            ReilMnemonic.SEXT: "sext",
            ReilMnemonic.SDIV: "sdiv",
            ReilMnemonic.SMOD: "smod",
        }

        return strings[mnemonic]

    @staticmethod
    def from_string(string):
        """Return the mnemonic represented by the given string.
        """
        mnemonics = {
            # Arithmetic Instructions
            "add": ReilMnemonic.ADD,
            "sub": ReilMnemonic.SUB,
            "mul": ReilMnemonic.MUL,
            "div": ReilMnemonic.DIV,
            "mod": ReilMnemonic.MOD,
            "bsh": ReilMnemonic.BSH,

            # Bitwise Instructions
            "and": ReilMnemonic.AND,
            "or":  ReilMnemonic.OR,
            "xor": ReilMnemonic.XOR,

            # Data Transfer Instructions
            "ldm": ReilMnemonic.LDM,
            "stm": ReilMnemonic.STM,
            "str": ReilMnemonic.STR,

            # Conditional Instructions
            "bisz": ReilMnemonic.BISZ,
            "jcc":  ReilMnemonic.JCC,

            # Other Instructions
            "unkn":  ReilMnemonic.UNKN,
            "undef": ReilMnemonic.UNDEF,
            "nop":   ReilMnemonic.NOP,

            # Added Instructions
            "sext": ReilMnemonic.SEXT,
            "sdiv": ReilMnemonic.SDIV,
            "smod": ReilMnemonic.SMOD,
        }

        return mnemonics[string]


REIL_MNEMONICS = (
    # Arithmetic Instructions
    ReilMnemonic.ADD,
    ReilMnemonic.SUB,
    ReilMnemonic.MUL,
    ReilMnemonic.DIV,
    ReilMnemonic.MOD,
    ReilMnemonic.BSH,

    # Bitwise Instructions
    ReilMnemonic.AND,
    ReilMnemonic.OR,
    ReilMnemonic.XOR,

    # Data Transfer Instructions
    ReilMnemonic.LDM,
    ReilMnemonic.STM,
    ReilMnemonic.STR,

    # Conditional Instructions
    ReilMnemonic.BISZ,
    ReilMnemonic.JCC,

    # Other Instructions
    ReilMnemonic.UNKN,
    ReilMnemonic.UNDEF,
    ReilMnemonic.NOP,

    # Extensions
    ReilMnemonic.SEXT,
    ReilMnemonic.SDIV,
    ReilMnemonic.SMOD,
)


def check_operands_size(instr, addr_size):
    """Enforce operands' size."""

    if instr.mnemonic in [ReilMnemonic.ADD, ReilMnemonic.SUB,
                            ReilMnemonic.MUL, ReilMnemonic.DIV,
                            ReilMnemonic.MOD, ReilMnemonic.BSH,
                            ReilMnemonic.AND, ReilMnemonic.OR,
                            ReilMnemonic.XOR]:
        # operand0 : Source 1 (Literal or register)
        # operand1 : Source 2 (Literal or register)
        # operand2 : Destination register

        # Check that source operands have the same size.
        assert instr.operands[0].size == instr.operands[1].size, \
            "Invalid operands size: %s" % instr

    elif instr.mnemonic in [ReilMnemonic.LDM]:
        # operand0 : Source address (Literal or register)
        # operand1 : Empty register
        # operand2 : Destination register

        assert instr.operands[0].size == addr_size, \
            "Invalid operands size: %s" % instr

    elif instr.mnemonic in [ReilMnemonic.STM]:
        # operand0 : Value to store (Literal or register)
        # operand1 : Empty register
        # operand2 : Destination address (Literal or register)

        assert instr.operands[2].size == addr_size, \
            "Invalid operands size: %s" % instr

    elif instr.mnemonic in [ReilMnemonic.STR]:
        # operand0 : Value to store (Literal or register)
        # operand1 : Empty register
        # operand2 : Destination register

        pass

    elif instr.mnemonic in [ReilMnemonic.BISZ]:
        # operand0 : Value to compare (Literal or register)
        # operand1 : Empty register
        # operand2 : Destination register

        pass

    elif instr.mnemonic in [ReilMnemonic.JCC]:
        # operand0 : Condition (Literal or register)
        # operand1 : Empty register
        # operand2 : Destination register

        # FIX: operand2.size should be addr_size + 1 byte

        assert instr.operands[2].size == addr_size + 8, \
            "Invalid operands size: %s" % instr

        pass

    elif instr.mnemonic in [ReilMnemonic.UNKN]:
        # operand0 : Empty register
        # operand1 : Empty register
        # operand2 : Empty register

        pass

    elif instr.mnemonic in [ReilMnemonic.UNDEF]:
        # operand0 : Empty register
        # operand1 : Empty register
        # operand2 : Destination register

        pass

    elif instr.mnemonic in [ReilMnemonic.NOP]:
        # operand0 : Empty register
        # operand1 : Empty register
        # operand2 : Empty register

        pass

    elif instr.mnemonic in [ReilMnemonic.SEXT]:
        # operand0 : Value to store (Literal or register)
        # operand1 : Empty register
        # operand2 : Destination register

        assert instr.operands[0].size <= instr.operands[2].size, \
            "Invalid operands size: %s" % instr


class ReilInstruction(object):

    """Representation of a REIL instruction.
    """

    __slots__ = [
        '_mnemonic',
        '_operands',
        '_comment',
        '_address',
    ]

    def __init__(self):

        # A REIL mnemonic
        self._mnemonic = None

        # A list of operand. Exactly 3.
        self._operands = [ReilEmptyOperand()] * 3

        # Optionally, a comment for the instruction.
        self._comment = None

        # A REIL address for the instruction.
        self._address = None

    @property
    def mnemonic(self):
        """Get instruction mnemonic.
        """
        return self._mnemonic

    @property
    def mnemonic_str(self):
        """Get instruction mnemonic as string.
        """
        return ReilMnemonic.to_string(self._mnemonic)

    @mnemonic.setter
    def mnemonic(self, value):
        """Set instruction mnemonic.
        """
        if value not in REIL_MNEMONICS:
            raise Exception("Invalid instruction mnemonic : %s" % str(value))

        self._mnemonic = value

    @property
    def operands(self):
        """Get instruction operands.
        """
        return self._operands

    @operands.setter
    def operands(self, value):
        """Set instruction operands.
        """
        if len(value) != 3:
            raise Exception("Invalid instruction operands : %s" % str(value))

        self._operands = value

    @property
    def address(self):
        """Get instruction address.
        """
        return self._address

    @address.setter
    def address(self, value):
        """Set instruction address.
        """
        self._address = value

    @property
    def comment(self):
        """Get instruction comment.
        """
        return self._comment

    @comment.setter
    def comment(self, value):
        """Set instruction comment.
        """
        self._comment = value

    def __str__(self):
        def print_oprnd(oprnd):
            oprnd_str = str(oprnd)

            sizes = {
                256: "DDQWORD",
                128: "DQWORD",
                72:  "POINTER",
                64:  "QWORD",
                40:  "POINTER",
                32:  "DWORD",
                16:  "WORD",
                8:   "BYTE",
                1:   "BIT",
                "":  "UNK",
            }

            if isinstance(oprnd, ReilEmptyOperand):
                return "%s" % oprnd_str
            else:
                return "%s %s" % (sizes[oprnd.size if oprnd.size else ""], oprnd_str)

        mnemonic_str = ReilMnemonic.to_string(self._mnemonic)

        if DISPLAY_SIZE:
            operands_str = ", ".join(map(print_oprnd, self._operands))
        else:
            operands_str = ", ".join(map(str, self._operands))

        return "%-5s [%s]" % (mnemonic_str, operands_str)

    def __repr__(self):
        if self._address:
            return "{:#08x}:{:#02x} {}".format(self._address >> 8, self._address & 0xff, self.__str__())
        else:
            return self.__str__()

    def __hash__(self):
        return hash(str(self))

    def __getstate__(self):
        state = {
            '_mnemonic': self._mnemonic,
            '_operands': self._operands,
            '_comment': self._comment,
            '_address': self._address
        }

        return state

    def __setstate__(self, state):
        self._mnemonic = state['_mnemonic']
        self._operands = state['_operands']
        self._comment = state['_comment']
        self._address = state['_address']


class ReilOperand(object):

    """Representation of an IR instruction's operand.
    """

    __slots__ = [
        '_size',
    ]

    def __init__(self, size):
        # Size of the operand, in bits.
        self._size = size

    @property
    def size(self):
        """Get operand size.
        """
        return self._size

    @size.setter
    def size(self, value):
        """Set operand size.
        """
        self._size = value

    def __eq__(self, other):
        return type(other) is type(self) and \
                self._size == other.size

    def __ne__(self, other):
        return not self.__eq__(other)

    def __getstate__(self):
        state = {
            '_size': self.size
        }

        return state

    def __setstate__(self, state):
        self._size = state['_size']


class ReilImmediateOperand(ReilOperand):

    """Representation of a REIL instruction immediate operand.
    """

    __slots__ = [
        '_immediate',
    ]

    def __init__(self, immediate, size=None):
        super(ReilImmediateOperand, self).__init__(size)

        assert type(immediate) in [int, long], "Invalid immediate value type."

        self._immediate = immediate

    @property
    def immediate(self):
        """Get immediate.
        """
        if not self._size:
            raise Exception("Operand size missing.")

        return self._immediate & 2**self._size-1

    def __str__(self):
        if not self._size:
            raise Exception("Operand size missing.")

        string = hex(self._immediate & 2**self._size-1)

        return string[:-1] if string[-1] == 'L' else string

    def __eq__(self, other):
        return type(other) is type(self) and \
                self._size == other.size and \
                self._immediate == other.immediate

    def __getstate__(self):
        state = super(ReilImmediateOperand, self).__getstate__()

        state['_immediate'] = self._immediate

        return state

    def __setstate__(self, state):
        super(ReilImmediateOperand, self).__setstate__(state)

        self._immediate = state['_immediate']


class ReilRegisterOperand(ReilOperand):

    """Representation of a REIL instruction register operand.
    """

    __slots__ = [
        '_name',
    ]

    def __init__(self, name, size=None):
        super(ReilRegisterOperand, self).__init__(size)

        # Register name.
        self._name = name

    @property
    def name(self):
        """Get IR register operand name.
        """
        return self._name

    def __str__(self):
        return self._name

    def __eq__(self, other):
        return type(other) is type(self) and \
                self._size == other.size and \
                self._name == other.name

    def __getstate__(self):
        state = super(ReilRegisterOperand, self).__getstate__()

        state['_name'] = self._name

        return state

    def __setstate__(self, state):
        super(ReilRegisterOperand, self).__setstate__(state)

        self._name = state['_name']


class ReilEmptyOperand(ReilOperand):

    """Representation of an IR instruction's empty operand.
    """

    def __init__(self):
        super(ReilEmptyOperand, self).__init__(size=None)

    def __str__(self):
        return "EMPTY"

    def __eq__(self, other):
        return type(other) is type(self)


class DualInstruction(object):

    """Represents an assembler instruction paired with its IR
    representation.

    """

    __slots__ = [
        '_address',
        '_asm_instr',
        '_ir_instrs',
    ]

    def __init__(self, address, asm_instr, ir_instrs):

        # Address of the assembler instruction.
        self._address = address

        # Assembler instruction.
        self._asm_instr = asm_instr

        # REIL translation of the assembler instruction. Note that one
        # assembler instruction is mapped to more than one REIL
        # instruction.
        self._ir_instrs = ir_instrs

    @property
    def address(self):
        """Get instruction address.
        """
        return self._address

    @property
    def asm_instr(self):
        """Get assembly instruction.
        """
        return self._asm_instr

    @property
    def ir_instrs(self):
        """Get IR representation of the assembly instruction.
        """
        return self._ir_instrs

    def __eq__(self, other):
        return self.address == other.address and \
                self.asm_instr == other.asm_instr

    def __ne__(self, other):
        return not self.__eq__(other)

    def __getstate__(self):
        state = {
            '_address': self._address,
            '_asm_instr': self._asm_instr,
            '_ir_instrs': self._ir_instrs
        }

        return state

    def __setstate__(self, state):
        self._address = state['_address']
        self._asm_instr = state['_asm_instr']
        self._ir_instrs = state['_ir_instrs']
