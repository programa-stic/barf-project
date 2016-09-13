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

# Display operands size in intruction
show_size = True

# TODO: Create module util and move this function there.
def split_address(address):
    return address >> 0x08, address & 0xff

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

    # Added Instructions
    RET   = 18

    # Extensions
    SEXT  = 19
    SDIV  = 20
    SMOD  = 21

    @staticmethod
    def to_string(mnemonic):
        """Return the string representation of the given mnemonic.
        """
        strings = {
            # Arithmetic Instructions
            ReilMnemonic.ADD : "add",
            ReilMnemonic.SUB : "sub",
            ReilMnemonic.MUL : "mul",
            ReilMnemonic.DIV : "div",
            ReilMnemonic.MOD : "mod",
            ReilMnemonic.BSH : "bsh",

            # Bitwise Instructions
            ReilMnemonic.AND : "and",
            ReilMnemonic.OR : "or",
            ReilMnemonic.XOR : "xor",

            # Data Transfer Instructions
            ReilMnemonic.LDM : "ldm",
            ReilMnemonic.STM : "stm",
            ReilMnemonic.STR : "str",

            # Conditional Instructions
            ReilMnemonic.BISZ : "bisz",
            ReilMnemonic.JCC : "jcc",

            # Other Instructions
            ReilMnemonic.UNKN  : "unkn" ,
            ReilMnemonic.UNDEF : "undef" ,
            ReilMnemonic.NOP : "nop" ,

            # Added Instructions
            ReilMnemonic.RET : "ret",

            # Extensions
            ReilMnemonic.SEXT : "sext",
            ReilMnemonic.SDIV : "sdiv",
            ReilMnemonic.SMOD : "smod",
        }

        return strings[mnemonic]

    @staticmethod
    def from_string(string):
        """Return the mnemonic represented by the given string.
        """
        mnemonics = {
            # Arithmetic Instructions
            "add" : ReilMnemonic.ADD,
            "sub" : ReilMnemonic.SUB,
            "mul" : ReilMnemonic.MUL,
            "div" : ReilMnemonic.DIV,
            "mod" : ReilMnemonic.MOD,
            "bsh" : ReilMnemonic.BSH,

            # Bitwise Instructions
            "and" : ReilMnemonic.AND,
            "or" : ReilMnemonic.OR,
            "xor" : ReilMnemonic.XOR,

            # Data Transfer Instructions
            "ldm" : ReilMnemonic.LDM,
            "stm" : ReilMnemonic.STM,
            "str" : ReilMnemonic.STR,

            # Conditional Instructions
            "bisz" : ReilMnemonic.BISZ,
            "jcc" : ReilMnemonic.JCC,

            # Other Instructions
            "unkn" : ReilMnemonic.UNKN,
            "undef" : ReilMnemonic.UNDEF,
            "nop" : ReilMnemonic.NOP,

            # Added Instructions
            "ret" : ReilMnemonic.RET,

            # Added Instructions
            "sext" : ReilMnemonic.SEXT,
            "sdiv" : ReilMnemonic.SDIV,
            "smod" : ReilMnemonic.SMOD,
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

    # Added Instructions
    ReilMnemonic.RET,

    # Extensions
    ReilMnemonic.SEXT,
    ReilMnemonic.SDIV,
    ReilMnemonic.SMOD,
)

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
            size_str = str(oprnd.size) if oprnd.size else ""

            sizes = {
                256 : "DDQWORD",
                128 : "DQWORD",
                72  : "POINTER",
                64  : "QWORD",
                40  : "POINTER",
                32  : "DWORD",
                16  : "WORD",
                8   : "BYTE",
                1   : "BIT",
                ""  : "UNK",
            }

            if isinstance(oprnd, ReilEmptyOperand):
                return "%s" % (oprnd_str)
            else:
                return "%s %s" % (sizes[oprnd.size if oprnd.size else ""], oprnd_str)

        mnemonic_str = ReilMnemonic.to_string(self._mnemonic)

        if show_size:
            operands_str = ", ".join(map(print_oprnd, self._operands))
        else:
            operands_str = ", ".join(map(str, self._operands))

        return "%-5s [%s]" % (mnemonic_str, operands_str)

    def __hash__(self):
        return hash(str(self))

    def __getstate__(self):
        state = {}
        state['_mnemonic'] = self._mnemonic
        state['_operands'] = self._operands
        state['_comment'] = self._comment
        state['_address'] = self._address

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
        return  type(other) is type(self) and \
                self._size == other._size

    def __ne__(self, other):
        return not self.__eq__(other)

    def __getstate__(self):
        state = {}
        state['_size'] = self._size

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
        return  type(other) is type(self) and \
                self._size == other._size and \
                self._immediate == other._immediate

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
        return  type(other) is type(self) and \
                self._size == other._size and \
                self._name == other._name

    def __getstate__(self):
        state = super(ReilRegisterOperand, self).__getstate__()

        state['_name'] = self._name

        return state

    def __setstate__(self, state):
        super(ReilRegisterOperand, self).__setstate__(state)

        self._name = state['_name']


class ReilEmptyOperand(ReilRegisterOperand):

    """Representation of an IR instruction's empty operand.
    """

    def __init__(self):
        super(ReilEmptyOperand, self).__init__("EMPTY", size=None)


class ReilInstructionBuilder(object):

    """REIL Instruction Builder. Generate REIL instructions, easily.
    """

    # Arithmetic Instructions
    # ======================================================================== #
    def gen_add(self, src1, src2, dst):
        """Return an ADD instruction.
        """
        return self.build(ReilMnemonic.ADD, src1, src2, dst)

    def gen_sub(self, src1, src2, dst):
        """Return a SUB instruction.
        """
        return self.build(ReilMnemonic.SUB, src1, src2, dst)

    def gen_mul(self, src1, src2, dst):
        """Return a MUL instruction.
        """
        return self.build(ReilMnemonic.MUL, src1, src2, dst)

    def gen_div(self, src1, src2, dst):
        """Return a DIV instruction.
        """
        return self.build(ReilMnemonic.DIV, src1, src2, dst)

    def gen_mod(self, src1, src2, dst):
        """Return a MOD instruction.
        """
        return self.build(ReilMnemonic.MOD, src1, src2, dst)

    def gen_bsh(self, src1, src2, dst):
        """Return a BSH instruction.
        """
        return self.build(ReilMnemonic.BSH, src1, src2, dst)

    # Bitwise Instructions
    # ======================================================================== #
    def gen_and(self, src1, src2, dst):
        """Return an AND instruction.
        """
        return self.build(ReilMnemonic.AND, src1, src2, dst)

    def gen_or(self, src1, src2, dst):
        """Return an OR instruction.
        """
        return self.build(ReilMnemonic.OR, src1, src2, dst)

    def gen_xor(self, src1, src2, dst):
        """Return a XOR instruction.
        """
        return self.build(ReilMnemonic.XOR, src1, src2, dst)

    # Data Transfer Instructions
    # ======================================================================== #
    def gen_ldm(self, src, dst):
        """Return a LDM instruction.
        """
        return self.build(ReilMnemonic.LDM, src, ReilEmptyOperand(), dst)

    def gen_stm(self, src, dst):
        """Return a STM instruction.
        """
        return self.build(ReilMnemonic.STM, src, ReilEmptyOperand(), dst)

    def gen_str(self, src, dst):
        """Return a STR instruction.
        """
        return self.build(ReilMnemonic.STR, src, ReilEmptyOperand(), dst)

    # Conditional Instructions
    # ======================================================================== #
    def gen_bisz(self, src, dst):
        """Return a BISZ instruction.
        """
        return self.build(ReilMnemonic.BISZ, src, ReilEmptyOperand(), dst)

    def gen_jcc(self, src, dst):
        """Return a JCC instruction.
        """
        return self.build(ReilMnemonic.JCC, src, ReilEmptyOperand(), dst)

    # Other Instructions
    # ======================================================================== #
    def gen_unkn(self):
        """Return an UNKN instruction.
        """
        empty_reg = ReilEmptyOperand()

        return self.build(ReilMnemonic.UNKN, empty_reg, empty_reg, empty_reg)

    def gen_undef(self):
        """Return an UNDEF instruction.
        """
        empty_reg = ReilEmptyOperand()

        return self.build(ReilMnemonic.UNDEF, empty_reg, empty_reg, empty_reg)

    def gen_nop(self):
        """Return a NOP instruction.
        """
        empty_reg = ReilEmptyOperand()

        return self.build(ReilMnemonic.NOP, empty_reg, empty_reg, empty_reg)

    # Ad hoc Instructions
    # ======================================================================== #
    def gen_ret(self):
        """Return a RET instruction.
        """
        empty_reg = ReilEmptyOperand()

        return self.build(ReilMnemonic.RET, empty_reg, empty_reg, empty_reg)

    # Extensions
    # ======================================================================== #
    def gen_sext(self, src, dst):
        """Return a SEXT instruction.
        """
        empty_reg = ReilEmptyOperand()

        return self.build(ReilMnemonic.SEXT, src, empty_reg, dst)

    def gen_sdiv(self, src1, src2, dst):
        """Return a SDIV instruction.
        """
        return self.build(ReilMnemonic.SDIV, src1, src2, dst)

    def gen_smod(self, src1, src2, dst):
        """Return a SMOD instruction.
        """
        return self.build(ReilMnemonic.SMOD, src1, src2, dst)

    # Auxiliary functions
    # ======================================================================== #
    def build(self, mnemonic, oprnd1, oprnd2, oprnd3):
        """Return the specified instruction.
        """
        ins = ReilInstruction()

        ins.mnemonic = mnemonic
        ins.operands = [oprnd1, oprnd2, oprnd3]

        return ins


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
        # assemlber instruction is mapped to more than one REIL
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
        return  self.address == other.address and \
                self.asm_instr == other.asm_instr

    def __ne__(self, other):
        return not self.__eq__(other)

    def __getstate__(self):
        state = {}
        state['_address'] = self._address
        state['_asm_instr'] = self._asm_instr
        state['_ir_instrs'] = self._ir_instrs

        return state

    def __setstate__(self, state):
        self._address = state['_address']
        self._asm_instr = state['_asm_instr']
        self._ir_instrs = state['_ir_instrs']


class ReilSequence(object):

    """Reil instruction sequence.
    """

    def __init__(self):
        self.__sequence = []
        self.__next_seq_address = None

    def append(self, instruction):
        self.__sequence.append(instruction)

    def get(self, index):
        return self.__sequence[index]

    def dump(self):
        for instr in self.__sequence:
            base_addr, index = split_address(instr.address)

            print("{:08x}:{:02x}\t{}".format(base_addr, index, instr))

    @property
    def address(self):
        return self.__sequence[0].address if self.__sequence else None

    @property
    def next_sequence_address(self):
        return self.__next_seq_address

    @next_sequence_address.setter
    def next_sequence_address(self, address):
        self.__next_seq_address = address

    def __len__(self):
        return len(self.__sequence)

    def __iter__(self):
        for instr in self.__sequence:
            yield instr


class ReilContainerInvalidAddressError(Exception):
    pass


class ReilContainer(object):

    """Reil instruction container.
    """

    def __init__(self):
        self.__container = {}

    def add(self, sequence):
        base_addr, _ = split_address(sequence.address)

        if base_addr in self.__container.keys():
            raise Exception("Invalid sequence")

        self.__container[base_addr] = sequence

    def fetch(self, address):
        base_addr, index = split_address(address)

        if base_addr not in self.__container.keys():
            raise ReilContainerInvalidAddressError()

        return self.__container[base_addr].get(index)

    def get_next_address(self, address):
        base_addr, index = split_address(address)

        if base_addr not in self.__container.keys():
            raise Exception("Invalid address.")

        addr = address

        if index < len(self.__container[base_addr]) - 1:
            addr += 1
        else:
            addr = self.__container[base_addr].next_sequence_address

        return addr

    def dump(self):
        for base_addr in sorted(self.__container.keys()):
            self.__container[base_addr].dump()

            print("-" * 80)

    def __iter__(self):
        for addr in sorted(self.__container.keys()):
            for instr in self.__container[addr]:
                yield instr


def check_operands_size(instr, arch_size):
    """Enforce operands' size."""

    if instr.mnemonic in [  ReilMnemonic.ADD, ReilMnemonic.SUB,
                            ReilMnemonic.MUL, ReilMnemonic.DIV,
                            ReilMnemonic.MOD, ReilMnemonic.BSH,
                            ReilMnemonic.AND, ReilMnemonic.OR,
                            ReilMnemonic.XOR]:
        # operand0 : Source 1 (Literal or register)
        # operand1 : Source 2 (Literal or register)
        # operand2 : Destination resgister

        # Check that source operands have the same size.
        assert instr.operands[0].size == instr.operands[1].size, \
            "Invalid operands size: %s" % instr

    elif instr.mnemonic in [ReilMnemonic.LDM]:
        # operand0 : Source address (Literal or register)
        # operand1 : Empty register
        # operand2 : Destination register

        assert instr.operands[0].size == arch_size, \
            "Invalid operands size: %s" % instr

    elif instr.mnemonic in [ReilMnemonic.STM]:
        # operand0 : Value to store (Literal or register)
        # operand1 : Empty register
        # operand2 : Destination address (Literal or register)

        assert instr.operands[2].size == arch_size, \
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

        # FIX: operand2.size should be arch_size + 1 byte

        assert instr.operands[2].size == arch_size + 8, \
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
