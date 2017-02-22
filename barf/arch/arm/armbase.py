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
This module contains all the classes that handle the ARM instruction
representation.

"""
from barf.arch import ARCH_ARM_MODE_ARM
from barf.arch import ARCH_ARM_MODE_THUMB
from barf.arch import ArchitectureInformation

# Used in CS->BARF translator
arm_alias_reg_map = {
     "a1" : "r0",
     "a2" : "r1",
     "a3" : "r2",
     "a4" : "r3",

     "v1" : "r4",
     "v2" : "r5",
     "v3" : "r6",
     "v4" : "r7",
     "v5" : "r8",
     "v6" : "r9",
     "v7" : "r10",
     "v8" : "r11",

     "sb" : "r9",
     "sl" : "r10",
     "fp" : "r11",
     "ip" : "r12",

     "sp" : "r13",
     "lr" : "r14",
     "pc" : "r15",
}

ARM_COND_CODE_EQ = 0
ARM_COND_CODE_NE = 1
ARM_COND_CODE_CS = 2
ARM_COND_CODE_CC = 3
ARM_COND_CODE_MI = 4
ARM_COND_CODE_PL = 5
ARM_COND_CODE_VS = 6
ARM_COND_CODE_VC = 7
ARM_COND_CODE_HI = 8
ARM_COND_CODE_LS = 9
ARM_COND_CODE_GE = 10
ARM_COND_CODE_LT = 11
ARM_COND_CODE_GT = 12
ARM_COND_CODE_LE = 13
ARM_COND_CODE_AL = 14
ARM_COND_CODE_HS = 15
ARM_COND_CODE_LO = 16

cc_mapper = {
    "eq" : ARM_COND_CODE_EQ,
    "ne" : ARM_COND_CODE_NE,
    "cs" : ARM_COND_CODE_CS,
    "hs" : ARM_COND_CODE_HS,
    "cc" : ARM_COND_CODE_CC,
    "lo" : ARM_COND_CODE_LO,
    "mi" : ARM_COND_CODE_MI,
    "pl" : ARM_COND_CODE_PL,
    "vs" : ARM_COND_CODE_VS,
    "vc" : ARM_COND_CODE_VC,
    "hi" : ARM_COND_CODE_HI,
    "ls" : ARM_COND_CODE_LS,
    "ge" : ARM_COND_CODE_GE,
    "lt" : ARM_COND_CODE_LT,
    "gt" : ARM_COND_CODE_GT,
    "le" : ARM_COND_CODE_LE,
    "al" : ARM_COND_CODE_AL,
}

cc_inverse_mapper = {v: k for k, v in cc_mapper.items()}

ARM_LDM_STM_IA = 0
ARM_LDM_STM_IB = 1
ARM_LDM_STM_DA = 2
ARM_LDM_STM_DB = 3
ARM_LDM_STM_FD = 4
ARM_LDM_STM_FA = 5
ARM_LDM_STM_ED = 6
ARM_LDM_STM_EA = 7

ldm_stm_am_mapper = {
    "ia" : ARM_LDM_STM_IA,
    "ib" : ARM_LDM_STM_IB,
    "da" : ARM_LDM_STM_DA,
    "db" : ARM_LDM_STM_DB,
    "fd" : ARM_LDM_STM_FD,
    "fa" : ARM_LDM_STM_FA,
    "ed" : ARM_LDM_STM_ED,
    "ea" : ARM_LDM_STM_EA,
}

ldm_stm_am_inverse_mapper = {v: k for k, v in ldm_stm_am_mapper.items()}

ldm_stack_am_to_non_stack_am = {
    ARM_LDM_STM_FA : ARM_LDM_STM_DA,
    ARM_LDM_STM_FD : ARM_LDM_STM_IA,
    ARM_LDM_STM_EA : ARM_LDM_STM_DB,
    ARM_LDM_STM_ED : ARM_LDM_STM_IB,
}

stm_stack_am_to_non_stack_am = {
    ARM_LDM_STM_ED : ARM_LDM_STM_DA,
    ARM_LDM_STM_EA : ARM_LDM_STM_IA,
    ARM_LDM_STM_FD : ARM_LDM_STM_DB,
    ARM_LDM_STM_FA : ARM_LDM_STM_IB,
}

ARM_MEMORY_INDEX_OFFSET = 0
ARM_MEMORY_INDEX_PRE = 1
ARM_MEMORY_INDEX_POST = 2


class ArmArchitectureInformation(ArchitectureInformation):
    """This class describe the ARM architecture."""

    regs_32 = [
        ("r0", 32),
        ("r1", 32),
        ("r2", 32),
        ("r3", 32),
        ("r4", 32),
        ("r5", 32),
        ("r6", 32),
        ("r7", 32),
        ("r8", 32),
        ("r9", 32),
        ("r10", 32),
        ("r11", 32),
        ("r12", 32),
        ("r13", 32),
        ("r14", 32),
        ("r15", 32),
        ("apsr", 32),
    ]

    regs_32_alias = [
        ("sp", 32),
        ("lr", 32),
        ("pc", 32),
        ("fp", 32),
    ]
    regs_flags = [
        ("nf", 1),
        ("zf", 1),
        ("cf", 1),
        ("vf", 1),
    ]

    def __init__(self, architecture_mode):
        self._arch_mode = architecture_mode

        self._registers_all = []
        self._registers_gp_all = []
        self._registers_gp_base = []
        self._registers_flags = []

        self._registers_size = {}

        self._alias_mapper = {}

        self._load_registers()

        self._load_alias_mapper()

    @property
    def architecture_mode(self):
        return self._arch_mode

    @property
    def architecture_size(self):
        arch_size_map = {
            ARCH_ARM_MODE_ARM : 32,
            ARCH_ARM_MODE_THUMB : 32,
        }

        return arch_size_map[self._arch_mode]

    @property
    def operand_size(self):
        operand_size_map = {
            ARCH_ARM_MODE_ARM : 32,
            ARCH_ARM_MODE_THUMB : 32,
        }

        return operand_size_map[self._arch_mode]

    @property
    def address_size(self):
        address_size_map = {
            ARCH_ARM_MODE_ARM : 32,
            ARCH_ARM_MODE_THUMB : 32,
        }

        return address_size_map[self._arch_mode]

    @property
    def registers_all(self):
        """Return all registers.
        """
        return self._registers_all

    @property
    def registers_gp_all(self):
        """Return all general purpose registers.
        """
        return self._registers_gp_all

    @property
    def registers_gp_base(self):
        """Return base general purpose registers.
        """
        return self._registers_gp_base

    @property
    def registers_flags(self):
        """Return flag registers.
        """
        return self._registers_flags

    @property
    def registers_size(self):
        """Return the size of all registers.
        """
        return self._registers_size

    @property
    def alias_mapper(self):
        """Return registers alias mapper.
        """
        return self._alias_mapper

    @property
    def max_instruction_size(self):
        """Return the maximum instruction size in bytes.
        """
        instruction_size_map = {
            ARCH_ARM_MODE_ARM : 4,
            ARCH_ARM_MODE_THUMB : 2,
        }

        return instruction_size_map[self._arch_mode]

    def instr_is_ret(self, instruction):
        is_ret = False

        # ARM: "POP reg, {reg*, pc}" instr.
        if instruction.mnemonic == "pop" and \
           ("pc" in str(instruction.operands[1]) or \
           "r15" in str(instruction.operands[1])):
            is_ret = True

        # ARM: "LDR pc, *" instr.
        if instruction.mnemonic == "ldr" and \
           ("pc" in str(instruction.operands[0]) or \
           "r15" in str(instruction.operands[0])):
            is_ret = True

        return is_ret

    def instr_is_call(self, instruction):
        return instruction.mnemonic == "bl"

    def instr_is_halt(self, instruction):
        return False

    def instr_is_branch(self, instruction):
        branch_instr = [
            "b", "bx", "bne", "beq", "bpl", "ble", "bcs", "bhs", "blt", "bge",
            "bhi", "blo", "bls"
        ]

        return instruction.mnemonic_full in branch_instr

    def instr_is_branch_cond(self, instruction):
        branch_instr = [
            "bne", "beq", "bpl", "ble", "bcs", "bhs", "blt", "bge",
            "bhi", "blo", "bls"
        ]

        return instruction.mnemonic_full in branch_instr

    def _load_alias_mapper(self):
        alias_mapper = {
            "fp" : ("r11", 0),
            "sp" : ("r13", 0),
            "lr" : ("r14", 0),
            "pc" : ("r15", 0),
        }

        flags_reg = "apsr"

        flags_mapper = {
            "nf": (flags_reg, 31),
            "zf": (flags_reg, 30),
            "cf": (flags_reg, 29),
            "vf": (flags_reg, 28),
        }

        alias_mapper.update(flags_mapper)

        self._alias_mapper = alias_mapper

    def _load_registers(self):

        registers_all = self.regs_flags + self.regs_32 + self.regs_32_alias
        registers_gp_all = self.regs_32 + self.regs_32_alias
        registers_gp_base = self.regs_32

        for name, size in registers_all:
            self._registers_all.append(name)
            self._registers_size[name] = size

        for name, size in registers_gp_all:
            self._registers_gp_all.append(name)
            self._registers_size[name] = size

        for name, size in registers_gp_base:
            self._registers_gp_base.append(name)
            self._registers_size[name] = size

        self._registers_flags = [name for name, _ in self.regs_flags]

    def registers(self):
        return []


class ArmInstruction(object):
    """Representation of ARM instruction."""

    __slots__ = [
        '_orig_instr',
        '_mnemonic',
        '_operands',
        '_bytes',
        '_size',
        '_address',
        '_arch_mode',
        '_condition_code',
        '_update_flags',
        '_ldm_stm_addr_mode',
    ]

    def __init__(self, orig_instr, mnemonic, operands, arch_mode):
        self._orig_instr = orig_instr
        self._mnemonic = mnemonic
        self._operands = operands
        self._bytes = ""
        self._size = 4 # TODO: Thumb
        self._address = None
        self._arch_mode = arch_mode
        self._condition_code = None
        self._update_flags = False
        self._ldm_stm_addr_mode = None

    @property
    def orig_instr(self):
        """Get instruction string before parsing."""
        return self._orig_instr

    @property
    def mnemonic(self):
        """Get instruction mnemonic."""
        return self._mnemonic

    @property
    def mnemonic_full(self):
        """Get instruction mnemonic with condition code."""
        return self._mnemonic + cc_inverse_mapper[self.condition_code]

    @property
    def operands(self):
        """Get instruction operands."""
        return self._operands

    @operands.setter
    def operands(self, value):
        """Set instruction operands."""
        self._operands = value

    @property
    def bytes(self):
        """Get instruction byte representation."""
        return self._bytes

    @bytes.setter
    def bytes(self, value):
        """Set instruction byte representation."""
        self._bytes = value

    @property
    def size(self):
        """Get instruction size."""
        return self._size

    @size.setter
    def size(self, value):
        """Set instruction size."""
        self._size = value

    @property
    def address(self):
        """Get instruction address."""
        return self._address

    @address.setter
    def address(self, value):
        """Set instruction address."""
        self._address = value

    @property
    def condition_code(self):
        return self._condition_code

    @condition_code.setter
    def condition_code(self, value):
        self._condition_code = value

    @property
    def update_flags(self):
        return self._update_flags

    @update_flags.setter
    def update_flags(self, value):
        self._update_flags = value

    @property
    def ldm_stm_addr_mode(self):
        return self._ldm_stm_addr_mode

    @ldm_stm_addr_mode.setter
    def ldm_stm_addr_mode(self, value):
        self._ldm_stm_addr_mode = value

    def __str__(self):
        operands_str = ", ".join([str(oprnd) for oprnd in self._operands])

        string = self.mnemonic
        if self.condition_code is not None:
            string += cc_inverse_mapper[self.condition_code]
        if self.ldm_stm_addr_mode is not None:
            string += ldm_stm_am_inverse_mapper[self.ldm_stm_addr_mode]
        string += " " + operands_str if operands_str else ""

        return string

    def __eq__(self, other):
        return  self.prefix == other.prefix and \
                self.mnemonic == other.mnemonic and \
                self.operands == other.operands and \
                self.bytes == other.bytes and \
                self.size == other.size and \
                self.address == other.address

    def __ne__(self, other):
        return not self.__eq__(other)

    @property
    def prefix(self):
        return ""


class ArmOperand(object):
    """Representation of ARM operand."""

    __slots__ = [
        '_modifier',
        '_size',
    ]

    def __init__(self, modifier):
        self._modifier = modifier
        self._size = None

    @property
    def modifier(self):
        """Get operand modifier."""
        return self._modifier

    @modifier.setter
    def modifier(self, value):
        """Set operand modifier."""
        self._modifier = value

    @property
    def size(self):
        """Get operand size."""
        return self._size

    @size.setter
    def size(self, value):
        """Set operand size."""
        self._size = value

    def to_string(self, **kwargs):
        return self.__str__()


class ArmImmediateOperand(ArmOperand):
    """Representation of ARM immediate operand."""

    __slots__ = [
        '_immediate',
        '_base_hex',
        '_size',
    ]

    def __init__(self, immediate, size=None):
        super(ArmImmediateOperand, self).__init__("")

        self._base_hex = True

        if type(immediate) == str:
            immediate = immediate.replace("#", "")
            if '0x' in immediate:
                immediate = int(immediate, 16)
            else:
                immediate = int(immediate)
                self._base_hex = False

        assert type(immediate) in [int, long], "Invalid immediate value type."

        self._immediate = immediate
        self._size = size

    @property
    def immediate(self):
        """Get immediate."""
        if not self._size:
            raise Exception("Operand size missing.")

        return self._immediate

    def to_string(self, **kwargs):
        if not self._size:
            raise Exception("Operand size missing.")

        immediate_format = kwargs.get("immediate_format", "hex")

        if immediate_format == "hex":
            # string = "#" + hex(self._immediate)
            string = hex(self._immediate)
        elif immediate_format == "dec":
            string = str(self._immediate)
        else:
            raise Exception("Invalid immediate format: {}".format(imm_fmt))

        return string[:-1] if string[-1] == 'L' else string

    def __str__(self):
        if not self._size:
            raise Exception("Operand size missing.")

        string = '#' + (hex(self._immediate) if self._base_hex else str(self._immediate))

        return string[:-1] if string[-1] == 'L' else string

    def __eq__(self, other):
        return  self.immediate == other.immediate

    def __ne__(self, other):
        return not self.__eq__(other)


class ArmRegisterOperand(ArmOperand):
    """Representation of ARM register operand."""

    __slots__ = [
        '_name',
        '_size',
        '_wb',
    ]

    def __init__(self, name, size=None):
        super(ArmRegisterOperand, self).__init__("")

        self._name = name
        self._size = size
        self._wb = False

    @property
    def name(self):
        """Get register name."""
        if not self._size:
            raise Exception("Operand size missing.")

        return self._name

    @property
    def wb(self):
        return self._wb

    @wb.setter
    def wb(self, value):
        self._wb = value

    def __str__(self):
        if not self._size:
            raise Exception("Operand size missing.")

        string  = self._modifier + " " if self._modifier else ""
        string += self._name

        return string

    def __eq__(self, other):
        return  self.modifier == other.modifier and \
                self.size == other.size and \
                self.name == other.name

    def __ne__(self, other):
        return not self.__eq__(other)


class ArmRegisterListOperand(ArmOperand):
    """Representation of ARM register operand."""

    __slots__ = [
        '_reg_list',
        '_size',
    ]

    def __init__(self, reg_list, size=None):
        super(ArmRegisterListOperand, self).__init__("")

        self._reg_list = reg_list
        self._size = size

    @property
    def reg_list(self):
        """Get register list."""
        if not self._size:
            raise Exception("Operand size missing.")

        return self._reg_list

    def __str__(self):
        if not self._size:
            raise Exception("Operand size missing.")

        string = "{"
        for i in range(len(self._reg_list)):
            if i > 0:
                string += ", "
            reg_range = self._reg_list[i]
            string += str(reg_range[0])
            if len(reg_range) > 1:
                string += " - " + str(reg_range[1])
        string += "}"

        return string

    def __eq__(self, other):
        return  self._reg_list == other._reg_list and \
                self.size == other.size

    def __ne__(self, other):
        return not self.__eq__(other)


class ArmShiftedRegisterOperand(ArmOperand):
    """Representation of ARM register operand."""

    __slots__ = [
        '_base_reg',
        '_shift_type',
        '_shift_amount',
        '_size',
    ]

    def __init__(self, base_reg, shift_type, shift_amount, size=None):
        super(ArmShiftedRegisterOperand, self).__init__("")

        self._base_reg = base_reg
        self._shift_type = shift_type
        self._shift_amount = shift_amount
        self._size = size

    @property
    def base_reg(self):
        """Get base register."""
        if not self._size:
            raise Exception("Operand size missing.")
        return self._base_reg

    @property
    def shift_type(self):
        """Get shift type."""
        if not self._size:
            raise Exception("Operand size missing.")
        return self._shift_type

    @property
    def shift_amount(self):
        """Get shift amount."""
        if not self._size:
            raise Exception("Operand size missing.")
        return self._shift_amount

    def __str__(self):
        if not self._size:
            raise Exception("Operand size missing.")

        string  = str(self._base_reg) + ", " + str(self._shift_type)
        if self._shift_amount:
            string += " " + str(self._shift_amount)

        return string

    def __eq__(self, other):
        return  self._base_reg == other._base_reg  and \
                self._shift_type == other._shift_type  and \
                self._shift_amount == other._shift_amount


    def __ne__(self, other):
        return not self.__eq__(other)


class ArmMemoryOperand(ArmOperand):
    """Representation of ARM memory operand."""

    __slots__ = [
        '_base_reg',
        '_index_type',
        '_displacement',
        '_disp_minus',
        '_size',
    ]

    def __init__(self, base_reg, index_type, displacement, disp_minus = False, size=None):
        super(ArmMemoryOperand, self).__init__("")

        self._base_reg = base_reg
        self._index_type = index_type
        self._displacement = displacement
        self._disp_minus = disp_minus
        self._size = size

    @property
    def base_reg(self):
        """Get base register."""
        if not self._size:
            raise Exception("Operand size missing.")

        return self._base_reg

    @property
    def displacement(self):
        """Get displacement to the base register."""
        if not self._size:
            raise Exception("Operand size missing.")

        return self._displacement

    @property
    def index_type(self):
        """Get type of memory indexing."""
        if not self._size:
            raise Exception("Operand size missing.")

        return self._index_type

    @property
    def disp_minus(self):
        """Get sign of displacemnt."""
        if not self._size:
            raise Exception("Operand size missing.")

        return self._disp_minus


    def __str__(self):
        if not self._size:
            raise Exception("Operand size missing.")

        disp_str = "-" if self._disp_minus else ""
        disp_str += str(self._displacement)

        string = "[" + str(self._base_reg)

        if (self._index_type == ARM_MEMORY_INDEX_OFFSET):
            if self._displacement:
                string += ", " + disp_str
            string += "]"
        elif (self._index_type == ARM_MEMORY_INDEX_PRE):
            string += ", " + disp_str + "]!"
        elif (self._index_type == ARM_MEMORY_INDEX_POST):
            string += "], " + disp_str
        else:
            raise Exception("Unknown memory index type.")

        return string

    def __eq__(self, other):
        return  self._base_reg == other._base_reg  and \
                self._index_type == other._index_type  and \
                self._displacement == other._displacement


    def __ne__(self, other):
        return not self.__eq__(other)
