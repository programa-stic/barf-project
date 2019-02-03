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

from __future__ import absolute_import
from __future__ import print_function

import random

from barf.core.reil import ReilImmediateOperand
from barf.core.reil import ReilMnemonic
from barf.core.reil import ReilRegisterOperand
from barf.utils.utils import extract_sign_bit
from barf.utils.utils import extract_value
from barf.utils.utils import insert_value
from barf.utils.utils import twos_complement


DEBUG = False


class ReilCpuZeroDivisionError(Exception):
    pass


class ReilCpuInvalidAddressError(Exception):
    pass


class ReilCpuInvalidInstruction(Exception):
    pass


class ReilCpu(object):

    def __init__(self, memory, arch=None):
        # Reil memory instance.
        self.__mem = memory

        # Architecture information.
        self.__arch = arch

        # Registers.
        self.__regs = dict()
        self.__regs_written = set()
        self.__regs_read = set()

        # Instruction implementation.
        self.__executors = {
            # Arithmetic Instructions
            ReilMnemonic.ADD: self.__execute_binary_op,
            ReilMnemonic.SUB: self.__execute_binary_op,
            ReilMnemonic.MUL: self.__execute_binary_op,
            ReilMnemonic.DIV: self.__execute_binary_op,
            ReilMnemonic.MOD: self.__execute_binary_op,
            ReilMnemonic.BSH: self.__execute_bsh,

            # Bitwise Instructions
            ReilMnemonic.AND: self.__execute_binary_op,
            ReilMnemonic.OR:  self.__execute_binary_op,
            ReilMnemonic.XOR: self.__execute_binary_op,

            # Data Transfer Instructions
            ReilMnemonic.LDM: self.__execute_ldm,
            ReilMnemonic.STM: self.__execute_stm,
            ReilMnemonic.STR: self.__execute_str,

            # Conditional Instructions
            ReilMnemonic.BISZ: self.__execute_bisz,
            ReilMnemonic.JCC:  self.__execute_jcc,

            # Other Instructions
            ReilMnemonic.UNDEF: self.__execute_undef,
            ReilMnemonic.UNKN:  self.__execute_unkn,
            ReilMnemonic.NOP:   self.__execute_skip,

            # Extensions
            ReilMnemonic.SEXT: self.__execute_sext,
            ReilMnemonic.SDIV: self.__execute_binary_op,
            ReilMnemonic.SMOD: self.__execute_binary_op,
            ReilMnemonic.SMUL: self.__execute_binary_op,
        }

    def execute(self, instr):
        if DEBUG:
            print("0x%08x:%02x : %s" % (instr.address >> 8,
                                        instr.address & 0xff,
                                        instr))

        next_addr = self.__executors[instr.mnemonic](instr)

        return next_addr

    def reset(self):
        self.__regs = dict()
        self.__regs_written = set()
        self.__regs_read = set()

    # Properties
    # ======================================================================== #
    @property
    def registers(self):
        return self.__regs

    @registers.setter
    def registers(self, value):
        self.__regs = value

    @property
    def memory(self):
        return self.__mem

    @memory.setter
    def memory(self, value):
        self.__mem = value

    @property
    def read_registers(self):
        return self.__regs_read

    @property
    def written_registers(self):
        return self.__regs_written

    # Read/Write methods
    # ======================================================================== #
    def read_operand(self, operand):
        if isinstance(operand, ReilRegisterOperand):
            value = self.__read_register(operand)
        elif isinstance(operand, ReilImmediateOperand):
            value = operand.immediate
        else:
            raise Exception("Invalid operand type : %s" % str(operand))

        return value

    def write_operand(self, operand, value):
        if isinstance(operand, ReilRegisterOperand):
            self.__write_register(operand, value)
        else:
            raise Exception("Invalid operand type : %s" % str(operand))

    def read_memory(self, address, size):
        value = self.__mem.read(address, size)

        if DEBUG:
            self.__debug_read_memory(address, size, value)

        return value

    def write_memory(self, address, size, value):
        self.__mem.write(address, size, value)

        if DEBUG:
            self.__debug_write_memory(address, size, value)

    # Read/Write auxiliary methods
    # ======================================================================== #
    def __get_register_info(self, register):
        if self.__arch and register.name in self.__arch.alias_mapper:
            base_register, offset = self.__arch.alias_mapper[register.name]
            base_size = self.__arch.registers_size[base_register]
        else:
            base_register, offset = register.name, 0
            base_size = register.size

        return base_register, base_size, offset

    def __get_register_value(self, register):
        base_register, base_size, offset = self.__get_register_info(register)

        if base_register not in self.__regs:
            self.__regs[base_register] = random.randint(0, 2**base_size - 1)

        base_value = self.__regs[base_register]

        return base_register, base_value, offset

    def __read_register(self, register):
        base_register, base_value, offset = self.__get_register_value(register)
        value = extract_value(base_value, offset, register.size)

        # Keep track of native register reads.
        if self.__arch and register.name in self.__arch.registers_gp_all:
            self.__regs_read.add(register.name)

        if DEBUG:
            self.__debug_read_operand(base_register, register.name, value)

        return value

    def __write_register(self, register, value):
        base_register, base_value, offset = self.__get_register_value(register)
        base_value_new = insert_value(base_value, value, offset, register.size)

        self.__regs[base_register] = base_value_new

        # Keep track of native register writes.
        if self.__arch and register.name in self.__arch.registers_gp_all:
            self.__regs_written.add(register.name)

        if DEBUG:
            self.__debug_write_operand(base_register, register.name, value)

    # Debug methods
    # ======================================================================== #
    def __debug_read_operand(self, base_register, register, value):
        base_value = self.__regs[base_register]
        # taint = "T" if self.__tainter.get_register_taint(register) else "-"
        taint = "x"

        params = {
            "indent":        " " * 10,
            "register":      register,
            "value":         value,
            "base_register": base_register,
            "base_value":    base_value,
            "taint":         taint
        }

        fmt = "{indent}r{{ {register:s} = {value:08x} [{taint:s}] " + \
              "({base_register:s} = {base_value:08x})}}"

        print(fmt.format(**params))

    def __debug_write_operand(self, base_register, register, value):
        base_value = self.__regs[base_register]
        # taint = "T" if self.__tainter.get_register_taint(register) else "-"
        taint = "x"

        params = {
            "indent":        " " * 10,
            "register":      register,
            "value":         value,
            "base_register": base_register,
            "base_value":    base_value,
            "taint":         taint
        }

        fmt = "{indent}w{{ {register:s} = {value:08x} [{taint:s}] " + \
              "({base_register:s} = {base_value:08x})}}"

        print(fmt.format(**params))

    def __debug_read_memory(self, address, size, value):
        # taint = "T" if self.__tainter.get_memory_taint(address, size) else "-"
        taint = "x"

        params = {
            "indent":  " " * 10,
            "address": address,
            "value":   value,
            "taint":   taint
        }

        fmt = "{indent}r{{ m[{address:08x}] = {value:08x} [{taint:s}]}}"

        print(fmt.format(**params))

    def __debug_write_memory(self, address, size, value):
        # taint = "T" if self.__tainter.get_memory_taint(address, size) else "-"
        taint = "x"

        params = {
            "indent":  " " * 10,
            "address": address,
            "value":   value,
            "taint":   taint
        }

        fmt = "{indent}w{{ m[{address:08x}] = {value:08x} [{taint:s}]}}"

        print(fmt.format(**params))

    # ======================================================================== #
    # REIL instructions implementation
    # ======================================================================== #

    # Arithmetic instructions
    # ======================================================================== #
    def __execute_bsh(self, instr):
        """Execute BSH instruction.
        """
        op0_val = self.read_operand(instr.operands[0])
        op1_val = self.read_operand(instr.operands[1])

        op1_size = instr.operands[1].size

        # Check sign bit.
        if extract_sign_bit(op1_val, op1_size) == 0:
            op2_val = op0_val << op1_val
        else:
            op2_val = op0_val >> twos_complement(op1_val, op1_size)

        self.write_operand(instr.operands[2], op2_val)

        return None

    # Bitwise instructions
    # ======================================================================== #
    def __signed_div(self, oprnd0, oprnd1, result_size):
        op0_val = self.read_operand(oprnd0)
        op1_val = self.read_operand(oprnd1)

        op0_sign = op0_val >> oprnd0.size-1
        op1_sign = op1_val >> oprnd1.size-1
        result_sign = op0_sign ^ op1_sign

        if op0_sign == 0x1:
            op0_tmp = twos_complement(op0_val, oprnd0.size)
        else:
            op0_tmp = op0_val

        if op1_sign == 0x1:
            op1_tmp = twos_complement(op1_val, oprnd1.size)
        else:
            op1_tmp = op1_val

        result_tmp = op0_tmp // op1_tmp

        if result_sign == 0x1:
            result = twos_complement(result_tmp, result_size)
        else:
            result = result_tmp

        return result & (2**result_size-1)

    def __signed_mod(self, oprnd0, oprnd1, result_size):
        op0_val = self.read_operand(oprnd0)
        op1_val = self.read_operand(oprnd1)
        quotient = self.__signed_div(oprnd0, oprnd1, result_size)

        remainder = op0_val - (op1_val * quotient)

        return remainder & (2**result_size-1)

    def __signed_mul(self, oprnd0, oprnd1, result_size):
        op0_val = self.read_operand(oprnd0)
        op1_val = self.read_operand(oprnd1)

        op0_sign = op0_val >> oprnd0.size-1
        op1_sign = op1_val >> oprnd1.size-1
        result_sign = op0_sign ^ op1_sign

        if op0_sign == 0x1:
            op0_tmp = twos_complement(op0_val, oprnd0.size)
        else:
            op0_tmp = op0_val

        if op1_sign == 0x1:
            op1_tmp = twos_complement(op1_val, oprnd1.size)
        else:
            op1_tmp = op1_val

        result_tmp = op0_tmp * op1_tmp

        if result_sign == 0x1:
            result = twos_complement(result_tmp, result_size)
        else:
            result = result_tmp

        return result & (2**result_size-1)

    def __execute_binary_op(self, instr):
        op_map = {
            ReilMnemonic.ADD: lambda a, b: a + b,
            ReilMnemonic.SUB: lambda a, b: a - b,
            ReilMnemonic.MUL: lambda a, b: a * b,   # unsigned multiplication
            ReilMnemonic.DIV: lambda a, b: a // b,  # unsigned division
            ReilMnemonic.MOD: lambda a, b: a % b,   # unsigned modulo

            ReilMnemonic.AND: lambda a, b: a & b,
            ReilMnemonic.OR:  lambda a, b: a | b,
            ReilMnemonic.XOR: lambda a, b: a ^ b,
        }

        op0_val = self.read_operand(instr.operands[0])
        op1_val = self.read_operand(instr.operands[1])

        if instr.mnemonic in [ReilMnemonic.DIV, ReilMnemonic.MOD] and op1_val == 0:
            raise ReilCpuZeroDivisionError()

        if instr.mnemonic in [ReilMnemonic.SDIV]:
            op2_val = self.__signed_div(instr.operands[0], instr.operands[1], instr.operands[2].size)
        elif instr.mnemonic in [ReilMnemonic.SMOD]:
            op2_val = self.__signed_mod(instr.operands[0], instr.operands[1], instr.operands[2].size)
        elif instr.mnemonic in [ReilMnemonic.SMUL]:
            op2_val = self.__signed_mul(instr.operands[0], instr.operands[1], instr.operands[2].size)
        else:
            op2_val = op_map[instr.mnemonic](op0_val, op1_val)

        self.write_operand(instr.operands[2], op2_val)

        return None

    # Data transfer instructions
    # ======================================================================== #
    def __execute_ldm(self, instr):
        """Execute LDM instruction.
        """
        assert instr.operands[0].size == self.__mem.address_size
        assert instr.operands[2].size in [8, 16, 32, 64, 128, 256]

        # Memory address.
        op0_val = self.read_operand(instr.operands[0])
        # Data.
        op2_val = self.read_memory(op0_val, instr.operands[2].size // 8)

        self.write_operand(instr.operands[2], op2_val)

        return None

    def __execute_stm(self, instr):
        """Execute STM instruction.
        """
        assert instr.operands[0].size in [8, 16, 32, 64, 128, 256]
        assert instr.operands[2].size == self.__mem.address_size

        op0_val = self.read_operand(instr.operands[0])  # Data.
        op2_val = self.read_operand(instr.operands[2])  # Memory address.

        op0_size = instr.operands[0].size

        self.write_memory(op2_val, op0_size // 8, op0_val)

        return None

    def __execute_str(self, instr):
        """Execute STR instruction.
        """
        op0_val = self.read_operand(instr.operands[0])

        self.write_operand(instr.operands[2], op0_val)

        return None

    # Conditional instructions
    # ======================================================================== #
    def __execute_bisz(self, instr):
        """Execute BISZ instruction.
        """
        op0_val = self.read_operand(instr.operands[0])

        op2_val = 1 if op0_val == 0 else 0

        self.write_operand(instr.operands[2], op2_val)

        return None

    def __execute_jcc(self, instr):
        """Execute JCC instruction.
        """
        op0_val = self.read_operand(instr.operands[0])  # Branch condition.
        op2_val = self.read_operand(instr.operands[2])  # Target address.

        return op2_val if op0_val != 0 else None

    # Other instructions
    # ======================================================================== #
    def __execute_undef(self, instr):
        """Execute UNDEF instruction.
        """
        op2_val = random.randint(0, instr.operands[2].size)

        self.write_operand(instr.operands[2], op2_val)

        return None

    def __execute_unkn(self, instr):
        """Execute UNKN instruction.
        """
        raise ReilCpuInvalidInstruction()

    def __execute_skip(self, instr):
        """Skip instruction.
        """
        return None

    # REIL extension instructions
    # ======================================================================== #
    def __execute_sext(self, instr):
        """Execute SEXT instruction.
        """
        op0_size = instr.operands[0].size
        op2_size = instr.operands[2].size

        op0_val = self.read_operand(instr.operands[0])
        op0_msb = extract_sign_bit(op0_val, op0_size)

        op2_mask = (2**op2_size-1) & ~(2**op0_size-1) if op0_msb == 1 else 0x0

        op2_val = op0_val | op2_mask

        self.write_operand(instr.operands[2], op2_val)

        return None
