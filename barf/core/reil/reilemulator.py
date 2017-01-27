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
This module contains all the necesary classes to emulate REIL
instructions. So far, it only handles concrete values.

The emulator is compose of two main classes. The emulator itself,
**ReilEmulator** and a memory component **ReilMemory**.

ReilEmulator
------------

It has two main methods, e.i., **emulate** and **emulate_lite**. The
first, emulates REIL instructions completely and takes as parameters a
list of instruction and a start address (REIL address). The second, is a
more performing emulation where the list of instruction is execute from
beginning to end not considering branches.

ReilMemory
----------

Byte addressable memory based on a dictionary.

"""

import logging
import random

from barf.core.reil.reil import ReilImmediateOperand
from barf.core.reil.reil import ReilMnemonic
from barf.core.reil.reil import ReilRegisterOperand
from barf.core.reil.reil import ReilContainerInvalidAddressError
from barf.utils.utils import extract_sign_bit
from barf.utils.utils import extract_value
from barf.utils.utils import insert_value
from barf.utils.utils import twos_complement

logger = logging.getLogger("reilemulator")

DEBUG = False
# DEBUG = True

REIL_MEMORY_ENDIANNESS_LE = 0x0     # Little Endian
REIL_MEMORY_ENDIANNESS_BE = 0x1     # Big Endian


class ReilMemory(object):

    """A REIL memory model (byte addressable).
    """

    def __init__(self, address_size):

        # TODO: Set endianness through a parameter.
        # TODO: Check that all addresses have size address_size.
        # TODO: Use endianness parameter.

        # Memory's address size.
        self.__address_size = address_size

        # Memory's endianness.
        self.__endianness = REIL_MEMORY_ENDIANNESS_LE

        # Dictionary that implements the memory itself.
        self._memory = {}

    # Read methods
    # ======================================================================== #
    def read(self, address, size):
        """Read arbitrary size content from memory.
        """
        value = 0x0

        for i in xrange(0, size):
            value = self._read_byte(address + i) << (i * 8) | value

        return value

    def _read_byte(self, address):
        """Read a byte from memory.
        """
        # Initialize memory location with a random value.
        if not address in self._memory:
            self._memory[address] = random.randint(0x00, 0xff)

        return self._memory[address]

    # Write methods
    # ======================================================================== #
    def write(self, address, size, value):
        """Write arbitrary size content to memory.
        """
        for i in xrange(0, size):
            self.__write_byte(address + i, (value >> (i * 8)) & 0xff)

    def __write_byte(self, address, value):
        """Write byte in memory.
        """
        self._memory[address] = value & 0xff

    # Misc methods
    # ======================================================================== #
    def reset(self):
        # Dictionary that implements the memory itself.
        self._memory = {}

    # Magic methods
    # ======================================================================== #
    def __str__(self):
        lines = []

        for addr in sorted(self._memory.keys()):
            lines += ["0x%08x : 0x%08x" % (addr, self._memory[addr])]

        return "\n".join(lines)


class ReilMemoryEx(ReilMemory):

    """Reil memory extended class"""

    def __init__(self, address_size):
        super(ReilMemoryEx, self).__init__(address_size)

        # Previous state of memory.
        self.__memory_prev = {}

        # Write operations counter.
        self.__write_count = 0

    # Read methods
    # ======================================================================== #
    def read_inverse(self, value, size):
        """Return a list of memory addresses that contain the specified
        value.

        """
        addr_candidates = [addr for addr, val in self._memory.items()
                                    if val == (value & 0xff)]
        addr_matchings = []

        for addr in addr_candidates:
            match = True

            for i in xrange(0, size):
                byte_curr = (value >> (i * 8)) & 0xff
                try:
                    match = self._memory[addr + i] == byte_curr
                except KeyError:
                    match = False

                if not match:
                    break

            if match:
                addr_matchings += [addr]

        return addr_matchings

    def try_read(self, address, size):
        """Try to read memory content at specified address.

        If any location was not written before, it returns a tuple
        (False, None). Otherwise, it returns (True, memory content).

        """
        value = 0x0

        for i in xrange(0, size):
            addr = address + i

            if addr in self._memory:
                value = self._read_byte(addr) << (i * 8) | value
            else:
                return False, None

        return True, value

    def try_read_prev(self, address, size):
        """Try to read previous memory content at specified address.

        If any location was not written before, it returns a tuple
        (False, None). Otherwise, it returns (True, memory content).

        """
        value = 0x0

        for i in xrange(0, size):
            addr = address + i

            if addr in self.__memory_prev:
                _, val_byte = self.__try_read_byte_prev(addr)
                value = val_byte << (i * 8) | value
            else:
                return False, None

        return True, value

    def __try_read_byte_prev(self, address):
        """Read previous value for memory location.

        Return a tuple (True, Byte) in case of successful read,
        (False, None) otherwise.

        """
        # Initialize memory location with a random value
        if not address in self.__memory_prev:
            return False, None

        return True, self.__memory_prev[address]

    # Write methods
    # ======================================================================== #
    def write(self, address, size, value):
        """Write arbitrary size content to memory.
        """
        for i in xrange(0, size):
            self.__write_byte(address + i, (value >> (i * 8)) & 0xff)

        self.__write_count += 1

    def __write_byte(self, address, value):
        """Write byte in memory.
        """
        # Save previous address content.
        if address in self._memory:
            self.__memory_prev[address] = self._memory[address]

        self._memory[address] = value & 0xff

    # Misc methods
    # ======================================================================== #
    def reset(self):
        super(ReilMemoryEx, self).reset()

        # Previous state of memory.
        self.__memory_prev = {}

        # Write operations counter.
        self.__write_count = 0

    def get_addresses(self):
        """Get accessed addresses.
        """
        return self._memory.keys()

    def get_write_count(self):
        """Get number of write operations performed on the memory.
        """
        return self.__write_count


class ReilCpuZeroDivisionError(Exception):
    pass


class ReilCpuInvalidAddressError(Exception):
    pass


class ReilCpuInvalidInstruction(Exception):
    pass


class ReilCpu(object):

    def __init__(self, arch, memory, tainter, emulator):
        # Architecture information.
        self.__arch = arch

        # Reil emulator instance.
        self.__emu = emulator

        # Reil memory instance.
        self.__mem = memory

        # Reil tainter instance.
        self.__tainter = tainter

        # Registers.
        self.__regs = dict()
        self.__regs_written = set()
        self.__regs_read = set()

        # Instructions pre and post handlers.
        self.__instr_handler_pre = None, None
        self.__instr_handler_post = None, None

        # Instruction implementation.
        self.__executors = {
            # Arithmetic Instructions
            ReilMnemonic.ADD  : self.__execute_binary_op,
            ReilMnemonic.SUB  : self.__execute_binary_op,
            ReilMnemonic.MUL  : self.__execute_binary_op,
            ReilMnemonic.DIV  : self.__execute_binary_op,
            ReilMnemonic.SDIV : self.__execute_binary_op,
            ReilMnemonic.MOD  : self.__execute_binary_op,
            ReilMnemonic.SMOD : self.__execute_binary_op,
            ReilMnemonic.BSH  : self.__execute_bsh,

            # Bitwise Instructions
            ReilMnemonic.AND : self.__execute_binary_op,
            ReilMnemonic.OR  : self.__execute_binary_op,
            ReilMnemonic.XOR : self.__execute_binary_op,

            # Data Transfer Instructions
            ReilMnemonic.LDM : self.__execute_ldm,
            ReilMnemonic.STM : self.__execute_stm,
            ReilMnemonic.STR : self.__execute_str,

            # Conditional Instructions
            ReilMnemonic.BISZ : self.__execute_bisz,
            ReilMnemonic.JCC  : self.__execute_jcc,

            # Other Instructions
            ReilMnemonic.UNDEF : self.__execute_undef,
            ReilMnemonic.UNKN  : self.__execute_unkn,
            ReilMnemonic.NOP   : self.__execute_skip,

            # Ad hoc Instructions
            ReilMnemonic.RET : self.__execute_skip,

            # Extensions
            ReilMnemonic.SEXT : self.__execute_sext,
        }

        self.__set_default_handlers()

    def execute(self, instr):
        if DEBUG:
            print("0x%08x:%02x : %s" % (instr.address >> 8,
                                        instr.address & 0xff,
                                        instr))

        # Execute pre instruction handlers
        handler_fn_pre, handler_param_pre = self.__instr_handler_pre
        handler_fn_pre(self.__emu, instr, handler_param_pre)

        # Execute instruction
        next_addr = self.__executors[instr.mnemonic](instr)

        # Taint instruction
        self.__tainter.taint(instr)

        # Execute post instruction handlers
        handler_fn_post, handler_param_post = self.__instr_handler_post
        handler_fn_post(self.__emu, instr, handler_param_post)

        return next_addr

    def reset(self):
        # Registers.
        self.__regs = dict()
        self.__regs_written = set()
        self.__regs_read = set()

        # Instructions pre and post handlers.
        self.__instr_handler_pre = None, None
        self.__instr_handler_post = None, None

        self.__set_default_handlers()

    # Properties
    # ======================================================================== #
    @property
    def registers(self):
        return self.__regs

    @registers.setter
    def registers(self, value):
        self.__regs = value

    @property
    def read_registers(self):
        return self.__regs_read

    @property
    def written_registers(self):
        return self.__regs_written

    # Instruction's handler methods
    # ======================================================================== #
    def set_instruction_pre_handler(self, function, parameter):
        self.__instr_handler_pre = (function, parameter)

    def set_instruction_post_handler(self, function, parameter):
        self.__instr_handler_post = (function, parameter)

    # Instruction's handler auxiliary methods
    # ======================================================================== #
    def __set_default_handlers(self):
        empty_fn, empty_param = lambda emu, instr, param: None, None

        self.__instr_handler_pre = (empty_fn, empty_param)
        self.__instr_handler_post = (empty_fn, empty_param)

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
        if register.name in self.__arch.alias_mapper:
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
        if register.name in self.__arch.registers_gp_all:
            self.__regs_read.add(register.name)

        if DEBUG:
            self.__debug_read_operand(base_register, register.name, value)

        return value

    def __write_register(self, register, value):
        base_register, base_value, offset = self.__get_register_value(register)
        base_value_new = insert_value(base_value, value, offset, register.size)

        self.__regs[base_register] = base_value_new

        # Keep track of native register writes.
        if register.name in self.__arch.registers_gp_all:
            self.__regs_written.add(register.name)

        if DEBUG:
            self.__debug_write_operand(base_register, register.name, value)

    # Debug methods
    # ======================================================================== #
    def __debug_read_operand(self, base_register, register, value):
        base_value = self.__regs[base_register]
        taint = "T" if self.__tainter.get_register_taint(register) else "-"

        params = {
            "indent"        : " "*10,
            "register"      : register,
            "value"         : value,
            "base_register" : base_register,
            "base_value"    : base_value,
            "taint"         : taint
        }

        fmt = "{indent}r{{ {register:s} = {value:08x} [{taint:s}] " + \
              "({base_register:s} = {base_value:08x})}}"

        print(fmt.format(**params))

    def __debug_write_operand(self, base_register, register, value):
        base_value = self.__regs[base_register]
        taint = "T" if self.__tainter.get_register_taint(register) else "-"

        params = {
            "indent"        : " "*10,
            "register"      : register,
            "value"         : value,
            "base_register" : base_register,
            "base_value"    : base_value,
            "taint"         : taint
        }

        fmt = "{indent}w{{ {register:s} = {value:08x} [{taint:s}] " + \
              "({base_register:s} = {base_value:08x})}}"

        print(fmt.format(**params))

    def __debug_read_memory(self, address, size, value):
        taint = "T" if self.__tainter.get_memory_taint(address, size) else "-"

        params = {
            "indent"  : " "*10,
            "address" : address,
            "value"   : value,
            "taint"   : taint
        }

        fmt = "{indent}r{{ m[{address:08x}] = {value:08x} [{taint:s}]}}"

        print(fmt.format(**params))

    def __debug_write_memory(self, address, size, value):
        taint = "T" if self.__tainter.get_memory_taint(address, size) else "-"

        params = {
            "indent"  : " "*10,
            "address" : address,
            "value"   : value,
            "taint"   : taint
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

        result_tmp = op0_tmp / op1_tmp

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

    def __execute_binary_op(self, instr):
        op_map = {
            ReilMnemonic.ADD : lambda a, b: a + b,
            ReilMnemonic.SUB : lambda a, b: a - b,
            ReilMnemonic.MUL : lambda a, b: a * b,  # unsigned multiplication
            ReilMnemonic.DIV : lambda a, b: a / b,  # unsigned division
            ReilMnemonic.MOD : lambda a, b: a % b,  # unsigned modulo

            ReilMnemonic.AND : lambda a, b: a & b,
            ReilMnemonic.OR  : lambda a, b: a | b,
            ReilMnemonic.XOR : lambda a, b: a ^ b,
        }

        op0_val = self.read_operand(instr.operands[0])
        op1_val = self.read_operand(instr.operands[1])

        if instr.mnemonic in [ReilMnemonic.DIV, ReilMnemonic.MOD] and \
            op1_val == 0:
            raise ReilCpuZeroDivisionError()

        if instr.mnemonic in [ReilMnemonic.SDIV]:
            op2_val = self.__signed_div(instr.operands[0], instr.operands[1], instr.operands[2].size)
        elif instr.mnemonic in [ReilMnemonic.SMOD]:
            op2_val = self.__signed_mod(instr.operands[0], instr.operands[1], instr.operands[2].size)
        else:
            op2_val = op_map[instr.mnemonic](op0_val, op1_val)

        self.write_operand(instr.operands[2], op2_val)

        return None

    # Data transfer instructions
    # ======================================================================== #
    def __execute_ldm(self, instr):
        """Execute LDM instruction.
        """
        assert instr.operands[0].size == self.__arch.address_size
        assert instr.operands[2].size in [8, 16, 32, 64, 128]

        # Memory address.
        op0_val = self.read_operand(instr.operands[0])
        # Data.
        op2_val = self.read_memory(op0_val, instr.operands[2].size / 8)

        self.write_operand(instr.operands[2], op2_val)

        return None

    def __execute_stm(self, instr):
        """Execute STM instruction.
        """
        assert instr.operands[0].size in [8, 16, 32, 64, 128]
        assert instr.operands[2].size == self.__arch.address_size

        op0_val = self.read_operand(instr.operands[0])  # Data.
        op2_val = self.read_operand(instr.operands[2])  # Memory address.

        op0_size = instr.operands[0].size

        self.write_memory(op2_val, op0_size / 8, op0_val)

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


class ReilEmulatorTainter(object):

    def __init__(self, arch, emulator):
        # Architecture information.
        self.__arch = arch

        # Reil emulator instance.
        self.__emu = emulator

        # Taint information.
        self.__taint_reg = {}   # Register-level tainting
        self.__taint_mem = {}   # Byte-level tainting

        # Taint function lookup table.
        self.__tainter = {
            # Arithmetic Instructions
            ReilMnemonic.ADD  : self.__taint_binary_op,
            ReilMnemonic.SUB  : self.__taint_binary_op,
            ReilMnemonic.MUL  : self.__taint_binary_op,
            ReilMnemonic.DIV  : self.__taint_binary_op,
            ReilMnemonic.SDIV : self.__taint_binary_op,
            ReilMnemonic.MOD  : self.__taint_binary_op,
            ReilMnemonic.SMOD : self.__taint_binary_op,
            ReilMnemonic.BSH  : self.__taint_binary_op,

            # Bitwise Instructions
            ReilMnemonic.AND : self.__taint_binary_op,
            ReilMnemonic.OR  : self.__taint_binary_op,
            ReilMnemonic.XOR : self.__taint_binary_op,

            # Data Transfer Instructions
            ReilMnemonic.LDM : self.__taint_load,
            ReilMnemonic.STM : self.__taint_store,
            ReilMnemonic.STR : self.__taint_move,

            # Conditional Instructions
            ReilMnemonic.BISZ : self.__taint_move,
            ReilMnemonic.JCC  : self.__taint_nothing,

            # Other Instructions
            ReilMnemonic.UNDEF : self.__taint_undef,
            ReilMnemonic.UNKN  : self.__taint_nothing,
            ReilMnemonic.NOP   : self.__taint_nothing,

            # Ad hoc Instructions
            ReilMnemonic.RET : self.__taint_nothing,

            # Extensions
            ReilMnemonic.SEXT : self.__taint_move,
        }

    def taint(self, instruction):
        self.__tainter[instruction.mnemonic](instruction)

    def reset(self):
        # Taint information.
        self.__taint_reg = {}
        self.__taint_mem = {}

    # Operand taint methods
    # ======================================================================== #
    def get_operand_taint(self, operand):
        if isinstance(operand, ReilRegisterOperand):
            taint = self.get_register_taint(operand.name)
        elif isinstance(operand, ReilImmediateOperand):
            taint = False
        else:
            raise Exception("Invalid operand: %s" % str(operand))

        return taint

    def set_operand_taint(self, operand, taint):
        if isinstance(operand, ReilRegisterOperand):
            self.set_register_taint(operand.name, taint)
        else:
            raise Exception("Invalid operand: %s" % str(operand))

    def clear_operand_taint(self, operand):
        if isinstance(operand, ReilRegisterOperand):
            self.clear_register_taint(operand)
        else:
            raise Exception("Invalid operand: %s" % str(operand))

    # Memory taint methods
    # ======================================================================== #
    def get_memory_taint(self, address, size):
        tainted = False

        for i in xrange(0, size):
            tainted = tainted or self.__taint_mem.get(address + i, False)

        return tainted

    def set_memory_taint(self, address, size, taint):
        for i in xrange(0, size):
            self.__taint_mem[address + i] = taint

    def clear_memory_taint(self, address, size):
        for i in xrange(0, size):
            self.__taint_mem[address + i] = False

    # Register taint methods
    # ======================================================================== #
    def get_register_taint(self, register):
        return self.__taint_reg.get(self.__get_base_register(register), False)

    def set_register_taint(self, register, taint):
        self.__taint_reg[self.__get_base_register(register)] = taint

    def clear_register_taint(self, register):
        self.__taint_reg[self.__get_base_register(register)] = False

    # Taint auxiliary methods
    # ======================================================================== #
    def __get_base_register(self, register):
        if register in self.__arch.alias_mapper and \
            register not in self.__arch.registers_flags:
            # NOTE: Flags are tainted individually.
            base_name, _ = self.__arch.alias_mapper[register]
        else:
            base_name = register

        return base_name

    # Taint methods
    # ======================================================================== #
    def __taint_binary_op(self, instr):
        # Get taint information.
        op0_taint = self.get_operand_taint(instr.operands[0])
        op1_taint = self.get_operand_taint(instr.operands[1])

        # Propagate taint.
        self.set_operand_taint(instr.operands[2], op0_taint or op1_taint)

    def __taint_load(self, instr):
        """Taint LDM instruction.
        """
        # Get memory address.
        op0_val = self.__emu.read_operand(instr.operands[0])

        # Get taint information.
        op0_taint = self.get_memory_taint(op0_val, instr.operands[2].size / 8)

        # Propagate taint.
        self.set_operand_taint(instr.operands[2], op0_taint)

    def __taint_store(self, instr):
        """Taint STM instruction.
        """
        # Get memory address.
        op2_val = self.__emu.read_operand(instr.operands[2])

        # Get taint information.
        op0_size = instr.operands[0].size
        op0_taint = self.get_operand_taint(instr.operands[0])

        # Propagate taint.
        self.set_memory_taint(op2_val, op0_size / 8, op0_taint)

    def __taint_move(self, instr):
        """Taint registers move instruction.
        """
        # Get taint information.
        op0_taint = self.get_operand_taint(instr.operands[0])

        # Propagate taint.
        self.set_operand_taint(instr.operands[2], op0_taint)

    def __taint_undef(self, instr):
        """Taint UNDEF instruction.
        """
        # Propagate taint.
        self.set_operand_taint(instr.operands[2], False)

    def __taint_nothing(self, instr):
        """Taint nothing.
        """
        pass


class ReilEmulator(object):

    """Reil Emulator."""

    def __init__(self, arch, cpu=None, memory=None):
        # Architecture information.
        self.__arch = arch

        # An instance of a ReilTainter.
        self.__tainter = ReilEmulatorTainter(self.__arch, self)

        # An instance of a ReilMemory.
        self.__mem = memory if memory else ReilMemoryEx(self.__arch.address_size)

        # An instance of a ReilCpu.
        self.__cpu = cpu if cpu else ReilCpu(self.__arch, self.__mem, self.__tainter, self)

    # Execution methods
    # ======================================================================== #
    def execute(self, container, start=None, end=None, registers=None):
        """Execute instructions.
        """
        if registers:
            self.__cpu.registers = dict(registers)

        ip = start if start else container[0].address

        while ip and ip != end:
            try:
                instr = container.fetch(ip)
            except ReilContainerInvalidAddressError:
                logger.info("Invalid address: {:#010x}:{:#02x}".format(ip >> 8, ip & 0xff))

                raise ReilCpuInvalidAddressError()

            next_ip = self.__cpu.execute(instr)

            ip = next_ip if next_ip else container.get_next_address(ip)

        return dict(self.__cpu.registers), self.__mem

    def execute_lite(self, instructions, context=None):
        """Execute a list of instructions. It does not support loops.
        """
        if context:
            self.__cpu.registers = dict(context)

        for instr in instructions:
            self.__cpu.execute(instr)

        return dict(self.__cpu.registers), self.__mem

    def single_step(self, instruction):
        return self.__cpu.execute(instruction)

    # Reset methods
    # ======================================================================== #
    def reset(self):
        """Reset emulator. All registers and memory are reset.
        """
        self.__mem.reset()
        self.__cpu.reset()
        self.__tainter.reset()

    def reset_memory(self):
        self.__mem.reset()

    def reset_cpu(self):
        self.__cpu.reset()

    def reset_tainter(self):
        self.__tainter.reset()

    # Handler methods
    # ======================================================================== #
    def set_instruction_pre_handler(self, function, parameter):
        self.__cpu.set_instruction_pre_handler(function, parameter)

    def set_instruction_post_handler(self, function, parameter):
        self.__cpu.set_instruction_post_handler(function, parameter)

    # Read/Write methods
    # ======================================================================== #
    def read_operand(self, operand):
        return self.__cpu.read_operand(operand)

    def write_operand(self, operand, value):
        self.__cpu.write_operand(operand, value)

    def read_memory(self, address, size):
        return self.__mem.read(address, size)

    def write_memory(self, address, size, value):
        self.__mem.write(address, size, value)

    # Taint methods
    # ======================================================================== #
    def get_operand_taint(self, register):
        return self.__tainter.get_operand_taint(register)

    def set_operand_taint(self, register, value):
        self.__tainter.set_operand_taint(register, value)

    def clear_operand_taint(self, register):
        self.__tainter.clear_operand_taint(register)

    def get_register_taint(self, register):
        return self.__tainter.get_register_taint(register)

    def set_register_taint(self, register, value):
        self.__tainter.set_register_taint(register, value)

    def clear_register_taint(self, register):
        self.__tainter.clear_register_taint(register)

    def get_memory_taint(self, address, size):
        return self.__tainter.get_memory_taint(address, size)

    def set_memory_taint(self, address, size, value):
        self.__tainter.set_memory_taint(address, size, value)

    def clear_memory_taint(self, address, size):
        self.__tainter.clear_memory_taint(address, size)

    # Properties
    # ======================================================================== #
    @property
    def registers(self):
        """Return registers.
        """
        return self.__cpu.registers

    @registers.setter
    def registers(self, value):
        """Return registers.
        """
        self.__cpu.registers = value

    @property
    def memory(self):
        """Return memory.
        """
        return self.__mem

    @property
    def cpu(self):
        """Return memory.
        """
        return self.__cpu

    @property
    def read_registers(self):
        """Return read (native) registers.
        """
        return self.__cpu.read_registers

    @property
    def written_registers(self):
        """Return written (native) registers.
        """
        return self.__cpu.written_registers
