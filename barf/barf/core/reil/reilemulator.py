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
from barf.utils.utils import extract_value
from barf.utils.utils import insert_value
from barf.utils.utils import twos_complement

logger = logging.getLogger("reilemulator")

verbose = False
# verbose = True

REIL_MEMORY_ENDIANNESS_LE = 0x0     # Little Endian
REIL_MEMORY_ENDIANNESS_BE = 0x1     # Big Endian


class ReilMemory(object):

    """A REIL memory model (byte addressable).
    """

    def __init__(self, address_size):

        # TODO: Set endianness through a parameter.
        # TODO: Check that all addresses have size address_size.
        # TODO: Use _endianness parameter.

        # Memory's address size.
        self.__address_size = address_size

        # Memory's endianness.
        self.__endianness = REIL_MEMORY_ENDIANNESS_LE

        # Dictionary that implements the memory itself.
        self.__memory = {}

        # Previous state of memory. Requiere for some *special*
        # functions.
        self.__memory_prev = {}

        # Write operations counter.
        self.__write_count = 0

    # Read methods
    # ======================================================================== #
    def read(self, address, size):
        """Read arbitrary size content from memory.
        """
        value = 0x0

        for i in xrange(0, size / 8):
            value = self._read_byte(address + i) << (i * 8) | value

        if verbose:
            taint = None
            self._debug_read_memory(address, value, taint)

        return value

    def read_inverse(self, value, size):
        """Return a list of memory addresses that contain the specified
        value.

        """
        addr_candidates = [addr for addr, val in self.__memory.items()
                                    if val == (value & 0xff)]
        addr_matchings = []

        for addr in addr_candidates:
            match = True

            for i in xrange(0, size / 8):
                byte_curr = (value >> (i * 8)) & 0xff
                try:
                    match = self.__memory[addr + i] == byte_curr
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

        for i in xrange(0, size / 8):
            addr = address + i

            if addr in self.__memory:
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

        for i in xrange(0, size / 8):
            addr = address + i

            if addr in self.__memory_prev:
                _, val_byte = self._try_read_byte_prev(addr)
                value = val_byte << (i * 8) | value
            else:
                return False, None

        return True, value

    # Auxiliary read methods
    # ======================================================================== #
    def _read_byte(self, address):
        """Read a byte from memory.
        """
        # Initialize memory location with a random value.
        if not address in self.__memory:
            self.__memory[address] = random.randint(0x00, 0xff)

        return self.__memory[address]

    def _try_read_byte_prev(self, address):
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
        for i in xrange(0, size / 8):
            self._write_byte(address + i, (value >> (i * 8)) & 0xff)

        self.__write_count += 1

        if verbose:
            taint = None
            self._debug_write_memory(address, value, taint)

    # Auxiliary write methods
    # ======================================================================== #
    def _write_byte(self, address, value):
        """Write byte in memory.
        """
        # Save previous address content.
        if address in self.__memory:
            self.__memory_prev[address] = self.__memory[address]

        self.__memory[address] = value & 0xff

    # Misc methods
    # ======================================================================== #
    def get_addresses(self):
        """Get accessed addresses.
        """
        return self.__memory.keys()

    def get_write_count(self):
        """Get number of write operations performed on the memory.
        """
        return self.__write_count

    def reset(self):
        # Dictionary that implements the memory itself.
        self.__memory = {}

        # Previous state of memory. Requiere for some *special*
        # functions.
        self.__memory_prev = {}

        # Write operations counter.
        self.__write_count = 0

    # Debug methods
    # ======================================================================== #
    def _debug_read_memory(self, addr, val, tainted):
        fmt = "{indent}r{{ m[{addr:08x}] = {val:08x} [{taint:s}]}}"
        taint = "T" if tainted else "-"
        msg = fmt.format(indent=" "*10, addr=addr, val=val, taint=taint)

        print(msg)

    def _debug_write_memory(self, addr, val, tainted):
        fmt = "{indent}w{{ m[{addr:08x}] = {val:08x} [{taint:s}]}}"
        taint = "T" if tainted else "-"
        msg = fmt.format(indent=" "*10, addr=addr, val=val, taint=taint)

        print(msg)

    # Magic methods
    # ======================================================================== #
    def __str__(self):
        lines = []

        for addr in sorted(self.__memory.keys()):
            lines += ["0x%08x : 0x%08x" % (addr, self.__memory[addr])]

        return "\n".join(lines)


class ReilCpuZeroDivisionError(Exception):
    pass


class ReilCpuInvalidAddressError(Exception):
    pass


class ReilCpu(object):

    def __init__(self, arch, memory, tainter, emulator):
        self.__emu = emulator

        self.__arch = arch
        self.__mem = memory

        self.__tainter = tainter

        # Instruction Pointer.
        self.__ip = None

        # Registers.
        self.__regs = {}

        # Set of read and write registers during execution.
        self.__regs_written = set()
        self.__regs_read = set()

        # Instructions pre and post handlers.
        self.__instr_pre_handler = None, None
        self.__instr_post_handler = None, None

        self.__set_default_handlers()

        # Instruction implementation.
        self.__executors = {
            # Arithmetic Instructions
            ReilMnemonic.ADD : self.__execute_add,
            ReilMnemonic.SUB : self.__execute_sub,
            ReilMnemonic.MUL : self.__execute_mul,
            ReilMnemonic.DIV : self.__execute_div,
            ReilMnemonic.MOD : self.__execute_mod,
            ReilMnemonic.BSH : self.__execute_bsh,

            # Bitwise Instructions
            ReilMnemonic.AND : self.__execute_and,
            ReilMnemonic.OR  : self.__execute_or,
            ReilMnemonic.XOR : self.__execute_xor,

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
            ReilMnemonic.NOP   : self.__execute_nop,

            # Ad hoc Instructions
            ReilMnemonic.RET : self.__execute_ret,

            # Extensions
            ReilMnemonic.SEXT : self.__execute_sext,
        }

    # Auxiliary execution methods
    # ======================================================================== #
    def execute(self, instr):
        if verbose:
            print("0x%08x:%02x : %s" % (instr.address >> 8,
                                        instr.address & 0xff,
                                        instr))

        pre_handler_fn, pre_handler_param = self.__instr_pre_handler
        post_handler_fn, post_handler_param = self.__instr_post_handler

        # Execute pre instruction handlers
        pre_handler_fn(self.__emu, instr, pre_handler_param)

        # Execute instruction
        next_addr = self.__executors[instr.mnemonic](instr)

        # Taint instruction
        self.__tainter.taint(instr)

        # Execute post instruction handlers
        post_handler_fn(self.__emu, instr, post_handler_param)

        return next_addr

    def reset(self):
        # Instruction Pointer.
        self.__ip = None

        # Registers.
        self.__regs = {}

        # Set of read and write registers during execution.
        self.__regs_written = set()
        self.__regs_read = set()

        # Instructions pre and post handlers.
        self.__instr_pre_handler = None, None
        self.__instr_post_handler = None, None

        self.__set_default_handlers()

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
        self.__instr_pre_handler = (function, parameter)

    def set_instruction_post_handler(self, function, parameter):
        self.__instr_post_handler = (function, parameter)

    # Instruction's handler auxiliary methods
    # ======================================================================== #
    def __set_default_handlers(self):
        empty_fn, empty_param = lambda emu, instr, param: None, None

        self.__instr_pre_handler = (empty_fn, empty_param)
        self.__instr_post_handler = (empty_fn, empty_param)

    # Read/Write methods
    # ======================================================================== #
    def read_operand(self, operand):
        if isinstance(operand, ReilRegisterOperand):
            value = self._read_register(operand)
        elif isinstance(operand, ReilImmediateOperand):
            value = operand.immediate
        else:
            raise Exception("Invalid operand type : %s" % str(operand))

        return value

    def write_operand(self, operand, value):
        if isinstance(operand, ReilRegisterOperand):
            self._write_register(operand, value)
        else:
            raise Exception("Invalid operand type : %s" % str(operand))

    def read_memory(self, address, size):
        return self.__mem.read(address, size)

    def write_memory(self, address, size, value):
        self.__mem.write(address, size, value)

    # Read/Write auxiliary methods
    # ======================================================================== #
    def _get_register_value(self, register):
        if register.name in self.__arch.alias_mapper:
            base_reg_name, offset = self.__arch.alias_mapper[register.name]
            base_reg_size = self.__arch.registers_size[base_reg_name]
        else:
            base_reg_name, offset = register.name, 0
            base_reg_size = register.size

        if base_reg_name in self.__regs:
            base_val = self.__regs[base_reg_name]
        else:
            base_val = random.randint(0, 2**base_reg_size - 1)

        return base_reg_name, base_val, offset

    def _read_register(self, register):
        base_reg_name, base_val, offset = self._get_register_value(register)

        reg_val = extract_value(base_val, offset, register.size)

        # Keep track of native register reads.
        if register.name in self.__arch.registers_gp_all:
            self.__regs_read.add(register.name)

        # Debug
        if verbose:
            # taint = self._get_register_taint(register)
            taint = None
            self._debug_read_operand(register, reg_val, base_reg_name, \
                base_val, taint)

        return reg_val

    def _write_register(self, register, value):
        base_reg_name, base_val, offset = self._get_register_value(register)

        self.__regs[base_reg_name] = insert_value(base_val, value, offset, \
            register.size)

        # Keep track of native register writes.
        if register.name in self.__arch.registers_gp_all:
            self.__regs_written.add(register.name)

        # Debug
        if verbose:
            # taint = self._get_register_taint(register)
            taint = None
            self._debug_write_operand(register, value, base_reg_name, \
                self.__regs[base_reg_name], taint)

    # Debug methods
    # ======================================================================== #
    def _debug_read_operand(self, reg, val, base_reg, base_val, tainted):
        fmt = "{indent}r{{ {reg:s} = {val:08x} [{taint:s}] ({base_reg:s} = {base_val:08x})}}"

        taint = "T" if tainted == True else "-"

        msg = fmt.format(
            indent=" "*10, reg=reg, val=val, base_reg=base_reg,
            base_val=base_val, taint=taint
        )

        print(msg)

    def _debug_write_operand(self, reg, val, base_reg, base_val, tainted):
        fmt = "{indent}w{{ {reg:s} = {val:08x} [{taint:s}] ({base_reg:s} = {base_val:08x})}}"

        taint = "T" if tainted else "-"

        msg = fmt.format(
            indent=" "*10, reg=reg, val=val, base_reg=base_reg,
            base_val=base_val, taint=taint
        )

        print(msg)


    # ======================================================================== #
    # REIL instructions implementation
    # ======================================================================== #

    # Arithmetic instructions
    # ======================================================================== #
    def __execute_add(self, instr):
        """Execute ADD instruction.
        """
        op0_val = self.read_operand(instr.operands[0])
        op1_val = self.read_operand(instr.operands[1])

        op2_val = op0_val + op1_val

        self.write_operand(instr.operands[2], op2_val)

        return None

    def __execute_sub(self, instr):
        """Execute SUB instruction.
        """
        op0_val = self.read_operand(instr.operands[0])
        op1_val = self.read_operand(instr.operands[1])

        op2_val = op0_val - op1_val

        self.write_operand(instr.operands[2], op2_val)

        return None

    def __execute_mul(self, instr):
        """Execute MUL instruction.
        """
        op0_val = self.read_operand(instr.operands[0])
        op1_val = self.read_operand(instr.operands[1])

        op2_val = op0_val * op1_val

        self.write_operand(instr.operands[2], op2_val)

        return None

    def __execute_div(self, instr):
        """Execute DIV instruction.
        """
        op0_val = self.read_operand(instr.operands[0])
        op1_val = self.read_operand(instr.operands[1])

        if op1_val == 0:
            raise ReilCpuZeroDivisionError()

        op2_val = op0_val / op1_val

        self.write_operand(instr.operands[2], op2_val)

        return None

    def __execute_mod(self, instr):
        """Execute MOD instruction.
        """
        op0_val = self.read_operand(instr.operands[0])
        op1_val = self.read_operand(instr.operands[1])

        if op1_val == 0:
            raise ReilCpuZeroDivisionError()

        op2_val = op0_val % op1_val

        self.write_operand(instr.operands[2], op2_val)

        return None

    def __execute_bsh(self, instr):
        """Execute BSH instruction.
        """
        op0_val = self.read_operand(instr.operands[0])
        op1_val = self.read_operand(instr.operands[1])

        op1_size = instr.operands[1].size

        # Check sign bit.
        if op1_val & (2**(op1_size-1)) == 0:
            op2_val = op0_val << op1_val
        else:
            op2_val = op0_val >> twos_complement(op1_val, op1_size)

        self.write_operand(instr.operands[2], op2_val)

        return None

    # Bitwise instructions
    # ======================================================================== #
    def __execute_and(self, instr):
        """Execute AND instruction.
        """
        op0_val = self.read_operand(instr.operands[0])
        op1_val = self.read_operand(instr.operands[1])

        op2_val = op0_val & op1_val

        self.write_operand(instr.operands[2], op2_val)

        return None

    def __execute_or(self, instr):
        """Execute OR instruction.
        """
        op0_val = self.read_operand(instr.operands[0])
        op1_val = self.read_operand(instr.operands[1])

        op2_val = op0_val | op1_val

        self.write_operand(instr.operands[2], op2_val)

        return None

    def __execute_xor(self, instr):
        """Execute XOR instruction.
        """
        op0_val = self.read_operand(instr.operands[0])
        op1_val = self.read_operand(instr.operands[1])

        op2_val = op0_val ^ op1_val

        self.write_operand(instr.operands[2], op2_val)

        return None

    # Data transfer instructions
    # ======================================================================== #
    def __execute_ldm(self, instr):
        """Execute LDM instruction.
        """
        assert instr.operands[0].size == self.__arch.address_size
        assert instr.operands[2].size in [8, 16, 32, 64]

        # Memory address.
        op0_val = self.read_operand(instr.operands[0])
        # Data.
        op2_val = self.read_memory(op0_val, instr.operands[2].size)

        self.write_operand(instr.operands[2], op2_val)

        return None

    def __execute_stm(self, instr):
        """Execute STM instruction.
        """
        assert instr.operands[0].size in [8, 16, 32, 64]
        assert instr.operands[2].size == self.__arch.address_size

        op0_val = self.read_operand(instr.operands[0])  # Data.
        op2_val = self.read_operand(instr.operands[2])  # Memory address.

        op0_size = instr.operands[0].size

        self.write_memory(op2_val, op0_size, op0_val)

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
        raise Exception("Unknown instruction (UNKN).")

    def __execute_nop(self, instr):
        """Execute NOP instruction.
        """
        return None

    # Ad hoc Instructions
    # ======================================================================== #
    def __execute_ret(self, instr):
        """Execute RET instruction.
        """
        return None

    # Extension
    # ======================================================================== #
    def __execute_sext(self, instr):
        """Execute SEXT instruction.
        """
        op0_size = instr.operands[0].size
        op2_size = instr.operands[2].size

        op0_val = self.read_operand(instr.operands[0])
        op0_msb = op0_val >> (op0_size-1)

        op2_mask = (2**op2_size-1) & ~(2**op0_size-1) if op0_msb == 1 else 0x0

        op2_val = op0_val | op2_mask

        self.write_operand(instr.operands[2], op2_val)

        return None


class ReilEmulatorTainter(object):

    def __init__(self, arch, emulator):
        self.__arch = arch

        self.__emu = emulator

        # Taint information.
        self.__taint_reg = {}
        self.__taint_mem = {}

        self.__tainter = {
            # Arithmetic Instructions
            ReilMnemonic.ADD : self._taint_add,
            ReilMnemonic.SUB : self._taint_sub,
            ReilMnemonic.MUL : self._taint_mul,
            ReilMnemonic.DIV : self._taint_div,
            ReilMnemonic.MOD : self._taint_mod,
            ReilMnemonic.BSH : self._taint_bsh,

            # Bitwise Instructions
            ReilMnemonic.AND : self._taint_and,
            ReilMnemonic.OR  : self._taint_or,
            ReilMnemonic.XOR : self._taint_xor,

            # Data Transfer Instructions
            ReilMnemonic.LDM : self._taint_ldm,
            ReilMnemonic.STM : self._taint_stm,
            ReilMnemonic.STR : self._taint_str,

            # Conditional Instructions
            ReilMnemonic.BISZ : self._taint_bisz,
            ReilMnemonic.JCC  : self._taint_jcc,

            # Other Instructions
            ReilMnemonic.UNDEF : self._taint_undef,
            ReilMnemonic.UNKN  : self._taint_unkn,
            ReilMnemonic.NOP   : self._taint_nop,

            # Ad hoc Instructions
            ReilMnemonic.RET : self._taint_ret,

            # Extensions
            ReilMnemonic.SEXT : self._taint_sext,
        }

    def taint(self, instruction):
        self.__tainter[instruction.mnemonic](instruction)

    def reset(self):
        # Taint information.
        self.__taint_reg = {}
        self.__taint_mem = {}

    # Taint methods
    # ======================================================================== #
    def get_operand_taint(self, operand):
        if isinstance(operand, ReilRegisterOperand):
            taint = self.get_register_taint(operand)
        elif isinstance(operand, ReilImmediateOperand):
            taint = False
        else:
            raise Exception("Invalid operand: %s" % str(operand))

        return taint

    def set_operand_taint(self, operand, taint):
        if isinstance(operand, ReilRegisterOperand):
            self.set_register_taint(operand, taint)
        else:
            raise Exception("Invalid operand: %s" % str(operand))

    def clear_operand_taint(self, operand):
        if isinstance(operand, ReilRegisterOperand):
            self.clear_register_taint(operand)
        else:
            raise Exception("Invalid operand: %s" % str(operand))

    def get_memory_taint(self, address, size):
        tainted = False

        for i in xrange(0, size / 8):
            tainted = tainted or self.__taint_mem.get(address + i, False)

        return tainted

    def set_memory_taint(self, address, size, taint):
        for i in xrange(0, size / 8):
            self.__taint_mem[address + i] = taint

    def clear_memory_taint(self, address, size):
        for i in xrange(0, size / 8):
            self.__taint_mem[address + i] = False

    # Taint auxiliary methods
    # ======================================================================== #
    def get_register_taint(self, register):
        if register.name in self.__arch.alias_mapper and \
            register.name not in self.__arch.registers_flags:
            base_name, _ = self.__arch.alias_mapper[register.name]
        else:
            base_name = register.name

        return self.__taint_reg.get(base_name, False)

    def set_register_taint(self, register, taint):
        if register.name in self.__arch.alias_mapper and \
            register.name not in self.__arch.registers_flags:
            base_name, _ = self.__arch.alias_mapper[register.name]
        else:
            base_name = register.name

        self.__taint_reg[base_name] = taint

        if verbose:
            reg = register.name
            base_reg = base_name

            fmt = "{indent}t{{ {reg:s} ({base_reg:s})}}"

            msg = fmt.format(indent=" "*10, reg=reg, base_reg=base_reg)

            print(msg)

    def clear_register_taint(self, register):
        if register.name in self.__arch.alias_mapper and \
            register.name not in self.__arch.registers_flags:
            base_name, _ = self.__arch.alias_mapper[register.name]
        else:
            base_name = register.name

        self.__taint_reg[base_name] = False

        if verbose:
            reg = register.name
            base_reg = base_name

            fmt = "{indent}t{{ {reg:s} ({base_reg:s})}}"

            msg = fmt.format(indent=" "*10, reg=reg, base_reg=base_reg)

            print(msg)

    # ======================================================================== #
    # REIL instructions TAINT implementation
    # ======================================================================== #
    def _taint_add(self, instr):
        """Taint ADD instruction.
        """
        # Get taint information.
        op0_taint = self.get_operand_taint(instr.operands[0])
        op1_taint = self.get_operand_taint(instr.operands[1])

        # Propagate taint.
        self.set_operand_taint(instr.operands[2], op0_taint or op1_taint)

    def _taint_sub(self, instr):
        """Taint SUB instruction.
        """
        # Get taint information.
        op0_taint = self.get_operand_taint(instr.operands[0])
        op1_taint = self.get_operand_taint(instr.operands[1])

        # Propagate taint.
        self.set_operand_taint(instr.operands[2], op0_taint or op1_taint)

    def _taint_mul(self, instr):
        """Taint MUL instruction.
        """
        # Get taint information.
        op0_taint = self.get_operand_taint(instr.operands[0])
        op1_taint = self.get_operand_taint(instr.operands[1])

        # Propagate taint.
        self.set_operand_taint(instr.operands[2], op0_taint or op1_taint)

    def _taint_div(self, instr):
        """Taint DIV instruction.
        """
        # Get taint information.
        op0_taint = self.get_operand_taint(instr.operands[0])
        op1_taint = self.get_operand_taint(instr.operands[1])

        # Propagate taint.
        self.set_operand_taint(instr.operands[2], op0_taint or op1_taint)

    def _taint_mod(self, instr):
        """Taint MOD instruction.
        """
        # Get taint information.
        op0_taint = self.get_operand_taint(instr.operands[0])
        op1_taint = self.get_operand_taint(instr.operands[1])

        # Propagate taint.
        self.set_operand_taint(instr.operands[2], op0_taint or op1_taint)

    def _taint_bsh(self, instr):
        """Taint BSH instruction.
        """
        # Get taint information.
        op0_taint = self.get_operand_taint(instr.operands[0])
        op1_taint = self.get_operand_taint(instr.operands[1])

        # Propagate taint.
        self.set_operand_taint(instr.operands[2], op0_taint or op1_taint)

    # Bitwise instructions
    # ======================================================================== #
    def _taint_and(self, instr):
        """Taint AND instruction.
        """
        # Get taint information.
        op0_taint = self.get_operand_taint(instr.operands[0])
        op1_taint = self.get_operand_taint(instr.operands[1])

        # Propagate taint.
        self.set_operand_taint(instr.operands[2], op0_taint or op1_taint)

    def _taint_or(self, instr):
        """Taint OR instruction.
        """
        # Get taint information.
        op0_taint = self.get_operand_taint(instr.operands[0])
        op1_taint = self.get_operand_taint(instr.operands[1])

        # Propagate taint.
        self.set_operand_taint(instr.operands[2], op0_taint or op1_taint)

    def _taint_xor(self, instr):
        """Taint XOR instruction.
        """
        # Get taint information.
        op0_taint = self.get_operand_taint(instr.operands[0])
        op1_taint = self.get_operand_taint(instr.operands[1])

        # Propagate taint.
        self.set_operand_taint(instr.operands[2], op0_taint or op1_taint)

    # Data transfer instructions
    # ======================================================================== #
    def _taint_ldm(self, instr):
        """Taint LDM instruction.
        """
        # Memory address.
        op0_val = self.__emu.read_operand(instr.operands[0])

        # Get taint information.
        op0_taint = self.get_memory_taint(op0_val, instr.operands[2].size)

        # Propagate taint.
        self.set_operand_taint(instr.operands[2], op0_taint)

    def _taint_stm(self, instr):
        """Taint STM instruction.
        """
        # Memory address.
        op2_val = self.__emu.read_operand(instr.operands[2])

        # Get taint information.
        op0_size = instr.operands[0].size
        op0_taint = self.get_operand_taint(instr.operands[0])

        # Propagate taint.
        self.set_memory_taint(op2_val, op0_size, op0_taint)

    def _taint_str(self, instr):
        """Taint STR instruction.
        """
        # Get taint information.
        op0_taint = self.get_operand_taint(instr.operands[0])

        # Propagate taint.
        self.set_operand_taint(instr.operands[2], op0_taint)

    # Conditional instructions
    # ======================================================================== #
    def _taint_bisz(self, instr):
        """Taint BISZ instruction.
        """
        # Get taint information.
        op0_taint = self.get_operand_taint(instr.operands[0])

        # Propagate taint.
        self.set_operand_taint(instr.operands[2], op0_taint)

    def _taint_jcc(self, instr):
        """Taint JCC instruction.
        """
        pass

    # Other instructions
    # ======================================================================== #
    def _taint_undef(self, instr):
        """Taint UNDEF instruction.
        """
        # Propagate taint.
        self.set_operand_taint(instr.operands[2], False)

    def _taint_unkn(self, instr):
        """Taint UNKN instruction.
        """
        pass

    def _taint_nop(self, instr):
        """Taint NOP instruction.
        """
        pass

    # Ad hoc Instructions
    # ======================================================================== #
    def _taint_ret(self, instr):
        """Taint RET instruction.
        """
        pass

    # Extension
    # ======================================================================== #
    def _taint_sext(self, instr):
        """Taint SEXT instruction.
        """
        # Get taint information.
        op0_taint = self.get_operand_taint(instr.operands[0])

        # Propagate taint.
        self.set_operand_taint(instr.operands[2], op0_taint)


class ReilEmulator(object):

    """Reil Emulator."""

    def __init__(self, arch):
        # Architecture information.
        self.__arch = arch

        # An instance of a ReilTainter.
        self.__tainter = ReilEmulatorTainter(self.__arch, self)

        # An instance of a ReilMemory.
        self.__mem = ReilMemory(self.__arch.address_size)

        # An instance of a ReilCpu.
        self.__cpu = ReilCpu(self.__arch, self.__mem, self.__tainter, self)

    # Execution methods
    # ======================================================================== #
    def execute(self, container, start=None, end=None, registers=None):
        """Execute instructions.
        """
        if registers:
            self.__cpu.registers = dict(registers)

        ip = start if start else container[0].address

        while ip and ip != end:
            instr = container.fetch(ip)

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
