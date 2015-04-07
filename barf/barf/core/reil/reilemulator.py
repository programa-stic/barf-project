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
        # TODO: All addresses should be of size address_size.
        # TODO: Use _endianness parameter.

        # Memory's address size.
        self._address_size = address_size

        # Memory's endianness.
        self._endianness = REIL_MEMORY_ENDIANNESS_LE

        # Dictionary that implements the memory itself.
        self._memory = {}

        # Previous state of memory. Requiere for some *special*
        # functions.
        self._memory_prev = {}

        # Write operations counter.
        self._write_count = 0

    def read_byte(self, address):
        """Read a byte from memory.
        """
        # Initialize memory location with a random value.
        if not address in self._memory:
            self._memory[address] = random.randint(0x00, 0xff)

        return self._memory[address]

    def try_read_byte_prev(self, address):
        """Read previous value for memory location.

        Return a tuple (True, Byte) in case of successful read,
        (False, None) otherwise.

        """
        # Initialize memory location with a random value
        if not address in self._memory_prev:
            return False, None

        return True, self._memory_prev[address]

    def write_byte(self, address, value):
        """Write byte in memory.
        """
        # Save previous address content.
        if address in self._memory:
            self._memory_prev[address] = self._memory[address]

        self._memory[address] = value & 0xff

    def read(self, address, size):
        """Read arbitrary size content from memory.
        """
        value = 0x0

        for i in xrange(0, size / 8):
            value = self.read_byte(address + i) << (i * 8) | value

        # Debug...
        # print "Memory Read: ", hex(address), size, hex(value)

        return value

    def try_read(self, address, size):
        """Try to read memory content at specified address.

        If any location was not written before, it returns a tuple
        (False, None). Otherwise, it returns (True, memory content).

        """
        value = 0x0

        for i in xrange(0, size / 8):
            addr = address + i

            if addr in self._memory:
                value = self.read_byte(addr) << (i * 8) | value
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

            if addr in self._memory_prev:
                success, val_byte = self.try_read_byte_prev(addr)
                value = val_byte << (i * 8) | value
            else:
                return False, None

        return True, value

    def write(self, address, size, value):
        """Write arbitrary size content to memory.
        """
        # Debug...
        # print "Memory Write: ", hex(address), size, hex(value)

        for i in xrange(0, size / 8):
            self.write_byte(address + i, (value >> (i * 8)) & 0xff)

        self._write_count += 1

    def read_inverse(self, value, size):
        """Return a list of memory addresses that contain the specified value.
        """
        addr_candidates = [addr for addr, val in self._memory.items() if val == (value & 0xff)]
        addr_matchings = []

        for addr in addr_candidates:
            match = True

            for i in xrange(0, size / 8):
                byte_curr = (value >> (i * 8)) & 0xff
                try:
                    match = self._memory[addr + i] == byte_curr
                except:
                    match = False

                if not match:
                    break

            if match:
                addr_matchings += [addr]

        return addr_matchings

    def get_addresses(self):
        """Get accessed addresses.
        """
        return self._memory.keys()

    def get_write_count(self):
        """Get number of write operations performed on the memory.
        """
        return self._write_count

    def __str__(self):
        lines = []

        for addr in sorted(self._memory.keys()):
            lines += ["0x%08x : 0x%08x" % (addr, self._memory[addr])]

        return "\n".join(lines)


class ReilEmulator(object):

    """Reil Emulator."""

    def __init__(self, address_size):

        # TODO: pass memory as a parameter

        # Memory address size.
        self._address_size = address_size

        # Registers.
        self._regs = {}

        # An instance of a ReilMemory.
        self._mem = ReilMemory(address_size)

        # Instruction Pointer.
        self._ip = None

        # Set of read and write registers during execution.
        self._regs_written = set()
        self._regs_read = set()

        self._arch_regs = []
        self._arch_regs_size = {}

        # Instruction implementation.
        self._executors = {
            # Arithmetic Instructions
            ReilMnemonic.ADD : self._execute_add,
            ReilMnemonic.SUB : self._execute_sub,
            ReilMnemonic.MUL : self._execute_mul,
            ReilMnemonic.DIV : self._execute_div,
            ReilMnemonic.MOD : self._execute_mod,
            ReilMnemonic.BSH : self._execute_bsh,

            # Bitwise Instructions
            ReilMnemonic.AND : self._execute_and,
            ReilMnemonic.OR  : self._execute_or,
            ReilMnemonic.XOR : self._execute_xor,

            # Data Transfer Instructions
            ReilMnemonic.LDM : self._execute_ldm,
            ReilMnemonic.STM : self._execute_stm,
            ReilMnemonic.STR : self._execute_str,

            # Conditional Instructions
            ReilMnemonic.BISZ : self._execute_bisz,
            ReilMnemonic.JCC  : self._execute_jcc,

            # Other Instructions
            ReilMnemonic.UNDEF : self._execute_undef,
            ReilMnemonic.UNKN  : self._execute_unkn,
            ReilMnemonic.NOP   : self._execute_nop,

            # Ad hoc Instructions
            ReilMnemonic.RET : self._execute_ret,

            # Extensions
            ReilMnemonic.SEXT : self._execute_sext,
        }

    def execute_lite(self, instructions, context=None):
        """Execute a list of instructions. It does not support loops.
        """
        if verbose:
            print "[+] Executing instructions..."

        if context:
            self._regs = context.copy()

        for index, instr in enumerate(instructions):
            if verbose:
                print "    %03d : %s" % (index, instr)

            self._executors[instr.mnemonic](instr)

        return self._regs.copy(), self._mem

    def execute(self, instructions, start_address, end_address=None, context=None):
        """Execute instructions.
        """
        if verbose:
            print("[+] Executing instructions (full)...")

        if context:
            self._regs = context.copy()

        main_index = 0
        sub_index = 0

        self._ip = instructions[main_index][sub_index].address

        instr_count = 0

        while True:
            # fetch instruction
            instr = instructions[main_index][sub_index]

            if verbose:
                # print("    0x%08x:%02x : %s" % (self._ip >> 8, self._ip & 0xff, instr))
                print "    %03d : %s" % (main_index, instr)
                # logger.debug("    0x%08x:%02x : %s" % (self._ip >> 8, self._ip & 0xff, instr))

            # execute instruction
            next_addr = self._executors[instr.mnemonic](instr)

            # update instruction pointer
            if next_addr:
                if end_address and next_addr == end_address:
                    if verbose:
                        print("[+] End address reached...")

                    break

                found = False

                for idx, instrs in enumerate(instructions):
                    if instrs[0].address >> 8 == next_addr >> 8:
                        main_index = idx
                        sub_index = next_addr & 0xff

                        found = True

                if not found:
                    raise Exception("Invalid address: %s" % hex(next_addr))
            else:
                sub_index += 1

                if sub_index >= len(instructions[main_index]):
                    main_index += 1
                    sub_index = 0

                    if main_index >= len(instructions):
                        break

                next_addr = instructions[main_index][sub_index].address

            self._ip = next_addr

            # update instruction counter
            instr_count += 1

            if end_address and self._ip == end_address:
                if verbose:
                    print("[+] End address reached...")

                break

        if verbose:
            print("[+] Executed instruction count : %d" % instr_count)

        return self._regs.copy(), self._mem

    def reset(self):
        """Reset emulator. All registers and memory are reset.
        """
        self._regs = {}

        self._mem = ReilMemory(self._address_size)

        self._ip = None

        self._regs_written = set()
        self._regs_read = set()

    @property
    def registers(self):
        """Return registers.
        """
        return self._regs

    @property
    def memory(self):
        """Return memory.
        """
        return self._mem

    @property
    def read_registers(self):
        """Return read (native) registers.
        """
        return self._regs_read

    @property
    def written_registers(self):
        """Return write (native) registers.
        """
        return self._regs_written

    # ====================================================================== #
    def set_arch_registers(self, registers):
        """Set native registers.
        """
        self._arch_regs = registers

    def set_arch_registers_size(self, registers_size):
        """Set native registers size.
        """
        self._arch_regs_size = registers_size

    def set_reg_access_mapper(self, reg_access_mapper):
        """Set native register access mapper.

        This is necessary as some architecture has register alias. For
        example, in Intel x86 (32 bits), *ax* refers to the lower half
        of the *eax* register, so when *ax* is modified so it is *eax*.
        Then, this reg_access_mapper is a dictionary where its keys are
        registers (names, only) and each associated value is a tuple
        of the form (base register name, bit mask (a.k.a filter), shift).
        This information is used to modified the correct register at
        the correct location (within the register) when a register alias
        value is changed.

        """
        self._reg_access_mapper = reg_access_mapper

    # Auxiliary functions
    # ======================================================================== #
    def _get_operand_value(self, operand):
        """Get value from operand.
        """
        if type(operand) == ReilRegisterOperand:
            return self._get_reg_value(operand, keep_track=True)
        elif type(operand) == ReilImmediateOperand:
            return operand.immediate
        else:
            raise Exception("Unknown operand type : %s" % str(operand))

    def _get_reg_value(self, register, keep_track=False):
        """Get register value.
        """
        assert register.size

        base_reg_name, offset = self._reg_access_mapper.get(register.name, (register.name, 0))

        if base_reg_name not in self._regs:
            self._regs[base_reg_name] = random.randint(0, 2**self._arch_regs_size[base_reg_name] - 1)

        reg_value = self._regs[base_reg_name]

        if keep_track and register.name in self._arch_regs:
            self._regs_read.add(register.name)

        value = self._extract_value(reg_value, offset, register.size)

        # Debug
        if verbose:
            print "          r{ %s = %s (%s = %s) }" % (register, hex(value), base_reg_name, hex(self._regs[base_reg_name]))
            # logger.debug("          r{ %s = %s (%s = %s) }" % (register, hex(value), base_reg_name, hex(self._regs[base_reg_name])))

        return value

    def _set_reg_value(self, register, value, keep_track=False):
        """Set register value.
        """
        assert register.size

        base_reg_name, offset = self._reg_access_mapper.get(register.name, (register.name, 0))

        reg_value = self._regs.get(base_reg_name, random.randint(0, 2**register.size - 1))

        self._regs[base_reg_name] = self._insert_value(reg_value, value, offset, register.size)

        if keep_track and register.name in self._arch_regs:
            self._regs_written.add(register.name)

        # Debug
        if verbose:
            print "          w{ %s = %s (%s = %s) }" % (register, hex(value), base_reg_name, hex(self._regs[base_reg_name]))
            # logger.debug("          w{ %s = %s (%s = %s) }" % (register, hex(value), base_reg_name, hex(self._regs[base_reg_name])))

    def _extract_value(self, main_value, offset, size):
        return (main_value >> offset) & 2**size-1

    def _insert_value(self, main_value, value_to_insert, offset, size):
        main_value &= ~((2**size-1) << offset)
        main_value |= (value_to_insert & 2**size-1) << offset

        return main_value

    # Arithmetic instructions
    # ======================================================================== #
    def _execute_add(self, instr):
        """Execute ADD instruction.
        """
        op1_val = self._get_operand_value(instr.operands[0])
        op2_val = self._get_operand_value(instr.operands[1])
        op3_val = op1_val + op2_val

        self._set_reg_value(instr.operands[2], op3_val, keep_track=True)

        return None

    def _execute_sub(self, instr):
        """Execute SUB instruction.
        """
        op1_val = self._get_operand_value(instr.operands[0])
        op2_val = self._get_operand_value(instr.operands[1])
        op3_val = op1_val - op2_val

        self._set_reg_value(instr.operands[2], op3_val, keep_track=True)

        # print "op1_val: ", op1_val
        # print "op2_val: ", op2_val
        # print "op3_val: ", op3_val

        # print "sub {0}, {1}, {2}".format(op1_val, op2_val, op3_val)

        return None

    def _execute_mul(self, instr):
        """Execute MUL instruction.
        """
        op1_val = self._get_operand_value(instr.operands[0])
        op2_val = self._get_operand_value(instr.operands[1])
        op3_val = op1_val * op2_val

        self._set_reg_value(instr.operands[2], op3_val, keep_track=True)

        return None

    def _execute_div(self, instr):
        """Execute DIV instruction.
        """
        # TODO: See how to manage exceptions (instr.operands[1] == 0)

        op1_val = self._get_operand_value(instr.operands[0])
        op2_val = self._get_operand_value(instr.operands[1])
        op3_val = op1_val / op2_val

        self._set_reg_value(instr.operands[2], op3_val, keep_track=True)

        return None

    def _execute_mod(self, instr):
        """Execute MOD instruction.
        """
        # TODO: See how to manage exceptions (instr.operands[1] == 0)

        op1_val = self._get_operand_value(instr.operands[0])
        op2_val = self._get_operand_value(instr.operands[1])
        op3_val = op1_val % op2_val

        self._set_reg_value(instr.operands[2], op3_val, keep_track=True)

        return None

    def _execute_bsh(self, instr):
        """Execute BSH instruction.
        """
        op1_val = self._get_operand_value(instr.operands[0])
        op2_val = self._get_operand_value(instr.operands[1])

        # Check sign bit.
        if op2_val & (2**(instr.operands[1].size-1)) == 0:
            op3_val = op1_val << op2_val
        else:
            # Compute two's complement.
            op2_val = 2**instr.operands[1].size - op2_val

            op3_val = op1_val >> op2_val

        # print "op1_val: ", op1_val
        # print "op2_val: ", op2_val
        # print "op3_val: ", op3_val

        # print "bsh {0}, {1}, {2}".format(op1_val, op2_val, op3_val)

        self._set_reg_value(instr.operands[2], op3_val, keep_track=True)

        return None

    # Bitwise instructions
    # ======================================================================== #
    def _execute_and(self, instr):
        """Execute AND instruction.
        """
        op1_val = self._get_operand_value(instr.operands[0])
        op2_val = self._get_operand_value(instr.operands[1])
        op3_val = op1_val & op2_val

        # print "op1_val: ", op1_val
        # print "op2_val: ", op2_val
        # print "op3_val: ", op3_val

        # print "and {0}, {1}, {2}".format(op1_val, op2_val, op3_val)

        self._set_reg_value(instr.operands[2], op3_val, keep_track=True)

        return None

    def _execute_or(self, instr):
        """Execute OR instruction.
        """
        op1_val = self._get_operand_value(instr.operands[0])
        op2_val = self._get_operand_value(instr.operands[1])
        op3_val = op1_val | op2_val

        # print "op1_val: ", op1_val
        # print "op2_val: ", op2_val
        # print "op3_val: ", op3_val

        # print "or {0}, {1}, {2}".format(op1_val, op2_val, op3_val)

        self._set_reg_value(instr.operands[2], op3_val, keep_track=True)

        return None

    def _execute_xor(self, instr):
        """Execute XOR instruction.
        """
        op1_val = self._get_operand_value(instr.operands[0])
        op2_val = self._get_operand_value(instr.operands[1])
        op3_val = op1_val ^ op2_val

        self._set_reg_value(instr.operands[2], op3_val, keep_track=True)

        return None

    # Data transfer instructions
    # ======================================================================== #
    def _execute_ldm(self, instr):
        """Execute LDM instruction.
        """
        assert instr.operands[0].size == self._address_size
        assert instr.operands[2].size in [8, 16, 32, 64]

        mem_addr = self._get_operand_value(instr.operands[0])
        value = self._mem.read(mem_addr, instr.operands[2].size)

        self._set_reg_value(instr.operands[2], value, keep_track=True)

        return None

    def _execute_stm(self, instr):
        """Execute STM instruction.
        """
        assert instr.operands[0].size in [8, 16, 32, 64]
        assert instr.operands[2].size == self._address_size

        value    = self._get_operand_value(instr.operands[0])
        mem_addr = self._get_operand_value(instr.operands[2])

        self._mem.write(mem_addr, instr.operands[0].size, value)

        return None

    def _execute_str(self, instr):
        """Execute STR instruction.
        """

        value = self._get_operand_value(instr.operands[0])

        # print "op1_val: ", value
        # print "op3_val: ", value

        # print "str {0}, EMPTY, {1}".format(value, value)

        self._set_reg_value(instr.operands[2], value, keep_track=True)

        return None

    # Conditional instructions
    # ======================================================================== #
    def _execute_bisz(self, instr):
        """Execute BISZ instruction.
        """
        op1_val = self._get_operand_value(instr.operands[0])
        op3_val = 1 if op1_val == 0 else 0

        self._set_reg_value(instr.operands[2], op3_val, keep_track=True)

        return None

    def _execute_jcc(self, instr):
        """Execute JCC instruction.
        """
        op1_val = self._get_operand_value(instr.operands[0])
        op3_val = self._get_operand_value(instr.operands[2])

        if op1_val != 0:
            return op3_val
        else:
            return None

    # Other instructions
    # ======================================================================== #
    def _execute_undef(self, instr):
        """Execute UNDEF instruction.
        """
        op3_val = random.randint(0, instr.operands[2].size)

        self._set_reg_value(instr.operands[2], op3_val, keep_track=True)

        return None

    def _execute_unkn(self, instr):
        """Execute UNKN instruction.
        """
        raise Exception("Unknown instruction (UNKN).")

    def _execute_nop(self, instr):
        """Execute NOP instruction.
        """
        return None

    # Ad hoc Instructions
    # ======================================================================== #
    def _execute_ret(self, instr):
        """Execute RET instruction.
        """
        pass

    # Extension
    # ======================================================================== #
    def _execute_sext(self, instr):
        """Execute SEXT instruction.
        """
        op1_size = instr.operands[0].size
        op3_size = instr.operands[2].size

        op1_val = self._get_operand_value(instr.operands[0])
        op1_msb = op1_val >> (op1_size-1)

        op3_mask = (2**op3_size-1) & ~(2**op1_size-1) if op1_msb == 1 else 0x0

        op3_val = op1_val | op3_mask

        self._set_reg_value(instr.operands[2], op3_val, keep_track=True)

        return None
