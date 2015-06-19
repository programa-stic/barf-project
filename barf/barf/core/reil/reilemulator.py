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

from collections import defaultdict

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
        self._address_size = address_size

        # Memory's endianness.
        self._endianness = REIL_MEMORY_ENDIANNESS_LE

        # Dictionary that implements the memory itself.
        self._memory = {}

        # Taint information.
        self._taints = {}

        # Previous state of memory. Requiere for some *special*
        # functions.
        self._memory_prev = {}

        # Write operations counter.
        self._write_count = 0

    # Read methods
    # ======================================================================== #
    def read(self, address, size):
        """Read arbitrary size content from memory.
        """
        value = 0x0

        for i in xrange(0, size / 8):
            value = self._read_byte(address + i) << (i * 8) | value

        if verbose:
            taint = self.get_taint(address, size)
            self._debug_read_memory(address, value, taint)

        return value

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

        for i in xrange(0, size / 8):
            addr = address + i

            if addr in self._memory_prev:
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
        if not address in self._memory:
            self._memory[address] = random.randint(0x00, 0xff)

        return self._memory[address]

    def _try_read_byte_prev(self, address):
        """Read previous value for memory location.

        Return a tuple (True, Byte) in case of successful read,
        (False, None) otherwise.

        """
        # Initialize memory location with a random value
        if not address in self._memory_prev:
            return False, None

        return True, self._memory_prev[address]

    # Write methods
    # ======================================================================== #
    def write(self, address, size, value):
        """Write arbitrary size content to memory.
        """
        for i in xrange(0, size / 8):
            self._write_byte(address + i, (value >> (i * 8)) & 0xff)

        self._write_count += 1

        if verbose:
            taint = self.get_taint(address, size)
            self._debug_write_memory(address, value, taint)

    # Auxiliary write methods
    # ======================================================================== #
    def _write_byte(self, address, value):
        """Write byte in memory.
        """
        # Save previous address content.
        if address in self._memory:
            self._memory_prev[address] = self._memory[address]

        self._memory[address] = value & 0xff

    # Misc methods
    # ======================================================================== #
    def get_addresses(self):
        """Get accessed addresses.
        """
        return self._memory.keys()

    def get_write_count(self):
        """Get number of write operations performed on the memory.
        """
        return self._write_count

    def reset(self):
        # Dictionary that implements the memory itself.
        self._memory = {}

        # Taint information.
        self._taints = {}

        # Previous state of memory. Requiere for some *special*
        # functions.
        self._memory_prev = {}

        # Write operations counter.
        self._write_count = 0

    # Taint methods
    # ======================================================================== #
    def set_taint(self, address, size, taint):
        for i in xrange(0, size / 8):
            self._taints[address + i] = taint

    def get_taint(self, address, size):
        tainted = False

        for i in xrange(0, size / 8):
            tainted = tainted or self._taints.get(address + i, False)

        return tainted

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

        for addr in sorted(self._memory.keys()):
            lines += ["0x%08x : 0x%08x" % (addr, self._memory[addr])]

        return "\n".join(lines)


class ReilEmulatorZeroDivisionError(Exception):
    pass


class ReilEmulatorInvalidAddressError(Exception):
    pass


class ReilEmulator(object):

    """Reil Emulator."""

    def __init__(self, address_size):

        # TODO: Pass ReilMemory as a parameter.

        # Memory address size.
        self._address_size = address_size

        # An instance of a ReilMemory.
        self._mem = ReilMemory(self._address_size)

        # Instruction Pointer.
        self._ip = None

        # Registers.
        self._regs = {}

        # Set of read and write registers during execution.
        self._regs_written = set()
        self._regs_read = set()

        # Architecture information.
        self._arch_regs = []
        self._arch_flags = []
        self._arch_regs_size = {}
        self._arch_alias_mapper = {}

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

        # Taint information.
        self._taints_regs = {}

        # Instructions pre and post handlers.
        self._instr_pre_handler = {}
        self._instr_post_handler = {}

        self._instr_pre_handler_global = {}
        self._instr_post_handler_global = {}

        self._set_default_instruction_handlers()

    # Instruction's handler methods
    # ======================================================================== #
    def set_instruction_pre_handler(self, mnemonic, function, parameter):
        self._instr_pre_handler[mnemonic] = (function, parameter)

    def set_instruction_post_handler(self, mnemonic, function, parameter):
        self._instr_post_handler[mnemonic] = (function, parameter)

    def set_instruction_pre_handler_global(self, function, parameter):
        self._instr_pre_handler_global = (function, parameter)

    def set_instruction_post_handler_global(self, function, parameter):
        self._instr_post_handler_global = (function, parameter)

    # Instruction's handler auxiliary methods
    # ======================================================================== #
    def _set_default_instruction_handlers(self):
        empty_fn = lambda emu, instr, param: None
        empty_param = None

        self._instr_pre_handler = defaultdict(lambda: (empty_fn, empty_param))
        self._instr_post_handler = defaultdict(lambda: (empty_fn, empty_param))

        self._instr_pre_handler_global = (empty_fn, empty_param)
        self._instr_post_handler_global = (empty_fn, empty_param)

    # Execution methods
    # ======================================================================== #
    def execute_lite(self, instructions, context=None):
        """Execute a list of instructions. It does not support loops.
        """
        if verbose:
            print("[+] Executing instructions...")

        if context:
            self._regs = context.copy()

        for instr in instructions:
            self._execute_one(instr)

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

        if start_address == None:
            self._ip = instructions[main_index][sub_index].address
        else:
            next_addr = start_address

            found = False

            for idx, instrs in enumerate(instructions):
                if instrs[0].address >> 8 == next_addr >> 8:
                    main_index = idx
                    sub_index = next_addr & 0xff

                    found = True

            if not found:
                raise ReilEmulatorInvalidAddressError("Invalid address: %s" % hex(next_addr))

            self._ip = instructions[main_index][sub_index].address

        instr_count = 0

        while True:
            # fetch instruction
            instr = instructions[main_index][sub_index]

            # execute instruction
            next_addr = self._execute_one(instr)

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
                    raise ReilEmulatorInvalidAddressError("Invalid address: %s" % hex(next_addr))
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

    # Auxiliary execution methods
    # ======================================================================== #
    def _execute_one(self, instr):
        if verbose:
            print("0x%08x:%02x : %s" % (instr.address >> 8, instr.address & 0xff, instr))

        pre_handler_fn, pre_handler_param = self._instr_pre_handler[instr.mnemonic]
        post_handler_fn, post_handler_param = self._instr_post_handler[instr.mnemonic]

        pre_handler_fn_global, pre_handler_param_global = self._instr_pre_handler_global
        post_handler_fn_global, post_handler_param_global = self._instr_post_handler_global

        # Execute pre instruction handlers
        pre_handler_fn(self, instr, pre_handler_param)
        pre_handler_fn_global(self, instr, pre_handler_param_global)

        # Execute instruction
        next_addr = self._executors[instr.mnemonic](instr)

        # Execute post instruction handlers
        post_handler_fn(self, instr, post_handler_param)
        post_handler_fn_global(self, instr, post_handler_param_global)

        return next_addr

    # Misc methods
    # ======================================================================== #
    def reset(self):
        """Reset emulator. All registers and memory are reset.
        """
        # An instance of a ReilMemory.
        self._mem = ReilMemory(self._address_size)

        # Instruction Pointer.
        self._ip = None

        # Registers.
        self._regs = {}

        # Set of read and write registers during execution.
        self._regs_written = set()
        self._regs_read = set()

        # Taint information.
        self._taints_regs = {}

        # Instructions pre and post handlers.
        self._instr_pre_handler = {}
        self._instr_post_handler = {}

        self._instr_pre_handler_global = {}
        self._instr_post_handler_global = {}

        self._set_default_instruction_handlers()

    def reset_memory(self):
        self._mem.reset()

    # Properties
    # ======================================================================== #
    @property
    def registers(self):
        """Return registers.
        """
        return self._regs

    @registers.setter
    def registers(self, value):
        """Return registers.
        """
        self._regs = dict(value)

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
        """Return written (native) registers.
        """
        return self._regs_written

    # Architecture information methods
    # ======================================================================== #
    # TODO: Remove function. Use ArchitectureInformation instead.
    def set_arch_registers(self, registers):
        """Set native registers.
        """
        self._arch_regs = registers

    # TODO: Remove function. Use ArchitectureInformation instead.
    def set_arch_flags(self, flags):
        """Set native flags.
        """
        self._arch_flags = flags

    # TODO: Remove function. Use ArchitectureInformation instead.
    def set_arch_registers_size(self, registers_size):
        """Set native registers size.
        """
        self._arch_regs_size = registers_size

    # TODO: Remove function. Use ArchitectureInformation instead.
    def set_arch_alias_mapper(self, alias_mapper):
        """Set native register alias mapper.

        This is necessary as some architecture has register alias. For
        example, in Intel x86 (32 bits), *ax* refers to the lower half
        of the *eax* register, so when *ax* is modified so it is *eax*.
        Then, this alias_mapper is a dictionary where its keys are
        registers (names, only) and each associated value is a tuple
        of the form (base register name, offset).
        This information is used to modified the correct register at
        the correct location (within the register) when a register alias
        value is changed.

        """
        self._arch_alias_mapper = alias_mapper

    # Taint methods
    # ======================================================================== #
    def get_operand_taint(self, operand):
        if isinstance(operand, ReilRegisterOperand):
            taint = self._get_register_taint(operand)
        elif isinstance(operand, ReilImmediateOperand):
            taint = False
        else:
            raise Exception("Invalid operand: %s" % str(operand))

        return taint

    def set_operand_taint(self, operand, taint):
        if isinstance(operand, ReilRegisterOperand):
            self._set_register_taint(operand, taint)
        else:
            raise Exception("Invalid operand: %s" % str(operand))

    def get_memory_taint(self, address, size):
        return self._mem.get_taint(address, size)

    def set_memory_taint(self, address, size, taint):
        self._mem.set_taint(address, size, taint)

    # Taint auxiliary methods
    # ======================================================================== #
    def _get_register_taint(self, register):
        if register.name in self._arch_alias_mapper and register.name not in self._arch_flags:
            base_name, _ = self._arch_alias_mapper[register.name]
        else:
            base_name = register.name

        return self._taints_regs.get(base_name, False)

    def _set_register_taint(self, register, taint):
        if register.name in self._arch_alias_mapper and register.name not in self._arch_flags:
            base_name, _ = self._arch_alias_mapper[register.name]
        else:
            base_name = register.name

        self._taints_regs[base_name] = taint

        if verbose:
            reg = register.name
            base_reg = base_name

            fmt = "{indent}t{{ {reg:s} ({base_reg:s})}}"

            msg = fmt.format(indent=" "*10, reg=reg, base_reg=base_reg)

            print(msg)

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
        return self._mem.read(address, size)

    def write_memory(self, address, size, value):
        self._mem.write(address, size, value)

    # Read/Write auxiliary methods
    # ======================================================================== #
    def _get_register_value(self, register):
        if register.name in self._arch_alias_mapper:
            base_reg_name, offset = self._arch_alias_mapper[register.name]
            base_reg_size = self._arch_regs_size[base_reg_name]
        else:
            base_reg_name, offset = register.name, 0
            base_reg_size = register.size

        if base_reg_name in self._regs:
            base_val = self._regs[base_reg_name]
        else:
            base_val = random.randint(0, 2**base_reg_size - 1)

        return base_reg_name, base_val, offset

    def _read_register(self, register):
        base_reg_name, base_val, offset = self._get_register_value(register)

        reg_val = extract_value(base_val, offset, register.size)

        # Keep track of native register reads.
        if register.name in self._arch_regs:
            self._regs_read.add(register.name)

        # Debug
        if verbose:
            taint = self._get_register_taint(register)
            self._debug_read_operand(register, reg_val, base_reg_name, base_val, taint)

        return reg_val

    def _write_register(self, register, value):
        base_reg_name, base_val, offset = self._get_register_value(register)

        self._regs[base_reg_name] = insert_value(base_val, value, offset, register.size)

        # Keep track of native register writes.
        if register.name in self._arch_regs:
            self._regs_written.add(register.name)

        # Debug
        if verbose:
            taint = self._get_register_taint(register)
            self._debug_write_operand(register, value, base_reg_name, self._regs[base_reg_name], taint)

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
    def _execute_add(self, instr):
        """Execute ADD instruction.
        """
        op0_val = self.read_operand(instr.operands[0])
        op1_val = self.read_operand(instr.operands[1])
        op2_val = op0_val + op1_val

        # Get taint information.
        op0_taint = self.get_operand_taint(instr.operands[0])
        op1_taint = self.get_operand_taint(instr.operands[1])

        # Propagate taint.
        self.set_operand_taint(instr.operands[2], op0_taint or op1_taint)

        self.write_operand(instr.operands[2], op2_val)

        return None

    def _execute_sub(self, instr):
        """Execute SUB instruction.
        """
        op0_val = self.read_operand(instr.operands[0])
        op1_val = self.read_operand(instr.operands[1])
        op2_val = op0_val - op1_val

        # Get taint information.
        op0_taint = self.get_operand_taint(instr.operands[0])
        op1_taint = self.get_operand_taint(instr.operands[1])

        # Propagate taint.
        self.set_operand_taint(instr.operands[2], op0_taint or op1_taint)

        self.write_operand(instr.operands[2], op2_val)

        return None

    def _execute_mul(self, instr):
        """Execute MUL instruction.
        """
        op0_val = self.read_operand(instr.operands[0])
        op1_val = self.read_operand(instr.operands[1])
        op2_val = op0_val * op1_val

        # Get taint information.
        op0_taint = self.get_operand_taint(instr.operands[0])
        op1_taint = self.get_operand_taint(instr.operands[1])

        # Propagate taint.
        self.set_operand_taint(instr.operands[2], op0_taint or op1_taint)

        self.write_operand(instr.operands[2], op2_val)

        return None

    def _execute_div(self, instr):
        """Execute DIV instruction.
        """
        op0_val = self.read_operand(instr.operands[0])
        op1_val = self.read_operand(instr.operands[1])

        if op1_val == 0:
            raise ReilEmulatorZeroDivisionError()

        op2_val = op0_val / op1_val

        # Get taint information.
        op0_taint = self.get_operand_taint(instr.operands[0])
        op1_taint = self.get_operand_taint(instr.operands[1])

        # Propagate taint.
        self.set_operand_taint(instr.operands[2], op0_taint or op1_taint)

        self.write_operand(instr.operands[2], op2_val)

        return None

    def _execute_mod(self, instr):
        """Execute MOD instruction.
        """
        op0_val = self.read_operand(instr.operands[0])
        op1_val = self.read_operand(instr.operands[1])

        if op1_val == 0:
            raise ReilEmulatorZeroDivisionError()

        op2_val = op0_val % op1_val

        # Get taint information.
        op0_taint = self.get_operand_taint(instr.operands[0])
        op1_taint = self.get_operand_taint(instr.operands[1])

        # Propagate taint.
        self.set_operand_taint(instr.operands[2], op0_taint or op1_taint)

        self.write_operand(instr.operands[2], op2_val)

        return None

    def _execute_bsh(self, instr):
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

        # Get taint information.
        op0_taint = self.get_operand_taint(instr.operands[0])
        op1_taint = self.get_operand_taint(instr.operands[1])

        # Propagate taint.
        self.set_operand_taint(instr.operands[2], op0_taint or op1_taint)

        self.write_operand(instr.operands[2], op2_val)

        return None

    # Bitwise instructions
    # ======================================================================== #
    def _execute_and(self, instr):
        """Execute AND instruction.
        """
        op0_val = self.read_operand(instr.operands[0])
        op1_val = self.read_operand(instr.operands[1])
        op2_val = op0_val & op1_val

        # Get taint information.
        op0_taint = self.get_operand_taint(instr.operands[0])
        op1_taint = self.get_operand_taint(instr.operands[1])

        # Propagate taint.
        self.set_operand_taint(instr.operands[2], op0_taint or op1_taint)

        self.write_operand(instr.operands[2], op2_val)

        return None

    def _execute_or(self, instr):
        """Execute OR instruction.
        """
        op0_val = self.read_operand(instr.operands[0])
        op1_val = self.read_operand(instr.operands[1])
        op2_val = op0_val | op1_val

        # Get taint information.
        op0_taint = self.get_operand_taint(instr.operands[0])
        op1_taint = self.get_operand_taint(instr.operands[1])

        # Propagate taint.
        self.set_operand_taint(instr.operands[2], op0_taint or op1_taint)

        self.write_operand(instr.operands[2], op2_val)

        return None

    def _execute_xor(self, instr):
        """Execute XOR instruction.
        """
        op0_val = self.read_operand(instr.operands[0])
        op1_val = self.read_operand(instr.operands[1])
        op2_val = op0_val ^ op1_val

        # Get taint information.
        op0_taint = self.get_operand_taint(instr.operands[0])
        op1_taint = self.get_operand_taint(instr.operands[1])

        # Propagate taint.
        self.set_operand_taint(instr.operands[2], op0_taint or op1_taint)

        self.write_operand(instr.operands[2], op2_val)

        return None

    # Data transfer instructions
    # ======================================================================== #
    def _execute_ldm(self, instr):
        """Execute LDM instruction.
        """
        assert instr.operands[0].size == self._address_size
        assert instr.operands[2].size in [8, 16, 32, 64]

        op0_val = self.read_operand(instr.operands[0])                  # Memory address.
        op2_val = self.read_memory(op0_val, instr.operands[2].size)     # Data.

        # Get taint information.
        op0_taint = self.get_memory_taint(op0_val, instr.operands[2].size)

        # Propagate taint.
        self.set_operand_taint(instr.operands[2], op0_taint)

        self.write_operand(instr.operands[2], op2_val)

        return None

    def _execute_stm(self, instr):
        """Execute STM instruction.
        """
        assert instr.operands[0].size in [8, 16, 32, 64]
        assert instr.operands[2].size == self._address_size

        op0_val = self.read_operand(instr.operands[0])  # Data.
        op2_val = self.read_operand(instr.operands[2])  # Memory address.

        op0_size = instr.operands[0].size

        # Get taint information.
        op0_taint = self.get_operand_taint(instr.operands[0])

        # Propagate taint.
        self.set_memory_taint(op2_val, op0_size, op0_taint)

        self.write_memory(op2_val, op0_size, op0_val)

        return None

    def _execute_str(self, instr):
        """Execute STR instruction.
        """
        op0_val = self.read_operand(instr.operands[0])

        # Get taint information.
        op0_taint = self.get_operand_taint(instr.operands[0])

        # Propagate taint.
        self.set_operand_taint(instr.operands[2], op0_taint)

        self.write_operand(instr.operands[2], op0_val)

        return None

    # Conditional instructions
    # ======================================================================== #
    def _execute_bisz(self, instr):
        """Execute BISZ instruction.
        """
        op0_val = self.read_operand(instr.operands[0])
        op2_val = 1 if op0_val == 0 else 0

        # Get taint information.
        op0_taint = self.get_operand_taint(instr.operands[0])

        # Propagate taint.
        self.set_operand_taint(instr.operands[2], op0_taint)

        self.write_operand(instr.operands[2], op2_val)

        return None

    def _execute_jcc(self, instr):
        """Execute JCC instruction.
        """
        op0_val = self.read_operand(instr.operands[0])  # Branch condition.
        op2_val = self.read_operand(instr.operands[2])  # Target address.

        return op2_val if op0_val != 0 else None

    # Other instructions
    # ======================================================================== #
    def _execute_undef(self, instr):
        """Execute UNDEF instruction.
        """
        op2_val = random.randint(0, instr.operands[2].size)

        self.write_operand(instr.operands[2], op2_val)

        # Propagate taint.
        self.set_operand_taint(instr.operands[2], False)

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
        op0_size = instr.operands[0].size
        op2_size = instr.operands[2].size

        op0_val = self.read_operand(instr.operands[0])
        op0_msb = op0_val >> (op0_size-1)

        op2_mask = (2**op2_size-1) & ~(2**op0_size-1) if op0_msb == 1 else 0x0

        op2_val = op0_val | op2_mask

        # Get taint information.
        op0_taint = self.get_operand_taint(instr.operands[0])

        # Propagate taint.
        self.set_operand_taint(instr.operands[2], op0_taint)

        self.write_operand(instr.operands[2], op2_val)

        return None
