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

import random

from barf.core.reil.reil import ReilImmediateOperand
from barf.core.reil.reil import ReilMnemonic
from barf.core.reil.reil import ReilRegisterOperand

# verbose = False
verbose = True

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

        self._taints = {}

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

        if verbose:
            taint = self.get_taint(address, size)
            self._debug_read_memory(address, value, taint)

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
        for i in xrange(0, size / 8):
            self.write_byte(address + i, (value >> (i * 8)) & 0xff)

        self._write_count += 1

        if verbose:
            taint = self.get_taint(address, size)
            self._debug_write_memory(address, value, taint)

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

    # Taint functions
    # ======================================================================== #
    def set_taint(self, address, size, taint):
        for i in xrange(0, size / 8):
            self._taints[address + i] = taint

    def get_taint(self, address, size):
        tainted = False

        for i in xrange(0, size / 8):
            tainted = tainted or self._taints.get(address + i, False)

        return tainted

    # Auxiliary functions
    # ======================================================================== #
    def _debug_read_memory(self, addr, val, tainted):
        fmt = "{indent}r{{ m[{addr:08x}] = {val:08x} [{taint:s}]}}"
        taint = "T" if tainted else "-"
        msg = fmt.format(indent=" "*10, addr=addr , val=val, taint=taint)

        print(msg)

    def _debug_write_memory(self, addr, val, tainted):
        fmt = "{indent}w{{ m[{addr:08x}] = {val:08x} [{taint:s}]}}"
        taint = "T" if tainted else "-"
        msg = fmt.format(indent=" "*10, addr=addr , val=val, taint=taint)

        print(msg)


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

        # Set of read and write memory addresses during execution.
        self._mem_written = set()
        self._mem_read = set()

        self._arch_regs = []
        self._arch_regs_size = {}
        self._alias_mapper = {}

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
        }

        # Taint information.
        self._taints = {}

        self._process = None

    def execute_lite(self, instructions, context=None):
        """Execute a list of instructions. It does not support loops.
        """
        # if verbose:
        #     print "[+] Executing instructions..."

        if context:
            self._regs = context.copy()

        for index, instr in enumerate(instructions):
            if verbose:
                print("0x%08x:%02x : %s" % (instr.address >> 8, instr.address & 0xff, instr))
                # print "    %03d : %s" % (index, instr)

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
                print("    0x%08x:%02x : %s" % (self._ip >> 8, self._ip & 0xff, instr))
                # print "    %03d : %s" % (main_index, instr)

            # execute instruction
            next_addr = self._executors[instr.mnemonic](instr)

            # update instruction pointer
            if next_addr:
                for idx, instrs in enumerate(instructions):
                    if instrs[0].address >> 8 == next_addr >> 8:
                        main_index = idx
                        sub_index = next_addr & 0xff
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

            if self._ip == end_address:
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
    def context(self):
        """Set context.
        """
        return self._regs

    @context.setter
    def context(self, value):
        """Get context.
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
        """Return write (native) registers.
        """
        return self._regs_written

    # ====================================================================== #
    # TODO: Remove function. Use ArchitectureInformation instead.
    def set_arch_registers(self, registers):
        """Set native registers.
        """
        self._arch_regs = registers

    # TODO: Remove function. Use ArchitectureInformation instead.
    def set_arch_registers_size(self, registers_size):
        """Set native registers size.
        """
        self._registers_size = registers_size

    # TODO: Remove function. Use ArchitectureInformation instead.
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
        self._alias_mapper = reg_access_mapper

    # Taint functions
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

    # Taint auxiliary functions
    # ======================================================================== #
    def _get_register_taint(self, register):
        if register.name in self._alias_mapper and register.name not in self._flags:
            base_name, _ = self._alias_mapper[register.name]
        else:
            base_name = register.name

        return self._taints.get(base_name, False)

    def _set_register_taint(self, register, taint):
        if register.name in self._alias_mapper and register.name not in self._flags:
            base_name, _ = self._alias_mapper[register.name]
        else:
            base_name = register.name

        self._taints[base_name] = taint

        if verbose:
            reg = register.name
            base_reg = base_name

            fmt = "{indent}t{{ {reg:s} ({base_reg:s})}}"

            msg = fmt.format(indent=" "*10, reg=reg, base_reg=base_reg)

            print(msg)

    # Read/Write functions
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

    # Read/Write auxiliary functions
    # ======================================================================== #
    def _read_register(self, register):
        if register.name in self._alias_mapper:
            base_reg_name, offset = self._alias_mapper[register.name]
            base_reg_size = self._registers_size[base_reg_name]
        else:
            base_reg_name, offset = register.name, 0
            base_reg_size = register.size

        # TODO: Rename _regs to _context.
        if base_reg_name in self._regs:
            base_val = self._regs[base_reg_name]
        else:
            base_val = random.randint(0, 2**base_reg_size - 1)

        reg_val = self._extract_value(base_val, offset, register.size)

        # Keep track of native register reads.
        if register.name in self._arch_regs:
            self._regs_read.add(register.name)

        # Debug
        if verbose:
            taint = self._get_register_taint(register)
            self._debug_read_operand(register, reg_val, base_reg_name, base_val, taint)

        return reg_val

    def _write_register(self, register, value):
        if register.name in self._alias_mapper:
            base_reg_name, offset = self._alias_mapper[register.name]
            base_reg_size = self._registers_size[base_reg_name]
        else:
            base_reg_name, offset = register.name, 0
            base_reg_size = register.size

        # TODO: Rename _regs to _context.
        if base_reg_name in self._regs:
            base_val = self._regs[base_reg_name]
        else:
            base_val = random.randint(0, 2**base_reg_size - 1)

        self._regs[base_reg_name] = self._insert_value(base_val, value, offset, register.size)

        # Keep track of native register writes.
        if register.name in self._arch_regs:
            self._regs_written.add(register.name)

        # Debug
        if verbose:
            taint = self._get_register_taint(register)
            self._debug_write_operand(register, value, base_reg_name, self._regs[base_reg_name], taint)

    def _extract_value(self, main_value, offset, size):
        return (main_value >> offset) & 2**size-1

    def _insert_value(self, main_value, value_to_insert, offset, size):
        main_value &= ~((2**size-1) << offset)
        main_value |= (value_to_insert & 2**size-1) << offset

        return main_value

    def _debug_read_operand(self, reg, val, base_reg, base_val, tainted):
        fmt = "{indent}r{{ {reg:s} = {val:08x} [{taint:s}] ({base_reg:s} = {base_val:08x})}}"

        taint = "T" if tainted == True else "-"

        msg = fmt.format(
            indent=" "*10, reg=reg , val=val, base_reg=base_reg,
            base_val=base_val, taint=taint
        )

        print(msg)

    def _debug_write_operand(self, reg, val, base_reg, base_val, tainted):
        fmt = "{indent}w{{ {reg:s} = {val:08x} [{taint:s}] ({base_reg:s} = {base_val:08x})}}"

        taint = "T" if tainted else "-"

        msg = fmt.format(
            indent=" "*10, reg=reg , val=val, base_reg=base_reg,
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
        # TODO: See how to manage exceptions (instr.operands[1] == 0)
        op0_val = self.read_operand(instr.operands[0])
        op1_val = self.read_operand(instr.operands[1])
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
        # TODO: See how to manage exceptions (instr.operands[1] == 0)
        op0_val = self.read_operand(instr.operands[0])
        op1_val = self.read_operand(instr.operands[1])
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
            # Compute two's complement.
            op1_val = 2**op1_size - op1_val

            op2_val = op0_val >> op1_val

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

		# FIXME: Ugly, ugly hack!! Remove!
        size = instr.operands[2].size

        for i in xrange(0, size / 8):
            if not self._mem._memory.has_key(op0_val + i):
                try:
                    chunk = self._process.readBytes(op0_val + i, 1)

                    self.write_memory(op0_val + i, 8, ord(chunk))
                except:
                    pass

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

        return op2_val if op0_val == 1 else None

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
