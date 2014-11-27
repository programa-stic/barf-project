"""
This module contains all lthe classes that handle the x86 instruction
representation.

"""

from barf.arch import ARCH_X86_MODE_32
from barf.arch import ARCH_X86_MODE_64
from barf.arch import ArchitectureInformation

# TODO: This class need a *heavy* refactor.
class X86ArchitectureInformation(ArchitectureInformation):

    """This class describe the Intel x86 architecture.
    """

    registers_seg = [
        "cs", "ds", "ss", "es", "fs", "gs",
    ]

    registers_gp_8b_mode_32 = [
        "al", "ah", "bl", "bh", "cl", "ch", "dl", "dh",
    ]

    registers_gp_8b_mode_64 = [
        "dil", "sil", "bpl", "spl",
        "r8b", "r9b", "r10b", "r11b", "r12b", "r13b", "r14b", "r15b",
    ]

    registers_gp_16b_mode_32 = [
        "ax", "bx", "cx", "dx", "bp", "si", "di", "sp",
    ]

    registers_gp_16b_mode_64 = [
        "r8w", "r9w", "r10w", "r11w", "r12w", "r13w", "r14w", "r15w",
    ]

    registers_gp_32b_mode_32 = [
        "eax", "ebx", "ecx", "edx", "ebp", "esi", "edi", "esp", "eip", "eflags"
    ]

    registers_gp_32b_mode_64 = [
        "r8d", "r9d", "r10d", "r11d", "r12d", "r13d", "r14d", "r15d",
    ]

    registers_gp_64b = [
        "rax", "rbx", "rcx", "rdx", "rdi", "rsi", "rbp", "rsp", "rip",
        "r8", "r9", "r10", "r11", "r12", "r13", "r14", "r15", "rflags"
    ]

    registers_fpu = [
        "st0", "st1", "st2", "st3", "st4", "st5", "st6", "st7",
        "st(0)", "st(1)", "st(2)", "st(3)", "st(4)", "st(5)", "st(6)", "st(7)",
    ]

    registers_mmx = [
        "mm0", "mm1", "mm2", "mm3", "mm4", "mm5", "mm6", "mm7",
    ]

    registers_sse_mode_32 = [
        "xmm0", "xmm1", "xmm2", "xmm3", "xmm4", "xmm5", "xmm6", "xmm7",
    ]

    registers_sse_mode_64 = [
        "xmm8", "xmm9", "xmm10", "xmm11", "xmm12", "xmm13", "xmm14", "xmm15",
    ]

    registers_avx_mode_32 = [
        "ymm0", "ymm1", "ymm2", "ymm3", "ymm4", "ymm5", "ymm6", "ymm7",
    ]

    registers_avx_mode_64 = [
        "ymm8", "ymm9", "ymm10", "ymm11", "ymm12", "ymm13", "ymm14", "ymm15",
    ]

    flags = [
        "af", "cf", "of", "pf", "sf", "zf",
        "df",
    ]

    debug_registers = [
        "dr0", "dr1", "dr2", "dr3", "dr4", "dr5", "dr6", "dr7"
    ]

    control_registers = [
        "cr0", "cr1", "cr2", "cr3", "cr4"
    ]

    def __init__(self, architecture_mode):
        self._arch_mode = architecture_mode
        self._registers = []
        self._registers_size = {}

        self._load_registers()
        self._load_registers_size()

    @property
    def architecture_mode(self):
        return self._arch_mode

    @property
    def architecture_size(self):
        arch_size_map = {
            ARCH_X86_MODE_32 : 32,
            ARCH_X86_MODE_64 : 64,
        }

        return arch_size_map[self._arch_mode]

    @property
    def operand_size(self):
        operand_size_map = {
            ARCH_X86_MODE_32 : 32,
            ARCH_X86_MODE_64 : 64,
        }

        return operand_size_map[self._arch_mode]

    @property
    def address_size(self):
        address_size_map = {
            ARCH_X86_MODE_32 : 32,
            ARCH_X86_MODE_64 : 64,
        }

        return address_size_map[self._arch_mode]

    @property
    def registers(self):
        """Return general purpose registers.
        """
        return self._registers

    @property
    def registers_gp(self):
        """Return general purpose registers.
        """
        return self._registers_gp

    @property
    def registers_gp_parent(self):
        """Return general purpose registers.
        """
        return [reg for reg in self._registers_gp if not reg in self.register_access_mapper()]

    @property
    def registers_base(self):
        if self._arch_mode == ARCH_X86_MODE_32:
            return self.registers_gp_32b_mode_32
        else:
            return self.registers_gp_64b

    @property
    def registers_flags(self):
        return self.flags

    @property
    def register_size(self):
        """Return general purpose registers size.
        """
        return self._registers_size

    def _load_registers(self):
        if self._arch_mode == ARCH_X86_MODE_32:
            self._registers = \
                self.registers_gp_8b_mode_32  + \
                self.registers_gp_16b_mode_32 + \
                self.registers_gp_32b_mode_32 + \
                self.registers_sse_mode_32 + \
                self.registers_avx_mode_32

            self._registers_gp = \
                self.registers_gp_8b_mode_32  + \
                self.registers_gp_16b_mode_32 + \
                self.registers_gp_32b_mode_32
        else:
            self._registers = \
                self.registers_gp_8b_mode_32  + \
                self.registers_gp_8b_mode_64  + \
                self.registers_gp_16b_mode_32 + \
                self.registers_gp_16b_mode_64 + \
                self.registers_gp_32b_mode_32 + \
                self.registers_gp_32b_mode_64 + \
                self.registers_gp_64b + \
                self.registers_sse_mode_32 + \
                self.registers_sse_mode_64 + \
                self.registers_avx_mode_32 + \
                self.registers_avx_mode_64

            self._registers_gp = \
                self.registers_gp_8b_mode_32  + \
                self.registers_gp_8b_mode_64  + \
                self.registers_gp_16b_mode_32 + \
                self.registers_gp_16b_mode_64 + \
                self.registers_gp_32b_mode_32 + \
                self.registers_gp_32b_mode_64 + \
                self.registers_gp_64b

        self._registers += \
            self.registers_fpu + \
            self.registers_mmx + \
            self.flags + \
            self.registers_seg + \
            self.debug_registers + \
            self.control_registers

    def _load_registers_size(self):
        for reg in self._registers:
            if reg in self.registers_seg:
                self._registers_size[reg] = 16
            elif reg in self.registers_gp_8b_mode_32:
                self._registers_size[reg] = 8
            elif reg in self.registers_gp_8b_mode_64:
                self._registers_size[reg] = 8
            elif reg in self.registers_gp_16b_mode_32:
                self._registers_size[reg] = 16
            elif reg in self.registers_gp_16b_mode_64:
                self._registers_size[reg] = 16
            elif reg in self.registers_gp_32b_mode_32:
                self._registers_size[reg] = 32
            elif reg in self.registers_gp_32b_mode_64:
                self._registers_size[reg] = 32
            elif reg in self.registers_gp_64b:
                self._registers_size[reg] = 64
            elif reg in self.registers_fpu:
                self._registers_size[reg] = 80
            elif reg in self.registers_mmx:
                self._registers_size[reg] = 64
            elif reg in self.registers_sse_mode_32:
                self._registers_size[reg] = 128
            elif reg in self.registers_sse_mode_64:
                self._registers_size[reg] = 128
            elif reg in self.registers_avx_mode_32:
                self._registers_size[reg] = 256
            elif reg in self.registers_avx_mode_64:
                self._registers_size[reg] = 256
            elif reg in self.flags:
                self._registers_size[reg] = 1
            elif reg in self.debug_registers:
                self._registers_size[reg] = 32
            elif reg in self.control_registers:
                self._registers_size[reg] = 32
            else:
                raise Exception()

    def register_access_mapper(self):
        if self._arch_mode == ARCH_X86_MODE_32:
            mapper = {
                "al" : ("eax", 0x000000ff, 0),
                "ah" : ("eax", 0x0000ff00, 8),
                "ax" : ("eax", 0x0000ffff, 0),
                "bl" : ("ebx", 0x000000ff, 0),
                "bh" : ("ebx", 0x0000ff00, 8),
                "bx" : ("ebx", 0x0000ffff, 0),
                "cl" : ("ecx", 0x000000ff, 0),
                "ch" : ("ecx", 0x0000ff00, 8),
                "cx" : ("ecx", 0x0000ffff, 0),
                "dl" : ("edx", 0x000000ff, 0),
                "dh" : ("edx", 0x0000ff00, 8),
                "dx" : ("edx", 0x0000ffff, 0),

                # flags
                "cf": ("eflags", 0x00000001, 0),  # bit 0
                "pf": ("eflags", 0x00000004, 2),  # bit 2
                "af": ("eflags", 0x00000008, 4),  # bit 4
                "zf": ("eflags", 0x00000040, 6),  # bit 6
                "sf": ("eflags", 0x00000080, 7),  # bit 7
                "df": ("eflags", 0x00000400, 10), # bit 10
                "of": ("eflags", 0x00000800, 11), # bit 11
            }
        else:
            mapper = {
                "al"   : ("rax", 0x00000000000000ff, 0),
                "ah"   : ("rax", 0x000000000000ff00, 8),
                "ax"   : ("rax", 0x000000000000ffff, 0),
                "bl"   : ("rbx", 0x00000000000000ff, 0),
                "bh"   : ("rbx", 0x000000000000ff00, 8),
                "bx"   : ("rbx", 0x000000000000ffff, 0),
                "cl"   : ("rcx", 0x00000000000000ff, 0),
                "ch"   : ("rcx", 0x000000000000ff00, 8),
                "cx"   : ("rcx", 0x000000000000ffff, 0),
                "dl"   : ("rdx", 0x00000000000000ff, 0),
                "dh"   : ("rdx", 0x000000000000ff00, 8),
                "dx"   : ("rdx", 0x000000000000ffff, 0),
                "di"   : ("rdi", 0x000000000000ffff, 0),
                "si"   : ("rsi", 0x000000000000ffff, 0),
                "sp"   : ("rsp", 0x000000000000ffff, 0),
                "bp"   : ("rbp", 0x000000000000ffff, 0),
                "dil"  : ("rdi", 0x00000000000000ff, 0),
                "sil"  : ("rsi", 0x00000000000000ff, 0),
                "bpl"  : ("rbp", 0x00000000000000ff, 0),
                "spl"  : ("rsp", 0x00000000000000ff, 0),
                "eax"  : ("rax", 0x00000000ffffffff, 0),
                "ebx"  : ("rbx", 0x00000000ffffffff, 0),
                "ecx"  : ("rcx", 0x00000000ffffffff, 0),
                "edx"  : ("rdx", 0x00000000ffffffff, 0),
                "edi"  : ("rdi", 0x00000000ffffffff, 0),
                "esi"  : ("rsi", 0x00000000ffffffff, 0),
                "ebp"  : ("rbp", 0x00000000ffffffff, 0),
                "esp"  : ("rsp", 0x00000000ffffffff, 0),
                "eip"  : ("rip", 0x00000000ffffffff, 0),
                "r8b"  : ( "r8", 0x00000000000000ff, 0),
                "r9b"  : ( "r9", 0x00000000000000ff, 0),
                "r10b" : ("r10", 0x00000000000000ff, 0),
                "r11b" : ("r11", 0x00000000000000ff, 0),
                "r12b" : ("r12", 0x00000000000000ff, 0),
                "r13b" : ("r13", 0x00000000000000ff, 0),
                "r14b" : ("r14", 0x00000000000000ff, 0),
                "r15b" : ("r15", 0x000000000000ffff, 0),
                "r8w"  : ( "r8", 0x000000000000ffff, 0),
                "r9w"  : ( "r9", 0x000000000000ffff, 0),
                "r10w" : ("r10", 0x000000000000ffff, 0),
                "r11w" : ("r11", 0x000000000000ffff, 0),
                "r12w" : ("r12", 0x000000000000ffff, 0),
                "r13w" : ("r13", 0x000000000000ffff, 0),
                "r14w" : ("r14", 0x000000000000ffff, 0),
                "r15w" : ("r15", 0x000000000000ffff, 0),
                "r8d"  : ( "r8", 0x00000000ffffffff, 0),
                "r9d"  : ( "r9", 0x00000000ffffffff, 0),
                "r10d" : ("r10", 0x00000000ffffffff, 0),
                "r11d" : ("r11", 0x00000000ffffffff, 0),
                "r12d" : ("r12", 0x00000000ffffffff, 0),
                "r13d" : ("r13", 0x00000000ffffffff, 0),
                "r14d" : ("r14", 0x00000000ffffffff, 0),
                "r15d" : ("r15", 0x00000000ffffffff, 0),

                # flags
                "cf": ("rflags", 0x0000000000000001, 0),  # bit 0
                "pf": ("rflags", 0x0000000000000004, 2),  # bit 2
                "af": ("rflags", 0x0000000000000008, 4),  # bit 4
                "zf": ("rflags", 0x0000000000000040, 6),  # bit 6
                "sf": ("rflags", 0x0000000000000080, 7),  # bit 7
                "df": ("rflags", 0x0000000000000400, 10), # bit 10
                "of": ("rflags", 0x0000000000000800, 11), # bit 11
            }

        return mapper

    def read_register(self, register, registers):
        register_size = self._arch_regs_size[register]

        base_reg_name, value_filter, shift = self.register_access_mapper().get(register, (register, 2**register_size - 1, 0))

        if base_reg_name not in registers:
            registers[base_reg_name] = random.randint(0, 2**self._arch_regs_size[base_reg_name] - 1)

        reg_value = registers[base_reg_name]

        return (reg_value & value_filter) >> shift

    def write_register(self, register, registers, value):
        register_size = self._arch_regs_size[register]

        base_reg_name, value_filter, shift = self.register_access_mapper().get(register.name, (register, 2**register_size - 1, 0))

        reg_value = registers.get(base_reg_name, random.randint(0, 2**register_size - 1))

        registers[base_reg_name] = (reg_value & ~value_filter) | ((value << shift) & value_filter)

        return registers[base_reg_name]


class X86InstructionBase(object):
    """Representation of x86 instruction."""

    __slots__ = [
        '_prefix',
        '_mnemonic',
        '_operands',
        '_bytes',
        '_size',
        '_flags_affected',
        '_address',
        '_arch_mode',
    ]

    def __init__(self, prefix, mnemonic, operands, arch_mode):
        self._prefix = prefix
        self._mnemonic = mnemonic
        self._operands = operands
        self._bytes = None
        self._size = None
        self._flags_affected = []
        self._address = None
        self._arch_mode = arch_mode

    @property
    def prefix(self):
        """Get instruction prefix."""
        return self._prefix

    @property
    def mnemonic(self):
        """Get instruction mnemonic."""
        return self._mnemonic

    @property
    def operands(self):
        """Get instruction operands."""
        return self._operands

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
    def source_operands(self):
        """Get instruction sources."""
        raise NotImplementedError()

    @property
    def destination_operands(self):
        """Get instruction destinations."""
        raise NotImplementedError()

    @property
    def flags_affected(self):
        """Get flags affected by the instruction."""
        return self._flags_affected

    @flags_affected.setter
    def flags_affected(self, value):
        """Set flags affected by the instruction."""
        self._flags_affected = value

    @property
    def address(self):
        """Get instruction address."""
        return self._address

    @address.setter
    def address(self, value):
        """Set instruction address."""
        self._address = value

    def __str__(self):
        operands_str = ", ".join([str(oprnd) for oprnd in self._operands])
        # operands_str = ", ".join(["%s (%s)" % (str(oprnd), oprnd.size) for oprnd in self._operands])

        string  = self._prefix + " " if self._prefix else ""
        string += self._mnemonic
        string += " " + operands_str if operands_str else ""

        return string

    def __eq__(self, other):
        return self.prefix == other.prefix and \
            self.mnemonic == other.mnemonic and \
            self.operands == other.operands and \
            self.bytes == other.bytes and \
            self.size == other.size and \
            self.flags_affected == other.flags_affected and \
            self.address == other.address

    def __ne__(self, other):
        return not self.__eq__(other)


class X86Operand(object):
    """Representation of x86 operand."""

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


class X86ImmediateOperand(X86Operand):
    """Representation of x86 immediate operand."""

    __slots__ = [
        '_immediate'
    ]

    def __init__(self, immediate):
        super(X86ImmediateOperand, self).__init__("")

        if type(immediate) == str:
            self._immediate = int(immediate, 16)
        else:
            self._immediate = immediate

    @property
    def immediate(self):
        """Get immediate."""
        return self._immediate

    def __str__(self):
        # TODO: Take into account if it's a 32-bits o 64-bits architecture.
        string  = self._modifier + " " if self._modifier else ""

        if self._size:
            string += hex(self._immediate & 2**self._size-1)
        else:
            string += hex(self._immediate & 0xffffffff)

        return string if string[-1] != 'L' else string[:-1]

    def __eq__(self, other):
        return self.modifier == other.modifier and self.size == other.size and \
            self.immediate == other.immediate

    def __ne__(self, other):
        return not self.__eq__(other)


class X86RegisterOperand(X86Operand):
    """Representation of x86 register operand."""

    __slots__ = [
        '_name',
        '_size',
    ]

    def __init__(self, name, size=None):
        super(X86RegisterOperand, self).__init__("")

        self._name = name
        self._size = size

    @property
    def name(self):
        """Get register name."""
        return self._name

    def __str__(self):
        string  = self._modifier + " " if self._modifier else ""
        string += self._name

        return string

    def __eq__(self, other):
        return self.modifier == other.modifier and self.size == other.size and \
            self.name == other.name

    def __ne__(self, other):
        return not self.__eq__(other)


class X86MemoryOperand(X86Operand):
    """Representation of x86 memory operand."""

    __slots__ = [
        '_segment',
        '_base',
        '_index',
        '_index',
        '_scale',
        '_displacement',
    ]

    def __init__(self, segment, base, index, scale, displacement):
        super(X86MemoryOperand, self).__init__("")

        self._segment = segment
        self._base = base
        self._index = index
        self._scale = scale
        self._displacement = displacement

    @property
    def segment(self):
        """Get segment selector register."""
        return self._segment

    @property
    def base(self):
        """Get base register."""
        return self._base

    @property
    def index(self):
        """Get index register."""
        return self._index

    @property
    def scale(self):
        """Get scale value."""
        return self._scale

    @property
    def displacement(self):
        """Get displacement value."""
        return self._displacement

    def __str__(self):
        sep = ""

        string = ""

        if self._modifier:
            string = self._modifier + " "

        if self._segment:
            string += self._segment + ":"

        string += "["

        if self._base:
            string += self._base

        if self._index:
            if self._base:
                string += sep + "+" + sep
            string += self._index
            string += sep + "*" + sep + str(self._scale)

        # TODO: Take into account if it's a 32-bits o 64-bits architecture.
        if self._displacement != 0:
            if self._base or self._index:
                string += sep + "+" + sep
            imm_hex = hex(self._displacement & 0xffffffff)
            string += imm_hex if imm_hex[-1] != 'L' else imm_hex[:-1]

        string += "]"

        return string

    def __eq__(self, other):
        return self.modifier == other.modifier and self.size == other.size and \
            self.segment == other.segment and self.base == other.base and \
            self.index == other.index and self.scale == self.scale and \
            self.displacement == other.displacement

    def __ne__(self, other):
        return not self.__eq__(other)
