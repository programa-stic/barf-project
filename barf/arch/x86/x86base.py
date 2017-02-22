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
This module contains all lthe classes that handle the x86 instruction
representation.

"""
from barf.arch import ARCH_X86_MODE_32
from barf.arch import ARCH_X86_MODE_64
from barf.arch import ArchitectureInformation


class X86ArchitectureInformation(ArchitectureInformation):
    """This class describe the Intel x86 architecture."""

    regs_seg = [
        ("cs", 16),
        ("ds", 16),
        ("ss", 16),
        ("es", 16),
        ("fs", 16),
        ("gs", 16),
    ]

    regs_32 = [
        ("eax", 32), ("ax", 16), ("al", 8), ("ah", 8),
        ("ebx", 32), ("bx", 16), ("bl", 8), ("bh", 8),
        ("ecx", 32), ("cx", 16), ("cl", 8), ("ch", 8),
        ("edx", 32), ("dx", 16), ("dl", 8), ("dh", 8),
        ("esi", 32), ("si", 16),
        ("edi", 32), ("di", 16),
        ("esp", 32), ("sp", 16),
        ("ebp", 32), ("bp", 16),
        ("eip", 32),
        ("eflags", 32),
    ]

    regs_32_base = [
        ("eax", 32),
        ("ebx", 32),
        ("ecx", 32),
        ("edx", 32),
        ("esi", 32),
        ("edi", 32),
        ("esp", 32),
        ("ebp", 32),
        ("eip", 32),
        ("eflags", 32),
    ]

    regs_64 = [
        ("rax", 64), ("eax",  32), ("ax",   16), ("al",   8), ("ah", 8),
        ("rbx", 64), ("ebx",  32), ("bx",   16), ("bl",   8), ("bh", 8),
        ("rcx", 64), ("ecx",  32), ("cx",   16), ("cl",   8), ("ch", 8),
        ("rdx", 64), ("edx",  32), ("dx",   16), ("dl",   8), ("dh", 8),
        ("rsi", 64), ("esi",  32), ("si",   16), ("sil",  8),
        ("rdi", 64), ("edi",  32), ("di",   16), ("dil",  8),
        ("rsp", 64), ("esp",  32), ("sp",   16), ("spl",  8),
        ("rbp", 64), ("ebp",  32), ("bp",   16), ("bpl",  8),
        ("r8",  64), ("r8d",  32), ("r8w",  16), ("r8b",  8),
        ("r9",  64), ("r9d",  32), ("r9w",  16), ("r9b",  8),
        ("r10", 64), ("r10d", 32), ("r10w", 16), ("r10b", 8),
        ("r11", 64), ("r11d", 32), ("r11w", 16), ("r11b", 8),
        ("r12", 64), ("r12d", 32), ("r12w", 16), ("r12b", 8),
        ("r13", 64), ("r13d", 32), ("r13w", 16), ("r13b", 8),
        ("r14", 64), ("r14d", 32), ("r14w", 16), ("r14b", 8),
        ("r15", 64), ("r15d", 32), ("r15w", 16), ("r15b", 8),
        ("rip", 64),
        ("rflags", 64)
    ]

    regs_64_base = [
        ("rax", 64),
        ("rbx", 64),
        ("rcx", 64),
        ("rdx", 64),
        ("rsi", 64),
        ("rdi", 64),
        ("rsp", 64),
        ("rbp", 64),
        ("r8",  64),
        ("r9",  64),
        ("r10", 64),
        ("r11", 64),
        ("r12", 64),
        ("r13", 64),
        ("r14", 64),
        ("r15", 64),
        ("rip", 64),
        ("rflags", 64)
    ]

    regs_fpu = [
        ("st0", 80),
        ("st1", 80),
        ("st2", 80),
        ("st3", 80),
        ("st4", 80),
        ("st5", 80),
        ("st6", 80),
        ("st7", 80),
    ]

    regs_mmx = [
        ("mm0", 64),
        ("mm1", 64),
        ("mm2", 64),
        ("mm3", 64),
        ("mm4", 64),
        ("mm5", 64),
        ("mm6", 64),
        ("mm7", 64),
    ]

    regs_xmm_32 = [
        ("xmm0", 128),
        ("xmm1", 128),
        ("xmm2", 128),
        ("xmm3", 128),
        ("xmm4", 128),
        ("xmm5", 128),
        ("xmm6", 128),
        ("xmm7", 128),
    ]

    regs_xmm_64 = [
        ("xmm0",  128),
        ("xmm1",  128),
        ("xmm2",  128),
        ("xmm3",  128),
        ("xmm4",  128),
        ("xmm5",  128),
        ("xmm6",  128),
        ("xmm7",  128),
        ("xmm8",  128),
        ("xmm9",  128),
        ("xmm10", 128),
        ("xmm11", 128),
        ("xmm12", 128),
        ("xmm13", 128),
        ("xmm14", 128),
        ("xmm15", 128),
    ]

    regs_ymm_32 = [
        ("ymm0", 256),
        ("ymm1", 256),
        ("ymm2", 256),
        ("ymm3", 256),
        ("ymm4", 256),
        ("ymm5", 256),
        ("ymm6", 256),
        ("ymm7", 256),
    ]

    regs_ymm_64 = [
        ("ymm0",  256),
        ("ymm1",  256),
        ("ymm2",  256),
        ("ymm3",  256),
        ("ymm4",  256),
        ("ymm5",  256),
        ("ymm6",  256),
        ("ymm7",  256),
        ("ymm8",  256),
        ("ymm9",  256),
        ("ymm10", 256),
        ("ymm11", 256),
        ("ymm12", 256),
        ("ymm13", 256),
        ("ymm14", 256),
        ("ymm15", 256),
    ]

    regs_flags = [
        ("af", 1),
        ("cf", 1),
        ("of", 1),
        ("pf", 1),
        ("sf", 1),
        ("zf", 1),
        ("df", 1),
    ]

    regs_debug = [
        ("dr0", 32),
        ("dr1", 32),
        ("dr2", 32),
        ("dr3", 32),
        ("dr4", 32),
        ("dr5", 32),
        ("dr6", 32),
        ("dr7", 32),
    ]

    regs_control = [
        ("cr0", 32),
        ("cr1", 32),
        ("cr2", 32),
        ("cr3", 32),
        ("cr4", 32),
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
            ARCH_X86_MODE_32: 32,
            ARCH_X86_MODE_64: 64,
        }

        return arch_size_map[self._arch_mode]

    @property
    def operand_size(self):
        operand_size_map = {
            ARCH_X86_MODE_32: 32,
            ARCH_X86_MODE_64: 64,
        }

        return operand_size_map[self._arch_mode]

    @property
    def address_size(self):
        address_size_map = {
            ARCH_X86_MODE_32: 32,
            ARCH_X86_MODE_64: 64,
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
            ARCH_X86_MODE_32: 16,
            ARCH_X86_MODE_64: 16,
        }

        return instruction_size_map[self._arch_mode]

    def instr_is_ret(self, instruction):
        return instruction.mnemonic == "ret"

    def instr_is_call(self, instruction):
        return instruction.mnemonic == "call"

    def instr_is_halt(self, instruction):
        return instruction.mnemonic == "hlt"

    def instr_is_branch(self, instruction):
        branch_instrs = [
            "jmp", "ja", "jae", "jb", "jbe", "jc", "je", "jg", "jge", "jl",
            "jle", "jna", "jnae", "jnb", "jnbe", "jnc", "jne", "jng", "jnge",
            "jnl", "jnle", "jno", "jnp", "jns", "jnz", "jo", "jp", "jpe",
            "jpo", "js", "jz", "jcxz", "jecxz", "jrcxz", "loop", "loope", "loopne"
        ]

        return instruction.mnemonic in branch_instrs

    def instr_is_branch_cond(self, instruction):
        branch_instrs = [
            "ja", "jae", "jb", "jbe", "jc", "je", "jg", "jge", "jl",
            "jle", "jna", "jnae", "jnb", "jnbe", "jnc", "jne", "jng", "jnge",
            "jnl", "jnle", "jno", "jnp", "jns", "jnz", "jo", "jp", "jpe",
            "jpo", "js", "jz", "jcxz", "jecxz", "jrcxz", "loop", "loope", "loopne"
        ]

        return instruction.mnemonic in branch_instrs

    def instr_is_syscall(self, instruction):
        syscall_instrs = [
            "int", "syscall", "sysenter"
        ]

        return instruction.mnemonic in syscall_instrs

    def _load_alias_mapper(self):
        if self._arch_mode == ARCH_X86_MODE_32:
            alias_mapper = {
                "al" : ("eax", 0), "ah" : ("eax", 8), "ax" : ("eax", 0),
                "bl" : ("ebx", 0), "bh" : ("ebx", 8), "bx" : ("ebx", 0),
                "cl" : ("ecx", 0), "ch" : ("ecx", 8), "cx" : ("ecx", 0),
                "dl" : ("edx", 0), "dh" : ("edx", 8), "dx" : ("edx", 0),
                "si" : ("esi", 0),
                "di" : ("edi", 0),
                "bp" : ("ebp", 0),
                "sp" : ("esp", 0),
            }

            flags_reg = "eflags"
        else:
            alias_mapper = {
                "al"   : ("rax", 0), "ah"   : ("rax", 8), "ax"   : ("rax", 0),
                "bl"   : ("rbx", 0), "bh"   : ("rbx", 8), "bx"   : ("rbx", 0),
                "cl"   : ("rcx", 0), "ch"   : ("rcx", 8), "cx"   : ("rcx", 0),
                "dl"   : ("rdx", 0), "dh"   : ("rdx", 8), "dx"   : ("rdx", 0),
                "di"   : ("rdi", 0), "dil"  : ("rdi", 0),
                "si"   : ("rsi", 0), "sil"  : ("rsi", 0),
                "sp"   : ("rsp", 0), "bpl"  : ("rbp", 0),
                "bp"   : ("rbp", 0), "spl"  : ("rsp", 0),
                "eax"  : ("rax", 0),
                "ebx"  : ("rbx", 0),
                "ecx"  : ("rcx", 0),
                "edx"  : ("rdx", 0),
                "edi"  : ("rdi", 0),
                "esi"  : ("rsi", 0),
                "ebp"  : ("rbp", 0),
                "esp"  : ("rsp", 0),
                "eip"  : ("rip", 0),
                "r8b"  : ( "r8", 0), "r8w"  : ( "r8", 0), "r8d"  : ( "r8", 0),
                "r9b"  : ( "r9", 0), "r9w"  : ( "r9", 0), "r9d"  : ( "r9", 0),
                "r10b" : ("r10", 0), "r10w" : ("r10", 0), "r10d" : ("r10", 0),
                "r11b" : ("r11", 0), "r11w" : ("r11", 0), "r11d" : ("r11", 0),
                "r12b" : ("r12", 0), "r12w" : ("r12", 0), "r12d" : ("r12", 0),
                "r13b" : ("r13", 0), "r13w" : ("r13", 0), "r13d" : ("r13", 0),
                "r14b" : ("r14", 0), "r14w" : ("r14", 0), "r14d" : ("r14", 0),
                "r15b" : ("r15", 0), "r15w" : ("r15", 0), "r15d" : ("r15", 0),
            }

            flags_reg = "rflags"

        flags_mapper = {
            "cf": (flags_reg, 0),
            "pf": (flags_reg, 2),
            "af": (flags_reg, 4),
            "zf": (flags_reg, 6),
            "sf": (flags_reg, 7),
            "df": (flags_reg, 10),
            "of": (flags_reg, 11),
        }

        alias_mapper.update(flags_mapper)

        self._alias_mapper = alias_mapper

    def _load_registers(self):
        registers_all = self.regs_seg + \
                        self.regs_fpu + \
                        self.regs_mmx + \
                        self.regs_flags + \
                        self.regs_debug + \
                        self.regs_control

        if self._arch_mode == ARCH_X86_MODE_32:
            registers_all += self.regs_32 + \
                             self.regs_xmm_32 + \
                             self.regs_ymm_32

            registers_gp_all = self.regs_32

            self._registers_gp_base = [name for name, _ in self.regs_32_base]
        else:
            registers_all += self.regs_64 + \
                             self.regs_xmm_64 + \
                             self.regs_ymm_64

            registers_gp_all = self.regs_64

            self._registers_gp_base = [name for name, _ in self.regs_64_base]

        for name, size in registers_all:
            self._registers_all.append(name)
            self._registers_size[name] = size

        for name, size in registers_gp_all:
            self._registers_gp_all.append(name)
            self._registers_size[name] = size

        self._registers_flags = [name for name, _ in self.regs_flags]


class X86Instruction(object):
    """Representation of x86 instruction."""

    __slots__ = [
        '_prefix',
        '_mnemonic',
        '_operands',
        '_bytes',
        '_size',
        '_address',
        '_arch_mode',
    ]

    def __init__(self, prefix, mnemonic, operands, arch_mode):
        self._prefix = prefix
        self._mnemonic = mnemonic
        self._operands = operands
        self._bytes = ""
        self._size = None
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
    def address(self):
        """Get instruction address."""
        return self._address

    @address.setter
    def address(self, value):
        """Set instruction address."""
        self._address = value

    def __str__(self):
        operands_str = ", ".join([str(oprnd) for oprnd in self._operands])

        string  = self._prefix + " " if self._prefix else ""
        string += self._mnemonic
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

    def __getstate__(self):
        state = {}
        state['_prefix'] = self._prefix
        state['_mnemonic'] = self._mnemonic
        state['_operands'] = self._operands
        state['_bytes'] = self._bytes
        state['_size'] = self._size
        state['_address'] = self._address
        state['_arch_mode'] = self._arch_mode

        return state

    def __setstate__(self, state):
        self._prefix = state['_prefix']
        self._mnemonic = state['_mnemonic']
        self._operands = state['_operands']
        self._bytes = state['_bytes']
        self._size = state['_size']
        self._address = state['_address']
        self._arch_mode = state['_arch_mode']


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

    def to_string(self, **kwargs):
        return self.__str__()

    def __getstate__(self):
        state = {}
        state['_modifier'] = self._modifier
        state['_size'] = self._size

        return state

    def __setstate__(self, state):
        self._modifier = state['_modifier']
        self._size = state['_size']


class X86ImmediateOperand(X86Operand):
    """Representation of x86 immediate operand."""

    __slots__ = [
        '_immediate',
    ]

    def __init__(self, immediate, size=None):
        super(X86ImmediateOperand, self).__init__("")

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

        string  = self._modifier + " " if self._modifier else ""

        if immediate_format == "hex":
            string += hex(self._immediate & 2**self._size-1)
        elif immediate_format == "dec":
            string += str(self._immediate & 2**self._size-1)
        else:
            raise Exception("Invalid immediate format: {}".format(imm_fmt))

        return string[:-1] if string[-1] == 'L' else string

    def __str__(self):
        if not self._size:
            raise Exception("Operand size missing.")

        string  = self._modifier + " " if self._modifier else ""
        string += hex(self._immediate & 2**self._size-1)

        return string[:-1] if string[-1] == 'L' else string

    def __eq__(self, other):
        return  self.modifier == other.modifier and \
                self.size == other.size and \
                self.immediate == other.immediate

    def __ne__(self, other):
        return not self.__eq__(other)

    def __getstate__(self):
        state = super(X86ImmediateOperand, self).__getstate__()

        state['_immediate'] = self._immediate

        return state

    def __setstate__(self, state):
        super(X86ImmediateOperand, self).__setstate__(state)

        self._immediate = state['_immediate']


class X86RegisterOperand(X86Operand):
    """Representation of x86 register operand."""

    __slots__ = [
        '_name',
    ]

    def __init__(self, name, size=None):
        super(X86RegisterOperand, self).__init__("")

        self._name = name
        self._size = size

    @property
    def name(self):
        """Get register name."""
        if not self._size:
            raise Exception("Operand size missing.")

        return self._name

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

    def __getstate__(self):
        state = super(X86RegisterOperand, self).__getstate__()

        state['_name'] = self._name

        return state

    def __setstate__(self, state):
        super(X86RegisterOperand, self).__setstate__(state)

        self._name = state['_name']


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

        if self._displacement != 0:
            imm_hex = hex(self._displacement)

            if self._base or self._index:
                if imm_hex[0] == "-":
                    string += sep + sep
                else:
                    string += sep + "+" + sep

            string += imm_hex[:-1] if imm_hex[-1] == 'L' else imm_hex

        string += "]"

        return string

    def __eq__(self, other):
        return  self.modifier == other.modifier and \
                self.size == other.size and \
                self.segment == other.segment and \
                self.base == other.base and \
                self.index == other.index and \
                self.scale == self.scale and \
                self.displacement == other.displacement

    def __ne__(self, other):
        return not self.__eq__(other)

    def __getstate__(self):
        state = super(X86MemoryOperand, self).__getstate__()

        state['_segment'] = self._segment
        state['_base'] = self._base
        state['_index'] = self._index
        state['_index'] = self._index
        state['_scale'] = self._scale
        state['_displacement'] = self._displacement

        return state

    def __setstate__(self, state):
        super(X86MemoryOperand, self).__setstate__(state)

        self._segment = state['_segment']
        self._base = state['_base']
        self._index = state['_index']
        self._index = state['_index']
        self._scale = state['_scale']
        self._displacement = state['_displacement']
