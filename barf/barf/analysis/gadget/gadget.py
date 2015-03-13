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
This module contains two basic classes for gaget processing: RawGadget
and TypedGadgets. The first is used to describe the gadgets found by
GadgetFinder. These are candidate gadgets as they are not validated yet.
However, they contains (the RawGadget object) the assembly code as well
as its REIL representation. One given gadget can be classified in one or
more gadget type. At this point, a TypedGadget object is created for
each classified type and the RawGadget object is associated with them.

"""

from barf.core.reil import ReilEmptyOperand
from barf.core.reil import ReilImmediateOperand

class RawGadget(object):

    """Represent a gadget as a list of instructions.
    """

    __slots__ = [
        '_instrs',
        '_id',
    ]

    def __init__(self, instrs):

        # List of instructions (dual instructions.)
        self._instrs = instrs

        # Id of gadget.
        self._id = None

    @property
    def address(self):
        """Get gadget start address.
        """
        return self._instrs[0].address

    @property
    def instrs(self):
        """Get gadget dual instructions.
        """
        return self._instrs

    def get_ir_instrs(self):
        """Get gadget IR instructions.
        """
        ir_instrs_list = [dual_ins.ir_instrs for dual_ins in self._instrs]

        instrs = []

        for ir_instrs in ir_instrs_list:
            instrs += ir_instrs

        return instrs

    @property
    def id(self):
        """Get gadget validity status.
        """
        return self._id

    @id.setter
    def id(self, value):
        """Set gadget validity status.
        """
        self._id = value

    def __str__(self):
        lines = []

        for dinstr in self._instrs:
            lines += ["0x%08x : %s" % (dinstr.asm_instr.address, dinstr.asm_instr)]

            for instr in dinstr.ir_instrs:
                lines += ["  %s" % (instr)]

        return "\n".join(lines)


class TypedGadget(RawGadget):

    """Represents a gadget with its semantic classification.
    """

    __slots__ = [
        '_gadget',
        '_sources',
        '_destination',
        '_modified_regs',
        '_gadget_type',
        '_verified',
        '_is_valid',
        '_operation',
    ]

    def __init__(self, gadget, gadget_type):

        # A raw gaget.
        self._gadget = gadget

        # A list of sources.
        self._sources = []

        # A list of destinations.
        self._destination = []

        # A list of registers that are modified after gadget execution.
        self._modified_regs = []

        # Type of the gaget.
        self._gadget_type = gadget_type

        # Verification flag.
        self._verified = False

        # If the gadget was verified and it turned out to be correctly
        # classifies, this flags is True. Otherwise, is False.
        self._is_valid = None

        # Operation computed by the gadget.
        self._operation = None

    # Properties
    # ======================================================================== #
    @property
    def sources(self):
        """Get gadget sources.
        """
        return self._sources

    @sources.setter
    def sources(self, value):
        """Set gadget sources.
        """
        self._sources = value

    @property
    def destination(self):
        """Get gadget destination.
        """
        return self._destination

    @destination.setter
    def destination(self, value):
        """Set gadget destination.
        """
        self._destination = value

    @property
    def modified_registers(self):
        """Get gadget modified registers.
        """
        return self._modified_regs

    @modified_registers.setter
    def modified_registers(self, value):
        """Set gadget modified registers.
        """
        self._modified_regs = value

    @property
    def verified(self):
        """Get gadget verification status.
        """
        return self._verified

    @verified.setter
    def verified(self, value):
        """Set gadget verification status.
        """
        self._verified = value

    @property
    def is_valid(self):
        """Get gadget validity status.
        """
        if not self._verified:
            raise Exception("Typed Gadget not Verified!")

        return self._is_valid

    @is_valid.setter
    def is_valid(self, value):
        """Set gadget validity status.
        """
        self._verified = True
        self._is_valid = value

    @property
    def type(self):
        """Get gadget type.
        """
        return self._gadget_type

    @property
    def operation(self):
        """Get gadget operation.
        """
        return self._operation

    @operation.setter
    def operation(self, value):
        """Set gadget operation.
        """
        self._operation = value

    def __str__(self):
        strings = {
            GadgetType.NoOperation     : dump_no_operation,
            GadgetType.Jump            : dump_jump,
            GadgetType.MoveRegister    : dump_move_register,
            GadgetType.LoadConstant    : dump_load_constant,
            GadgetType.Arithmetic      : dump_arithmetic,
            GadgetType.LoadMemory      : dump_load_memory,
            GadgetType.StoreMemory     : dump_store_memory,
            GadgetType.ArithmeticLoad  : dump_arithmetic_load,
            GadgetType.ArithmeticStore : dump_arithmetic_store,
            GadgetType.Undefined       : dump_undefined,
        }

        return strings[self._gadget_type](self)

    def __eq__(self, other):
        """Return self == other."""
        if type(other) is type(self):
            same_sources = self._sources == other._sources
            same_destination = self._destination == other._destination
            same_modified = self._modified_regs == other._modified_regs
            same_operation = self._operation == other._operation

            return same_sources and same_destination and same_modified and \
                same_operation
        else:
            return False

    def __ne__(self, other):
        """Return self != other."""
        return not self.__eq__(other)

    # Misc
    # ======================================================================== #
    def __getattr__(self, name):
        return getattr(self._gadget, name)


class GadgetType(object):

    """Enumeration of Gadget Types.
    """

    NoOperation     = 0
    Jump            = 1
    MoveRegister    = 2
    LoadConstant    = 3
    Arithmetic      = 4
    LoadMemory      = 5
    StoreMemory     = 6
    ArithmeticLoad  = 7
    ArithmeticStore = 8
    Undefined       = 9

    @staticmethod
    def to_string(gadget_type):
        strings = {
            GadgetType.NoOperation     : "No Operation",
            GadgetType.Jump            : "Jump",
            GadgetType.MoveRegister    : "Move Register",
            GadgetType.LoadConstant    : "Load Constant",
            GadgetType.Arithmetic      : "Arithmetic",
            GadgetType.LoadMemory      : "Load Memory",
            GadgetType.StoreMemory     : "Store Memory",
            GadgetType.ArithmeticLoad  : "Arithmetic Load",
            GadgetType.ArithmeticStore : "Arithmetic Store",
            GadgetType.Undefined       : "Undefined",
        }

        return strings[gadget_type]


# Gadget dump functions
# ============================================================================ #
def dump_no_operation(gadget):
    return "nop <- nop > {}"

def dump_jump(gadget):
    return "NOT SUPPORTED YET!"

def dump_move_register(gadget):
    fmt = "%s <- %s > {%s}"

    mod_regs = [r for r in gadget.modified_registers]

    fmt_params = (str(gadget.destination[0]), str(gadget.sources[0]),
        "; ".join(map(str, mod_regs)))

    return fmt % fmt_params

def dump_load_constant(gadget):
    fmt = "%s <- %s > {%s}"

    mod_regs = [r for r in gadget.modified_registers]

    fmt_params = (str(gadget.destination[0]), str(gadget.sources[0]),
        "; ".join(map(str, mod_regs)))

    return fmt % fmt_params

def dump_arithmetic(gadget):
    fmt = "%s <- %s %s %s > {%s}"

    mod_regs = [r for r in gadget.modified_registers]

    fmt_params = (str(gadget.destination[0]), str(gadget.sources[0]),
        gadget.operation, str(gadget.sources[1]), "; ".join(map(str, mod_regs)))

    return fmt % fmt_params

def dump_load_memory(gadget):
    fmt = "%s <- mem[%s] > {%s}"

    mod_regs = [r for r in gadget.modified_registers]

    src_regs = []
    for src in gadget.sources:
        if isinstance(src, ReilEmptyOperand):
            continue

        if isinstance(src, ReilImmediateOperand) and src.immediate == 0:
            continue

        src_regs += [src]

    fmt_params = (
        str(gadget.destination[0]),
        " + ".join(map(str, src_regs)),
        "; ".join(map(str, mod_regs))
    )

    return fmt % fmt_params

def dump_store_memory(gadget):
    fmt = "mem[%s] <- %s > {%s}"

    mod_regs = [r for r in gadget.modified_registers]

    dst_regs = []
    for dst in gadget.destination:
        if isinstance(dst, ReilEmptyOperand):
            continue

        if isinstance(dst, ReilImmediateOperand) and dst.immediate == 0:
            continue

        dst_regs += [dst]

    fmt_params = (
        " + ".join(map(str, dst_regs)),
        str(gadget.sources[0]),
        "; ".join(map(str, mod_regs))
    )

    return  fmt % fmt_params

def dump_arithmetic_load(gadget):
    fmt = "%s <- %s %s mem[%s] > {%s}"

    mod_regs = [r for r in gadget.modified_registers]

    src_regs = []
    for src in gadget.sources[1:]:
        if isinstance(src, ReilEmptyOperand):
            continue

        if isinstance(src, ReilImmediateOperand) and src.immediate == 0:
            continue

        src_regs += [src]

    fmt_params = (
        str(gadget.destination[0]),
        str(gadget.sources[0]),
        gadget.operation,
        " + ".join(map(str, src_regs)),
        "; ".join(map(str, mod_regs)))

    return fmt % fmt_params

def dump_arithmetic_store(gadget):
    fmt = "mem[%s] <- mem[%s] %s %s > {%s}"

    mod_regs = [r for r in gadget.modified_registers]

    src_regs = []
    for src in gadget.sources[0:2]:
        if isinstance(src, ReilEmptyOperand):
            continue

        if isinstance(src, ReilImmediateOperand) and src.immediate == 0:
            continue

        src_regs += [src]

    dst_regs = []
    for dst in gadget.destination:
        if isinstance(dst, ReilEmptyOperand):
            continue

        if isinstance(dst, ReilImmediateOperand) and dst.immediate == 0:
            continue

        dst_regs += [dst]

    fmt_params = (
        " + ".join(map(str, dst_regs)),
        " + ".join(map(str, src_regs)),
        gadget.operation,
        str(gadget.sources[2]),
        "; ".join(map(str, mod_regs))
    )

    return fmt % fmt_params

def dump_undefined(gadget):
    return "undefined"
