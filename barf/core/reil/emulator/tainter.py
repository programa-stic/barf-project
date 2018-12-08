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

from barf.core.reil import ReilImmediateOperand
from barf.core.reil import ReilMnemonic
from barf.core.reil import ReilRegisterOperand


class ReilEmulatorTainter(object):

    def __init__(self, emulator, arch=None):
        # Reil emulator instance.
        self.__emu = emulator

        # Architecture information.
        self.__arch = arch

        # Taint information.
        self.__taint_reg = set()   # Register-level tainting
        self.__taint_mem = set()   # Byte-level tainting

        # Taint function lookup table.
        self.__tainter = {
            # Arithmetic Instructions
            ReilMnemonic.ADD: self.__taint_binary_op,
            ReilMnemonic.SUB: self.__taint_binary_op,
            ReilMnemonic.MUL: self.__taint_binary_op,
            ReilMnemonic.DIV: self.__taint_binary_op,
            ReilMnemonic.MOD: self.__taint_binary_op,
            ReilMnemonic.BSH: self.__taint_binary_op,

            # Bitwise Instructions
            ReilMnemonic.AND: self.__taint_binary_op,
            ReilMnemonic.OR:  self.__taint_binary_op,
            ReilMnemonic.XOR: self.__taint_binary_op,

            # Data Transfer Instructions
            ReilMnemonic.LDM: self.__taint_load,
            ReilMnemonic.STM: self.__taint_store,
            ReilMnemonic.STR: self.__taint_move,

            # Conditional Instructions
            ReilMnemonic.BISZ: self.__taint_move,
            ReilMnemonic.JCC:  self.__taint_nothing,

            # Other Instructions
            ReilMnemonic.UNDEF: self.__taint_undef,
            ReilMnemonic.UNKN:  self.__taint_nothing,
            ReilMnemonic.NOP:   self.__taint_nothing,

            # Extensions
            ReilMnemonic.SEXT: self.__taint_move,
            ReilMnemonic.SDIV: self.__taint_binary_op,
            ReilMnemonic.SMOD: self.__taint_binary_op,
            ReilMnemonic.SMUL: self.__taint_binary_op,
        }

    def taint(self, instruction):
        self.__tainter[instruction.mnemonic](instruction)

    def reset(self):
        # Taint information.
        self.__taint_reg = set()
        self.__taint_mem = set()

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
            self.clear_register_taint(operand.name)
        else:
            raise Exception("Invalid operand: %s" % str(operand))

    # Memory taint methods
    # ======================================================================== #
    def get_memory_taint(self, address, size):
        tainted = False

        for i in range(0, size):
            tainted = tainted or address + i in self.__taint_mem

        return tainted

    def set_memory_taint(self, address, size, taint):
        for i in range(0, size):
            if taint:
                self.__taint_mem.add(address + i)
            else:
                self.__taint_mem.discard(address + i)

    def clear_memory_taint(self, address, size):
        for i in range(0, size):
            self.__taint_mem.discard(address + i)

    # Register taint methods
    # ======================================================================== #
    def get_register_taint(self, register):
        return self.__get_base_register(register) in self.__taint_reg

    def set_register_taint(self, register, taint):
        if taint:
            self.__taint_reg.add(self.__get_base_register(register))
        else:
            self.__taint_reg.discard(self.__get_base_register(register))

    def clear_register_taint(self, register):
        self.__taint_reg.discard(self.__get_base_register(register))

    # Taint auxiliary methods
    # ======================================================================== #
    def __get_base_register(self, register):
        if self.__arch and register in self.__arch.alias_mapper and \
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
        op0_taint = self.get_memory_taint(op0_val, instr.operands[2].size // 8)

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
        self.set_memory_taint(op2_val, op0_size // 8, op0_taint)

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
