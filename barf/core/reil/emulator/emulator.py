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
This module contains all the necessary classes to emulate REIL
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
from __future__ import absolute_import

import logging

from barf.core.reil.container import ReilContainerInvalidAddressError
from barf.core.reil.emulator import ReilCpu
from barf.core.reil.emulator import ReilCpuInvalidAddressError
from barf.core.reil.emulator import ReilEmulatorTainter
from barf.core.reil.emulator import ReilMemoryEx


logger = logging.getLogger("reilemulator")


class ReilEmulator(object):

    """Reil Emulator."""

    def __init__(self, arch, cpu=None, memory=None):
        # Architecture information.
        self.__arch = arch

        # An instance of a ReilMemory.
        self.__mem = memory if memory else ReilMemoryEx(self.__arch.address_size)

        # An instance of a ReilCpu.
        self.__cpu = cpu if cpu else ReilCpu(self.__mem, arch=self.__arch)

        # An instance of a ReilTainter.
        self.__tainter = ReilEmulatorTainter(self, arch=self.__arch)

        # Instructions pre and post handlers.
        self.__instr_handler_pre = None, None
        self.__instr_handler_post = None, None

        self.__set_default_handlers()

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

            next_ip = self.__execute_one(instr)

            ip = next_ip if next_ip else container.get_next_address(ip)

        return dict(self.__cpu.registers), self.__mem

    def execute_lite(self, instructions, context=None):
        """Execute a list of instructions. It does not support loops.
        """
        if context:
            self.__cpu.registers = dict(context)

        for instr in instructions:
            self.__execute_one(instr)

        return dict(self.__cpu.registers), self.__mem

    def single_step(self, instruction):
        return self.__execute_one(instruction)

    def __execute_one(self, instruction):
        # Execute pre instruction handlers
        handler_fn_pre, handler_param_pre = self.__instr_handler_pre
        handler_fn_pre(self, instruction, handler_param_pre)

        # Execute instruction
        next_addr = self.__cpu.execute(instruction)

        # Taint instruction
        self.__tainter.taint(instruction)

        # Execute post instruction handlers
        handler_fn_post, handler_param_post = self.__instr_handler_post
        handler_fn_post(self, instruction, handler_param_post)

        return next_addr

    # Reset methods
    # ======================================================================== #
    def reset(self):
        """Reset emulator. All registers and memory are reset.
        """
        self.__mem.reset()
        self.__cpu.reset()
        self.__tainter.reset()

        # Instructions pre and post handlers.
        self.__instr_handler_pre = None, None
        self.__instr_handler_post = None, None

        self.__set_default_handlers()

    def reset_memory(self):
        self.__mem.reset()

    def reset_cpu(self):
        self.__cpu.reset()

    def reset_tainter(self):
        self.__tainter.reset()

    # Instruction's handler methods
    # ======================================================================== #
    def set_instruction_pre_handler(self, func, parameter):
        self.__instr_handler_pre = (func, parameter)

    def set_instruction_post_handler(self, func, parameter):
        self.__instr_handler_post = (func, parameter)

    # Instruction's handler auxiliary methods
    # ======================================================================== #
    def __set_default_handlers(self):
        empty_fn, empty_param = lambda emu, instr, param: None, None

        self.__instr_handler_pre = (empty_fn, empty_param)
        self.__instr_handler_post = (empty_fn, empty_param)

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
