# Copyright (c) 2017, Fundacion Dr. Manuel Sadosky
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
from __future__ import print_function

import codecs
import logging
import pefile

from barf.arch import ARCH_ARM_MODE_ARM
from barf.arch import ARCH_ARM_MODE_THUMB
from barf.arch import ARCH_X86_MODE_32
from barf.arch import ARCH_X86_MODE_64
from barf.arch.arm import ArmArchitectureInformation
from barf.arch.x86 import X86ArchitectureInformation
from barf.arch.x86.translator import X86Translator
from barf.core.reil import ReilMnemonic
from barf.core.reil.container import ReilContainer
from barf.core.reil.container import ReilContainerInvalidAddressError
from barf.core.reil.container import ReilSequence
from barf.core.reil.helpers import split_address
from barf.core.reil.helpers import to_asm_address
from barf.core.reil.helpers import to_reil_address
from barf.utils.utils import ExecutionCache
from barf.utils.utils import InvalidAddressError

from elftools.elf.elffile import ELFFile

logger = logging.getLogger(__name__)


class Syscall(Exception):
    pass


class InstructionNotImplemented(Exception):

    def __init__(self, instruction):
        self.__instruction = instruction

    @property
    def instruction(self):
        return self.__instruction


class Emulator(object):

    def __init__(self, arch_info, ir_emulator, ir_translator, disassembler):
        self.arch_info = arch_info
        self._arch_mode = self.arch_info.architecture_mode
        self.ir_emulator = ir_emulator
        self.ir_translator = ir_translator
        self.disassembler = disassembler
        self.ip = None
        self.sp = None
        self.ws = None

        # Load instruction pointer register.
        if isinstance(self.arch_info, X86ArchitectureInformation):
            if self.arch_info.architecture_mode == ARCH_X86_MODE_32:
                self.ip = "eip"
                self.sp = "esp"
                self.ws = 4
            elif self.arch_info.architecture_mode == ARCH_X86_MODE_64:
                self.ip = "rip"
                self.sp = "rsp"
                self.ws = 8
            else:
                raise Exception("Invalid architecture mode.")

        # Load instruction pointer register.
        if isinstance(self.arch_info, ArmArchitectureInformation):
            if self.arch_info.architecture_mode == ARCH_ARM_MODE_THUMB:
                self.ip = "r15"
                self.sp = "r13"
                self.ws = 2  # TODO Check.
            elif self.arch_info.architecture_mode == ARCH_ARM_MODE_ARM:
                self.ip = "r15"
                self.sp = "r13"
                self.ws = 4
            else:
                raise Exception("Invalid architecture mode.")

        self.__instr_handler_post = None, None

        self.__set_default_handlers()

    def set_registers(self, registers):
        for reg, value in registers.items():
            if not reg.endswith("_next"):
                self.ir_emulator.registers[reg] = value

    def set_memory(self, memory):
        for addr, value in memory.items():
            for i, b in enumerate(bytearray(codecs.decode(value, 'hex'))):
                self.ir_emulator.write_memory(addr + i, 1, b)

    def add_reil_hook(self, func, param):
        self.ir_emulator.set_instruction_post_handler(func, param)

    def add_asm_hook(self, func, param):
        self.__instr_handler_post = (func, param)

    def __set_default_handlers(self):
        empty_fn, empty_param = lambda emu, instr, param: None, None

        self.__instr_handler_post = (empty_fn, empty_param)

    def execute(self, asm_instr):
        """Execute an assembler instruction.

        Args:
            asm_instr (X86Instruction): A instruction to execute.

        Returns:
            A int. The address of the next instruction to execute.
        """
        # Update the instruction pointer.
        self.ir_emulator.registers[self.ip] = asm_instr.address + asm_instr.size

        # Process syscall.
        if self.arch_info.instr_is_syscall(asm_instr):
            raise Syscall()

        # Process instruction and return next address instruction to execute.
        return self.__execute(asm_instr)

    def __execute(self, asm_instr):
        # Process one assembler instruction. Translate it to REIL instruction and
        # process each one.
        instr_container = self.__translate(asm_instr)
        ip = to_reil_address(asm_instr.address)
        next_addr = None

        while ip:
            # Fetch instruction.
            try:
                reil_instr = instr_container.fetch(ip)
            except ReilContainerInvalidAddressError:
                next_addr, _ = split_address(ip)
                break

            if reil_instr.mnemonic == ReilMnemonic.UNKN:
                raise InstructionNotImplemented(asm_instr)

            # Execute instruction.
            next_ip = self.ir_emulator.single_step(reil_instr)

            # Update instruction pointer.
            ip = next_ip if next_ip else instr_container.get_next_address(ip)

        del instr_container

        # Execute post instruction handlers
        handler_fn_post, handler_param_post = self.__instr_handler_post
        handler_fn_post(self, asm_instr, handler_param_post)

        # delete temporal registers
        regs = self.ir_emulator.registers.keys()

        for r in regs:
            if r.startswith("t"):
                del self.ir_emulator.registers[r]

        return next_addr if next_addr else asm_instr.address + asm_instr.size

    def __translate(self, asm_instr):
        reil_translator = X86Translator(self.arch_info.architecture_mode)

        # Create ReilContainer
        instr_container = ReilContainer()
        instr_seq = ReilSequence()
        for reil_instr in reil_translator.translate(asm_instr):
            instr_seq.append(reil_instr)
        instr_container.add(instr_seq)

        return instr_container

    def emulate(self, start_addr, end_addr, hooks, max_instrs, print_asm):
        # Switch arch mode accordingly for ARM base on the start address.
        if isinstance(self.arch_info, ArmArchitectureInformation):
            if start_addr & 0x1 == 0x1:
                start_addr = start_addr & ~0x1
                end_addr = end_addr & ~0x1

                self._arch_mode = ARCH_ARM_MODE_THUMB
            else:
                self._arch_mode = ARCH_ARM_MODE_ARM

        execution_cache = ExecutionCache()

        next_addr = start_addr
        instr_count = 0
        asm_instr = None

        while next_addr != end_addr:
            if max_instrs and instr_count > max_instrs:
                break

            # Process hooks.
            if next_addr in hooks:
                logger.debug("Hooking @ {:#x}".format(next_addr))

                fn, param, skip, offset = hooks[next_addr]

                fn(self.ir_emulator, param)

                # Compute next address after hook.
                if skip:
                    if isinstance(self.arch_info, X86ArchitectureInformation):
                        # Pop return address from the stack.
                        next_addr = self.ir_emulator.read_memory(self.ir_emulator.registers[self.sp], self.ws)
                        self.ir_emulator.registers[self.sp] += self.ws

                    if isinstance(self.arch_info, ArmArchitectureInformation):
                        # Load return address from the link register.
                        next_addr = self.ir_emulator.registers["r14"]

                logger.debug("Continuing @ {:#x}".format(next_addr))

            try:
                # Retrieve next instruction from the execution cache.
                asm_instr, reil_container = execution_cache.retrieve(next_addr)
            except InvalidAddressError:
                # Fetch the instruction.
                encoding = self.__fetch_instr(next_addr)

                # Decode it.
                asm_instr = self.disassembler.disassemble(encoding, next_addr,
                                                          architecture_mode=self._arch_mode)

                # Translate it.
                reil_container = self.__build_reil_container(asm_instr)

                # Add it to the execution cache.
                execution_cache.add(next_addr, asm_instr, reil_container)

            # Update the instruction pointer.
            self.__update_ip(asm_instr)

            # Execute instruction.
            if print_asm:
                print("{:#x} {}".format(asm_instr.address, asm_instr))

            target_addr = self.__process_reil_container(reil_container, to_reil_address(next_addr))

            # Execute post instruction handlers
            handler_fn_post, handler_param_post = self.__instr_handler_post
            handler_fn_post(self, asm_instr, handler_param_post)

            # Get next address to execute.
            next_addr = to_asm_address(target_addr) if target_addr else asm_instr.address + asm_instr.size

            # Count instruction.
            instr_count += 1

    def __process_reil_container(self, container, ip):
        next_addr = None

        while ip:
            # Fetch instruction.
            try:
                reil_instr = container.fetch(ip)
            except ReilContainerInvalidAddressError:
                next_addr = ip
                break

            next_ip = self.ir_emulator.single_step(reil_instr)

            # Update instruction pointer.
            ip = next_ip if next_ip else container.get_next_address(ip)

        # Delete temporal registers.
        regs = list(self.ir_emulator.registers.keys())

        for r in regs:
            # TODO Remove None test.
            if r and r.startswith("t"):
                del self.ir_emulator.registers[r]

        return next_addr

    def __build_reil_container(self, asm_instr):
        reil_translator = self.ir_translator

        container = ReilContainer()
        instr_seq = ReilSequence()

        for reil_instr in reil_translator.translate(asm_instr):
            instr_seq.append(reil_instr)

        container.add(instr_seq)

        return container

    def __fetch_instr(self, next_addr):
        start, end = next_addr, next_addr + self.arch_info.max_instruction_size

        encoding = bytearray()
        for i in range(end - start):
            encoding.append(self.ir_emulator.read_memory(start + i, 1))

        return encoding

    def __update_ip(self, asm_instr):
        if isinstance(self.arch_info, X86ArchitectureInformation):
            self.ir_emulator.registers[self.ip] = asm_instr.address + asm_instr.size

        if isinstance(self.arch_info, ArmArchitectureInformation):
            if self._arch_mode == ARCH_ARM_MODE_ARM:
                self.ir_emulator.registers[self.ip] = asm_instr.address + 8
            elif self._arch_mode == ARCH_ARM_MODE_THUMB:
                self.ir_emulator.registers[self.ip] = asm_instr.address + 2

    # Binary loader auxiliary methods.
    # ======================================================================= #
    def _load_binary_elf(self, filename):
        logger.info("Loading ELF image into memory")

        f = open(filename, 'rb')

        elffile = ELFFile(f)

        for index, segment in enumerate(elffile.iter_segments()):
            logger.info("Loading segment #{} ({:#x}-{:#x})".format(index, segment.header.p_vaddr,
                                                                   segment.header.p_vaddr + segment.header.p_filesz))

            for i, b in enumerate(bytearray(segment.data())):
                self.ir_emulator.write_memory(segment.header.p_vaddr + i, 1, b)

        f.close()

    def _load_binary_pe(self, filename):
        logger.info("Loading PE image into memory")

        pe = pefile.PE(filename)

        pe.parse_data_directories()

        for index, section in enumerate(pe.sections):
            logger.info("Loading section #{} ({:#x}-{:#x})".format(index, pe.OPTIONAL_HEADER.ImageBase + section.VirtualAddress,
                                                                   pe.OPTIONAL_HEADER.ImageBase + section.VirtualAddress + len(section.get_data())))

            for i, b in enumerate(bytearray(section.get_data())):
                self.ir_emulator.write_memory(pe.OPTIONAL_HEADER.ImageBase + section.VirtualAddress + i, 1, b)

    def load_binary(self, binary):
        try:
            fd = open(binary.filename, 'rb')
            signature = fd.read(4)
            fd.close()
        except:
            raise Exception("Error loading file.")

        if signature[:4] == b"\x7f\x45\x4c\x46":
            self._load_binary_elf(binary.filename)
        elif signature[:2] == b"\x4d\x5a":
            self._load_binary_pe(binary.filename)
        else:
            raise Exception("Unknown file format.")

    def write_memory(self, address, size, value):
        self.ir_emulator.write_memory(address, size, value)

    def read_memory(self, address, size):
        return self.ir_emulator.read_memory(address, size)

    def set_memory_taint(self, address, size, value):
        self.ir_emulator.set_memory_taint(address, size, value)

    @property
    def registers(self):
        return self.ir_emulator.registers
