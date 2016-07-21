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

from barf.analysis.basicblock import BasicBlockBuilder
from barf.analysis.basicblock import ControlFlowGraph
from barf.arch.x86.x86base import X86ArchitectureInformation
from barf.arch.x86.x86disassembler import X86Disassembler
from barf.arch.x86.x86translator import X86Translator
from barf.core.reil import ReilContainer
from barf.core.reil import ReilSequence
from barf.core.reil import split_address


class ReilContainerBuilder(object):

    def __init__(self, binary):
        self.__binary = binary
        self.__arch_mode = self.__binary.architecture_mode
        self.__arch = X86ArchitectureInformation(self.__arch_mode)
        self.__disassembler = X86Disassembler(architecture_mode=self.__arch_mode)
        self.__translator = X86Translator(architecture_mode=self.__arch_mode)
        self.__bb_builder = BasicBlockBuilder(self.__disassembler, self.__binary.text_section, self.__translator, self.__arch)

    def build(self, functions):
        reil_container = ReilContainer()

        for _, start, end in functions:
            bbs, _ = self.__bb_builder.build(start, end)

            cfg = ControlFlowGraph(bbs)

            reil_container = self.__translate_cfg(cfg, reil_container=reil_container)

        return reil_container

    # Auxiliary methods
    # ======================================================================== #
    def __translate_cfg(self, cfg, reil_container=None):
        if not reil_container:
            reil_container = ReilContainer()

        asm_instrs = []

        for bb in cfg.basic_blocks:
            for dual_instr in bb:
                asm_instrs += [dual_instr.asm_instr]

        reil_container = self.__translate(asm_instrs, reil_container)

        return reil_container

    def __translate(self, asm_instrs, reil_container):
        asm_instr_last = None
        instr_seq_prev = None

        for asm_instr in asm_instrs:
            instr_seq = ReilSequence()

            for reil_instr in self.__translator.translate(asm_instr):
                instr_seq.append(reil_instr)

            if instr_seq_prev:
                instr_seq_prev.next_sequence_address = instr_seq.address

            reil_container.add(instr_seq)

            instr_seq_prev = instr_seq

        if instr_seq_prev:
            if asm_instr_last:
                instr_seq_prev.next_sequence_address = (asm_instr_last.address + asm_instr_last.size) << 8

        return reil_container

    def translate(self, asm_instrs, reil_container):
        return self.__translator(asm_instrs, reil_container)


class ReilContainerEx(object):

    def __init__(self, binary, symbols):
        self.__binary = binary
        self.__arch_mode = self.__binary.architecture_mode
        self.__arch = X86ArchitectureInformation(self.__arch_mode)
        self.__disassembler = X86Disassembler(architecture_mode=self.__arch_mode)
        self.__translator = X86Translator(architecture_mode=self.__arch_mode)
        self.__bb_builder = BasicBlockBuilder(self.__disassembler, self.__binary.text_section, self.__translator, self.__arch)

        self.__container = {}
        self.__symbols = symbols

        self.__symbols_by_addr = {}

        for name, start, end in symbols:
            self.__symbols_by_addr[start] = (name, end)

    # Auxiliary methods
    # ======================================================================== #
    def __translate_cfg(self, cfg, reil_container=None):
        if not reil_container:
            reil_container = ReilContainer()

        asm_instrs = []

        for bb in cfg.basic_blocks:
            for dual_instr in bb:
                asm_instrs += [dual_instr.asm_instr]

        reil_container = self.__translate(asm_instrs, reil_container)

        return reil_container

    def __translate(self, asm_instrs, reil_container):
        asm_instr_last = None
        instr_seq_prev = None

        for asm_instr in asm_instrs:
            instr_seq = ReilSequence()

            for reil_instr in self.__translator.translate(asm_instr):
                instr_seq.append(reil_instr)

            if instr_seq_prev:
                instr_seq_prev.next_sequence_address = instr_seq.address

            reil_container.add(instr_seq)

            instr_seq_prev = instr_seq

        if instr_seq_prev:
            if asm_instr_last:
                instr_seq_prev.next_sequence_address = (asm_instr_last.address + asm_instr_last.size) << 8

        return reil_container

    def add(self, sequence):
        base_addr, _ = split_address(sequence.address)

        if base_addr in self.__container.keys():
            raise Exception("Invalid sequence")
        else:
            self.__container[base_addr] = sequence

    def fetch(self, address):
        base_addr, index = split_address(address)

        if base_addr not in self.__container.keys():
            self.__resolve_address(base_addr)

        return self.__container[base_addr].get(index)

    def get_next_address(self, address):
        base_addr, index = split_address(address)

        if base_addr not in self.__container.keys():
            raise Exception("Invalid address.")

        addr = address

        if index < len(self.__container[base_addr]) - 1:
            addr += 1
        else:
            addr = self.__container[base_addr].next_sequence_address

        return addr

    def dump(self):
        for base_addr in sorted(self.__container.keys()):
            self.__container[base_addr].dump()

            print("-" * 80)

    def __iter__(self):
        for addr in sorted(self.__container.keys()):
            for instr in self.__container[addr]:
                yield instr

    def __resolve_address(self, address):
        if address not in self.__symbols_by_addr:
            # print("Not symbol : {:#010x}".format(address))
            raise Exception("Symbol not found!")

        name, end = self.__symbols_by_addr[address]

        # print("Resolving {:s} @ {:#010x}".format(name, address))

        cfg = ControlFlowGraph(self.__bb_builder.build(address, end))

        _ = self.__translate_cfg(cfg, reil_container=self)
