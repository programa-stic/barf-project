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
BARF : Binary Analysis Framework.

"""
import logging
import os
import time

import arch

from analysis.basicblock import BasicBlockBuilder
from analysis.basicblock import BasicBlockGraph
from analysis.codeanalyzer import CodeAnalyzer
from analysis.gadget import GadgetClassifier
from analysis.gadget import GadgetFinder
from analysis.gadget import GadgetVerifier
from arch.arm.armbase import ArmArchitectureInformation
from arch.arm.armdisassembler import ArmDisassembler
from arch.arm.armtranslator import ArmTranslator
from arch.x86.x86base import X86ArchitectureInformation
from arch.x86.x86disassembler import X86Disassembler
from arch.x86.x86translator import X86Translator
from core.bi import BinaryFile
from core.reil import ReilEmulator
from core.smt.smtlibv2 import CVC4Solver
from core.smt.smtlibv2 import Z3Solver
from core.smt.smttranslator import SmtTranslator

logger = logging.getLogger(__name__)

# Choose between SMT Solvers...
SMT_SOLVER = "Z3"
# SMT_SOLVER = "CVC4"
# SMT_SOLVER = None

class BARF(object):
    """Binary Analysis Framework."""

    def __init__(self, filename):
        logger.info("[+] BARF: Initializing...")

        self.code_analyzer = None
        self.ir_translator = None
        self.binary = None
        self.smt_solver = None
        self.gadget_classifier = None
        self.gadget_verifier = None
        self.arch_info = None
        self.gadget_finder = None
        self.text_section = None
        self.disassembler = None
        self.smt_translator = None
        self.ir_emulator = None
        self.bb_builder = None

        self.open(filename)

    def _load(self):
        # setup architecture
        self._setup_arch()

        # set up core modules
        self._setup_core_modules()

        # setup analysis modules
        self._setup_analysis_modules()

    def _setup_arch(self):
        """Set up architecture.
        """
        # set up architecture information
        self.arch_info = None

        if self.binary.architecture == arch.ARCH_X86:
            self._setup_x86_arch()
        else:
            # TODO: add arch in the binary file class
            self._setup_arm_arch()

    def _setup_arm_arch(self):
        """Set up ARM architecture.
        """
        arch_mode = arch.ARCH_ARM_MODE_THUMB

        self.arch_info = ArmArchitectureInformation(arch_mode)
        self.disassembler = ArmDisassembler(architecture_mode=arch_mode)
        self.ir_translator = ArmTranslator(architecture_mode=arch_mode)

    def _setup_x86_arch(self):
        """Set up x86 architecture.
        """
        arch_mode = self.binary.architecture_mode

        # Set up architecture information
        self.arch_info = X86ArchitectureInformation(arch_mode)
        self.disassembler = X86Disassembler(architecture_mode=arch_mode)
        self.ir_translator = X86Translator(architecture_mode=arch_mode)

    def _setup_core_modules(self):
        """Set up core modules.
        """
        self.ir_emulator = None
        self.smt_solver = None
        self.smt_translator = None

        if self.arch_info:
            # Set REIL emulator.
            self.ir_emulator = ReilEmulator(self.arch_info)

            # Set SMT Solver.
            if SMT_SOLVER == "Z3":
                self.smt_solver = Z3Solver()
            elif SMT_SOLVER == "CVC4":
                self.smt_solver = CVC4Solver()
            elif SMT_SOLVER is not None:
                raise Exception("Invalid SMT solver.")

            # Set SMT translator.
            if self.smt_solver:
                self.smt_translator = SmtTranslator(self.smt_solver, self.arch_info.address_size)

                self.smt_translator.set_arch_alias_mapper(self.arch_info.alias_mapper)
                self.smt_translator.set_arch_registers_size(self.arch_info.registers_size)

    def _setup_analysis_modules(self):
        """Set up analysis modules.
        """
        ## basic block
        self.bb_builder = BasicBlockBuilder(self.disassembler, self.text_section, self.ir_translator, self.arch_info)

        ## code analyzer
        self.code_analyzer = CodeAnalyzer(self.smt_solver, self.smt_translator, self.arch_info)

        ## gadget
        self.gadget_classifier = GadgetClassifier(self.ir_emulator, self.arch_info)
        self.gadget_finder = GadgetFinder(self.disassembler, self.text_section, self.ir_translator, self.binary.architecture, self.binary.architecture_mode)
        self.gadget_verifier = GadgetVerifier(self.code_analyzer, self.arch_info)

    # ======================================================================== #

    def open(self, filename):
        """Open a file for analysis.

        :param filename: name of an executable file
        :type filename: str

        """
        if filename:
            self.binary = BinaryFile(filename)
            self.text_section = self.binary.text_section

            self._load()

    def translate(self, ea_start=None, ea_end=None):
        """Translate to REIL instructions.

        :param ea_start: start address
        :type ea_start: int
        :param ea_end: end address
        :type ea_end: int

        :returns: a tuple of the form (address, assembler instruction, instruction size)
        :rtype: (int, Instruction, int)

        """
        start_addr = ea_start if ea_start else self.binary.ea_start
        end_addr = ea_end if ea_end else self.binary.ea_end

        self.ir_translator.reset()

        for addr, asm, _ in self.disassemble(start_addr, end_addr):
            yield addr, asm, self.ir_translator.translate(asm)

    def disassemble(self, ea_start=None, ea_end=None):
        """Disassemble assembler instructions.

        :param ea_start: start address
        :type ea_start: int
        :param ea_end: end address
        :type ea_end: int

        :returns: a tuple of the form (address, assembler instruction, instruction size)
        :rtype: (int, Instruction, int)

        """
        curr_addr = ea_start if ea_start else self.binary.ea_start
        end_addr = ea_end if ea_end else self.binary.ea_end

        while curr_addr < end_addr:
            # disassemble instruction
            start, end = curr_addr, min(curr_addr + 16, self.binary.ea_end + 1)

            asm = self.disassembler.disassemble(self.text_section[start:end], curr_addr)

            if not asm:
                return

            yield curr_addr, asm, asm.size

            # update instruction pointer
            curr_addr += asm.size

    def recover_cfg(self, ea_start=None, ea_end=None, symbols=None):
        """Recover CFG

        :param ea_start: start address
        :type ea_start: int
        :param ea_end: end address
        :type ea_end: int

        :returns: a graph where each node is a basic block
        :rtype: BasicBlockGraph

        """
        start_addr = ea_start if ea_start else self.binary.ea_start
        end_addr = ea_end if ea_end else self.binary.ea_end

        bb_list = self.bb_builder.build(start_addr, end_addr, symbols)
        bb_graph = BasicBlockGraph(bb_list)

        return bb_graph

    def recover_bbs(self, ea_start=None, ea_end=None):
        """Recover basic blocks.

        :param ea_start: start address
        :type ea_start: int
        :param ea_end: end address
        :type ea_end: int

        :returns: a list of basic blocks
        :rtype: list

        """
        start_addr = ea_start if ea_start else self.binary.ea_start
        end_addr = ea_end if ea_end else self.binary.ea_end

        bb_list = self.bb_builder.build(start_addr, end_addr)

        return bb_list

    def emulate_full(self, context, ea_start=None, ea_end=None):
        """Emulate REIL instructions.

        :param context: processor context
        :type context: dict

        :returns: a context
        :rtype: dict

        """
        start_addr = ea_start if ea_start else self.binary.ea_start
        end_addr = ea_end if ea_end else self.binary.ea_end

        # load registers
        if 'registers' in context:
            for reg, val in context['registers'].items():
                self.ir_emulator.registers[reg] = val

        # load memory
        if 'memory' in context:
            for addr, val in context['memory'].items():
                self.ir_emulator.memory.write(addr, 32 / 8, val)

        # instrs = [reil for _, _, reil in self.translate(ea_start, ea_end)]

        # self.ir_emulator.execute(instrs, start_addr << 8, end_address=end_addr << 8)

        # Create ReilContainer
        # ==================================================================== #
        from core.reil.reil import ReilContainer
        from core.reil.reil import ReilSequence

        instr_container = ReilContainer()

        asm_instr_last = None
        instr_seq_prev = None

        for asm_addr, asm_instr, asm_size in self.disassemble(ea_start, ea_end):
            instr_seq = ReilSequence()

            for reil_instr in self.ir_translator.translate(asm_instr):
                instr_seq.append(reil_instr)

            if instr_seq_prev:
                instr_seq_prev.next_sequence_address = instr_seq.address

            instr_container.add(instr_seq)

            instr_seq_prev = instr_seq

        if instr_seq_prev:
            if asm_instr_last:
                instr_seq_prev.next_sequence_address = (asm_instr_last.address + asm_instr_last.size) << 8
        # ==================================================================== #

        instr_container.dump()

        self.ir_emulator.execute(instr_container, start_addr << 8, end=end_addr << 8)

        context_out = {}

        # save registers
        context_out['registers'] = {}
        for reg, val in self.ir_emulator.registers.items():
            context_out['registers'][reg] = val

        # save memory
        context_out['memory'] = {}

        return context_out
