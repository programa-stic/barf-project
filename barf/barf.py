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
from __future__ import absolute_import

import logging

from .analysis.codeanalyzer import CodeAnalyzer
from .analysis.graphs.controlflowgraph import CFGRecoverer
from .analysis.graphs.controlflowgraph import ControlFlowGraph
from .analysis.graphs.controlflowgraph import RecursiveDescent
from .analysis.gadgets import GadgetClassifier
from .analysis.gadgets import GadgetFinder
from .analysis.gadgets import GadgetVerifier
from .arch import ARCH_ARM_MODE_THUMB
from .arch import ARCH_X86
from .arch.arm import ArmArchitectureInformation
from .arch.arm.disassembler import ArmDisassembler
from .arch.arm.translator import ArmTranslator
from .arch.emulator import Emulator
from .arch.x86 import X86ArchitectureInformation
from .arch.x86.disassembler import X86Disassembler
from .arch.x86.translator import X86Translator
from .core.binary import BinaryFile
from .core.reil.emulator import ReilEmulator
from .core.smt.smtsolver import CVC4Solver
from .core.smt.smtsolver import SmtSolverNotFound
from .core.smt.smtsolver import Z3Solver
from .core.smt.smttranslator import SmtTranslator

logger = logging.getLogger(__name__)

# Choose between SMT Solvers...
SMT_SOLVER = "Z3"
# SMT_SOLVER = "CVC4"
# SMT_SOLVER = None


class BARF(object):
    """Binary Analysis Framework."""

    def __init__(self, filename, load_bin=True):
        logger.info("Initializing BARF")

        self.name = None
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
        self._load_bin = load_bin

        self.emulator = None

        self._arch_mode = None

        self.open(filename)

    def _load(self, arch_mode=None):
        # setup architecture
        self._setup_arch(arch_mode=arch_mode)

        # set up core modules
        self._setup_core_modules()

        # setup analysis modules
        self._setup_analysis_modules()

        if self._load_bin:
            self.emulator.load_binary(self.binary)

    def _setup_arch(self, arch_mode=None):
        """Set up architecture.
        """
        # set up architecture information
        self.arch_info = None

        if self.binary.architecture == ARCH_X86:
            self._setup_x86_arch(arch_mode)
        else:
            # TODO: add arch to the binary file class.
            self._setup_arm_arch(arch_mode)

    def _setup_arm_arch(self, arch_mode=None):
        """Set up ARM architecture.
        """
        if arch_mode is None:
            arch_mode = ARCH_ARM_MODE_THUMB

        self.name = "ARM"
        self.arch_info = ArmArchitectureInformation(arch_mode)
        self.disassembler = ArmDisassembler(architecture_mode=arch_mode)
        self.ir_translator = ArmTranslator(architecture_mode=arch_mode)

    def _setup_x86_arch(self, arch_mode=None):
        """Set up x86 architecture.
        """
        if arch_mode is None:
            arch_mode = self.binary.architecture_mode

        # Set up architecture information
        self.name = "x86"
        self.arch_info = X86ArchitectureInformation(arch_mode)
        self.disassembler = X86Disassembler(arch_mode)
        self.ir_translator = X86Translator(arch_mode)

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
            self.smt_solver = None

            if SMT_SOLVER not in ("Z3", "CVC4"):
                raise Exception("{} SMT solver not supported.".format(SMT_SOLVER))

            try:
                if SMT_SOLVER == "Z3":
                    self.smt_solver = Z3Solver()
                elif SMT_SOLVER == "CVC4":
                    self.smt_solver = CVC4Solver()
            except SmtSolverNotFound:
                logger.warn("{} Solver is not installed. Run 'barf-install-solvers.sh' to install it.".format(SMT_SOLVER))

            # Set SMT translator.
            self.smt_translator = None

            if self.smt_solver:
                self.smt_translator = SmtTranslator(self.smt_solver, self.arch_info.address_size)

                self.smt_translator.set_arch_alias_mapper(self.arch_info.alias_mapper)
                self.smt_translator.set_arch_registers_size(self.arch_info.registers_size)

    def _setup_analysis_modules(self):
        """Set up analysis modules.
        """
        # Basic block.
        self.bb_builder = CFGRecoverer(RecursiveDescent(self.disassembler, self.text_section, self.ir_translator,
                                                        self.arch_info))

        # Code analyzer.
        self.code_analyzer = None

        if self.smt_translator:
            self.code_analyzer = CodeAnalyzer(self.smt_solver, self.smt_translator, self.arch_info)

        # Gadgets classifier.
        self.gadget_classifier = GadgetClassifier(self.ir_emulator, self.arch_info)

        # Gadgets finder.
        self.gadget_finder = GadgetFinder(self.disassembler, self.text_section, self.ir_translator,
                                          self.binary.architecture, self.binary.architecture_mode)

        # Gadget verifier.
        self.gadget_verifier = None

        if self.code_analyzer:
            self.gadget_verifier = GadgetVerifier(self.code_analyzer, self.arch_info)

        self.emulator = Emulator(self.arch_info, self.ir_emulator, self.ir_translator, self.disassembler)

    # ======================================================================== #

    def open(self, filename):
        """Open a file for analysis.

        Args:
            filename (str): Name of an executable file.
        """
        if filename:
            self.binary = BinaryFile(filename)
            self.text_section = self.binary.text_section

            self._load(arch_mode=self.binary.architecture_mode)

    def load_architecture(self, name, arch_info, disassembler, translator):
        """Translate to REIL instructions.

        Args:
            name (str): Architecture's name.
            arch_info (ArchitectureInformation): Architecture information object.
            disassembler (Disassembler): Disassembler for the architecture.
            translator (Translator): Translator for the architecture.
        """
        # Set up architecture information.
        self.name = name
        self.arch_info = arch_info
        self.disassembler = disassembler
        self.ir_translator = translator

        # Setup analysis modules.
        self._setup_analysis_modules()

    def translate(self, start=None, end=None, arch_mode=None):
        """Translate to REIL instructions.

        Args:
            start (int): Start address.
            end (int): End address.
            arch_mode (int): Architecture mode.

        Returns:
            (int, Instruction, list): A tuple of the form (address, assembler instruction, REIL instructions).
        """
        start_addr = start if start else self.binary.ea_start
        end_addr = end if end else self.binary.ea_end

        self.ir_translator.reset()

        for addr, asm, _ in self.disassemble(start=start_addr, end=end_addr, arch_mode=arch_mode):
            yield addr, asm, self.ir_translator.translate(asm)

    def disassemble(self, start=None, end=None, arch_mode=None):
        """Disassemble native instructions.

        Args:
            start (int): Start address.
            end (int): End address.
            arch_mode (int): Architecture mode.

        Returns:
            (int, Instruction, int): A tuple of the form (address, assembler instruction, instruction size).
        """
        if arch_mode is None:
            arch_mode = self.binary.architecture_mode

        curr_addr = start if start else self.binary.ea_start
        end_addr = end if end else self.binary.ea_end

        while curr_addr < end_addr:
            # Fetch the instruction.
            encoding = self.__fetch_instr(curr_addr)

            # Decode it.
            asm_instr = self.disassembler.disassemble(encoding, curr_addr, architecture_mode=arch_mode)

            if not asm_instr:
                return

            yield curr_addr, asm_instr, asm_instr.size

            # update instruction pointer
            curr_addr += asm_instr.size

    def recover_cfg(self, start=None, end=None, symbols=None, callback=None, arch_mode=None):
        """Recover CFG.

        Args:
            start (int): Start address.
            end (int): End address.
            symbols (dict): Symbol table.
            callback (function): A callback function which is called after each successfully recovered CFG.
            arch_mode (int): Architecture mode.

        Returns:
            ControlFlowGraph: A CFG.
        """
        # Set architecture in case it wasn't already set.
        if arch_mode is None:
            arch_mode = self.binary.architecture_mode

        # Reload modules.
        self._load(arch_mode=arch_mode)

        # Check start address.
        start = start if start else self.binary.entry_point

        cfg, _ = self._recover_cfg(start=start, end=end, symbols=symbols, callback=callback)

        return cfg

    def recover_cfg_all(self, entries, symbols=None, callback=None, arch_mode=None):
        """Recover CFG for all functions from an entry point and/or symbol table.

        Args:
            entries (list): A list of function addresses' to start the CFG recovery process.
            symbols (dict): Symbol table.
            callback (function): A callback function which is called after each successfully recovered CFG.
            arch_mode (int): Architecture mode.

        Returns:
            list: A list of recovered CFGs.
        """
        # Set architecture in case it wasn't already set.
        if arch_mode is None:
            arch_mode = self.binary.architecture_mode

        # Reload modules.
        self._load(arch_mode=arch_mode)

        # Set symbols.
        symbols = {} if not symbols else symbols

        # Recover the CFGs.
        cfgs = []
        addrs_processed = set()
        calls = entries

        while len(calls) > 0:
            start, calls = calls[0], calls[1:]

            cfg, calls_tmp = self._recover_cfg(start=start, symbols=symbols, callback=callback)

            addrs_processed.add(start)

            cfgs.append(cfg)

            for addr in sorted(calls_tmp):
                if addr not in addrs_processed and addr not in calls:
                    calls.append(addr)

        return cfgs

    def _recover_cfg(self, start=None, end=None, symbols=None, callback=None):
        """Recover CFG

        """
        # Retrieve symbol name in case it is available.
        if symbols and start in symbols:
            name = symbols[start][0]
            size = symbols[start][1] - 1 if symbols[start][1] != 0 else 0
        else:
            name = "sub_{:x}".format(start)
            size = 0

        # Compute start and end address.
        start_addr = start if start else self.binary.ea_start
        end_addr = end if end else self.binary.ea_end

        # Set callback.
        if callback:
            callback(start, name, size)

        # Recover basic blocks.
        bbs, calls = self.bb_builder.build(start_addr, end_addr, symbols)

        # Build CFG.
        cfg = ControlFlowGraph(bbs, name=name)

        return cfg, calls

    def emulate(self, context=None, start=None, end=None, arch_mode=None, hooks=None, max_instrs=None, print_asm=False):
        """Emulate native code.

        Args:
            context (dict): Processor context (register and/or memory).
            start (int): Start address.
            end (int): End address.
            arch_mode (int): Architecture mode.
            hooks (dict): Hooks by address.
            max_instrs (int): Maximum number of instructions to execute.
            print_asm (bool): Print asm.

        Returns:
            dict: Processor context.
        """
        if arch_mode is not None:
            # Reload modules.
            self._load(arch_mode=arch_mode)

        context = context if context else {}

        start_addr = start if start else self.binary.ea_start
        end_addr = end if end else self.binary.ea_end

        hooks = hooks if hooks else {}

        # Load registers
        for reg, val in context.get('registers', {}).items():
            self.ir_emulator.registers[reg] = val

        # Load memory
        # TODO Memory content should be encoded as hex strings so each
        # entry can be of different sizes.
        for addr, val in context.get('memory', {}).items():
            self.ir_emulator.memory.write(addr, 4, val)

        # Execute the code.
        self.emulator.emulate(start_addr, end_addr, hooks, max_instrs, print_asm)

        context_out = {
            'registers': {},
            'memory': {}
        }

        # save registers
        for reg, val in self.ir_emulator.registers.items():
            context_out['registers'][reg] = val

        return context_out

    def __fetch_instr(self, next_addr):
        start, end = next_addr, next_addr + self.arch_info.max_instruction_size

        encoding = bytearray()
        for i in range(end - start):
            encoding.append(self.ir_emulator.read_memory(start + i, 1))

        return encoding
