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
import subprocess

import arch

from analysis.basicblock import CFGRecoverer
from analysis.basicblock import ControlFlowGraph
from analysis.basicblock import RecursiveDescent
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
from core.reil import ReilContainer
from core.reil import ReilContainerInvalidAddressError
from core.reil import ReilEmulator
from core.reil import ReilSequence
from core.reil import split_address
from core.smt.smtlibv2 import CVC4Solver
from core.smt.smtlibv2 import Z3Solver
from core.smt.smttranslator import SmtTranslator

logger = logging.getLogger(__name__)

# Choose between SMT Solvers...
SMT_SOLVER = "Z3"
# SMT_SOLVER = "CVC4"
# SMT_SOLVER = None


def _check_solver_installation(solver):
    found = True
    try:
        path = subprocess.check_output(["which", solver])
    except subprocess.CalledProcessError as e:
        if e.returncode == 0x1:
            found = False
    return found


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

    def _load(self, arch_mode=None):
        # setup architecture
        self._setup_arch(arch_mode=arch_mode)

        # set up core modules
        self._setup_core_modules()

        # setup analysis modules
        self._setup_analysis_modules()

    def _setup_arch(self, arch_mode=None):
        """Set up architecture.
        """
        # set up architecture information
        self.arch_info = None

        if self.binary.architecture == arch.ARCH_X86:
            self._setup_x86_arch(arch_mode)
        else:
            # TODO: add arch to the binary file class.
            self._setup_arm_arch(arch_mode)

    def _setup_arm_arch(self, arch_mode=None):
        """Set up ARM architecture.
        """
        if arch_mode is None:
            arch_mode = arch.ARCH_ARM_MODE_THUMB

        self.arch_info = ArmArchitectureInformation(arch_mode)
        self.disassembler = ArmDisassembler(architecture_mode=arch_mode)
        self.ir_translator = ArmTranslator(architecture_mode=arch_mode)

    def _setup_x86_arch(self, arch_mode=None):
        """Set up x86 architecture.
        """
        if arch_mode is None:
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
            self.smt_solver = None

            if SMT_SOLVER == "Z3":
                if _check_solver_installation("z3"):
                    self.smt_solver = Z3Solver()
                else:
                    logger.warn("z3 solver is not installed. Run 'barf-install-solvers.sh' to install it.")
            elif SMT_SOLVER == "CVC4":
                if _check_solver_installation("cvc4"):
                    self.smt_solver = CVC4Solver()
                else:
                    logger.warn("cvc4 solver is not installed. Run 'barf-install-solvers.sh' to install it.")
            elif SMT_SOLVER is not None:
                raise Exception("Invalid SMT solver.")

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

    def load_architecture(self, name, arch_info, disassembler, translator):
        # Set up architecture information
        self.arch_info = arch_info
        self.disassembler = disassembler
        self.ir_translator = translator

        # setup analysis modules
        self._setup_analysis_modules()

    def translate(self, ea_start=None, ea_end=None, arch_mode=None):
        """Translate to REIL instructions.

        :param ea_start: start address
        :type ea_start: int
        :param ea_end: end address
        :type ea_end: int
        :param arch_mode: architecture mode
        :type arch_mode: int

        :returns: a tuple of the form (address, assembler instruction, instruction size)
        :rtype: (int, Instruction, int)

        """
        start_addr = ea_start if ea_start else self.binary.ea_start
        end_addr = ea_end if ea_end else self.binary.ea_end

        self.ir_translator.reset()

        for addr, asm, _ in self.disassemble(ea_start=start_addr, ea_end=end_addr, arch_mode=arch_mode):
            yield addr, asm, self.ir_translator.translate(asm)

    def disassemble(self, ea_start=None, ea_end=None, arch_mode=None):
        """Disassemble assembler instructions.

        :param ea_start: start address
        :type ea_start: int
        :param ea_end: end address
        :type ea_end: int
        :param arch_mode: architecture mode
        :type arch_mode: int

        :returns: a tuple of the form (address, assembler instruction, instruction size)
        :rtype: (int, Instruction, int)

        """
        if arch_mode is None:
            arch_mode = self.binary.architecture_mode

        curr_addr = ea_start if ea_start else self.binary.ea_start
        end_addr = ea_end if ea_end else self.binary.ea_end

        while curr_addr < end_addr:
            # disassemble instruction
            start, end = curr_addr, min(curr_addr + 16, self.binary.ea_end + 1)

            asm = self.disassembler.disassemble(self.text_section[start:end], curr_addr, architecture_mode=arch_mode)

            if not asm:
                return

            yield curr_addr, asm, asm.size

            # update instruction pointer
            curr_addr += asm.size

    def recover_cfg(self, ea_start=None, ea_end=None, symbols=None, callback=None, arch_mode=None):
        """Recover CFG

        :int start: Start address.
        :int end: End address.

        :returns: A CFG.

        """
        # Set architecture in case it wasn't already set.
        if arch_mode is None:
            arch_mode = self.binary.architecture_mode

        # Reload modules.
        self._load(arch_mode=arch_mode)

        cfg, _ = self._recover_cfg(start=ea_start, end=ea_end, symbols=symbols, callback=callback)

        return cfg

    def recover_cfg_all(self, entries, symbols=None, callback=None, arch_mode=None):
        """Recover CFG for all functions from an entry point and/or symbol table.

        :int start: Start address.
        :returns: A list of CFGs.

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

    def emulate_full(self, context, ea_start=None, ea_end=None, arch_mode=None):
        """Emulate REIL instructions.

        :param context: processor context (register and/or memory)
        :type context: dict
        :param ea_start: start address
        :type ea_start: int
        :param ea_end: end address
        :type ea_end: int
        :param arch_mode: architecture mode
        :type arch_mode: int

        :returns: a context
        :rtype: dict

        """
        def _translate_asm_instruction(asm_instr):
            reil_translator = self.ir_translator

            # Create ReilContainer
            instr_container = ReilContainer()
            instr_seq = ReilSequence()
            for reil_instr in reil_translator.translate(asm_instr):
                instr_seq.append(reil_instr)
            instr_container.add(instr_seq)

            return instr_container

        def _process_asm_instruction(reil_emulator, asm_instr):
            instr_container = _translate_asm_instruction(asm_instr)
            ip = asm_instr.address << 8 | 0x0
            next_addr = None

            while ip:
                # Fetch instruction.
                try:
                    reil_instr = instr_container.fetch(ip)
                except ReilContainerInvalidAddressError:
                    next_addr = split_address(ip)[0]
                    break

                next_ip = reil_emulator.single_step(reil_instr)

                # Update instruction pointer.
                ip = next_ip if next_ip else instr_container.get_next_address(ip)

            if next_addr is None:
                next_addr = asm_instr.address + asm_instr.size

            return next_addr

        if arch_mode is not None:
            # Reload modules.
            self._load(arch_mode=arch_mode)

        start_addr = ea_start if ea_start else self.binary.ea_start
        end_addr = ea_end if ea_end else self.binary.ea_end

        # Load registers
        for reg, val in context.get('registers', {}).items():
            self.ir_emulator.registers[reg] = val

        # Load memory
        for addr, val in context.get('memory', {}).items():
            self.ir_emulator.memory.write(addr, 4, val)

        next_addr = start_addr
        while next_addr != end_addr:
            start, end = next_addr, next_addr + self.arch_info.max_instruction_size
            asm_instr = self.disassembler.disassemble(self.text_section[start:end], next_addr)
            next_addr = _process_asm_instruction(self.ir_emulator, asm_instr)

        context_out = {
            'registers': {},
            'memory': {}
        }

        # save registers
        for reg, val in self.ir_emulator.registers.items():
            context_out['registers'][reg] = val

        return context_out

    def emulate_full_ex(self, context, instr_container, ea_start=None, ea_end=None, arch_mode=None):
        """Emulate REIL instructions from an instruction container.

        :param context: processor context (register and/or memory)
        :type context: dict
        :param instr_container: instruction container
        :type instr_container: ReilContainer
        :param ea_start: start address
        :type ea_start: int
        :param ea_end: end address
        :type ea_end: int
        :param arch_mode: architecture mode
        :type arch_mode: int

        :returns: a context
        :rtype: dict

        """
        if arch_mode is not None:
            # Reload modules.
            self._load(arch_mode=arch_mode)

        start_addr = ea_start if ea_start else self.binary.ea_start
        end_addr = ea_end if ea_end else self.binary.ea_end

        # Load registers
        for reg, val in context.get('registers', {}).items():
            self.ir_emulator.registers[reg] = val

        # Load memory
        for addr, val in context.get('memory', {}).items():
            self.ir_emulator.memory.write(addr, 4, val)

        self.ir_emulator.execute(instr_container, start=start_addr << 8, end=end_addr << 8)

        context_out = {
            'registers': {},
            'memory': {}
        }

        # save registers
        for reg, val in self.ir_emulator.registers.items():
            context_out['registers'][reg] = val

        return context_out
