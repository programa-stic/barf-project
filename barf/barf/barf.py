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
from arch.x86.x86base import X86ArchitectureInformation
from arch.x86.x86disassembler import X86Disassembler
from arch.x86.x86translator import X86Translator

from arch.arm.armbase import ArmArchitectureInformation
from arch.arm.armdisassembler import ArmDisassembler
from arch.arm.armtranslator import ArmTranslator

from arch.arm.armbase import ARCH_ARM_MODE_32

from core.bi import BinaryFile
from core.reil import ReilEmulator
from core.smt.smtlibv2 import Z3Solver
from core.smt.smtlibv2 import CVC4Solver

from core.smt.smttranslator import SmtTranslator

logging.basicConfig(
    filename = os.path.dirname(os.path.realpath(__file__)) + os.sep + "log/barf." + str(int(time.time())) + ".log",
    format = "%(asctime)s: %(name)s:%(levelname)s: %(message)s",
    level = logging.DEBUG
)

verbose = False

# Choose between SMT Solvers...
SMT_SOLVER  = "Z3"
# SMT_SOLVER  = "CVC4"

class BARF(object):
    """Binary Analysis Framework."""

    def __init__(self, filename):
        if verbose:
            print("[+] BARF: Initializing...")

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
            self._setup_arm_arch() # TODO: add arch in the binary file class


    def _setup_arm_arch(self):
        """Set up ARM architecture.
        """
        self.arch_info = ArmArchitectureInformation(ARCH_ARM_MODE_32)
        self.disassembler = ArmDisassembler(architecture_mode=ARCH_ARM_MODE_32)
        self.ir_translator = ArmTranslator(architecture_mode=ARCH_ARM_MODE_32)

    def _setup_x86_arch(self):
        """Set up x86 architecture.
        """
        # set up architecture information
        self.arch_info = X86ArchitectureInformation(self.binary.architecture_mode)
        self.disassembler = X86Disassembler(architecture_mode=self.arch_info.architecture_mode)
        self.ir_translator = X86Translator(architecture_mode=self.arch_info.architecture_mode)

    def _setup_core_modules(self):
        """Set up core modules.
        """
#         self.disassembler = None
        self.ir_emulator = None
#         self.ir_translator = None
        self.smt_solver = None
        self.smt_translator = None

        if self.arch_info:
            
            self.ir_emulator = ReilEmulator(self.arch_info.address_size)
            

            if SMT_SOLVER == "Z3":
                self.smt_solver = Z3Solver()
            elif SMT_SOLVER == "CVC4":
                self.smt_solver = CVC4Solver()
            else:
                raise Exception("Invalid SMT solver.")

            self.smt_translator = SmtTranslator(self.smt_solver, self.arch_info.address_size)

            self.ir_emulator.set_arch_registers(self.arch_info.registers_gp_all)
            self.ir_emulator.set_arch_registers_size(self.arch_info.registers_size)
            self.ir_emulator.set_reg_access_mapper(self.arch_info.registers_access_mapper())

            self.smt_translator.set_reg_access_mapper(self.arch_info.registers_access_mapper())
            self.smt_translator.set_arch_registers_size(self.arch_info.registers_size)

    def _setup_analysis_modules(self):
        """Set up analysis modules.
        """
        ## basic block
        self.bb_builder = BasicBlockBuilder(self.disassembler, self.text_section, self.ir_translator)

        ## code analyzer
        self.code_analyzer = CodeAnalyzer(self.smt_solver, self.smt_translator)

        # TODO: This should not be part of the framework, but something that
        # it is build upon.
        ## gadget
        self.gadget_classifier = GadgetClassifier(self.ir_emulator, self.arch_info)
        self.gadget_finder = GadgetFinder(self.disassembler, self.text_section, self.ir_translator)
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

        for addr, asm, size in self.disassemble(start_addr, end_addr):
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

    def recover_cfg(self, ea_start=None, ea_end=None, mode=None):
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

        bb_list = self.bb_builder.build(start_addr, end_addr)
        bb_graph = BasicBlockGraph(bb_list)

        return bb_graph

    def recover_bbs(self, ea_start=None, ea_end=None, mode=None):
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
                self.ir_emulator.get_memory().write(addr, 32, val)

        instrs = [reil for addr, asm, reil in self.translate(ea_start, ea_end)]

        self.ir_emulator.execute(instrs, ea_start << 8, end_address=ea_end << 8)

        context_out = {}

        # save registers
        context_out['registers'] = {}
        for reg, val in self.ir_emulator.registers.items():
            context_out['registers'][reg] = val

        # save memory
        context_out['memory'] = {}

        return context_out
