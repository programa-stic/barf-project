import logging
import sys
import traceback

import barf
import barf.arch.x86.x86disassembler

from barf.arch import ARCH_X86_MODE_32
from barf.arch import ARCH_X86_MODE_64
from barf.arch.x86.x86base import X86ArchitectureInformation
from barf.arch.x86.x86base import X86ImmediateOperand
from barf.arch.x86.x86base import X86MemoryOperand
from barf.arch.x86.x86base import X86RegisterOperand
from barf.arch.x86.x86instructiontranslator import FULL_TRANSLATION, LITE_TRANSLATION
from barf.arch.x86.x86instructiontranslator import X86InstructionTranslator
from barf.core.reil import ReilEmptyOperand
from barf.core.reil import ReilImmediateOperand
from barf.core.reil import ReilInstructionBuilder
from barf.core.reil import ReilRegisterOperand
from barf.utils.utils import VariableNamer

from barf.arch.x86.x86instructiontranslator import add_register_size

logger = logging.getLogger("X86Translator")

class X86Translator(object):

    """x86 to IR Translator."""

    def __init__(self, architecture_mode=ARCH_X86_MODE_32, translation_mode=FULL_TRANSLATION):

        # Set *Architecture Mode*. The translation of each instruction
        # into the REIL language is based on this.
        self.arch_mode = architecture_mode

        # Set *Translation Mode*.
        self._translation_mode = translation_mode

        # An instance of a ReilInstructionBuilder.
        self.ir_builder = ReilInstructionBuilder()

        # An instance of *ArchitectureInformation*.
        self.arch_info = X86ArchitectureInformation(self.arch_mode)

        # An instance of a *VariableNamer*. This is used so all the
        # temporary REIL registers are unique.
        self.ir_reg_name_generator = VariableNamer("t", separator="")

        # An instance of a X86InstructionTranslator
        self.instr_translator = X86InstructionTranslator(self.ir_reg_name_generator, self.arch_mode, self._translation_mode)

    def translate(self, instruction):
        """Return IR representation of an instruction.
        """
        try:
            trans_instrs = self.instr_translator.translate(instruction)
        except NotImplementedError:
            trans_instrs = [self.ir_builder.gen_unkn()]

            self._log_not_supported_instruction(instruction)
        except:
            self._log_translation_exception(instruction)

        return trans_instrs

    def reset(self):
        """Restart IR register name generator.
        """
        self.ir_reg_name_generator.reset()

    @property
    def translation_mode(self):
        """Get translation mode.
        """
        return self._translation_mode

    @translation_mode.setter
    def translation_mode(self, value):
        """Set translation mode.
        """
        self._translation_mode = value
        self.instr_translator._translation_mode = value

    def _log_not_supported_instruction(self, instruction):
        if instruction.bytes:
            bytes_str = " ".join("%02x" % ord(b) for b in instruction.bytes)
        else:
            bytes_str = ""

        logger.info(
            "Instruction not supported: %s (%s  %s)",
            instruction.mnemonic,
            bytes_str,
            instruction
        )

    def _log_translation_exception(self, instruction):
        if instruction.bytes:
            bytes_str = " ".join("%02x" % ord(b) for b in instruction.bytes)
        else:
            bytes_str = ""

        logger.error(
            "Failed to translate x86 to REIL: %s (%s)",
            instruction,
            bytes_str,
            exc_info=True
        )
