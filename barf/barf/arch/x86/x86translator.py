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

def print_translation_exception(instruction, err):
    logger.debug("[-] Exception (%s:%d) : '%s'" % \
        (__name__, sys.exc_traceback.tb_lineno, str(err)))
    logger.debug("")
    logger.debug(traceback.format_exc())

    logger.debug(str(instruction))
    logger.debug("%s (%s)" % (str(instruction.mnemonic), type(instruction)))

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

    @add_register_size
    def translate(self, instruction):
        """Return IR representation of an instruction.
        """
        trans_instrs = []

        try:
            src_read_instrs = []
            dst_write_instrs = []

            src_regs, src_read_instrs = self._translate_src_oprnds(instruction)
            dst_regs, dst_write_instrs = self._translate_dst_oprnds(instruction)

            trans_instrs = self.instr_translator.translate(instruction, src_regs, dst_regs)
        except NotImplementedError as err:
            src_read_instrs = []
            dst_write_instrs = []

            trans_instrs = [self.ir_builder.gen_unkn()]

            logger.debug("[E] x86 Translator :: Instruction not supported : '%s' (%s)" % (instruction, instruction.mnemonic))
        except Exception as err:
            print_translation_exception(instruction, err)

        translation = src_read_instrs + trans_instrs + dst_write_instrs

        self._translate_instr_addresses(instruction.address, translation)

        return translation

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

    # Auxiliary functions
    # ======================================================================== #
    def _translate_instr_addresses(self, base_address, translation):
        if base_address:
            for index, instr in enumerate(translation):
                instr.address = (base_address << 8) | (index & 0xff)

    def _translate_src_oprnds(self, instruction):
        """Return instruction sources access translation.
        """
        src_regs = []
        src_read_instrs = []

        for src, acc_mem in instruction.source_operands:
            if isinstance(src, barf.arch.x86.x86base.X86ImmediateOperand):
                read_src_reg = ReilImmediateOperand(src.immediate, src.size)
            elif isinstance(src, barf.arch.x86.x86base.X86RegisterOperand):
                read_src_reg = ReilRegisterOperand(src.name, src.size)
            elif isinstance(src, barf.arch.x86.x86base.X86MemoryOperand):
                read_src_reg = ReilRegisterOperand(self.ir_reg_name_generator.get_next(), src.size)

                src_read_instrs += self._generate_read_instr(src, read_src_reg, acc_mem)
            else:
                raise Exception()

            src_regs += [read_src_reg]

        return src_regs, src_read_instrs

    def _translate_dst_oprnds(self, instruction):
        """Return instruction destination access translation.
        """
        dst_regs = []
        dst_write_instrs = []

        src_regs = filter(lambda r : isinstance(r, barf.arch.x86.x86base.X86RegisterOperand), map(lambda t : t[0], instruction.source_operands))

        for dst in instruction.destination_operands:
            # print type(dst)

            if isinstance(dst, barf.arch.x86.x86base.X86RegisterOperand):
                if dst.name in [src.name for src in src_regs]:
                    write_dst_reg = ReilRegisterOperand(self.ir_reg_name_generator.get_next(), dst.size)

                    dst_reg = ReilRegisterOperand(dst.name, dst.size)

                    dst_write_instrs += [self.ir_builder.gen_str(write_dst_reg, dst_reg)]
                else:
                    write_dst_reg = ReilRegisterOperand(dst.name, dst.size)
            elif isinstance(dst, barf.arch.x86.x86base.X86MemoryOperand):
                write_dst_reg = ReilRegisterOperand(self.ir_reg_name_generator.get_next(), dst.size)

                dst_write_instrs += self._generate_write_instrs(dst, write_dst_reg)
            else:
                raise Exception()

            dst_regs += [write_dst_reg]

        return dst_regs, dst_write_instrs

    def _generate_read_instr(self, operand, dst_reg, access_memory):
        """Return operand read memory access translation.
        """
        if access_memory:
            addr_reg, instrs = self._compute_memory_address(operand, None)

            instrs += [self.ir_builder.gen_ldm(addr_reg, dst_reg)]
        else:
            addr_reg, instrs = self._compute_memory_address(operand, dst_reg)

            if len(instrs) == 0:
                instrs += [self.ir_builder.gen_str(addr_reg, dst_reg)]

        return instrs

    def _generate_write_instrs(self, operand, dst_reg):
        """Return operand write memory access translation.
        """
        addr_reg, instrs = self._compute_memory_address(operand, None)

        return instrs + [self.ir_builder.gen_stm(dst_reg, addr_reg)]

    def _compute_memory_address(self, mem_operand, dst_reg):
        """Return operand memory access translation.
        """
        # reil code generation:
        #   add  base,  disp, t0
        #   mul index, scale, t1
        #   add    t1,    t0, t2
        size = self.arch_info.architecture_size

        regs, instrs = self._unpack_memory_operand(mem_operand)

        addr_reg = dst_reg if dst_reg else None

        if len(regs) == 3:
            temp_reg = ReilRegisterOperand(self.ir_reg_name_generator.get_next(), size)

            if not dst_reg:
                addr_reg = ReilRegisterOperand(self.ir_reg_name_generator.get_next(), size)

            instrs += [self.ir_builder.gen_add(regs[0], regs[1], temp_reg)]
            instrs += [self.ir_builder.gen_add(temp_reg, regs[2], addr_reg)]
        elif len(regs) == 2:
            if not dst_reg:
                addr_reg = ReilRegisterOperand(self.ir_reg_name_generator.get_next(), size)

            instrs += [self.ir_builder.gen_add(regs[0], regs[1], addr_reg)]
        elif len(regs) == 1:
            addr_reg = regs[0]

        return addr_reg, instrs

    def _unpack_memory_operand(self, operand):
        """Return memory operand components.
        """
        # [base + scale * index + disp] ->
        #    [base, index * scale, disp], [index * scale instr]

        size = self.arch_info.architecture_size

        instrs = []

        base_reg, index_reg, disp_reg = None, None, None

        if operand.base:
            base_reg = ReilRegisterOperand(operand.base, size)

        if operand.index and operand.scale != 0x0:
            index_temp_reg = ReilRegisterOperand(operand.index, size)
            scale_temp_reg = ReilImmediateOperand(operand.scale, size)
            index_reg = ReilRegisterOperand(self.ir_reg_name_generator.get_next(), size)

            mul_instr = self.ir_builder.gen_mul(index_temp_reg, scale_temp_reg, index_reg)

            instrs += [mul_instr]

        if operand.displacement and operand.displacement != 0x0:
            disp_reg = ReilImmediateOperand(operand.displacement, size)

        regs = filter(lambda x : x, [base_reg, index_reg, disp_reg])

        return regs, instrs
