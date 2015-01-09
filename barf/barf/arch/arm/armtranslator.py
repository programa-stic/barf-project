import logging

import barf

from barf.arch import ARCH_ARM_MODE_32
from barf.arch import ARCH_ARM_MODE_64
from barf.arch.arm.armbase import ArmArchitectureInformation
from barf.arch.arm.armbase import ArmImmediateOperand
from barf.arch.arm.armbase import ArmMemoryOperand
from barf.arch.arm.armbase import ArmRegisterOperand
from barf.core.reil import ReilEmptyOperand
from barf.core.reil import ReilImmediateOperand
from barf.core.reil import ReilInstructionBuilder
from barf.core.reil import ReilInstruction
from barf.core.reil import ReilMnemonic
from barf.core.reil import ReilRegisterOperand
from barf.utils.utils import VariableNamer

FULL_TRANSLATION = 0
LITE_TRANSLATION = 1

logger = logging.getLogger(__name__)

class Label(object):

    def __init__(self, name):
        self.name = name

    def __str__(self):
        string = self.name + ":"

        return string

class TranslationBuilder(object):

    def __init__(self, ir_name_generator, architecture_mode):
        self._ir_name_generator = ir_name_generator

        self._arch_info = ArmArchitectureInformation(architecture_mode)

        self._instructions = []

        self._builder = ReilInstructionBuilder()

    def add(self, instr):
        self._instructions.append(instr)

    def temporal(self, size):
        return ReilRegisterOperand(self._ir_name_generator.get_next(), size)

    def immediate(self, value, size):
        return ReilImmediateOperand(value, size)

    def label(self, name):
        return Label(name)

    def instanciate(self, address):
        # Set instructions address.
        instrs = self._instructions

        for instr in instrs:
            instr.address = address << 8

        instrs = self._resolve_loops(instrs)

        return instrs

    def read(self, arm_operand):

        if isinstance(arm_operand, ArmImmediateOperand):

            reil_operand = ReilImmediateOperand(arm_operand.immediate, arm_operand.size)

        elif isinstance(arm_operand, ArmRegisterOperand):

            reil_operand = ReilRegisterOperand(arm_operand.name, arm_operand.size)

        elif isinstance(arm_operand, ArmMemoryOperand):

            addr = self._compute_memory_address(arm_operand)

            reil_operand = self.temporal(arm_operand.size)

            self.add(self._builder.gen_ldm(addr, reil_operand))

        else:
            raise Exception()

        return reil_operand

    def write(self, arm_operand, value):

        if isinstance(arm_operand, ArmRegisterOperand):

            reil_operand = ReilRegisterOperand(arm_operand.name, arm_operand.size)

            self.add(self._builder.gen_str(value, reil_operand))

        elif isinstance(arm_operand, ArmMemoryOperand):

            addr = self._compute_memory_address(arm_operand)

            self.add(self._builder.gen_stm(value, addr))

        else:
            raise Exception()

    def _resolve_loops(self, instrs):
        idx_by_labels = {}

        # Collect labels.
        curr = 0
        for index, instr in enumerate(instrs):
            if isinstance(instr, Label):
                idx_by_labels[instr.name] = curr

                del instrs[index]
            else:
                curr += 1

        # Resolve instruction addresses and JCC targets.
        for index, instr in enumerate(instrs):
            assert isinstance(instr, ReilInstruction)

            instr.address |= index

            if instr.mnemonic == ReilMnemonic.JCC:
                target = instr.operands[2]

                if isinstance(target, Label):
                    idx = idx_by_labels[target.name]
                    address = (instr.address & ~0xff) | idx

                    instr.operands[2] = ReilImmediateOperand(address, 40)

        return instrs

    def _compute_memory_address(self, mem_operand):
        """Return operand memory access translation.
        """
        size = self._arch_info.architecture_size

        addr = None

        if mem_operand.base:
            addr = ReilRegisterOperand(mem_operand.base, size)

        if mem_operand.index and mem_operand.scale != 0x0:
            index = ReilRegisterOperand(mem_operand.index, size)
            scale = ReilImmediateOperand(mem_operand.scale, size)
            scaled_index = self.temporal(size)

            self.add(self._builder.gen_mul(index, scale, scaled_index))

            if addr:
                tmp = self.temporal(size)

                self.add(self._builder.gen_add(addr, scaled_index, tmp))

                addr = tmp
            else:
                addr = scaled_index

        if mem_operand.displacement and mem_operand.displacement != 0x0:
            disp = ReilImmediateOperand(mem_operand.displacement, size)

            if addr:
                tmp = self.temporal(size)

                self.add(self._builder.gen_add(addr, disp, tmp))

                addr = tmp
            else:
                addr = disp

        return addr

class ArmTranslator(object):

    """ARM to IR Translator."""

    def __init__(self, architecture_mode=ARCH_ARM_MODE_32, translation_mode=FULL_TRANSLATION):

        # Set *Architecture Mode*. The translation of each instruction
        # into the REIL language is based on this.
        self._arch_mode = architecture_mode

        # An instance of *ArchitectureInformation*.
        self._arch_info = ArmArchitectureInformation(architecture_mode)

        # Set *Translation Mode*.
        self._translation_mode = translation_mode

        # An instance of a *VariableNamer*. This is used so all the
        # temporary REIL registers are unique.
        self._ir_name_generator = VariableNamer("t", separator="")

        self._builder = ReilInstructionBuilder()

        self._flags = {
            "af" : ReilRegisterOperand("af", 1),
            "cf" : ReilRegisterOperand("cf", 1),
            "df" : ReilRegisterOperand("df", 1),
            "of" : ReilRegisterOperand("of", 1),
            "pf" : ReilRegisterOperand("pf", 1),
            "sf" : ReilRegisterOperand("sf", 1),
            "zf" : ReilRegisterOperand("zf", 1),
        }

        if self._arch_mode == ARCH_ARM_MODE_32:
            self._sp = ReilRegisterOperand("esp", 32)
            self._bp = ReilRegisterOperand("ebp", 32)
            self._ip = ReilRegisterOperand("eip", 32)

            self._ws = ReilImmediateOperand(4, 32) # word size
        elif self._arch_mode == ARCH_ARM_MODE_64:
            self._sp = ReilRegisterOperand("rsp", 64)
            self._bp = ReilRegisterOperand("rbp", 64)
            self._ip = ReilRegisterOperand("rip", 64)

            self._ws = ReilImmediateOperand(8, 64) # word size

    def translate(self, instruction):
        """Return IR representation of an instruction.
        """
        try:
            trans_instrs = self._translate(instruction)
        except NotImplementedError:
            trans_instrs = [self._builder.gen_unkn()]

            self._log_not_supported_instruction(instruction)
        except:
            self._log_translation_exception(instruction)
            print(instruction)

        return trans_instrs

    def _translate(self, instruction):
        """Translate a arm instruction into REIL language.

        :param instruction: a arm instruction
        :type instruction: ArmInstruction
        """
        # Retrieve translation function.
        translator_name = "_translate_" + instruction.mnemonic
        translator_fn = getattr(self, translator_name, self._not_implemented)

        # Translate instruction.
        tb = TranslationBuilder(self._ir_name_generator, self._arch_mode)

        translator_fn(tb, instruction)

        return tb.instanciate(instruction.address)

    def reset(self):
        """Restart IR register name generator.
        """
        self._ir_name_generator.reset()

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

    def _log_not_supported_instruction(self, instruction):
        bytes_str = " ".join("%02x" % ord(b) for b in instruction.bytes)

        logger.info(
            "Instruction not supported: %s (%s [%s])",
            instruction.mnemonic,
            instruction,
            bytes_str
        )

    def _log_translation_exception(self, instruction):
        bytes_str = " ".join("%02x" % ord(b) for b in instruction.bytes)

        logger.error(
            "Failed to translate arm to REIL: %s (%s)",
            instruction,
            bytes_str,
            exc_info=True
        )

# ============================================================================ #

    def _not_implemented(self, tb, instruction):
        raise NotImplementedError("Instruction Not Implemented")

# Translators
# ============================================================================ #
# ============================================================================ #

# "Flags"
# ============================================================================ #
    def _update_af(self, tb, oprnd0, oprnd1, result):
        # TODO: Implement
        pass

    def _update_pf(self, tb, oprnd0, oprnd1, result):
        # TODO: Implement
        pass

    def _update_sf(self, tb, oprnd0, oprnd1, result):
        # Create temporal variables.
        tmp0 = tb.temporal(result.size)

        mask0 = tb.immediate(2**result.size-1, result.size)
        shift0 = tb.immediate(-(result.size-1), result.size)

        sf = self._flags["sf"]

        tb.add(self._builder.gen_and(result, mask0, tmp0))  # filter sign bit
        tb.add(self._builder.gen_bsh(tmp0, shift0, sf))     # extract sign bit

    def _update_of(self, tb, oprnd0, oprnd1, result):
        of = self._flags["of"]

        imm0 = tb.immediate(2**(oprnd0.size-1), oprnd0.size)
        imm1 = tb.immediate(1, oprnd0.size)
        imm3 = tb.immediate(-(oprnd0.size-1), oprnd0.size)
        imm4 = tb.immediate(2**(oprnd0.size-1), result.size)

        tmp0 = tb.temporal(oprnd0.size)
        tmp1 = tb.temporal(oprnd1.size)
        tmp2 = tb.temporal(oprnd0.size)
        tmp3 = tb.temporal(oprnd0.size)
        tmp4 = tb.temporal(oprnd0.size)
        tmp5 = tb.temporal(oprnd0.size)
        tmp6 = tb.temporal(oprnd0.size)

        tb.add(self._builder.gen_and(oprnd0, imm0, tmp0))   # filter sign bit oprnd 1
        tb.add(self._builder.gen_and(oprnd1, imm0, tmp1))   # filter sign bit oprnd 2
        tb.add(self._builder.gen_and(result, imm4, tmp2))   # filter sign bit result
        tb.add(self._builder.gen_xor(tmp0, tmp1, tmp3))     # sign bit oprnd0 ^ sign bit oprnd1
        tb.add(self._builder.gen_xor(tmp3, imm1, tmp4))     # sign bit oprnd0 ^ sign bit oprnd1 ^ 1
        tb.add(self._builder.gen_xor(tmp0, tmp2, tmp5))     # sign bit oprnd0 ^ sign bit result
        tb.add(self._builder.gen_and(tmp4, tmp5, tmp6))     # (sign bit oprnd0 ^ sign bit oprnd1 ^ 1) & (sign bit oprnd0 ^ sign bit result)
        tb.add(self._builder.gen_bsh(tmp6, imm3, of))

    def _update_cf(self, tb, oprnd0, oprnd1, result):
        cf = self._flags["cf"]

        imm0 = tb.immediate(2**oprnd0.size, result.size)
        imm1 = tb.immediate(-oprnd0.size, result.size)

        tmp0 = tb.temporal(result.size)

        tb.add(self._builder.gen_and(result, imm0, tmp0))   # filter carry bit
        tb.add(self._builder.gen_bsh(tmp0, imm1, cf))

    def _update_zf(self, tb, oprnd0, oprnd1, result):
        zf = self._flags["zf"]

        imm0 = tb.immediate((2**oprnd0.size)-1, result.size)

        tmp0 = tb.temporal(oprnd0.size)

        tb.add(self._builder.gen_and(result, imm0, tmp0))  # filter low part of result
        tb.add(self._builder.gen_bisz(tmp0, zf))

    def _undefine_flag(self, tb, flag):
        # NOTE: In every test I've made, each time a flag is leave
        # undefined it is always set to 0.

        imm = tb.immediate(0, flag.size)

        tb.add(self._builder.gen_str(imm, flag))

    def _clear_flag(self, tb, flag):
        imm = tb.immediate(0, flag.size)

        tb.add(self._builder.gen_str(imm, flag))

    def _set_flag(self, tb, flag):
        imm = tb.immediate(1, flag.size)

        tb.add(self._builder.gen_str(imm, flag))

# "Data Transfer Instructions"
# ============================================================================ #
    def _translate_mov(self, tb, instruction):
        # Flags Affected
        # None.

        oprnd1 = tb.read(instruction.operands[1])

        tb.write(instruction.operands[0], oprnd1)
