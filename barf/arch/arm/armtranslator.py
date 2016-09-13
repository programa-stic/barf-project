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

import logging

from barf.arch import ARCH_ARM_MODE_ARM
from barf.arch import ARCH_ARM_MODE_THUMB
from barf.arch.arm.armbase import ARM_COND_CODE_AL
from barf.arch.arm.armbase import ARM_COND_CODE_CC
from barf.arch.arm.armbase import ARM_COND_CODE_CS
from barf.arch.arm.armbase import ARM_COND_CODE_EQ
from barf.arch.arm.armbase import ARM_COND_CODE_GE
from barf.arch.arm.armbase import ARM_COND_CODE_GT
from barf.arch.arm.armbase import ARM_COND_CODE_HI
from barf.arch.arm.armbase import ARM_COND_CODE_HS
from barf.arch.arm.armbase import ARM_COND_CODE_LE
from barf.arch.arm.armbase import ARM_COND_CODE_LO
from barf.arch.arm.armbase import ARM_COND_CODE_LS
from barf.arch.arm.armbase import ARM_COND_CODE_LT
from barf.arch.arm.armbase import ARM_COND_CODE_MI
from barf.arch.arm.armbase import ARM_COND_CODE_NE
from barf.arch.arm.armbase import ARM_COND_CODE_PL
from barf.arch.arm.armbase import ARM_COND_CODE_VC
from barf.arch.arm.armbase import ARM_COND_CODE_VS
from barf.arch.arm.armbase import ARM_LDM_STM_DA
from barf.arch.arm.armbase import ARM_LDM_STM_DB
from barf.arch.arm.armbase import ARM_LDM_STM_FD
from barf.arch.arm.armbase import ARM_LDM_STM_IA
from barf.arch.arm.armbase import ARM_LDM_STM_IB
from barf.arch.arm.armbase import ARM_MEMORY_INDEX_OFFSET
from barf.arch.arm.armbase import ARM_MEMORY_INDEX_POST
from barf.arch.arm.armbase import ARM_MEMORY_INDEX_PRE
from barf.arch.arm.armbase import ArmArchitectureInformation
from barf.arch.arm.armbase import ArmImmediateOperand
from barf.arch.arm.armbase import ArmMemoryOperand
from barf.arch.arm.armbase import ArmRegisterListOperand
from barf.arch.arm.armbase import ArmRegisterOperand
from barf.arch.arm.armbase import ArmShiftedRegisterOperand
from barf.arch.arm.armbase import ldm_stack_am_to_non_stack_am
from barf.arch.arm.armbase import stm_stack_am_to_non_stack_am
from barf.arch.translator import Translator
from barf.arch.translator import TranslationBuilder
from barf.core.reil import check_operands_size
from barf.core.reil import ReilImmediateOperand
from barf.core.reil import ReilInstructionBuilder
from barf.core.reil import ReilMnemonic
from barf.core.reil import ReilRegisterOperand
from barf.utils.utils import VariableNamer

FULL_TRANSLATION = 0
LITE_TRANSLATION = 1

logger = logging.getLogger(__name__)


class ArmTranslationBuilder(TranslationBuilder):

    def __init__(self, ir_name_generator, architecture_mode):
        super(ArmTranslationBuilder, self).__init__(ir_name_generator, architecture_mode)

        self._arch_info = ArmArchitectureInformation(architecture_mode)

    def read(self, arm_operand):

        if isinstance(arm_operand, ArmImmediateOperand):

            reil_operand = ReilImmediateOperand(arm_operand.immediate, arm_operand.size)

        elif isinstance(arm_operand, ArmRegisterOperand):

            reil_operand = ReilRegisterOperand(arm_operand.name, arm_operand.size)

        elif isinstance(arm_operand, ArmShiftedRegisterOperand):

            reil_operand = self._compute_shifted_register(arm_operand)

        elif isinstance(arm_operand, ArmMemoryOperand):

            addr = self._compute_memory_address(arm_operand)

            reil_operand = self.temporal(arm_operand.size)

            self.add(self._builder.gen_ldm(addr, reil_operand))

        elif isinstance(arm_operand, ArmRegisterListOperand):

            reil_operand = self._compute_register_list(arm_operand)

        else:
            raise NotImplementedError("Instruction Not Implemented: Unknown operand for read operation.")

        return reil_operand

    def write(self, arm_operand, value):

        if isinstance(arm_operand, ArmRegisterOperand):

            reil_operand = ReilRegisterOperand(arm_operand.name, arm_operand.size)

            self.add(self._builder.gen_str(value, reil_operand))

        elif isinstance(arm_operand, ArmMemoryOperand):

            addr = self._compute_memory_address(arm_operand)

            self.add(self._builder.gen_stm(value, addr))

        else:
            raise NotImplementedError("Instruction Not Implemented: Unknown operand for write operation.")

    def _compute_shifted_register(self, sh_op):

        base = ReilRegisterOperand(sh_op.base_reg.name, sh_op.size)

        if sh_op.shift_amount:
            ret = self.temporal(sh_op.size)

            if isinstance(sh_op.shift_amount, ArmImmediateOperand):
                sh_am = ReilImmediateOperand(sh_op.shift_amount.immediate, sh_op.size)
            elif isinstance(sh_op.shift_amount, ArmRegisterOperand):
                sh_am = ReilRegisterOperand(sh_op.shift_amount.name, sh_op.shift_amount.size)
            else:
                raise NotImplementedError("Instruction Not Implemented: Unknown shift amount type.")

            if sh_op.shift_type == 'lsl':
                if isinstance(sh_am, ReilImmediateOperand):
                    self.add(self._builder.gen_bsh(base, sh_am, ret))
                else:
                    sh_am_greater_32_label = self.label('sh_am_greater_32_label')
                    sh_am_end_label = self.label('sh_am_end_label')

                    sh_am_7_0 = self._and_regs(sh_am, self.immediate(0xFF, sh_am.size))

                    self.add(self._builder.gen_jcc(self._greater_than_or_equal(sh_am_7_0, self.immediate(33, sh_am_7_0.size)),
                                                 sh_am_greater_32_label))

                    # Shift < 32 => shited_register = base lsl sh_am
                    self.add(self._builder.gen_bsh(base, sh_am_7_0, ret))
                    self._jump_to(sh_am_end_label)

                    # Shift >= 32 => shited_register = 0
                    self.add(sh_am_greater_32_label)
                    self.add(self._builder.gen_str(self.immediate(0x0, ret.size), ret))

                    self.add(sh_am_end_label)
            else:
                # TODO: Implement other shift types
                raise NotImplementedError("Instruction Not Implemented: Shift type.")
        else:
            ret = base

        return ret

    def _compute_memory_address(self, mem_operand):
        """Return operand memory access translation.
        """
        base = ReilRegisterOperand(mem_operand.base_reg.name, mem_operand.size)

        if mem_operand.displacement:
            address = self.temporal(mem_operand.size)

            if isinstance(mem_operand.displacement, ArmRegisterOperand):
                disp = ReilRegisterOperand(mem_operand.displacement.name, mem_operand.size)
            elif isinstance(mem_operand.displacement, ArmImmediateOperand):
                disp = ReilImmediateOperand(mem_operand.displacement.immediate, mem_operand.size)
            elif isinstance(mem_operand.displacement, ArmShiftedRegisterOperand):
                disp = self._compute_shifted_register(mem_operand.displacement)
            else:
                raise Exception("_compute_memory_address: displacement type unknown")

            if mem_operand.index_type == ARM_MEMORY_INDEX_PRE:
                if mem_operand.disp_minus:
                    self.add(self._builder.gen_sub(base, disp, address))
                else:
                    self.add(self._builder.gen_add(base, disp, address))
                self.add(self._builder.gen_str(address, base))
            elif mem_operand.index_type == ARM_MEMORY_INDEX_OFFSET:
                if mem_operand.disp_minus:
                    self.add(self._builder.gen_sub(base, disp, address))
                else:
                    self.add(self._builder.gen_add(base, disp, address))
            elif mem_operand.index_type == ARM_MEMORY_INDEX_POST:
                self.add(self._builder.gen_str(base, address))
                tmp = self.temporal(base.size)
                if mem_operand.disp_minus:
                    self.add(self._builder.gen_sub(base, disp, tmp))
                else:
                    self.add(self._builder.gen_add(base, disp, tmp))
                self.add(self._builder.gen_str(tmp, base))
            else:
                raise Exception("_compute_memory_address: indexing type unknown")

        else:
            address = base

        return address

    def _compute_register_list(self, operand):
        """Return operand register list.
        """

        ret = []
        for reg_range in operand.reg_list:
            if len(reg_range) == 1:
                ret.append(ReilRegisterOperand(reg_range[0].name, reg_range[0].size))
            else:
                reg_num = int(reg_range[0].name[1:]) # Assuming the register is named with one letter + number
                reg_end = int(reg_range[1].name[1:])
                if reg_num > reg_end:
                    raise NotImplementedError("Instruction Not Implemented: Invalid register range.")
                while reg_num <= reg_end:
                    ret.append(ReilRegisterOperand(reg_range[0].name[0] + str(reg_num), reg_range[0].size))
                    reg_num = reg_num + 1

        return ret


class ArmTranslator(Translator):

    """ARM to IR Translator."""

    def __init__(self, architecture_mode=ARCH_ARM_MODE_THUMB, translation_mode=FULL_TRANSLATION):

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
            "nf" : ReilRegisterOperand("nf", 1),
            "zf" : ReilRegisterOperand("zf", 1),
            "cf" : ReilRegisterOperand("cf", 1),
            "vf" : ReilRegisterOperand("vf", 1),
        }

        if self._arch_mode in [ARCH_ARM_MODE_ARM, ARCH_ARM_MODE_THUMB]:
            self._sp = ReilRegisterOperand("r13", 32) # TODO: Implement alias
            self._pc = ReilRegisterOperand("r15", 32)
            self._lr = ReilRegisterOperand("r14", 32)

            self._ws = ReilImmediateOperand(4, 32) # word size

        # TODO: Remove this code?
        # elif self._arch_mode == ARCH_ARM_MODE_64:
        #     self._sp = ReilRegisterOperand("r13", 64)
        #     self._pc = ReilRegisterOperand("r15", 64)
        #     self._lr = ReilRegisterOperand("r14", 64)

        #     self._ws = ReilImmediateOperand(8, 64) # word size

    def translate(self, instruction):
        """Return IR representation of an instruction.
        """
        try:
            trans_instrs = self._translate(instruction)
        except NotImplementedError as e:
            unkn_instr = self._builder.gen_unkn()
            unkn_instr.address = instruction.address << 8 | (0x0 & 0xff)
            trans_instrs = [unkn_instr]

            self._log_not_supported_instruction(instruction, str(e))
        except Exception:
            self._log_translation_exception(instruction)

            raise

        # Some sanity check....
        for instr in trans_instrs:
            try:
                check_operands_size(instr, self._arch_info.architecture_size)
            except:
                logger.error(
                    "Invalid operand size: %s (%s)",
                    instr,
                    instruction
                )

                raise

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
        tb = ArmTranslationBuilder(self._ir_name_generator, self._arch_mode)

        # TODO: Improve this.
        if instruction.mnemonic in ["b", "bl", "bx", "blx", "bne", "beq", "bpl",
                                    "ble", "bcs", "bhs", "blt", "bge", "bhi",
                                    "blo", "bls"]:
            if instruction.condition_code == None:
                instruction.condition_code = ARM_COND_CODE_AL  # TODO: unify translations
            translator_fn(tb, instruction)
        else:
            # Pre-processing: evaluate flags
            if instruction.condition_code != None:
                self._evaluate_condition_code(tb, instruction)

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

    def _log_not_supported_instruction(self, instruction, reason = "unknown"):
        bytes_str = " ".join("%02x" % ord(b) for b in instruction.bytes)

        logger.info(
            "Instruction not supported: %s (%s [%s]). Reason: %s",
            instruction.mnemonic,
            instruction,
            bytes_str,
            reason
        )

    def _log_translation_exception(self, instruction):
        bytes_str = " ".join("%02x" % ord(b) for b in instruction.bytes)

        logger.error(
            "Failed to translate arm to REIL: %s (%s)",
            instruction,
            bytes_str,
            exc_info=True
        )

    def _not_implemented(self, tb, instruction):
        raise NotImplementedError("Instruction Not Implemented")

# Translators
# ============================================================================ #
# ============================================================================ #

# "Flags"
# ============================================================================ #
    def _update_nf(self, tb, oprnd0, oprnd1, result):
        sign = tb._extract_bit(result, oprnd0.size - 1)
        tb.add(self._builder.gen_str(sign, self._flags["nf"]))

    def _carry_from_uf(self, tb, oprnd0, oprnd1, result):
        assert (result.size == oprnd0.size * 2)

        carry = tb._extract_bit(result, oprnd0.size)
        tb.add(self._builder.gen_str(carry, self._flags["cf"]))

    def _borrow_from_uf(self, tb, oprnd0, oprnd1, result):
        # BorrowFrom as defined in the ARM Reference Manual has the same implementation as CarryFrom
        self._carry_from_uf(tb, oprnd0, oprnd1, result)

    def _overflow_from_add_uf(self, tb, oprnd0, oprnd1, result):
        op1_sign = tb._extract_bit(oprnd0, oprnd0.size - 1)
        op2_sign = tb._extract_bit(oprnd1, oprnd0.size - 1)
        res_sign = tb._extract_bit(result, oprnd0.size - 1)

        overflow = tb._and_regs(tb._equal_regs(op1_sign, op2_sign), tb._unequal_regs(op1_sign, res_sign))
        tb.add(self._builder.gen_str(overflow, self._flags["vf"]))

    # Evaluate overflow and update the flag
    def _overflow_from_sub_uf(self, tb, oprnd0, oprnd1, result):
        tb.add(self._builder.gen_str(tb._overflow_from_sub(oprnd0, oprnd1, result), self._flags["vf"]))

    def _update_zf(self, tb, oprnd0, oprnd1, result):
        zf = self._flags["zf"]

        imm0 = tb.immediate((2**oprnd0.size)-1, result.size)

        tmp0 = tb.temporal(oprnd0.size)

        tb.add(self._builder.gen_and(result, imm0, tmp0))  # filter low part of result
        tb.add(self._builder.gen_bisz(tmp0, zf))

    def _carry_out(self, tb, carry_operand, oprnd0, oprnd1, result):
        if isinstance(carry_operand, ArmImmediateOperand):
            return
        elif isinstance(carry_operand, ArmRegisterOperand):
            return
        elif isinstance(carry_operand, ArmShiftedRegisterOperand):
            base = ReilRegisterOperand(carry_operand.base_reg.name, carry_operand.size)
            shift_type = carry_operand.shift_type
            shift_amount = carry_operand.shift_amount

            if (shift_type == 'lsl'):

                if isinstance(shift_amount, ArmImmediateOperand):
                    if shift_amount.immediate == 0:
                        return
                    else:
                        # carry_out = Rm[32 - shift_imm]
                        shift_carry_out = tb._extract_bit(base, 32 - shift_amount.immediate)

                elif isinstance(shift_amount, ArmRegisterOperand):
                    # Rs: register with shift amount
                    # if Rs[7:0] == 0 then
                    #     carry_out = C Flag
                    # else if Rs[7:0] <= 32 then
                    #     carry_out = Rm[32 - Rs[7:0]]
                    # else /* Rs[7:0] > 32 */
                    #     carry_out = 0

                    shift_carry_out = tb.temporal(1)
                    tb.add(self._builder.gen_str(self._flags["cf"], shift_carry_out))
                    rs = ReilRegisterOperand(shift_amount.name, shift_amount.size)
                    rs_7_0 = tb._and_regs(rs, tb.immediate(0xFF, rs.size))

                    end_label = tb.label('end_label')
                    rs_greater_32_label = tb.label('rs_greater_32_label')

                    # if Rs[7:0] == 0 then
                    #     carry_out = C Flag
                    tb._jump_if_zero(rs_7_0, end_label) # shift_carry_out already has the C flag set, so do nothing

                    tb.add(self._builder.gen_jcc(tb._greater_than_or_equal(rs_7_0, tb.immediate(33, rs_7_0.size)),
                                                 rs_greater_32_label))

                    # Rs > 0 and Rs <= 32
                    #     carry_out = Rm[32 - Rs[7:0]]
                    extract_bit_number = tb.temporal(rs_7_0.size)
                    tb.add(self._builder.gen_sub(tb.immediate(32, rs_7_0.size), rs_7_0, extract_bit_number))
                    tb.add(self._builder.gen_str(tb._extract_bit_with_register(base, extract_bit_number),
                                                 shift_carry_out))
                    tb._jump_to(end_label)

                    # else /* Rs[7:0] > 32 */
                    #     carry_out = 0
                    tb.add(rs_greater_32_label)
                    tb.add(self._builder.gen_str(tb.immediate(0, 1), shift_carry_out))
#                     tb._jump_to(end_label)

                    tb.add(end_label)

                else:
                    raise Exception("carry_out: Unknown shift amount type.")

            else:
                # TODO: Implement other shift types
                raise NotImplementedError("Instruction Not Implemented: carry_out: shift type " + carry_operand.shift_type)

        else:
            raise Exception("carry_out: Unknown operand type.")

        tb.add(self._builder.gen_str(shift_carry_out, self._flags["cf"]))

    def _update_flags_data_proc_add(self, tb, oprnd0, oprnd1, result):
        self._update_zf(tb, oprnd0, oprnd1, result)
        self._update_nf(tb, oprnd0, oprnd1, result)
        self._carry_from_uf(tb, oprnd0, oprnd1, result)
        self._overflow_from_add_uf(tb, oprnd0, oprnd1, result)

    def _update_flags_data_proc_sub(self, tb, oprnd0, oprnd1, result):
        self._update_zf(tb, oprnd0, oprnd1, result)
        self._update_nf(tb, oprnd0, oprnd1, result)
        self._borrow_from_uf(tb, oprnd0, oprnd1, result)
        # C Flag = NOT BorrowFrom (to be used by subsequent instructions like SBC and RSC)
        tb.add(self._builder.gen_str(tb._negate_reg(self._flags["cf"]), self._flags["cf"]))
        self._overflow_from_sub_uf(tb, oprnd0, oprnd1, result)

    def _update_flags_data_proc_other(self, tb, second_operand, oprnd0, oprnd1, result):
        self._update_zf(tb, oprnd0, oprnd1, result)
        self._update_nf(tb, oprnd0, oprnd1, result)
        self._carry_out(tb, second_operand, oprnd0, oprnd1, result)
        # Overflow Flag (V) unaffected

    def _update_flags_other(self, tb, oprnd0, oprnd1, result):
        self._update_zf(tb, oprnd0, oprnd1, result)
        self._update_nf(tb, oprnd0, oprnd1, result)
        # Carry Flag (C) unaffected
        # Overflow Flag (V) unaffected

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

    def _evaluate_eq(self, tb):
        # EQ: Z set
        return self._flags["zf"]

    def _evaluate_ne(self, tb):
        # NE: Z clear
        return tb._negate_reg(self._flags["zf"])

    def _evaluate_cs(self, tb):
        # CS: C set
        return self._flags["cf"]

    def _evaluate_cc(self, tb):
        # CC: C clear
        return tb._negate_reg(self._flags["cf"])

    def _evaluate_mi(self, tb):
        # MI: N set
        return self._flags["nf"]

    def _evaluate_pl(self, tb):
        # PL: N clear
        return tb._negate_reg(self._flags["nf"])

    def _evaluate_vs(self, tb):
        # VS: V set
        return self._flags["vf"]

    def _evaluate_vc(self, tb):
        # VC: V clear
        return tb._negate_reg(self._flags["vf"])

    def _evaluate_hi(self, tb):
        # HI: C set and Z clear
        return tb._and_regs(self._flags["cf"], tb._negate_reg(self._flags["zf"]))

    def _evaluate_ls(self, tb):
        # LS: C clear or Z set
        return tb._or_regs(tb._negate_reg(self._flags["cf"]), self._flags["zf"])

    def _evaluate_ge(self, tb):
        # GE: N == V
        return tb._equal_regs(self._flags["nf"], self._flags["vf"])

    def _evaluate_lt(self, tb):
        # LT: N != V
        return tb._negate_reg(self._evaluate_ge(tb))

    def _evaluate_gt(self, tb):
        # GT: (Z == 0) and (N == V)
        return tb._and_regs(tb._negate_reg(self._flags["zf"]), self._evaluate_ge(tb))

    def _evaluate_le(self, tb):
        # LE: (Z == 1) or (N != V)
        return tb._or_regs(self._flags["zf"], self._evaluate_lt(tb))

    def _evaluate_condition_code(self, tb, instruction):
        if instruction.condition_code == ARM_COND_CODE_AL:
            return

        eval_cc_fn = {
            ARM_COND_CODE_EQ : self._evaluate_eq,
            ARM_COND_CODE_NE : self._evaluate_ne,
            ARM_COND_CODE_CS : self._evaluate_cs,
            ARM_COND_CODE_HS : self._evaluate_cs,
            ARM_COND_CODE_CC : self._evaluate_cc,
            ARM_COND_CODE_LO : self._evaluate_cc,
            ARM_COND_CODE_MI : self._evaluate_mi,
            ARM_COND_CODE_PL : self._evaluate_pl,
            ARM_COND_CODE_VS : self._evaluate_vs,
            ARM_COND_CODE_VC : self._evaluate_vc,
            ARM_COND_CODE_HI : self._evaluate_hi,
            ARM_COND_CODE_LS : self._evaluate_ls,
            ARM_COND_CODE_GE : self._evaluate_ge,
            ARM_COND_CODE_LT : self._evaluate_lt,
            ARM_COND_CODE_GT : self._evaluate_gt,
            ARM_COND_CODE_LE : self._evaluate_le,
        }


        neg_cond = tb._negate_reg(eval_cc_fn[instruction.condition_code](tb))

        end_addr = ReilImmediateOperand((instruction.address + instruction.size) << 8, self._arch_info.address_size + 8)

        tb.add(self._builder.gen_jcc(neg_cond, end_addr))

        return


# "Data-processing Instructions"
# ============================================================================ #
    def _translate_mov(self, tb, instruction):

        oprnd1 = tb.read(instruction.operands[1])

        tb.write(instruction.operands[0], oprnd1)

        if instruction.update_flags:
            self._update_flags_data_proc_other(tb, instruction.operands[1], oprnd1, None, oprnd1)

    def _translate_mvn(self, tb, instruction):

        oprnd1 = tb.read(instruction.operands[1])

        tb.write(instruction.operands[0], tb._negate_reg(oprnd1))

        if instruction.update_flags:
            self._update_flags_data_proc_other(tb, instruction.operands[1], oprnd1, None, tb._negate_reg(oprnd1))

    def _translate_movw(self, tb, instruction):

        reil_operand = ReilRegisterOperand(instruction.operands[0].name, instruction.operands[0].size)
        word_mask = ReilImmediateOperand(0x0000FFFF, reil_operand.size)
        and_temp = tb.temporal(reil_operand.size)

        oprnd1 = tb.read(instruction.operands[1])

        tb.write(instruction.operands[0], oprnd1)

        tb.add(self._builder.gen_and(reil_operand, word_mask, and_temp))  # filter bits [7:0] part of result

        tb.add(self._builder.gen_str(and_temp, reil_operand))

        # It doesn't update flags

    def _translate_and(self, tb, instruction):
        oprnd1 = tb.read(instruction.operands[1])
        oprnd2 = tb.read(instruction.operands[2])

        result = tb.temporal(oprnd1.size)

        tb.add(self._builder.gen_and(oprnd1, oprnd2, result))

        tb.write(instruction.operands[0], result)

        if instruction.update_flags:
            self._update_flags_data_proc_other(tb, instruction.operands[2], oprnd1, oprnd2, result)

    def _translate_orr(self, tb, instruction):
        oprnd1 = tb.read(instruction.operands[1])
        oprnd2 = tb.read(instruction.operands[2])

        result = tb.temporal(oprnd1.size)

        tb.add(self._builder.gen_or(oprnd1, oprnd2, result))

        tb.write(instruction.operands[0], result)

        if instruction.update_flags:
            self._update_flags_data_proc_other(tb, instruction.operands[2], oprnd1, oprnd2, result)

    def _translate_eor(self, tb, instruction):
        oprnd1 = tb.read(instruction.operands[1])
        oprnd2 = tb.read(instruction.operands[2])

        result = tb.temporal(oprnd1.size)

        tb.add(self._builder.gen_xor(oprnd1, oprnd2, result))

        tb.write(instruction.operands[0], result)

        if instruction.update_flags:
            self._update_flags_data_proc_other(tb, instruction.operands[2], oprnd1, oprnd2, result)

    def _translate_add(self, tb, instruction):
        oprnd1 = tb.read(instruction.operands[1])
        oprnd2 = tb.read(instruction.operands[2])

        result = tb.temporal(oprnd1.size * 2)

        tb.add(self._builder.gen_add(oprnd1, oprnd2, result))

        tb.write(instruction.operands[0], result)

        if instruction.update_flags:
            self._update_flags_data_proc_add(tb, oprnd1, oprnd2, result)

    def _translate_sub(self, tb, instruction):
        oprnd1 = tb.read(instruction.operands[1])
        oprnd2 = tb.read(instruction.operands[2])

        result = tb.temporal(oprnd1.size * 2)

        tb.add(self._builder.gen_sub(oprnd1, oprnd2, result))

        tb.write(instruction.operands[0], result)

        if instruction.update_flags:
            self._update_flags_data_proc_sub(tb, oprnd1, oprnd2, result)

    def _translate_rsb(self, tb, instruction):
        instruction.operands[1], instruction.operands[2] = instruction.operands[2], instruction.operands[1]

        self._translate_sub(tb, instruction)

    def _translate_mul(self, tb, instruction):
        oprnd1 = tb.read(instruction.operands[1])
        oprnd2 = tb.read(instruction.operands[2])

        result = tb.temporal(oprnd1.size * 2)

        tb.add(self._builder.gen_mul(oprnd1, oprnd2, result))

        tb.write(instruction.operands[0], result)

        if instruction.update_flags:
            self._update_zf(tb, oprnd1, oprnd2, result)
            self._update_nf(tb, oprnd1, oprnd2, result)

    def _translate_cmn(self, tb, instruction):
        oprnd1 = tb.read(instruction.operands[0])
        oprnd2 = tb.read(instruction.operands[1])

        result = tb.temporal(oprnd1.size * 2)

        tb.add(self._builder.gen_add(oprnd1, oprnd2, result))

        self._update_flags_data_proc_add(tb, oprnd1, oprnd2, result) # S = 1 (implied in the instruction)

    def _translate_cmp(self, tb, instruction):
        oprnd1 = tb.read(instruction.operands[0])
        oprnd2 = tb.read(instruction.operands[1])

        result = tb.temporal(oprnd1.size * 2)

        tb.add(self._builder.gen_sub(oprnd1, oprnd2, result))

        self._update_flags_data_proc_sub(tb, oprnd1, oprnd2, result) # S = 1 (implied in the instruction)

    def _translate_cbz(self, tb, instruction):
        oprnd1 = tb.read(instruction.operands[0])
        arm_operand = instruction.operands[1]

        if isinstance(arm_operand, ArmImmediateOperand):
            target = ReilImmediateOperand(arm_operand.immediate << 8, self._pc.size + 8)
        elif isinstance(arm_operand, ArmRegisterOperand):
            target = ReilRegisterOperand(arm_operand.name, arm_operand.size)
            target = tb._and_regs(target, ReilImmediateOperand(0xFFFFFFFE, target.size))

            tmp0 = tb.temporal(target.size + 8)
            tmp1 = tb.temporal(target.size + 8)

            tb.add(self._builder.gen_str(target, tmp0))
            tb.add(self._builder.gen_bsh(tmp0, ReilImmediateOperand(8, target.size + 8), tmp1))

            target = tmp1
        else:
            raise Exception()

        tb._jump_if_zero(oprnd1, target)

    def _translate_cbnz(self, tb, instruction):
        oprnd0 = tb.read(instruction.operands[0])
        arm_operand = instruction.operands[1]

        if isinstance(arm_operand, ArmImmediateOperand):
            target = ReilImmediateOperand(arm_operand.immediate << 8, self._pc.size + 8)
        elif isinstance(arm_operand, ArmRegisterOperand):
            target = ReilRegisterOperand(arm_operand.name, arm_operand.size)
            target = tb._and_regs(target, ReilImmediateOperand(0xFFFFFFFE, target.size))

            tmp0 = tb.temporal(target.size + 8)
            tmp1 = tb.temporal(target.size + 8)

            tb.add(self._builder.gen_str(target, tmp0))
            tb.add(self._builder.gen_bsh(tmp0, ReilImmediateOperand(8, target.size + 8), tmp1))

            target = tmp1
        else:
            raise Exception()

        neg_oprnd = tb._negate_reg(oprnd0)

        tb._jump_if_zero(neg_oprnd, target)

    def _translate_lsl(self, tb, instruction):
        # LSL (register)
        if len(instruction.operands) == 3 and isinstance(instruction.operands[1], ArmRegisterOperand):
            sh_op = ArmShiftedRegisterOperand(instruction.operands[1], "lsl", instruction.operands[2], instruction.operands[1].size)
            disp = tb._compute_shifted_register(sh_op)
            tb.write(instruction.operands[0], disp)
            return

        if len(instruction.operands) == 2 and isinstance(instruction.operands[1], ArmShiftedRegisterOperand):
            # Capstone is incorrectly packing <Rm>, #<imm5> into a shifted register, unpack it
            instruction.operands.append(instruction.operands[1]._shift_amount)
            instruction.operands[1] = instruction.operands[1]._base_reg

        oprnd1 = tb.read(instruction.operands[1])
        oprnd2 = tb.read(instruction.operands[2])
        result = tb.temporal(oprnd1.size)

        tb.add(self._builder.gen_bsh(oprnd1, oprnd2, result))
        tb.write(instruction.operands[0], result)

        if instruction.update_flags:
            self._update_zf(tb, oprnd1, oprnd2, result)
            self._update_nf(tb, oprnd1, oprnd2, result)
            # TODO: Encapsulate this new kind of flag update (different from the data proc instructions like add, and, orr)
            if oprnd2.immediate == 0:
                return
            else:
                # carry_out = Rm[32 - shift_imm]
                shift_carry_out = tb._extract_bit(oprnd1, 32 - oprnd2.immediate)
                tb.add(self._builder.gen_str(shift_carry_out, self._flags["cf"]))


# "Load/store word and unsigned byte Instructions"
# ============================================================================ #
    def _translate_ldr(self, tb, instruction):

        oprnd1 = tb.read(instruction.operands[1])

        tb.write(instruction.operands[0], oprnd1)

    def _translate_str(self, tb, instruction):

        oprnd0 = tb.read(instruction.operands[0])

        tb.write(instruction.operands[1], oprnd0)

    # TODO: Check if the byte suffix ('b') should be coded as extra information
    # and removed from the mnemonic (handling all ldr/str translations in only
    # two functions).
    def _translate_ldrb(self, tb, instruction):

        op0_reil = ReilRegisterOperand(instruction.operands[0].name, instruction.operands[0].size)
        addr_reg = tb._compute_memory_address(instruction.operands[1])
        byte_reg = tb.temporal(8)

        tb.add(tb._builder.gen_ldm(addr_reg, byte_reg))

        tb.add(self._builder.gen_str(byte_reg, op0_reil))

    def _translate_strb(self, tb, instruction):

        reil_operand = ReilRegisterOperand(instruction.operands[0].name, instruction.operands[0].size)
        byte_reg = tb.temporal(8)

        tb.add(self._builder.gen_str(reil_operand, byte_reg))  # filter bits [7:0] part of result

        addr = tb._compute_memory_address(instruction.operands[1])

        tb.add(self._builder.gen_stm(byte_reg, addr))

    # TODO: Generalize LDR to handle byte and half word in a single function
    def _translate_ldrh(self, tb, instruction):

        op0_reil = ReilRegisterOperand(instruction.operands[0].name, instruction.operands[0].size)
        addr_reg = tb._compute_memory_address(instruction.operands[1])
        byte_reg = tb.temporal(16)

        tb.add(tb._builder.gen_ldm(addr_reg, byte_reg))

        tb.add(self._builder.gen_str(byte_reg, op0_reil))

    def _translate_strh(self, tb, instruction):

        reil_operand = ReilRegisterOperand(instruction.operands[0].name, instruction.operands[0].size)
        half_word_reg = tb.temporal(16)

        tb.add(self._builder.gen_str(reil_operand, half_word_reg))  # filter bits [15:0] part of result

        addr = tb._compute_memory_address(instruction.operands[1])

        tb.add(self._builder.gen_stm(half_word_reg, addr))

    def _translate_ldrd(self, tb, instruction):

        if len(instruction.operands) > 2: # Rd2 has been specified (UAL syntax)
            addr_reg = tb._compute_memory_address(instruction.operands[2])
        else:
            addr_reg = tb._compute_memory_address(instruction.operands[1])

        reil_operand = ReilRegisterOperand(instruction.operands[0].name, instruction.operands[0].size)

        tb.add(tb._builder.gen_ldm(addr_reg, reil_operand))

        addr_reg = tb._add_to_reg(addr_reg, ReilImmediateOperand(4, reil_operand.size))

        if len(instruction.operands) > 2: # Rd2 has been specified (UAL syntax)
            reil_operand = ReilRegisterOperand(instruction.operands[1].name, instruction.operands[0].size)
        else:
            # TODO: Assuming the register is written in its number format
            # (no alias like lr or pc).
            reil_operand = ReilRegisterOperand('r' + str(int(reil_operand.name[1:]) + 1), reil_operand.size)

        tb.add(tb._builder.gen_ldm(addr_reg, reil_operand))

    def _translate_strd(self, tb, instruction):

        if len(instruction.operands) > 2: # Rd2 has been specified (UAL syntax)
            addr_reg = tb._compute_memory_address(instruction.operands[2])
        else:
            addr_reg = tb._compute_memory_address(instruction.operands[1])

        reil_operand = ReilRegisterOperand(instruction.operands[0].name, instruction.operands[0].size)

        tb.add(tb._builder.gen_stm(reil_operand, addr_reg))

        addr_reg = tb._add_to_reg(addr_reg, ReilImmediateOperand(4, reil_operand.size))

        if len(instruction.operands) > 2: # Rd2 has been specified (UAL syntax)
            reil_operand = ReilRegisterOperand(instruction.operands[1].name, instruction.operands[0].size)
        else:
            # TODO: Assuming the register is written in its number format
            # (no alias like lr or pc).
            reil_operand = ReilRegisterOperand('r' + str(int(reil_operand.name[1:]) + 1), reil_operand.size)

        tb.add(tb._builder.gen_stm(reil_operand, addr_reg))


# "Load/store multiple Instructions"
# ============================================================================ #
    def _translate_ldm(self, tb, instruction):
        self._translate_ldm_stm(tb, instruction, True)

    def _translate_stm(self, tb, instruction):
        self._translate_ldm_stm(tb, instruction, False)

    def _translate_ldm_stm(self, tb, instruction, load=True):
        # LDM and STM have exactly the same logic except one loads and the
        # other stores It is assumed that the disassembler (for example
        # Capstone) writes the register list in increasing order

        base = tb.read(instruction.operands[0])
        reg_list = tb.read(instruction.operands[1])

        if instruction.ldm_stm_addr_mode == None:
            instruction.ldm_stm_addr_mode = ARM_LDM_STM_IA # default mode for load and store

        if load:
            load_store_fn = self._load_value
            # Convert stack addressing modes to non-stack addressing modes
            if instruction.ldm_stm_addr_mode in ldm_stack_am_to_non_stack_am:
                instruction.ldm_stm_addr_mode = ldm_stack_am_to_non_stack_am[instruction.ldm_stm_addr_mode]
        else: # Store
            load_store_fn = self._store_value
            if instruction.ldm_stm_addr_mode in stm_stack_am_to_non_stack_am:
                instruction.ldm_stm_addr_mode = stm_stack_am_to_non_stack_am[instruction.ldm_stm_addr_mode]

        pointer = tb.temporal(base.size)
        tb.add(self._builder.gen_str(base, pointer))
        reg_list_size_bytes = ReilImmediateOperand(self._ws.immediate * len(reg_list), base.size)

        if instruction.ldm_stm_addr_mode == ARM_LDM_STM_IA:
            for reg in reg_list:
                load_store_fn(tb, pointer, reg)
                pointer = tb._add_to_reg(pointer, self._ws)
        elif  instruction.ldm_stm_addr_mode == ARM_LDM_STM_IB:
            for reg in reg_list:
                pointer = tb._add_to_reg(pointer, self._ws)
                load_store_fn(tb, pointer, reg)
        elif  instruction.ldm_stm_addr_mode == ARM_LDM_STM_DA:
            reg_list.reverse() # Assuming the registry list was in increasing registry number
            for reg in reg_list:
                load_store_fn(tb, pointer, reg)
                pointer = tb._sub_to_reg(pointer, self._ws)
        elif  instruction.ldm_stm_addr_mode == ARM_LDM_STM_DB:
            reg_list.reverse()
            for reg in reg_list:
                pointer = tb._sub_to_reg(pointer, self._ws)
                load_store_fn(tb, pointer, reg)
        else:
            raise Exception("Unknown addressing mode.")

        # Write-back
        if instruction.operands[0].wb:
            if instruction.ldm_stm_addr_mode == ARM_LDM_STM_IA or instruction.ldm_stm_addr_mode == ARM_LDM_STM_IB:
                tmp = tb._add_to_reg(base, reg_list_size_bytes)
            elif instruction.ldm_stm_addr_mode == ARM_LDM_STM_DA or instruction.ldm_stm_addr_mode == ARM_LDM_STM_DB:
                tmp = tb._sub_to_reg(base, reg_list_size_bytes)
            tb.add(self._builder.gen_str(tmp, base))

    def _load_value(self, tb, mem_dir, value):
        tb.add(self._builder.gen_ldm(mem_dir, value))

    def _store_value(self, tb, mem_dir, value):
        tb.add(self._builder.gen_stm(value, mem_dir))

    def _translate_push_pop(self, tb, instruction, translate_fn):
        # PUSH and POP are equivalent to STM and LDM in FD mode with the SP
        # (and write-back) Instructions are modified to adapt it to the
        # LDM/STM interface

        sp_name = "r13" # TODO: Use self._sp
        sp_size = instruction.operands[0].reg_list[0][0].size # Infer it from the registers list
        sp_reg = ArmRegisterOperand(sp_name, sp_size)
        sp_reg.wb = True
        instruction.operands = [sp_reg, instruction.operands[0]]
        instruction.ldm_stm_addr_mode = ARM_LDM_STM_FD
        translate_fn(tb, instruction)

    def _translate_push(self, tb, instruction):
        self._translate_push_pop(tb, instruction, self._translate_stm)

    def _translate_pop(self, tb, instruction):
        self._translate_push_pop(tb, instruction, self._translate_ldm)


# "Branch Instructions"
# ============================================================================ #
    def _translate_b(self, tb, instruction):
        self._translate_branch(tb, instruction, link=False)

    def _translate_bl(self, tb, instruction):
        self._translate_branch(tb, instruction, link=True)

    # TODO: Thumb
    def _translate_bx(self, tb, instruction):
        self._translate_branch(tb, instruction, link=False)

    def _translate_blx(self, tb, instruction):
        self._translate_branch(tb, instruction, link=True)

    def _translate_bne(self, tb, instruction):
        self._translate_branch(tb, instruction, link=False)

    def _translate_beq(self, tb, instruction):
        self._translate_branch(tb, instruction, link=False)

    def _translate_bpl(self, tb, instruction):
        self._translate_branch(tb, instruction, link=False)

    def _translate_ble(self, tb, instruction):
        self._translate_branch(tb, instruction, link=False)

    def _translate_bcs(self, tb, instruction):
        self._translate_branch(tb, instruction, link=False)

    def _translate_bhs(self, tb, instruction):
        self._translate_branch(tb, instruction, link=False)

    def _translate_blt(self, tb, instruction):
        self._translate_branch(tb, instruction, link=False)

    def _translate_bge(self, tb, instruction):
        self._translate_branch(tb, instruction, link=False)

    def _translate_bhi(self, tb, instruction):
        self._translate_branch(tb, instruction, link=False)

    def _translate_blo(self, tb, instruction):
        self._translate_branch(tb, instruction, link=False)

    def _translate_bls(self, tb, instruction):
        self._translate_branch(tb, instruction, link=False)

    def _translate_branch(self, tb, instruction, link):
        if (instruction.condition_code == ARM_COND_CODE_AL):
            cond = tb.immediate(1, 1)
        else:
            eval_cc_fn = {
                ARM_COND_CODE_EQ : self._evaluate_eq,
                ARM_COND_CODE_NE : self._evaluate_ne,
                ARM_COND_CODE_CS : self._evaluate_cs,
                ARM_COND_CODE_HS : self._evaluate_cs,
                ARM_COND_CODE_CC : self._evaluate_cc,
                ARM_COND_CODE_LO : self._evaluate_cc,
                ARM_COND_CODE_MI : self._evaluate_mi,
                ARM_COND_CODE_PL : self._evaluate_pl,
                ARM_COND_CODE_VS : self._evaluate_vs,
                ARM_COND_CODE_VC : self._evaluate_vc,
                ARM_COND_CODE_HI : self._evaluate_hi,
                ARM_COND_CODE_LS : self._evaluate_ls,
                ARM_COND_CODE_GE : self._evaluate_ge,
                ARM_COND_CODE_LT : self._evaluate_lt,
                ARM_COND_CODE_GT : self._evaluate_gt,
                ARM_COND_CODE_LE : self._evaluate_le,
            }

            cond = eval_cc_fn[instruction.condition_code](tb)

        arm_operand = instruction.operands[0]

        if isinstance(arm_operand, ArmImmediateOperand):
            target = ReilImmediateOperand(arm_operand.immediate << 8, self._pc.size + 8)
        elif isinstance(arm_operand, ArmRegisterOperand):
            target = ReilRegisterOperand(arm_operand.name, arm_operand.size)
            target = tb._and_regs(target, ReilImmediateOperand(0xFFFFFFFE, target.size))

            tmp0 = tb.temporal(target.size + 8)
            tmp1 = tb.temporal(target.size + 8)

            tb.add(self._builder.gen_str(target, tmp0))
            tb.add(self._builder.gen_bsh(tmp0, ReilImmediateOperand(8, target.size + 8), tmp1))

            target = tmp1
        else:
            raise NotImplementedError("Instruction Not Implemented: Unknown operand for branch operation.")

        if link:
            tb.add(self._builder.gen_str(ReilImmediateOperand(instruction.address + instruction.size, self._pc.size), self._lr))

        tb.add(self._builder.gen_jcc(cond, target))

        return
