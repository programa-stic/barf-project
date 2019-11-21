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

from __future__ import absolute_import

import logging

import barf.arch.arm.translators as translators

from barf.arch import ARCH_ARM_MODE_THUMB
from barf.arch.arm import ARM_COND_CODE_AL
from barf.arch.arm import ARM_MEMORY_INDEX_OFFSET
from barf.arch.arm import ARM_MEMORY_INDEX_POST
from barf.arch.arm import ARM_MEMORY_INDEX_PRE
from barf.arch.arm import ArmArchitectureInformation
from barf.arch.arm import ArmImmediateOperand
from barf.arch.arm import ArmMemoryOperand
from barf.arch.arm import ArmRegisterListOperand
from barf.arch.arm import ArmRegisterOperand
from barf.arch.arm import ArmShiftedRegisterOperand
from barf.arch.arm.helpers import ArmConditionCodeHelper
from barf.arch.helper import and_regs
from barf.arch.helper import equal_regs
from barf.arch.helper import extract_bit
from barf.arch.helper import extract_bit_with_register
from barf.arch.helper import greater_than_or_equal
from barf.arch.helper import jump_if_zero
from barf.arch.helper import jump_to
from barf.arch.helper import negate_reg
from barf.arch.helper import overflow_from_sub
from barf.arch.helper import unequal_regs
from barf.arch.translator import FlagTranslator
from barf.arch.translator import InstructionTranslator
from barf.arch.translator import RegisterTranslator
from barf.arch.translator import TranslationBuilder
from barf.core.reil import ReilImmediateOperand
from barf.core.reil import ReilLabel
from barf.core.reil import ReilRegisterOperand
from barf.core.reil.builder import ReilBuilder


logger = logging.getLogger(__name__)


class ArmFlagTranslator(object):

    def __init__(self, flags):
        # NOTE: it needs: a) a translation builder (to store the instructions),
        # and b) a REIL builder to build the instructions.

        self._flags = flags

    def update_nf(self, tb, oprnd0, oprnd1, result):
        sign = extract_bit(tb, result, oprnd0.size - 1)
        tb.add(tb._builder.gen_str(sign, self._flags.nf))

    def update_zf(self, tb, oprnd0, oprnd1, result):
        imm0 = tb.immediate((2**oprnd0.size)-1, result.size)
        tmp0 = tb.temporal(oprnd0.size)

        tb.add(tb._builder.gen_and(result, imm0, tmp0))  # filter low part of result
        tb.add(tb._builder.gen_bisz(tmp0, self._flags.zf))

    def update_flags_data_proc_add(self, tb, oprnd0, oprnd1, result):
        self.update_zf(tb, oprnd0, oprnd1, result)
        self.update_nf(tb, oprnd0, oprnd1, result)
        self._carry_from_uf(tb, oprnd0, oprnd1, result)
        self._overflow_from_add_uf(tb, oprnd0, oprnd1, result)

    def update_flags_data_proc_sub(self, tb, oprnd0, oprnd1, result):
        self.update_zf(tb, oprnd0, oprnd1, result)
        self.update_nf(tb, oprnd0, oprnd1, result)
        self._borrow_from_uf(tb, oprnd0, oprnd1, result)
        # C Flag = NOT BorrowFrom (to be used by subsequent instructions like SBC and RSC)
        tb.add(tb._builder.gen_str(negate_reg(tb, self._flags.cf), self._flags.cf))
        self._overflow_from_sub_uf(tb, oprnd0, oprnd1, result)

    def update_flags_data_proc_other(self, tb, second_operand, oprnd0, oprnd1, result):
        self.update_zf(tb, oprnd0, oprnd1, result)
        self.update_nf(tb, oprnd0, oprnd1, result)
        self._carry_out(tb, second_operand, oprnd0, oprnd1, result)
        # Overflow Flag (V) unaffected

    # Helper methods
    # ======================================================================== #
    def _carry_from_uf(self, tb, oprnd0, oprnd1, result):
        assert (result.size == oprnd0.size * 2)

        carry = extract_bit(tb, result, oprnd0.size)
        tb.add(tb._builder.gen_str(carry, self._flags.cf))

    def _borrow_from_uf(self, tb, oprnd0, oprnd1, result):
        # BorrowFrom as defined in the ARM Reference Manual has the same implementation as CarryFrom
        self._carry_from_uf(tb, oprnd0, oprnd1, result)

    def _overflow_from_add_uf(self, tb, oprnd0, oprnd1, result):
        op1_sign = extract_bit(tb, oprnd0, oprnd0.size - 1)
        op2_sign = extract_bit(tb, oprnd1, oprnd0.size - 1)
        res_sign = extract_bit(tb, result, oprnd0.size - 1)

        overflow = and_regs(tb, equal_regs(tb, op1_sign, op2_sign), unequal_regs(tb, op1_sign, res_sign))
        tb.add(tb._builder.gen_str(overflow, self._flags.vf))

    def _overflow_from_sub_uf(self, tb, oprnd0, oprnd1, result):
        # Evaluate overflow and update the flag
        tb.add(tb._builder.gen_str(overflow_from_sub(tb, oprnd0, oprnd1, result), self._flags.vf))

    def _carry_out(self, tb, carry_operand, oprnd0, oprnd1, result):
        if isinstance(carry_operand, ArmImmediateOperand):
            return
        elif isinstance(carry_operand, ArmRegisterOperand):
            return
        elif isinstance(carry_operand, ArmShiftedRegisterOperand):
            base = ReilRegisterOperand(carry_operand.base_reg.name, carry_operand.size)
            shift_type = carry_operand.shift_type
            shift_amount = carry_operand.shift_amount

            if shift_type == 'lsl':

                if isinstance(shift_amount, ArmImmediateOperand):
                    if shift_amount.immediate == 0:
                        return
                    else:
                        # carry_out = Rm[32 - shift_imm]
                        shift_carry_out = extract_bit(tb, base, 32 - shift_amount.immediate)

                elif isinstance(shift_amount, ArmRegisterOperand):
                    # Rs: register with shift amount
                    # if Rs[7:0] == 0 then
                    #     carry_out = C Flag
                    # else if Rs[7:0] <= 32 then
                    #     carry_out = Rm[32 - Rs[7:0]]
                    # else /* Rs[7:0] > 32 */
                    #     carry_out = 0

                    shift_carry_out = tb.temporal(1)
                    tb.add(tb._builder.gen_str(self._flags.cf, shift_carry_out))
                    rs = ReilRegisterOperand(shift_amount.name, shift_amount.size)
                    rs_7_0 = and_regs(tb, rs, tb.immediate(0xFF, rs.size))

                    end_label = tb.label('end_label')
                    rs_greater_32_label = tb.label('rs_greater_32_label')

                    # if Rs[7:0] == 0 then
                    #     carry_out = C Flag
                    jump_if_zero(tb, rs_7_0, end_label)     # shift_carry_out already has the C flag set, so do nothing

                    tb.add(tb._builder.gen_jcc(greater_than_or_equal(tb, rs_7_0, tb.immediate(33, rs_7_0.size)), rs_greater_32_label))

                    # Rs > 0 and Rs <= 32
                    #     carry_out = Rm[32 - Rs[7:0]]
                    extract_bit_number = tb.temporal(rs_7_0.size)
                    tb.add(tb._builder.gen_sub(tb.immediate(32, rs_7_0.size), rs_7_0, extract_bit_number))
                    tb.add(tb._builder.gen_str(extract_bit_with_register(tb, base, extract_bit_number), shift_carry_out))
                    jump_to(tb, end_label)

                    # else /* Rs[7:0] > 32 */
                    #     carry_out = 0
                    tb.add(rs_greater_32_label)
                    tb.add(tb._builder.gen_str(tb.immediate(0, 1), shift_carry_out))
                    # tb._jump_to(end_label)

                    tb.add(end_label)

                else:
                    raise Exception("carry_out: Unknown shift amount type.")

            else:
                # TODO: Implement other shift types
                raise NotImplementedError("Instruction Not Implemented: carry_out: shift type " + carry_operand.shift_type)

        else:
            raise Exception("carry_out: Unknown operand type.")

        tb.add(tb._builder.gen_str(shift_carry_out, self._flags.cf))

    def _update_flags_other(self, tb, oprnd0, oprnd1, result):
        self.update_zf(tb, oprnd0, oprnd1, result)
        self.update_nf(tb, oprnd0, oprnd1, result)
        # Carry Flag (C) unaffected
        # Overflow Flag (V) unaffected


class ArmOperandAccessTranslator(object):

    def __init__(self, arch_info):
        # NOTE: it needs: a) a translation context (to store the instructions),
        # and b) a REIL builder to build the instructions.

        self._arch_info = arch_info

        self._regs_mapper = self._arch_info.alias_mapper

        self._regs_size = self._arch_info.registers_size

    def read(self, tb, arm_operand):
        if isinstance(arm_operand, ArmImmediateOperand):
            reil_operand = ReilImmediateOperand(arm_operand.immediate, arm_operand.size)
        elif isinstance(arm_operand, ArmRegisterOperand):
            reil_operand = ReilRegisterOperand(arm_operand.name, arm_operand.size)
        elif isinstance(arm_operand, ArmShiftedRegisterOperand):
            reil_operand = self.compute_shifted_register(tb, arm_operand)
        elif isinstance(arm_operand, ArmMemoryOperand):
            reil_operand = tb.temporal(arm_operand.size)
            addr = self.compute_memory_address(tb, arm_operand)
            tb.add(tb._builder.gen_ldm(addr, reil_operand))
        elif isinstance(arm_operand, ArmRegisterListOperand):
            reil_operand = self._compute_register_list(arm_operand)
        else:
            raise NotImplementedError("Instruction Not Implemented: Unknown operand for read operation.")

        return reil_operand

    def write(self, tb, arm_operand, value):
        if isinstance(arm_operand, ArmRegisterOperand):
            reil_operand = ReilRegisterOperand(arm_operand.name, arm_operand.size)
            tb.add(tb._builder.gen_str(value, reil_operand))
        elif isinstance(arm_operand, ArmMemoryOperand):
            addr = self.compute_memory_address(tb, arm_operand)
            tb.add(tb._builder.gen_stm(value, addr))
        else:
            raise NotImplementedError("Instruction Not Implemented: Unknown operand for write operation.")

    def compute_shifted_register(self, tb, sh_op):
        base = ReilRegisterOperand(sh_op.base_reg.name, sh_op.size)

        if sh_op.shift_amount:
            ret = tb.temporal(sh_op.size)

            if isinstance(sh_op.shift_amount, ArmImmediateOperand):
                sh_am = ReilImmediateOperand(sh_op.shift_amount.immediate, sh_op.size)
            elif isinstance(sh_op.shift_amount, ArmRegisterOperand):
                sh_am = ReilRegisterOperand(sh_op.shift_amount.name, sh_op.shift_amount.size)
            else:
                raise NotImplementedError("Instruction Not Implemented: Unknown shift amount type.")

            if sh_op.shift_type == 'lsl':
                if isinstance(sh_am, ReilImmediateOperand):
                    tb.add(tb._builder.gen_bsh(base, sh_am, ret))
                else:
                    sh_am_greater_32_label = tb.label('sh_am_greater_32_label')
                    sh_am_end_label = tb.label('sh_am_end_label')

                    sh_am_7_0 = and_regs(tb, sh_am, tb.immediate(0xFF, sh_am.size))

                    tb.add(tb._builder.gen_jcc(greater_than_or_equal(tb, sh_am_7_0, tb.immediate(33, sh_am_7_0.size)), sh_am_greater_32_label))

                    # Shift < 32 => shifted_register = base lsl sh_am
                    tb.add(tb._builder.gen_bsh(base, sh_am_7_0, ret))
                    jump_to(tb, sh_am_end_label)

                    # Shift >= 32 => shifted_register = 0
                    tb.add(sh_am_greater_32_label)
                    tb.add(tb._builder.gen_str(tb.immediate(0x0, ret.size), ret))

                    tb.add(sh_am_end_label)
            else:
                # TODO: Implement other shift types
                raise NotImplementedError("Instruction Not Implemented: Shift type.")
        else:
            ret = base

        return ret

    def compute_memory_address(self, tb, mem_operand):
        """Return operand memory access translation.
        """
        base = ReilRegisterOperand(mem_operand.base_reg.name, mem_operand.size)

        if mem_operand.displacement:
            address = tb.temporal(mem_operand.size)

            if isinstance(mem_operand.displacement, ArmRegisterOperand):
                disp = ReilRegisterOperand(mem_operand.displacement.name, mem_operand.size)
            elif isinstance(mem_operand.displacement, ArmImmediateOperand):
                disp = ReilImmediateOperand(mem_operand.displacement.immediate, mem_operand.size)
            elif isinstance(mem_operand.displacement, ArmShiftedRegisterOperand):
                disp = self.compute_shifted_register(tb, mem_operand.displacement)
            else:
                raise Exception("compute_memory_address: displacement type unknown")

            if mem_operand.index_type == ARM_MEMORY_INDEX_PRE:
                if mem_operand.disp_minus:
                    tb.add(tb._builder.gen_sub(base, disp, address))
                else:
                    tb.add(tb._builder.gen_add(base, disp, address))
                tb.add(tb._builder.gen_str(address, base))
            elif mem_operand.index_type == ARM_MEMORY_INDEX_OFFSET:
                if mem_operand.disp_minus:
                    tb.add(tb._builder.gen_sub(base, disp, address))
                else:
                    tb.add(tb._builder.gen_add(base, disp, address))
            elif mem_operand.index_type == ARM_MEMORY_INDEX_POST:
                tb.add(tb._builder.gen_str(base, address))
                tmp = tb.temporal(base.size)
                if mem_operand.disp_minus:
                    tb.add(tb._builder.gen_sub(base, disp, tmp))
                else:
                    tb.add(tb._builder.gen_add(base, disp, tmp))
                tb.add(tb._builder.gen_str(tmp, base))
            else:
                raise Exception("compute_memory_address: indexing type unknown")

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
                reg_num = int(reg_range[0].name[1:])    # Assuming the register is named with one letter + number
                reg_end = int(reg_range[1].name[1:])
                if reg_num > reg_end:
                    raise NotImplementedError("Instruction Not Implemented: Invalid register range.")
                while reg_num <= reg_end:
                    ret.append(ReilRegisterOperand(reg_range[0].name[0] + str(reg_num), reg_range[0].size))
                    reg_num = reg_num + 1

        return ret


class ArmTranslator(InstructionTranslator):

    """ARM to IR Translator."""

    def __init__(self, architecture_mode=ARCH_ARM_MODE_THUMB):
        super(ArmTranslator, self).__init__()

        # Set *Architecture Mode*. The translation of each instruction
        # into the REIL language is based on this.
        self._arch_mode = architecture_mode

        # An instance of *ArchitectureInformation*.
        self._arch_info = ArmArchitectureInformation(architecture_mode)

        self._builder = ReilBuilder()

        self._registers = RegisterTranslator(self._arch_info)

        self._reg_acc_translator = ArmOperandAccessTranslator(self._arch_info)

        self._flags = FlagTranslator(self._arch_info)

        self._flag_translator = ArmFlagTranslator(self._flags)

        # Special registers.
        self._sp = ReilRegisterOperand("r13", 32)
        self._lr = ReilRegisterOperand("r14", 32)
        self._pc = ReilRegisterOperand("r15", 32)

        # Word size.
        self._ws = ReilImmediateOperand(4, 32)

    def _translate(self, instruction):
        # Retrieve translation function.
        mnemonic = instruction.mnemonic

        tb = TranslationBuilder(self._ir_name_generator, self._arch_info)

        if instruction.condition_code is None:
            instruction.condition_code = ARM_COND_CODE_AL

        # Translate instruction.
        if mnemonic in translators.dispatcher:
            if instruction.mnemonic in ["b", "bl", "bx", "blx", "bne", "beq", "bpl",
                                        "ble", "bcs", "bhs", "blt", "bge", "bhi",
                                        "blo", "bls"]:
                translators.dispatcher[mnemonic](self, tb, instruction)
            else:
                # Pre-processing: evaluate flags
                if instruction.condition_code != ARM_COND_CODE_AL:
                    cond_not_met = ReilLabel('cond_not_met')
                    cond = ArmConditionCodeHelper.evaluate_cond_code(self._flags, tb, instruction.condition_code)
                    neg_cond = negate_reg(tb, cond)
                    tb.add(tb._builder.gen_jcc(neg_cond, cond_not_met))
                    translators.dispatcher[mnemonic](self, tb, instruction)
                    tb.add(cond_not_met)
                    tb.add(tb._builder.gen_nop())
                else:
                    translators.dispatcher[mnemonic](self, tb, instruction)
        else:
            tb.add(self._builder.gen_unkn())

            self._log_not_supported_instruction(instruction)

        return tb.instanciate(instruction.address)
