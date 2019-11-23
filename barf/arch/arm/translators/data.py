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

from barf.arch.arm import ArmImmediateOperand
from barf.arch.arm import ArmRegisterOperand
from barf.arch.arm import ArmShiftedRegisterOperand
from barf.arch.helper import and_regs
from barf.arch.helper import extract_bit
from barf.arch.helper import jump_if_zero
from barf.arch.helper import negate_reg
from barf.core.reil import ReilImmediateOperand
from barf.core.reil import ReilRegisterOperand


# "Data-processing Instructions"
# ============================================================================ #
def _translate_mov(self, tb, instruction):
    oprnd1 = self._reg_acc_translator.read(tb, instruction.operands[1])

    self._reg_acc_translator.write(tb, instruction.operands[0], oprnd1)

    if instruction.update_flags:
        self._flag_translator.update_flags_data_proc_other(tb, instruction.operands[1], oprnd1, None, oprnd1)


def _translate_mvn(self, tb, instruction):
    oprnd1 = self._reg_acc_translator.read(tb, instruction.operands[1])

    self._reg_acc_translator.write(tb, instruction.operands[0], negate_reg(tb, oprnd1))

    if instruction.update_flags:
        self._flag_translator.update_flags_data_proc_other(tb, instruction.operands[1], oprnd1, None, negate_reg(tb, oprnd1))


def _translate_movw(self, tb, instruction):
    reil_operand = ReilRegisterOperand(instruction.operands[0].name, instruction.operands[0].size)
    word_mask = ReilImmediateOperand(0x0000FFFF, reil_operand.size)
    and_temp = tb.temporal(reil_operand.size)

    oprnd1 = self._reg_acc_translator.read(tb, instruction.operands[1])

    self._reg_acc_translator.write(tb, instruction.operands[0], oprnd1)

    tb.add(self._builder.gen_and(reil_operand, word_mask, and_temp))  # filter bits [7:0] part of result
    tb.add(self._builder.gen_str(and_temp, reil_operand))

    # It doesn't update flags


def _translate_and(self, tb, instruction):
    oprnd1 = self._reg_acc_translator.read(tb, instruction.operands[1])
    oprnd2 = self._reg_acc_translator.read(tb, instruction.operands[2])

    result = tb.temporal(oprnd1.size)

    tb.add(self._builder.gen_and(oprnd1, oprnd2, result))

    self._reg_acc_translator.write(tb, instruction.operands[0], result)

    if instruction.update_flags:
        self._flag_translator.update_flags_data_proc_other(tb, instruction.operands[2], oprnd1, oprnd2, result)


def _translate_orr(self, tb, instruction):
    oprnd1 = self._reg_acc_translator.read(tb, instruction.operands[1])
    oprnd2 = self._reg_acc_translator.read(tb, instruction.operands[2])

    result = tb.temporal(oprnd1.size)

    tb.add(self._builder.gen_or(oprnd1, oprnd2, result))

    self._reg_acc_translator.write(tb, instruction.operands[0], result)

    if instruction.update_flags:
        self._flag_translator.update_flags_data_proc_other(tb, instruction.operands[2], oprnd1, oprnd2, result)


def _translate_eor(self, tb, instruction):
    oprnd1 = self._reg_acc_translator.read(tb, instruction.operands[1])
    oprnd2 = self._reg_acc_translator.read(tb, instruction.operands[2])

    result = tb.temporal(oprnd1.size)

    tb.add(self._builder.gen_xor(oprnd1, oprnd2, result))

    self._reg_acc_translator.write(tb, instruction.operands[0], result)

    if instruction.update_flags:
        self._flag_translator.update_flags_data_proc_other(tb, instruction.operands[2], oprnd1, oprnd2, result)


def _translate_add(self, tb, instruction):
    oprnd1 = self._reg_acc_translator.read(tb, instruction.operands[1])
    oprnd2 = self._reg_acc_translator.read(tb, instruction.operands[2])

    result = tb.temporal(oprnd1.size * 2)

    tb.add(self._builder.gen_add(oprnd1, oprnd2, result))

    self._reg_acc_translator.write(tb, instruction.operands[0], result)

    if instruction.update_flags:
        self._flag_translator.update_flags_data_proc_add(tb, oprnd1, oprnd2, result)


def _translate_sub(self, tb, instruction):
    oprnd1 = self._reg_acc_translator.read(tb, instruction.operands[1])
    oprnd2 = self._reg_acc_translator.read(tb, instruction.operands[2])

    result = tb.temporal(oprnd1.size * 2)

    tb.add(self._builder.gen_sub(oprnd1, oprnd2, result))

    self._reg_acc_translator.write(tb, instruction.operands[0], result)

    if instruction.update_flags:
        self._flag_translator.update_flags_data_proc_sub(tb, oprnd1, oprnd2, result)


def _translate_rsb(self, tb, instruction):
    instruction.operands[1], instruction.operands[2] = instruction.operands[2], instruction.operands[1]

    _translate_sub(self, tb, instruction)


def _translate_mul(self, tb, instruction):
    oprnd1 = self._reg_acc_translator.read(tb, instruction.operands[1])
    oprnd2 = self._reg_acc_translator.read(tb, instruction.operands[2])

    result = tb.temporal(oprnd1.size * 2)

    tb.add(self._builder.gen_mul(oprnd1, oprnd2, result))

    self._reg_acc_translator.write(tb, instruction.operands[0], result)

    if instruction.update_flags:
        self._flag_translator.update_zf(tb, oprnd1, oprnd2, result)
        self._flag_translator.update_nf(tb, oprnd1, oprnd2, result)


def _translate_cmn(self, tb, instruction):
    oprnd1 = self._reg_acc_translator.read(tb, instruction.operands[0])
    oprnd2 = self._reg_acc_translator.read(tb, instruction.operands[1])

    result = tb.temporal(oprnd1.size * 2)

    tb.add(self._builder.gen_add(oprnd1, oprnd2, result))

    self._flag_translator.update_flags_data_proc_add(tb, oprnd1, oprnd2, result)  # S = 1 (implied in the instruction)


def _translate_cmp(self, tb, instruction):
    oprnd1 = self._reg_acc_translator.read(tb, instruction.operands[0])
    oprnd2 = self._reg_acc_translator.read(tb, instruction.operands[1])

    result = tb.temporal(oprnd1.size * 2)

    tb.add(self._builder.gen_sub(oprnd1, oprnd2, result))

    self._flag_translator.update_flags_data_proc_sub(tb, oprnd1, oprnd2, result)  # S = 1 (implied in the instruction)


def _translate_cbz(self, tb, instruction):
    oprnd1 = self._reg_acc_translator.read(tb, instruction.operands[0])
    arm_operand = instruction.operands[1]

    if isinstance(arm_operand, ArmImmediateOperand):
        target = ReilImmediateOperand(arm_operand.immediate << 8, self._pc.size + 8)
    elif isinstance(arm_operand, ArmRegisterOperand):
        target = ReilRegisterOperand(arm_operand.name, arm_operand.size)
        target = and_regs(tb, target, ReilImmediateOperand(0xFFFFFFFE, target.size))

        tmp0 = tb.temporal(target.size + 8)
        tmp1 = tb.temporal(target.size + 8)

        tb.add(self._builder.gen_str(target, tmp0))
        tb.add(self._builder.gen_bsh(tmp0, ReilImmediateOperand(8, target.size + 8), tmp1))

        target = tmp1
    else:
        raise Exception()

    jump_if_zero(tb, oprnd1, target)


def _translate_cbnz(self, tb, instruction):
    oprnd0 = self._reg_acc_translator.read(tb, instruction.operands[0])
    arm_operand = instruction.operands[1]

    if isinstance(arm_operand, ArmImmediateOperand):
        target = ReilImmediateOperand(arm_operand.immediate << 8, self._pc.size + 8)
    elif isinstance(arm_operand, ArmRegisterOperand):
        target = ReilRegisterOperand(arm_operand.name, arm_operand.size)
        target = and_regs(tb, target, ReilImmediateOperand(0xFFFFFFFE, target.size))

        tmp0 = tb.temporal(target.size + 8)
        tmp1 = tb.temporal(target.size + 8)

        tb.add(self._builder.gen_str(target, tmp0))
        tb.add(self._builder.gen_bsh(tmp0, ReilImmediateOperand(8, target.size + 8), tmp1))

        target = tmp1
    else:
        raise Exception()

    neg_oprnd = negate_reg(tb, oprnd0)

    jump_if_zero(tb, neg_oprnd, target)


def _translate_lsl(self, tb, instruction):
    # LSL (register)
    if len(instruction.operands) == 3 and isinstance(instruction.operands[1], ArmRegisterOperand):
        sh_op = ArmShiftedRegisterOperand(instruction.operands[1], "lsl", instruction.operands[2],
                                          instruction.operands[1].size)
        disp = self._reg_acc_translator.compute_shifted_register(tb, sh_op)
        self._reg_acc_translator.write(tb, instruction.operands[0], disp)
        return

    if len(instruction.operands) == 2 and isinstance(instruction.operands[1], ArmShiftedRegisterOperand):
        # Capstone is incorrectly packing <Rm>, #<imm5> into a shifted register, unpack it
        instruction.operands.append(instruction.operands[1].shift_amount)
        instruction.operands[1] = instruction.operands[1].base_reg

    oprnd1 = self._reg_acc_translator.read(tb, instruction.operands[1])
    oprnd2 = self._reg_acc_translator.read(tb, instruction.operands[2])
    result = tb.temporal(oprnd1.size)

    tb.add(self._builder.gen_bsh(oprnd1, oprnd2, result))
    self._reg_acc_translator.write(tb, instruction.operands[0], result)

    if instruction.update_flags:
        self._flag_translator.update_zf(tb, oprnd1, oprnd2, result)
        self._flag_translator.update_nf(tb, oprnd1, oprnd2, result)
        # TODO: Encapsulate this new kind of flag update (different from the data proc instructions like add, and, orr)
        if oprnd2.immediate == 0:
            return
        else:
            # carry_out = Rm[32 - shift_imm]
            shift_carry_out = extract_bit(tb, oprnd1, 32 - oprnd2.immediate)
            tb.add(self._builder.gen_str(shift_carry_out, self._flags["cf"]))


dispatcher = {
    'mov': _translate_mov,
    'mvn': _translate_mvn,
    'movw': _translate_movw,
    'and': _translate_and,
    'orr': _translate_orr,
    'eor': _translate_eor,
    'add': _translate_add,
    'sub': _translate_sub,
    'rsb': _translate_rsb,
    'mul': _translate_mul,
    'cmn': _translate_cmn,
    'cmp': _translate_cmp,
    'cbz': _translate_cbz,
    'cbnz': _translate_cbnz,
    'lsl': _translate_lsl,
}
