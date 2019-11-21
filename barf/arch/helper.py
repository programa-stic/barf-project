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
from barf.arch.x86 import X86ImmediateOperand
from barf.core.reil.builder import ReilBuilder


def extract_branch_target(asm_instruction):
    address = None

    target_oprnd = asm_instruction.operands[0]
    if isinstance(target_oprnd, X86ImmediateOperand) or \
       isinstance(target_oprnd, ArmImmediateOperand):
        address = target_oprnd.immediate

    return address


def extract_call_target(asm_instruction):
    address = None

    target_oprnd = asm_instruction.operands[0]
    if isinstance(target_oprnd, X86ImmediateOperand) or \
       isinstance(target_oprnd, ArmImmediateOperand):
        address = target_oprnd.immediate

    return address


def extract_bit(tb, reg, bit):
    assert(0 <= bit < reg.size)

    tmp = tb.temporal(reg.size)
    ret = tb.temporal(1)

    tb.add(ReilBuilder.gen_bsh(reg, tb.immediate(-bit, reg.size), tmp))   # shift to LSB
    tb.add(ReilBuilder.gen_and(tmp, tb.immediate(1, reg.size), ret))      # filter LSB

    return ret


def extract_msb(tb, reg):
    return extract_bit(tb, reg, reg.size - 1)


def extract_sign_bit(tb, reg):
    return extract_msb(tb, reg)


def all_ones_imm(tb, reg):
    return tb.immediate((2**reg.size) - 1, reg.size)


def negate_reg(tb, reg):
    neg = tb.temporal(reg.size)
    tb.add(ReilBuilder.gen_xor(reg, all_ones_imm(tb, reg), neg))
    return neg


def and_regs(tb, reg1, reg2):
    ret = tb.temporal(reg1.size)
    tb.add(ReilBuilder.gen_and(reg1, reg2, ret))
    return ret


def or_regs(tb, reg1, reg2):
    ret = tb.temporal(reg1.size)
    tb.add(ReilBuilder.gen_or(reg1, reg2, ret))
    return ret


def xor_regs(tb, reg1, reg2):
    ret = tb.temporal(reg1.size)
    tb.add(ReilBuilder.gen_xor(reg1, reg2, ret))
    return ret


def equal_regs(tb, reg1, reg2):
    return negate_reg(tb, xor_regs(tb, reg1, reg2))


def unequal_regs(tb, reg1, reg2):
    return xor_regs(tb, reg1, reg2)


def add_to_reg(tb, reg, value):
    res = tb.temporal(reg.size)
    tb.add(tb._builder.gen_add(reg, value, res))

    return res


def sub_to_reg(tb, reg, value):
    res = tb.temporal(reg.size)
    tb.add(tb._builder.gen_sub(reg, value, res))

    return res


def shift_reg(tb, reg, sh):
    ret = tb.temporal(reg.size)
    tb.add(tb._builder.gen_bsh(reg, sh, ret))

    return ret


def extract_bit_with_register(tb, reg, bit):
    # Same as before but the bit number is indicated by a register and it will be resolved at runtime
    # assert(bit >= 0 and bit < reg.size2) # It is assumed, it is not checked
    tmp = tb.temporal(reg.size)
    neg_bit = tb.temporal(reg.size)
    ret = tb.temporal(1)

    tb.add(tb._builder.gen_sub(tb.immediate(0, bit.size), bit, neg_bit))  # as left bit is indicated by a negative number
    tb.add(tb._builder.gen_bsh(reg, neg_bit, tmp))                        # shift to LSB
    tb.add(tb._builder.gen_and(tmp, tb.immediate(1, reg.size), ret))      # filter LSB

    return ret


def greater_than_or_equal(tb, reg1, reg2):
    assert(reg1.size == reg2.size)
    result = tb.temporal(reg1.size * 2)

    tb.add(tb._builder.gen_sub(reg1, reg2, result))

    sign = extract_bit(tb, result, reg1.size - 1)
    overflow = overflow_from_sub(tb, reg1, reg2, result)

    return equal_regs(tb, sign, overflow)


def jump_to(tb, target):
    tb.add(tb._builder.gen_jcc(tb.immediate(1, 1), target))


def jump_if_zero(tb, reg, label):
    is_zero = tb.temporal(1)
    tb.add(tb._builder.gen_bisz(reg, is_zero))
    tb.add(tb._builder.gen_jcc(is_zero, label))


def overflow_from_sub(tb, oprnd0, oprnd1, result):
    op1_sign = extract_bit(tb, oprnd0, oprnd0.size - 1)
    op2_sign = extract_bit(tb, oprnd1, oprnd0.size - 1)
    res_sign = extract_bit(tb, result, oprnd0.size - 1)

    return and_regs(tb, unequal_regs(tb, op1_sign, op2_sign), unequal_regs(tb, op1_sign, res_sign))
