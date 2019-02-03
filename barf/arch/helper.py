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
