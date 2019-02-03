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

from barf.arch import ARCH_X86_MODE_32
from barf.arch import ARCH_X86_MODE_64
from barf.arch.helper import negate_reg
from barf.arch.x86 import X86RegisterOperand
from barf.arch.x86.translators.helpers import X86ConditionCodeHelper
from barf.core.reil import ReilImmediateOperand
from barf.core.reil import ReilRegisterOperand


# "Control Transfer Instructions"
# ============================================================================ #
def _translate_call(self, tb, instruction):
    # Flags Affected
    # All flags are affected if a task switch occurs; no flags are
    # affected if a task switch does not occur.

    oprnd0 = self._reg_acc_translator.read(tb, instruction.operands[0])

    addr_oprnd = _translate_address(self, tb, oprnd0)

    imm1 = tb.immediate(1, 1)

    tmp0 = tb.temporal(self._sp.size)

    ret_addr = ReilImmediateOperand((instruction.address + instruction.size), self._arch_info.address_size)

    tb.add(self._builder.gen_sub(self._sp, self._ws, tmp0))
    tb.add(self._builder.gen_str(tmp0, self._sp))
    tb.add(self._builder.gen_stm(ret_addr, self._sp))
    tb.add(self._builder.gen_jcc(imm1, addr_oprnd))


def _translate_jcc(self, tb, instruction, condition_code):
    # Jump if condition (condition_code) is met.
    # Flags Affected
    # None.

    oprnd0 = self._reg_acc_translator.read(tb, instruction.operands[0])

    oprnd_cc = X86ConditionCodeHelper.evaluate_cc(self._flags, tb, condition_code)

    addr_oprnd = _translate_address(self, tb, oprnd0)

    tb.add(self._builder.gen_jcc(oprnd_cc, addr_oprnd))


def _translate_ja(self, tb, instruction):
    _translate_jcc(self, tb, instruction, 'a')


def _translate_jae(self, tb, instruction):
    _translate_jcc(self, tb, instruction, 'ae')


def _translate_jb(self, tb, instruction):
    _translate_jcc(self, tb, instruction, 'b')


def _translate_jbe(self, tb, instruction):
    _translate_jcc(self, tb, instruction, 'be')


def _translate_jc(self, tb, instruction):
    _translate_jcc(self, tb, instruction, 'c')


def _translate_je(self, tb, instruction):
    _translate_jcc(self, tb, instruction, 'e')


def _translate_jecxz(self, tb, instruction):
    # Jump short if ECX register is 0.

    oprnd0 = self._reg_acc_translator.read(tb, instruction.operands[0])

    ecx_x86 = __get_jecxz_implicit_operand()

    ecx = self._reg_acc_translator.read(tb, ecx_x86)

    addr_oprnd = _translate_address(self, tb, oprnd0)

    tmp0 = tb.temporal(1)

    tb.add(self._builder.gen_bisz(ecx, tmp0))
    tb.add(self._builder.gen_jcc(tmp0, addr_oprnd))


def _translate_jg(self, tb, instruction):
    _translate_jcc(self, tb, instruction, 'g')


def _translate_jge(self, tb, instruction):
    _translate_jcc(self, tb, instruction, 'ge')


def _translate_jl(self, tb, instruction):
    _translate_jcc(self, tb, instruction, 'l')


def _translate_jle(self, tb, instruction):
    _translate_jcc(self, tb, instruction, 'le')


def _translate_jmp(self, tb, instruction):
    # Flags Affected
    # All flags are affected if a task switch occurs; no flags are
    # affected if a task switch does not occur.

    oprnd0 = self._reg_acc_translator.read(tb, instruction.operands[0])

    addr_oprnd = _translate_address(self, tb, oprnd0)

    imm0 = tb.immediate(1, 1)

    tb.add(self._builder.gen_jcc(imm0, addr_oprnd))


def _translate_jna(self, tb, instruction):
    _translate_jcc(self, tb, instruction, 'na')


def _translate_jnae(self, tb, instruction):
    _translate_jcc(self, tb, instruction, 'nae')


def _translate_jnb(self, tb, instruction):
    _translate_jcc(self, tb, instruction, 'nb')


def _translate_jnbe(self, tb, instruction):
    _translate_jcc(self, tb, instruction, 'nbe')


def _translate_jnc(self, tb, instruction):
    _translate_jcc(self, tb, instruction, 'nc')


def _translate_jne(self, tb, instruction):
    _translate_jcc(self, tb, instruction, 'ne')


def _translate_jng(self, tb, instruction):
    _translate_jcc(self, tb, instruction, 'ng')


def _translate_jnge(self, tb, instruction):
    _translate_jcc(self, tb, instruction, 'nge')


def _translate_jnl(self, tb, instruction):
    _translate_jcc(self, tb, instruction, 'nl')


def _translate_jnle(self, tb, instruction):
    _translate_jcc(self, tb, instruction, 'nle')


def _translate_jno(self, tb, instruction):
    _translate_jcc(self, tb, instruction, 'no')


def _translate_jnp(self, tb, instruction):
    _translate_jcc(self, tb, instruction, 'np')


def _translate_jns(self, tb, instruction):
    _translate_jcc(self, tb, instruction, 'ns')


def _translate_jnz(self, tb, instruction):
    _translate_jcc(self, tb, instruction, 'nz')


def _translate_jo(self, tb, instruction):
    _translate_jcc(self, tb, instruction, 'o')


def _translate_jp(self, tb, instruction):
    _translate_jcc(self, tb, instruction, 'p')


def _translate_jpe(self, tb, instruction):
    _translate_jcc(self, tb, instruction, 'pe')


def _translate_jpo(self, tb, instruction):
    _translate_jcc(self, tb, instruction, 'po')


def _translate_js(self, tb, instruction):
    _translate_jcc(self, tb, instruction, 's')


def _translate_jz(self, tb, instruction):
    _translate_jcc(self, tb, instruction, 'z')


def _translate_loop(self, tb, instruction):
    # Flags Affected
    # None.

    oprnd0 = self._reg_acc_translator.read(tb, instruction.operands[0])

    counter_x86 = __get_loopcc_implicit_operand(self._arch_mode)

    counter = self._reg_acc_translator.read(tb, counter_x86)

    addr_oprnd = _translate_address(self, tb, oprnd0)

    tmp0 = tb.temporal(counter.size)

    imm0 = tb.immediate(1, counter.size)

    tb.add(self._builder.gen_str(counter, tmp0))
    tb.add(self._builder.gen_sub(tmp0, imm0, counter))
    tb.add(self._builder.gen_jcc(counter, addr_oprnd))  # keep looping


def _translate_loopcc(self, tb, instruction, condition_code):
    # Flags Affected
    # None.

    oprnd0 = self._reg_acc_translator.read(tb, instruction.operands[0])

    counter_x86 = __get_loopcc_implicit_operand(self._arch_mode)

    counter = self._reg_acc_translator.read(tb, counter_x86)

    addr_oprnd = _translate_address(self, tb, oprnd0)

    end_addr = ReilImmediateOperand((instruction.address + instruction.size) << 8, self._arch_info.address_size + 8)

    tmp0 = tb.temporal(counter.size)

    counter_zero = tb.temporal(1)
    counter_not_zero = tb.temporal(1)
    branch_cond = tb.temporal(1)

    imm0 = tb.immediate(1, counter.size)
    imm1 = tb.immediate(1, 1)

    keep_looping_lbl = tb.label('keep_looping')

    neg_cond = negate_reg(tb, X86ConditionCodeHelper.evaluate_cc(self._flags, tb, condition_code))

    tb.add(self._builder.gen_str(counter, tmp0))
    tb.add(self._builder.gen_sub(tmp0, imm0, counter))
    tb.add(self._builder.gen_bisz(counter, counter_zero))
    tb.add(self._builder.gen_xor(counter_zero, imm1, counter_not_zero))
    tb.add(self._builder.gen_and(counter_not_zero, neg_cond, branch_cond))
    tb.add(self._builder.gen_jcc(branch_cond, keep_looping_lbl))
    tb.add(self._builder.gen_jcc(imm0, end_addr))  # exit loop
    tb.add(keep_looping_lbl)
    tb.add(self._builder.gen_jcc(imm0, addr_oprnd))


def _translate_loope(self, tb, instruction):
    return _translate_loopcc(self, tb, instruction, 'e')


def _translate_loopne(self, tb, instruction):
    return _translate_loopcc(self, tb, instruction, 'ne')


def _translate_loopnz(self, tb, instruction):
    return _translate_loopcc(self, tb, instruction, 'nz')


def _translate_loopz(self, tb, instruction):
    return _translate_loopcc(self, tb, instruction, 'z')


def _translate_ret(self, tb, instruction):
    # Flags Affected
    # None.

    imm1 = tb.immediate(1, 1)
    imm8 = tb.immediate(8, self._sp.size)

    tmp0 = tb.temporal(self._sp.size)
    tmp1 = tb.temporal(self._sp.size)
    tmp2 = tb.temporal(self._sp.size + 8)

    tb.add(self._builder.gen_ldm(self._sp, tmp1))
    tb.add(self._builder.gen_add(self._sp, self._ws, tmp0))
    tb.add(self._builder.gen_str(tmp0, self._sp))

    # Free stack.
    if len(instruction.operands) > 0:
        oprnd0 = self._reg_acc_translator.read(tb, instruction.operands[0])

        imm0 = tb.immediate(oprnd0.immediate & (2 ** self._sp.size - 1), self._sp.size)

        tmp3 = tb.temporal(self._sp.size)

        tb.add(self._builder.gen_add(self._sp, imm0, tmp3))
        tb.add(self._builder.gen_str(tmp3, self._sp))

    tb.add(self._builder.gen_bsh(tmp1, imm8, tmp2))
    tb.add(self._builder.gen_jcc(imm1, tmp2))


# Auxiliary functions
# ============================================================================ #
def _translate_address(self, tb, oprnd):
    addr_oprnd_size = oprnd.size + 8

    if isinstance(oprnd, ReilRegisterOperand):
        oprnd_tmp = tb.temporal(addr_oprnd_size)
        addr_oprnd = tb.temporal(addr_oprnd_size)
        imm = ReilImmediateOperand(8, addr_oprnd_size)

        tb.add(self._builder.gen_str(oprnd, oprnd_tmp))
        tb.add(self._builder.gen_bsh(oprnd_tmp, imm, addr_oprnd))
    elif isinstance(oprnd, ReilImmediateOperand):
        addr_oprnd = ReilImmediateOperand(oprnd.immediate << 8, addr_oprnd_size)

    return addr_oprnd


def __get_jecxz_implicit_operand():
    oprnd = X86RegisterOperand('ecx', 32)

    return oprnd


def __get_loopcc_implicit_operand(arch_mode):
    if arch_mode == ARCH_X86_MODE_32:
        oprnd = X86RegisterOperand('ecx', 32)
    elif arch_mode == ARCH_X86_MODE_64:
        oprnd = X86RegisterOperand('rcx', 64)

    return oprnd


dispatcher = {
    'call': _translate_call,
    'ja': _translate_ja,
    'jae': _translate_jae,
    'jb': _translate_jb,
    'jbe': _translate_jbe,
    'jc': _translate_jc,
    'je': _translate_je,
    'jecxz': _translate_jecxz,
    'jg': _translate_jg,
    'jge': _translate_jge,
    'jl': _translate_jl,
    'jle': _translate_jle,
    'jmp': _translate_jmp,
    'jna': _translate_jna,
    'jnae': _translate_jnae,
    'jnb': _translate_jnb,
    'jnbe': _translate_jnbe,
    'jnc': _translate_jnc,
    'jne': _translate_jne,
    'jng': _translate_jng,
    'jnge': _translate_jnge,
    'jnl': _translate_jnl,
    'jnle': _translate_jnle,
    'jno': _translate_jno,
    'jnp': _translate_jnp,
    'jns': _translate_jns,
    'jnz': _translate_jnz,
    'jo': _translate_jo,
    'jp': _translate_jp,
    'jpe': _translate_jpe,
    'jpo': _translate_jpo,
    'js': _translate_js,
    'jz': _translate_jz,
    'loop': _translate_loop,
    'loope': _translate_loope,
    'loopne': _translate_loopne,
    'loopnz': _translate_loopnz,
    'loopz': _translate_loopz,
    'ret': _translate_ret,
}
