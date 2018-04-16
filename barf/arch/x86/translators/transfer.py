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

from barf.arch.translator import Label
from barf.arch.x86 import X86RegisterOperand
from barf.core.reil import ReilImmediateOperand
from barf.core.reil import ReilRegisterOperand


# "Data Transfer Instructions"
# ============================================================================ #
def _translate_bswap(self, tb, instruction):
    # Flags Affected
    # None.
    oprnd0 = tb.read(instruction.operands[0])

    dst = tb.temporal(oprnd0.size)

    tb.add(self._builder.gen_str(tb.immediate(0, dst.size), dst))

    for i in xrange(oprnd0.size / 8):
        t1 = tb.temporal(8)
        t2 = tb.temporal(oprnd0.size)
        t3 = tb.temporal(oprnd0.size)

        dst_new = tb.temporal(oprnd0.size)

        imm1 = tb.immediate(-(i * 8), oprnd0.size)
        imm2 = tb.immediate(8, oprnd0.size)

        tb.add(self._builder.gen_bsh(oprnd0, imm1, t1))
        tb.add(self._builder.gen_str(t1, t2))
        tb.add(self._builder.gen_bsh(dst, imm2, t3))
        tb.add(self._builder.gen_or(t3, t2, dst_new))

        dst = dst_new

    tb.write(instruction.operands[0], dst)


def _translate_cdq(self, tb, instruction):
    # Flags Affected
    # None.
    eax = X86RegisterOperand("eax", 32)
    edx = X86RegisterOperand("edx", 32)

    oprnd1 = tb.read(eax)

    tmp0 = tb.temporal(64)
    tmp1 = tb.temporal(32)
    imm32 = tb.immediate(-32, 64)

    tb.add(self._builder.gen_sext(oprnd1, tmp0))
    tb.add(self._builder.gen_bsh(tmp0, imm32, tmp1))

    tb.write(edx, tmp1)  # if in 64 bit mode, it zeros the upper half of rdx.


def _translate_cdqe(self, tb, instruction):
    # Flags Affected
    # None.
    oprnd1 = ReilRegisterOperand("eax", 32)
    oprnd2 = ReilRegisterOperand("rax", 64)

    tmp0 = tb.temporal(oprnd1.size)

    tb.add(self._builder.gen_sext(oprnd1, tmp0))
    tb.add(self._builder.gen_sext(tmp0, oprnd2))


def _translate_mov(self, tb, instruction):
    # Flags Affected
    # None.

    oprnd1 = tb.read(instruction.operands[1])

    # For cases such as: mov rax, rax
    tmp0 = tb.temporal(oprnd1.size)
    tb.add(self._builder.gen_str(oprnd1, tmp0))

    tb.write(instruction.operands[0], tmp0)


def _translate_movabs(self, tb, instruction):
    # Alias for mov with 64bit operands.

    _translate_mov(self, tb, instruction)


def _translate_movsx(self, tb, instruction):
    # Flags Affected
    # None.

    oprnd1 = tb.read(instruction.operands[1])

    tmp0 = tb.temporal(instruction.operands[0].size)

    tb.add(self._builder.gen_sext(oprnd1, tmp0))

    tb.write(instruction.operands[0], tmp0)


def _translate_movsxd(self, tb, instruction):
    # Flags Affected
    # None.

    _translate_movsx(self, tb, instruction)


def _translate_movzx(self, tb, instruction):
    # Flags Affected
    # None.

    oprnd1 = tb.read(instruction.operands[1])

    # For cases such as: movzx eax, al
    tmp0 = tb.temporal(oprnd1.size)
    tb.add(self._builder.gen_str(oprnd1, tmp0))

    tb.write(instruction.operands[0], tmp0)


def _translate_cmov(self, tb, instruction, cmov_cond):
    # Move if condition (cmov_cond) is met.
    # Flags Affected
    # None.

    eval_cond_fn_name = "_evaluate_" + cmov_cond
    eval_cond_fn = getattr(self, eval_cond_fn_name, None)

    if not eval_cond_fn:
        raise NotImplementedError("Instruction Not Implemented")

    # NOTE: CMOV pseudocode (not its description) specifies that in 32 bit registers, even
    # if the condition is not met, the high 32 bits of the destiny are set to zero (DEST[63:32] <- 0).
    # So op0 (dest) is assigned to itself, in 32 bits that doesn't change anything, in 64 it sets high bits
    # to zero. Then if the condition is met the mov is performed and the previous assignment has no effect.
    # op0 <- op0:
    oprnd0 = tb.read(instruction.operands[0])
    tmp = tb.temporal(oprnd0.size)
    tb.add(self._builder.gen_str(oprnd0, tmp))
    tb.write(instruction.operands[0], tmp)

    cmov_cond_not_met = Label('cmov_cond_not_met')

    neg_cond = tb._negate_reg(eval_cond_fn(tb))

    tb.add(self._builder.gen_jcc(neg_cond, cmov_cond_not_met))

    oprnd1 = tb.read(instruction.operands[1])

    tb.write(instruction.operands[0], oprnd1)

    tb.add(cmov_cond_not_met)
    tb.add(self._builder.gen_nop())


def _translate_cmova(self, tb, instruction):
    _translate_cmov(self, tb, instruction, 'a')


def _translate_cmovae(self, tb, instruction):
    _translate_cmov(self, tb, instruction, 'ae')


def _translate_cmovb(self, tb, instruction):
    _translate_cmov(self, tb, instruction, 'b')


def _translate_cmovbe(self, tb, instruction):
    _translate_cmov(self, tb, instruction, 'be')


def _translate_cmovc(self, tb, instruction):
    _translate_cmov(self, tb, instruction, 'c')


def _translate_cmove(self, tb, instruction):
    _translate_cmov(self, tb, instruction, 'e')


def _translate_cmovg(self, tb, instruction):
    _translate_cmov(self, tb, instruction, 'g')


def _translate_cmovge(self, tb, instruction):
    _translate_cmov(self, tb, instruction, 'ge')


def _translate_cmovl(self, tb, instruction):
    _translate_cmov(self, tb, instruction, 'l')


def _translate_cmovle(self, tb, instruction):
    _translate_cmov(self, tb, instruction, 'le')


def _translate_cmovna(self, tb, instruction):
    _translate_cmov(self, tb, instruction, 'na')


def _translate_cmovnae(self, tb, instruction):
    _translate_cmov(self, tb, instruction, 'nae')


def _translate_cmovnb(self, tb, instruction):
    _translate_cmov(self, tb, instruction, 'nb')


def _translate_cmovnbe(self, tb, instruction):
    _translate_cmov(self, tb, instruction, 'nbe')


def _translate_cmovnc(self, tb, instruction):
    _translate_cmov(self, tb, instruction, 'nc')


def _translate_cmovne(self, tb, instruction):
    _translate_cmov(self, tb, instruction, 'ne')


def _translate_cmovng(self, tb, instruction):
    _translate_cmov(self, tb, instruction, 'ng')


def _translate_cmovnge(self, tb, instruction):
    _translate_cmov(self, tb, instruction, 'nge')


def _translate_cmovnl(self, tb, instruction):
    _translate_cmov(self, tb, instruction, 'nl')


def _translate_cmovnle(self, tb, instruction):
    _translate_cmov(self, tb, instruction, 'nle')


def _translate_cmovno(self, tb, instruction):
    _translate_cmov(self, tb, instruction, 'no')


def _translate_cmovnp(self, tb, instruction):
    _translate_cmov(self, tb, instruction, 'np')


def _translate_cmovns(self, tb, instruction):
    _translate_cmov(self, tb, instruction, 'ns')


def _translate_cmovnz(self, tb, instruction):
    _translate_cmov(self, tb, instruction, 'nz')


def _translate_cmovo(self, tb, instruction):
    _translate_cmov(self, tb, instruction, 'o')


def _translate_cmovp(self, tb, instruction):
    _translate_cmov(self, tb, instruction, 'p')


def _translate_cmovpe(self, tb, instruction):
    _translate_cmov(self, tb, instruction, 'pe')


def _translate_cmovpo(self, tb, instruction):
    _translate_cmov(self, tb, instruction, 'po')


def _translate_cmovs(self, tb, instruction):
    _translate_cmov(self, tb, instruction, 's')


def _translate_cmovz(self, tb, instruction):
    _translate_cmov(self, tb, instruction, 'z')


def _translate_set(self, tb, instruction, set_cond):
    # Set if condition (set_cond) is met.
    # Flags Affected
    # None.

    eval_cond_fn_name = "_evaluate_" + set_cond
    eval_cond_fn = getattr(self, eval_cond_fn_name, None)

    if not eval_cond_fn:
        raise NotImplementedError("Instruction Not Implemented")

    tb.write(instruction.operands[0], tb.immediate(0, 1))

    set_cond_not_met = Label('set_cond_not_met')

    neg_cond = tb._negate_reg(eval_cond_fn(tb))

    tb.add(self._builder.gen_jcc(neg_cond, set_cond_not_met))

    tb.write(instruction.operands[0], tb.immediate(1, 1))

    tb.add(set_cond_not_met)
    tb.add(self._builder.gen_nop())


def _translate_seta(self, tb, instruction):
    _translate_set(self, tb, instruction, 'a')


def _translate_setae(self, tb, instruction):
    _translate_set(self, tb, instruction, 'ae')


def _translate_setb(self, tb, instruction):
    _translate_set(self, tb, instruction, 'b')


def _translate_setbe(self, tb, instruction):
    _translate_set(self, tb, instruction, 'be')


def _translate_setc(self, tb, instruction):
    _translate_set(self, tb, instruction, 'c')


def _translate_sete(self, tb, instruction):
    _translate_set(self, tb, instruction, 'e')


def _translate_setg(self, tb, instruction):
    _translate_set(self, tb, instruction, 'g')


def _translate_setge(self, tb, instruction):
    _translate_set(self, tb, instruction, 'ge')


def _translate_setl(self, tb, instruction):
    _translate_set(self, tb, instruction, 'l')


def _translate_setle(self, tb, instruction):
    _translate_set(self, tb, instruction, 'le')


def _translate_setna(self, tb, instruction):
    _translate_set(self, tb, instruction, 'na')


def _translate_setnae(self, tb, instruction):
    _translate_set(self, tb, instruction, 'nae')


def _translate_setnb(self, tb, instruction):
    _translate_set(self, tb, instruction, 'nb')


def _translate_setnbe(self, tb, instruction):
    _translate_set(self, tb, instruction, 'nbe')


def _translate_setnc(self, tb, instruction):
    _translate_set(self, tb, instruction, 'nc')


def _translate_setne(self, tb, instruction):
    _translate_set(self, tb, instruction, 'ne')


def _translate_setng(self, tb, instruction):
    _translate_set(self, tb, instruction, 'ng')


def _translate_setnge(self, tb, instruction):
    _translate_set(self, tb, instruction, 'nge')


def _translate_setnl(self, tb, instruction):
    _translate_set(self, tb, instruction, 'nl')


def _translate_setnle(self, tb, instruction):
    _translate_set(self, tb, instruction, 'nle')


def _translate_setno(self, tb, instruction):
    _translate_set(self, tb, instruction, 'no')


def _translate_setnp(self, tb, instruction):
    _translate_set(self, tb, instruction, 'np')


def _translate_setns(self, tb, instruction):
    _translate_set(self, tb, instruction, 'ns')


def _translate_setnz(self, tb, instruction):
    _translate_set(self, tb, instruction, 'nz')


def _translate_seto(self, tb, instruction):
    _translate_set(self, tb, instruction, 'o')


def _translate_setp(self, tb, instruction):
    _translate_set(self, tb, instruction, 'p')


def _translate_setpe(self, tb, instruction):
    _translate_set(self, tb, instruction, 'pe')


def _translate_setpo(self, tb, instruction):
    _translate_set(self, tb, instruction, 'po')


def _translate_sets(self, tb, instruction):
    _translate_set(self, tb, instruction, 's')


def _translate_setz(self, tb, instruction):
    _translate_set(self, tb, instruction, 'z')


def _translate_xchg(self, tb, instruction):
    # Flags Affected
    # None.

    oprnd0 = tb.read(instruction.operands[0])
    oprnd1 = tb.read(instruction.operands[1])

    tmp0 = tb.temporal(oprnd1.size)

    tb.add(self._builder.gen_str(oprnd0, tmp0))

    tb.write(instruction.operands[0], oprnd1)
    tb.write(instruction.operands[1], tmp0)


def _translate_push(self, tb, instruction):
    # Flags Affected
    # None.

    oprnd0 = tb.read(instruction.operands[0])

    tmp0 = tb.temporal(self._sp.size)

    tb.add(self._builder.gen_sub(self._sp, self._ws, tmp0))
    tb.add(self._builder.gen_str(tmp0, self._sp))
    tb.add(self._builder.gen_stm(oprnd0, self._sp))


def _translate_pop(self, tb, instruction):
    # Flags Affected
    # None.

    oprnd0 = tb.read(instruction.operands[0])

    tmp0 = tb.temporal(self._sp.size)

    tb.add(self._builder.gen_ldm(self._sp, oprnd0))
    tb.add(self._builder.gen_add(self._sp, self._ws, tmp0))
    tb.add(self._builder.gen_str(tmp0, self._sp))


def _translate_cmpxchg(self, tb, instruction):
    # Flags Affected
    # The ZF flag is set if the values in the destination operand
    # and register AL, AX, or EAX are equal; otherwise it is
    # cleared. The CF, PF, AF, SF, and OF flags are set according
    # to the results of the comparison operation.

    # Accumulator = AL, AX, EAX, or RAX depending on whether a byte,
    # word, doubleword, or quadword comparison is being performed
    # IF accumulator = DEST
    # THEN
    #   ZF <- 1;
    #   DEST <- SRC;
    # ELSE
    #   ZF <- 0;
    #   accumulator <- DEST;
    # FI;

    oprnd0 = tb.read(instruction.operands[0])
    oprnd1 = tb.read(instruction.operands[1])

    # Define immediate registers
    end_addr = ReilImmediateOperand((instruction.address + instruction.size) << 8, self._arch_info.address_size + 8)

    # Define accum register.
    if oprnd0.size == 8:
        accum = ReilRegisterOperand("al", 8)
        accum_x86 = X86RegisterOperand("al", 8)
    elif oprnd0.size == 16:
        accum = ReilRegisterOperand("ax", 16)
        accum_x86 = X86RegisterOperand("ax", 16)
    elif oprnd0.size == 32:
        accum = ReilRegisterOperand("eax", 32)
        accum_x86 = X86RegisterOperand("eax", 32)
    elif oprnd0.size == 64:
        accum = ReilRegisterOperand("rax", 64)
        accum_x86 = X86RegisterOperand("rax", 64)
    else:
        raise Exception("Invalid operand size: %s" % oprnd0)

    tmp0 = tb.temporal(oprnd0.size * 2)

    one = tb.immediate(1, 1)

    change_dst_lbl = Label('change_dst')
    change_accum_lbl = Label('change_accum')

    # Compare.
    tb.add(self._builder.gen_sub(accum, oprnd0, tmp0))

    # Update flags : CF, OF, SF, ZF, AF, PF
    self._update_cf(tb, accum, oprnd0, tmp0)
    self._update_of_sub(tb, accum, oprnd0, tmp0)
    self._update_sf(tb, accum, oprnd0, tmp0)
    self._update_zf(tb, accum, oprnd0, tmp0)
    self._update_af_sub(tb, accum, oprnd0, tmp0)
    self._update_pf(tb, accum, oprnd0, tmp0)

    # Exchange
    tb.add(self._builder.gen_jcc(tmp0, change_accum_lbl))
    tb.add(change_dst_lbl)
    tb.write(instruction.operands[0], oprnd1)
    tb.add(self._builder.gen_jcc(one, end_addr))
    tb.add(change_accum_lbl)
    # tb.add(self._builder.gen_str(oprnd0, accum))
    tb.write(accum_x86, oprnd0)


def _translate_xadd(self, tb, instruction):
    # Flags Affected
    # The CF, PF, AF, SF, ZF, and OF flags are set according to the
    # result of the addition, which is stored in the destination
    # operand.

    # Operation
    # TEMP <- SRC + DEST;
    # SRC <- DEST;
    # DEST <- TEMP;

    oprnd0 = tb.read(instruction.operands[0])
    oprnd1 = tb.read(instruction.operands[1])

    tmp0 = tb.temporal(oprnd0.size * 2)

    tb.add(self._builder.gen_add(oprnd0, oprnd1, tmp0))

    # Flags : OF, SF, ZF, AF, CF, PF
    self._update_of(tb, oprnd0, oprnd1, tmp0)
    self._update_sf(tb, oprnd0, oprnd1, tmp0)
    self._update_zf(tb, oprnd0, oprnd1, tmp0)
    self._update_af(tb, oprnd0, oprnd1, tmp0)
    self._update_cf(tb, oprnd0, oprnd1, tmp0)
    self._update_pf(tb, oprnd0, oprnd1, tmp0)

    tb.write(instruction.operands[0], tmp0)
    tb.write(instruction.operands[1], oprnd0)


dispatcher = {
    'bswap': _translate_bswap,
    'cdq': _translate_cdq,
    'cdqe': _translate_cdqe,
    'mov': _translate_mov,
    'movabs': _translate_movabs,
    'movsx': _translate_movsx,
    'movsxd': _translate_movsxd,
    'movzx': _translate_movzx,
    'cmov': _translate_cmov,
    'cmova': _translate_cmova,
    'cmovae': _translate_cmovae,
    'cmovb': _translate_cmovb,
    'cmovbe': _translate_cmovbe,
    'cmovc': _translate_cmovc,
    'cmove': _translate_cmove,
    'cmovg': _translate_cmovg,
    'cmovge': _translate_cmovge,
    'cmovl': _translate_cmovl,
    'cmovle': _translate_cmovle,
    'cmovna': _translate_cmovna,
    'cmovnae': _translate_cmovnae,
    'cmovnb': _translate_cmovnb,
    'cmovnbe': _translate_cmovnbe,
    'cmovnc': _translate_cmovnc,
    'cmovne': _translate_cmovne,
    'cmovng': _translate_cmovng,
    'cmovnge': _translate_cmovnge,
    'cmovnl': _translate_cmovnl,
    'cmovnle': _translate_cmovnle,
    'cmovno': _translate_cmovno,
    'cmovnp': _translate_cmovnp,
    'cmovns': _translate_cmovns,
    'cmovnz': _translate_cmovnz,
    'cmovo': _translate_cmovo,
    'cmovp': _translate_cmovp,
    'cmovpe': _translate_cmovpe,
    'cmovpo': _translate_cmovpo,
    'cmovs': _translate_cmovs,
    'cmovz': _translate_cmovz,
    'set': _translate_set,
    'seta': _translate_seta,
    'setae': _translate_setae,
    'setb': _translate_setb,
    'setbe': _translate_setbe,
    'setc': _translate_setc,
    'sete': _translate_sete,
    'setg': _translate_setg,
    'setge': _translate_setge,
    'setl': _translate_setl,
    'setle': _translate_setle,
    'setna': _translate_setna,
    'setnae': _translate_setnae,
    'setnb': _translate_setnb,
    'setnbe': _translate_setnbe,
    'setnc': _translate_setnc,
    'setne': _translate_setne,
    'setng': _translate_setng,
    'setnge': _translate_setnge,
    'setnl': _translate_setnl,
    'setnle': _translate_setnle,
    'setno': _translate_setno,
    'setnp': _translate_setnp,
    'setns': _translate_setns,
    'setnz': _translate_setnz,
    'seto': _translate_seto,
    'setp': _translate_setp,
    'setpe': _translate_setpe,
    'setpo': _translate_setpo,
    'sets': _translate_sets,
    'setz': _translate_setz,
    'xchg': _translate_xchg,
    'push': _translate_push,
    'pop': _translate_pop,
    'cmpxchg': _translate_cmpxchg,
    'xadd': _translate_xadd,
}
