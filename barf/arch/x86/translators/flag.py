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

from barf.arch.x86 import X86RegisterOperand


# "Flag Control (EFLAG) Instructions"
# ============================================================================ #
def _translate_clc(self, tb, instruction):
    # Flags Affected
    # The CF flag is set to 0. The OF, ZF, SF, AF, and PF flags are
    # unaffected.

    self._flag_translator.clear_flag(tb, self._flags.cf)


def _translate_cld(self, tb, instruction):
    # Flags Affected
    # The DF flag is set to 0. The CF, OF, ZF, SF, AF, and PF flags
    # are unaffected.

    self._flag_translator.clear_flag(tb, self._flags.df)


def _translate_lahf(self, tb, instruction):
    # Operation
    # IF 64-Bit Mode
    #   THEN
    #       IF CPUID.80000001H:ECX.LAHF-SAHF[bit 0] = 1;
    #           THEN AH <- RFLAGS(SF:ZF:0:AF:0:PF:1:CF);
    #       ELSE #UD;
    #       FI;
    #   ELSE
    #       AH <- EFLAGS(SF:ZF:0:AF:0:PF:1:CF);
    # FI;

    # Flags Affected
    # None. The state of the flags in the EFLAGS register is not affected.

    oprnd0_x86 = __get_lahf_implicit_operand()

    dst = tb.temporal(8)

    tmp1 = tb.temporal(dst.size)

    shl_one = tb.immediate(1, 8)

    tb.add(self._builder.gen_str(tb.immediate(0, 8), dst))

    # Store SF.
    tb.add(self._builder.gen_str(self._flags.sf, tmp1))
    tb.add(self._builder.gen_or(tmp1, dst, dst))
    # Shift left.
    tb.add(self._builder.gen_bsh(dst, shl_one, dst))

    # Store ZF.
    tb.add(self._builder.gen_str(self._flags.zf, tmp1))
    tb.add(self._builder.gen_or(tmp1, dst, dst))
    # Shift left.
    tb.add(self._builder.gen_bsh(dst, shl_one, dst))

    # Store 0.
    tb.add(self._builder.gen_str(tb.immediate(0, 8), tmp1))
    tb.add(self._builder.gen_or(tmp1, dst, dst))
    # Shift left.
    tb.add(self._builder.gen_bsh(dst, shl_one, dst))

    # Store AF.
    tb.add(self._builder.gen_str(self._flags.af, tmp1))
    tb.add(self._builder.gen_or(tmp1, dst, dst))
    # Shift left.
    tb.add(self._builder.gen_bsh(dst, shl_one, dst))

    # Store 0.
    tb.add(self._builder.gen_str(tb.immediate(0, 8), tmp1))
    tb.add(self._builder.gen_or(tmp1, dst, dst))
    # Shift left.
    tb.add(self._builder.gen_bsh(dst, shl_one, dst))

    # Store PF.
    tb.add(self._builder.gen_str(self._flags.pf, tmp1))
    tb.add(self._builder.gen_or(tmp1, dst, dst))
    # Shift left.
    tb.add(self._builder.gen_bsh(dst, shl_one, dst))

    # Store 1.
    tb.add(self._builder.gen_str(tb.immediate(1, 8), tmp1))
    tb.add(self._builder.gen_or(tmp1, dst, dst))
    # Shift left.
    tb.add(self._builder.gen_bsh(dst, shl_one, dst))

    # Store CF.
    tb.add(self._builder.gen_str(self._flags.cf, tmp1))
    tb.add(self._builder.gen_or(tmp1, dst, dst))

    self._reg_acc_translator.write(tb, oprnd0_x86, dst)


def _translate_sahf(self, tb, instruction):
    # Flags Affected
    # The SF, ZF, AF, PF, and CF flags are loaded with values from
    # the AH register. Bits 1, 3, and 5 of the EFLAGS register are
    # unaffected, with the values remaining 1, 0, and 0,
    # respectively.

    oprnd0 = self._reg_acc_translator.read(tb, __get_sahf_implicit_operand())

    tmp0 = tb.temporal(oprnd0.size)
    tmp1 = tb.temporal(oprnd0.size)
    tmp2 = tb.temporal(oprnd0.size)
    tmp3 = tb.temporal(oprnd0.size)

    shl_two = tb.immediate(-2, 8)
    shl_one = tb.immediate(-1, 8)

    tb.add(self._builder.gen_str(oprnd0, self._flags.cf))
    tb.add(self._builder.gen_bsh(oprnd0, shl_two, tmp0))

    tb.add(self._builder.gen_str(tmp0, self._flags.pf))
    tb.add(self._builder.gen_bsh(tmp0, shl_two, tmp1))

    tb.add(self._builder.gen_str(tmp1, self._flags.af))
    tb.add(self._builder.gen_bsh(tmp1, shl_two, tmp2))

    tb.add(self._builder.gen_str(tmp2, self._flags.zf))
    tb.add(self._builder.gen_bsh(tmp2, shl_one, tmp3))

    tb.add(self._builder.gen_str(tmp3, self._flags.sf))


def _translate_popf(self, tb, instruction):
    # Flags Affected
    # All flags may be affected; see the Operation section for
    # details.

    tmp1 = tb.temporal(self._sp.size)

    shl_one = tb.immediate(-1, self._sp.size)
    shl_two = tb.immediate(-2, self._sp.size)
    shl_three = tb.immediate(-3, self._sp.size)

    tmp0 = tb.temporal(self._sp.size)

    tb.add(self._builder.gen_ldm(self._sp, tmp1))
    tb.add(self._builder.gen_add(self._sp, self._ws, tmp0))
    tb.add(self._builder.gen_str(tmp0, self._sp))

    tb.add(self._builder.gen_str(tmp1, self._flags.cf))
    tb.add(self._builder.gen_bsh(tmp1, shl_two, tmp1))
    tb.add(self._builder.gen_str(tmp1, self._flags.pf))
    tb.add(self._builder.gen_bsh(tmp1, shl_two, tmp1))
    tb.add(self._builder.gen_str(tmp1, self._flags.af))
    tb.add(self._builder.gen_bsh(tmp1, shl_two, tmp1))
    tb.add(self._builder.gen_str(tmp1, self._flags.zf))
    tb.add(self._builder.gen_bsh(tmp1, shl_one, tmp1))
    tb.add(self._builder.gen_str(tmp1, self._flags.sf))
    tb.add(self._builder.gen_bsh(tmp1, shl_three, tmp1))
    tb.add(self._builder.gen_str(tmp1, self._flags.df))
    tb.add(self._builder.gen_bsh(tmp1, shl_one, tmp1))
    tb.add(self._builder.gen_str(tmp1, self._flags.of))


def _translate_popfd(self, tb, instruction):
    # Flags Affected
    # None.

    _translate_popf(self, tb, instruction)


def _translate_popfq(self, tb, instruction):
    # Flags Affected
    # None.

    _translate_popf(self, tb, instruction)


def _translate_pushf(self, tb, instruction):
    # Flags Affected
    # None.

    tmp0 = tb.temporal(self._sp.size)
    tmp1 = tb.temporal(self._sp.size)

    shr_one = tb.immediate(1, self._sp.size)
    shr_two = tb.immediate(2, self._sp.size)
    shr_three = tb.immediate(3, self._sp.size)

    tb.add(self._builder.gen_str(self._flags.of, tmp1))
    tb.add(self._builder.gen_bsh(tmp1, shr_one, tmp1))
    tb.add(self._builder.gen_str(self._flags.df, tmp1))
    tb.add(self._builder.gen_bsh(tmp1, shr_three, tmp1))
    tb.add(self._builder.gen_str(self._flags.sf, tmp1))
    tb.add(self._builder.gen_bsh(tmp1, shr_one, tmp1))
    tb.add(self._builder.gen_str(self._flags.zf, tmp1))
    tb.add(self._builder.gen_bsh(tmp1, shr_two, tmp1))
    tb.add(self._builder.gen_str(self._flags.af, tmp1))
    tb.add(self._builder.gen_bsh(tmp1, shr_two, tmp1))
    tb.add(self._builder.gen_str(self._flags.pf, tmp1))
    tb.add(self._builder.gen_bsh(tmp1, shr_two, tmp1))
    tb.add(self._builder.gen_str(self._flags.cf, tmp1))

    tb.add(self._builder.gen_sub(self._sp, self._ws, tmp0))
    tb.add(self._builder.gen_str(tmp0, self._sp))
    tb.add(self._builder.gen_stm(tmp1, self._sp))


def _translate_pushfd(self, tb, instruction):
    # Flags Affected
    # None.

    _translate_pushf(self, tb, instruction)


def _translate_pushfq(self, tb, instruction):
    # Flags Affected
    # None.

    _translate_pushf(self, tb, instruction)


def _translate_stc(self, tb, instruction):
    # Flags Affected
    # The CF flag is set. The OF, ZF, SF, AF, and PF flags are
    # unaffected.

    self._flag_translator.set_flag(tb, self._flags.cf)


def _translate_std(self, tb, instruction):
    # Flags Affected
    # The DF flag is set. The CF, OF, ZF, SF, AF, and PF flags are
    # unaffected.

    self._flag_translator.set_flag(tb, self._flags.df)


# Auxiliary functions
# ============================================================================ #
def __get_lahf_implicit_operand():
    return X86RegisterOperand('ah', 8)


def __get_sahf_implicit_operand():
    return X86RegisterOperand('ah', 8)


dispatcher = {
    'clc': _translate_clc,
    'cld': _translate_cld,
    'lahf': _translate_lahf,
    'popf': _translate_popf,
    'popfd': _translate_popfd,
    'popfq': _translate_popfq,
    'pushf': _translate_pushf,
    'pushfd': _translate_pushfd,
    'pushfq': _translate_pushfq,
    'sahf': _translate_sahf,
    'stc': _translate_stc,
    'std': _translate_std,
}
