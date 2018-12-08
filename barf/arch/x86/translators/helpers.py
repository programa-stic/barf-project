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

from barf.arch.helper import and_regs
from barf.arch.helper import equal_regs
from barf.arch.helper import negate_reg
from barf.arch.helper import or_regs
from barf.arch.helper import unequal_regs


class X86ConditionCodeHelper(object):

    @staticmethod
    def evaluate_cc(flags, tb, condition_code):
        eval_cond_fn_name = 'evaluate_' + condition_code
        eval_cond_fn = getattr(X86ConditionCodeHelper, eval_cond_fn_name, None)

        if not eval_cond_fn:
            raise NotImplementedError('Invalid condition code')

        return eval_cond_fn(flags, tb)

    @staticmethod
    def evaluate_a(flags, tb):
        # above (CF=0 and ZF=0)
        return and_regs(tb, negate_reg(tb, flags.cf),
                        negate_reg(tb, flags.zf))

    @staticmethod
    def evaluate_ae(flags, tb):
        # above or equal (CF=0)
        return negate_reg(tb, flags.cf)

    @staticmethod
    def evaluate_b(flags, tb):
        # below (CF=1)
        return flags.cf

    @staticmethod
    def evaluate_be(flags, tb):
        # below or equal (CF=1 or ZF=1)
        return or_regs(tb, flags.cf, flags.zf)

    @staticmethod
    def evaluate_c(flags, tb):
        # carry (CF=1)
        return flags.cf

    @staticmethod
    def evaluate_e(flags, tb):
        # equal (ZF=1)
        return flags.zf

    @staticmethod
    def evaluate_g(flags, tb):
        # greater (ZF=0 and SF=OF)
        return and_regs(tb, negate_reg(tb, flags.zf),
                        equal_regs(tb, flags.sf, flags.of))

    @staticmethod
    def evaluate_ge(flags, tb):
        # greater or equal (SF=OF)
        return equal_regs(tb, flags.sf, flags.of)

    @staticmethod
    def evaluate_l(flags, tb):
        # less (SF != OF)
        return unequal_regs(tb, flags.sf, flags.of)

    @staticmethod
    def evaluate_le(flags, tb):
        # less or equal (ZF=1 or SF != OF)
        return or_regs(tb, flags.zf,
                       unequal_regs(tb, flags.sf, flags.of))

    @staticmethod
    def evaluate_na(flags, tb):
        # not above (CF=1 or ZF=1).
        return or_regs(tb, flags.cf, flags.zf)

    @staticmethod
    def evaluate_nae(flags, tb):
        # not above or equal (CF=1)
        return flags.cf

    @staticmethod
    def evaluate_nb(flags, tb):
        # not below (CF=0)
        return negate_reg(tb, flags.cf)

    @staticmethod
    def evaluate_nbe(flags, tb):
        # not below or equal (CF=0 and ZF=0)
        return and_regs(tb, negate_reg(tb, flags.cf),
                        negate_reg(tb, flags.zf))

    @staticmethod
    def evaluate_nc(flags, tb):
        # not carry (CF=0)
        return negate_reg(tb, flags.cf)

    @staticmethod
    def evaluate_ne(flags, tb):
        # not equal (ZF=0)
        return negate_reg(tb, flags.zf)

    @staticmethod
    def evaluate_ng(flags, tb):
        # not greater (ZF=1 or SF != OF)
        return or_regs(tb, flags.zf,
                       unequal_regs(tb, flags.sf, flags.of))

    @staticmethod
    def evaluate_nge(flags, tb):
        # not greater or equal (SF != OF)
        return unequal_regs(tb, flags.sf, flags.of)

    @staticmethod
    def evaluate_nl(flags, tb):
        # not less (SF=OF)
        return equal_regs(tb, flags.sf, flags.of)

    @staticmethod
    def evaluate_nle(flags, tb):
        # not less or equal (ZF=0 and SF=OF)
        return and_regs(tb, negate_reg(tb, flags.zf),
                        equal_regs(tb, flags.sf, flags.of))

    @staticmethod
    def evaluate_no(flags, tb):
        # not overflow (OF=0)
        return negate_reg(tb, flags.of)

    @staticmethod
    def evaluate_np(flags, tb):
        # not parity (PF=0)
        return negate_reg(tb, flags.pf)

    @staticmethod
    def evaluate_ns(flags, tb):
        # not sign (SF=0)
        return negate_reg(tb, flags.sf)

    @staticmethod
    def evaluate_nz(flags, tb):
        # not zero (ZF=0)
        return negate_reg(tb, flags.zf)

    @staticmethod
    def evaluate_o(flags, tb):
        # overflow (OF=1)
        return flags.of

    @staticmethod
    def evaluate_p(flags, tb):
        # parity (PF=1)
        return flags.pf

    @staticmethod
    def evaluate_pe(flags, tb):
        # parity even (PF=1)
        return flags.pf

    @staticmethod
    def evaluate_po(flags, tb):
        # parity odd (PF=0)
        return negate_reg(tb, flags.pf)

    @staticmethod
    def evaluate_s(flags, tb):
        # sign (SF=1)
        return flags.sf

    @staticmethod
    def evaluate_z(flags, tb):
        # zero (ZF=1)
        return flags.zf
