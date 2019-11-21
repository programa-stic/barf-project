# Copyright (c) 2019, Fundacion Dr. Manuel Sadosky
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

from barf.arch.arm import ARM_COND_CODE_AL
from barf.arch.arm import ARM_COND_CODE_CC
from barf.arch.arm import ARM_COND_CODE_CS
from barf.arch.arm import ARM_COND_CODE_EQ
from barf.arch.arm import ARM_COND_CODE_GE
from barf.arch.arm import ARM_COND_CODE_GT
from barf.arch.arm import ARM_COND_CODE_HI
from barf.arch.arm import ARM_COND_CODE_HS
from barf.arch.arm import ARM_COND_CODE_LE
from barf.arch.arm import ARM_COND_CODE_LO
from barf.arch.arm import ARM_COND_CODE_LS
from barf.arch.arm import ARM_COND_CODE_LT
from barf.arch.arm import ARM_COND_CODE_MI
from barf.arch.arm import ARM_COND_CODE_NE
from barf.arch.arm import ARM_COND_CODE_PL
from barf.arch.arm import ARM_COND_CODE_VC
from barf.arch.arm import ARM_COND_CODE_VS
from barf.arch.helper import and_regs
from barf.arch.helper import equal_regs
from barf.arch.helper import negate_reg
from barf.arch.helper import or_regs


def compare_contexts(context_init, arm_context, reil_context):
    match = True
    mask = 2**32-1

    for reg in sorted(context_init.keys()):
        if (arm_context[reg] & mask) != (reil_context[reg] & mask):
            match = False
            break

    return match


def print_contexts(context_init, arm_context, reil_context):
    header_fmt = " {0:^8s} : {1:^16s} | {2:>16s} ?= {3:<16s}\n"
    header = header_fmt.format("Register", "Initial", "ARM", "REIL")
    ruler = "-" * len(header) + "\n"

    out = header
    out += ruler

    fmt = " {0:>8s} : {1:08x} | {2:08x} {eq} {3:08x} {marker}\n"

    mask = 2**64-1

    for reg in sorted(context_init.keys()):
        if (arm_context[reg] & mask) != (reil_context[reg] & mask):
            eq, marker = "!=", "<"
        else:
            eq, marker = "==", ""

        out += fmt.format(
            reg,
            context_init[reg] & mask,
            arm_context[reg] & mask,
            reil_context[reg] & mask,
            eq=eq,
            marker=marker
        )

    # Pretty print flags.
    fmt = "{0:s} ({1:>4s}) : {2:08x} ({3:s})"

    reg = "apsr"

    arm_value = arm_context[reg] & mask
    reil_value = reil_context[reg] & mask

    if arm_value != reil_value:
        arm_flags_str = print_flags(arm_context[reg])
        reil_flags_str = print_flags(reil_context[reg])

        out += "\n"
        out += fmt.format(reg, "ARM", arm_value, arm_flags_str) + "\n"
        out += fmt.format(reg, "reil", reil_value, reil_flags_str)

    return out


def print_flags(flags_reg):
    # flags
    flags = {
         31: "nf",  # bit 31
         30: "zf",  # bit 30
         29: "cf",  # bit 29
         28: "vf",  # bit 28
    }

    out = ""

    for bit, flag in flags.items():
        flag_str = flag.upper() if flags_reg & 2**bit else flag.lower()
        out += flag_str + " "

    return out[:-1]


class ArmConditionCodeHelper(object):

    @staticmethod
    def evaluate_cond_code(flags, tb, condition_code):
        dispatcher = {
            ARM_COND_CODE_AL: ArmConditionCodeHelper.evaluate_al,
            ARM_COND_CODE_CC: ArmConditionCodeHelper.evaluate_cc,
            ARM_COND_CODE_CS: ArmConditionCodeHelper.evaluate_cs,
            ARM_COND_CODE_EQ: ArmConditionCodeHelper.evaluate_eq,
            ARM_COND_CODE_GE: ArmConditionCodeHelper.evaluate_ge,
            ARM_COND_CODE_GT: ArmConditionCodeHelper.evaluate_gt,
            ARM_COND_CODE_HI: ArmConditionCodeHelper.evaluate_hi,
            ARM_COND_CODE_HS: ArmConditionCodeHelper.evaluate_cs,
            ARM_COND_CODE_LE: ArmConditionCodeHelper.evaluate_le,
            ARM_COND_CODE_LO: ArmConditionCodeHelper.evaluate_cc,
            ARM_COND_CODE_LS: ArmConditionCodeHelper.evaluate_ls,
            ARM_COND_CODE_LT: ArmConditionCodeHelper.evaluate_lt,
            ARM_COND_CODE_MI: ArmConditionCodeHelper.evaluate_mi,
            ARM_COND_CODE_NE: ArmConditionCodeHelper.evaluate_ne,
            ARM_COND_CODE_PL: ArmConditionCodeHelper.evaluate_pl,
            ARM_COND_CODE_VC: ArmConditionCodeHelper.evaluate_vc,
            ARM_COND_CODE_VS: ArmConditionCodeHelper.evaluate_vs,
        }

        try:
            eval_cond_fn = dispatcher[condition_code]
        except KeyError:
            raise Exception('Invalid condition code')

        return eval_cond_fn(flags, tb)

    @staticmethod
    def evaluate_al(flags, tb):
        return tb.immediate(1, 1)

    @staticmethod
    def evaluate_eq(flags, tb):
        # EQ: Z set
        return flags.zf

    @staticmethod
    def evaluate_ne(flags, tb):
        # NE: Z clear
        return negate_reg(tb, flags.zf)

    @staticmethod
    def evaluate_cs(flags, tb):
        # CS: C set
        return flags.cf

    @staticmethod
    def evaluate_cc(flags, tb):
        # CC: C clear
        return negate_reg(tb, flags.cf)

    @staticmethod
    def evaluate_mi(flags, tb):
        # MI: N set
        return flags.nf

    @staticmethod
    def evaluate_pl(flags, tb):
        # PL: N clear
        return negate_reg(tb, flags.nf)

    @staticmethod
    def evaluate_vs(flags, tb):
        # VS: V set
        return flags.vf

    @staticmethod
    def evaluate_vc(flags, tb):
        # VC: V clear
        return negate_reg(tb, flags.vf)

    @staticmethod
    def evaluate_hi(flags, tb):
        # HI: C set and Z clear
        return and_regs(tb, flags.cf, negate_reg(tb, flags.zf))

    @staticmethod
    def evaluate_ls(flags, tb):
        # LS: C clear or Z set
        return or_regs(tb, negate_reg(tb, flags.cf), flags.zf)

    @staticmethod
    def evaluate_ge(flags, tb):
        # GE: N == V
        return equal_regs(tb, flags.nf, flags.vf)

    @staticmethod
    def evaluate_lt(flags, tb):
        # LT: N != V
        return negate_reg(tb, ArmConditionCodeHelper.evaluate_ge(flags, tb))

    @staticmethod
    def evaluate_gt(flags, tb):
        # GT: (Z == 0) and (N == V)
        return and_regs(tb, negate_reg(tb, flags.zf), ArmConditionCodeHelper.evaluate_ge(flags, tb))

    @staticmethod
    def evaluate_le(flags, tb):
        # LE: (Z == 1) or (N != V)
        return or_regs(tb, flags.zf, ArmConditionCodeHelper.evaluate_lt(flags, tb))
