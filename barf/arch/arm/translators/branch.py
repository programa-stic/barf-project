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
from barf.arch.arm import ArmImmediateOperand
from barf.arch.arm import ArmRegisterOperand
from barf.core.reil import ReilImmediateOperand
from barf.core.reil import ReilRegisterOperand


# "Branch Instructions"
# ============================================================================ #
def _translate_b(self, tb, instruction):
    _translate_branch(self, tb, instruction, link=False)


def _translate_bl(self, tb, instruction):
    _translate_branch(self, tb, instruction, link=True)


# TODO: Thumb
def _translate_bx(self, tb, instruction):
    _translate_branch(self, tb, instruction, link=False)


def _translate_blx(self, tb, instruction):
    _translate_branch(self, tb, instruction, link=True)


def _translate_bne(self, tb, instruction):
    _translate_branch(self, tb, instruction, link=False)


def _translate_beq(self, tb, instruction):
    _translate_branch(self, tb, instruction, link=False)


def _translate_bpl(self, tb, instruction):
    _translate_branch(self, tb, instruction, link=False)


def _translate_ble(self, tb, instruction):
    _translate_branch(self, tb, instruction, link=False)


def _translate_bcs(self, tb, instruction):
    _translate_branch(self, tb, instruction, link=False)


def _translate_bhs(self, tb, instruction):
    _translate_branch(self, tb, instruction, link=False)


def _translate_blt(self, tb, instruction):
    _translate_branch(self, tb, instruction, link=False)


def _translate_bge(self, tb, instruction):
    _translate_branch(self, tb, instruction, link=False)


def _translate_bhi(self, tb, instruction):
    _translate_branch(self, tb, instruction, link=False)


def _translate_blo(self, tb, instruction):
    _translate_branch(self, tb, instruction, link=False)


def _translate_bls(self, tb, instruction):
    _translate_branch(self, tb, instruction, link=False)


def _translate_branch(self, tb, instruction, link):
    if instruction.condition_code == ARM_COND_CODE_AL:
        cond = tb.immediate(1, 1)
    else:
        eval_cc_fn = {
            ARM_COND_CODE_EQ: self._evaluate_eq,
            ARM_COND_CODE_NE: self._evaluate_ne,
            ARM_COND_CODE_CS: self._evaluate_cs,
            ARM_COND_CODE_HS: self._evaluate_cs,
            ARM_COND_CODE_CC: self._evaluate_cc,
            ARM_COND_CODE_LO: self._evaluate_cc,
            ARM_COND_CODE_MI: self._evaluate_mi,
            ARM_COND_CODE_PL: self._evaluate_pl,
            ARM_COND_CODE_VS: self._evaluate_vs,
            ARM_COND_CODE_VC: self._evaluate_vc,
            ARM_COND_CODE_HI: self._evaluate_hi,
            ARM_COND_CODE_LS: self._evaluate_ls,
            ARM_COND_CODE_GE: self._evaluate_ge,
            ARM_COND_CODE_LT: self._evaluate_lt,
            ARM_COND_CODE_GT: self._evaluate_gt,
            ARM_COND_CODE_LE: self._evaluate_le,
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
        tb.add(self._builder.gen_str(ReilImmediateOperand(instruction.address + instruction.size, self._pc.size),
                                     self._lr))

    tb.add(self._builder.gen_jcc(cond, target))

    return


dispatcher = {
    'b': _translate_b,
    'bl': _translate_bl,
    'bx': _translate_bx,
    'blx': _translate_blx,
    'bne': _translate_bne,
    'beq': _translate_beq,
    'bpl': _translate_bpl,
    'ble': _translate_ble,
    'bcs': _translate_bcs,
    'bhs': _translate_bhs,
    'blt': _translate_blt,
    'bge': _translate_bge,
    'bhi': _translate_bhi,
    'blo': _translate_blo,
    'bls': _translate_bls,
}
