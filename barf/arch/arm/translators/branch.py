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
from barf.arch.arm.helpers import ArmConditionCodeHelper
from barf.arch.helper import and_regs
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
    oprnd_cc = ArmConditionCodeHelper.evaluate_cond_code(self._flags, tb, instruction.condition_code)

    arm_operand = instruction.operands[0]

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
        raise NotImplementedError("Instruction Not Implemented: Unknown operand for branch operation.")

    if link:
        tb.add(self._builder.gen_str(ReilImmediateOperand(instruction.address + instruction.size, self._pc.size),
                                     self._lr))

    tb.add(self._builder.gen_jcc(oprnd_cc, target))


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
