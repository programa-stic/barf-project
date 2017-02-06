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

from barf.core.reil import ReilEmptyOperand
from barf.core.reil import ReilRegisterOperand
from barf.core.reil import ReilImmediateOperand
from barf.core.reil import ReilInstruction
from barf.core.reil import ReilMnemonic
from barf.core.reil import ReilInstructionBuilder


class Label(object):

    def __init__(self, name):
        self.name = name

    def __str__(self):
        string = self.name + ":"

        return string


class Translator(object):

    def __init__(self):
        pass

    def translate(self, instruction):
        raise NotImplementedError()

    def reset(self):
        raise NotImplementedError()

    @property
    def translation_mode(self):
        raise NotImplementedError()

    @translation_mode.setter
    def translation_mode(self, value):
        raise NotImplementedError()


class TranslationBuilder(object):

    def __init__(self, ir_name_generator, architecture_mode):
        self._ir_name_generator = ir_name_generator

        self._instructions = []

        self._builder = ReilInstructionBuilder()

    def add(self, instr):
        self._instructions.append(instr)

    def temporal(self, size):
        return ReilRegisterOperand(self._ir_name_generator.get_next(), size)

    def immediate(self, value, size):
        return ReilImmediateOperand(value, size)

    def label(self, name):
        return Label(name)

    def instanciate(self, address):
        # Set instructions address.
        instrs = self._instructions

        for instr in instrs:
            instr.address = address << 8

        instrs = self._resolve_loops(instrs)

        return instrs

    # Auxiliary functions
    # ======================================================================== #

    def _resolve_loops(self, instrs):
        idx_by_labels = {}

        # Collect labels.
#         curr = 0
#         for index, instr in enumerate(instrs):
#             if isinstance(instr, Label):
#                 idx_by_labels[instr.name] = curr
#
#                 del instrs[index]
#             else:
#                 curr += 1

        # TODO: Hack to avoid deleting while iterating
        instrs_no_labels = []
        curr = 0
        for i in instrs:
            if isinstance(i, Label):
                idx_by_labels[i.name] = curr
            else:
                instrs_no_labels.append(i)
                curr += 1

        instrs[:] = instrs_no_labels

        # Resolve instruction addresses and JCC targets.
        for index, instr in enumerate(instrs):
            assert isinstance(instr, ReilInstruction)

            instr.address |= index

            if instr.mnemonic == ReilMnemonic.JCC:
                target = instr.operands[2]

                if isinstance(target, Label):
                    idx = idx_by_labels[target.name]
                    address = (instr.address & ~0xff) | idx

                    instr.operands[2] = ReilImmediateOperand(address, self._arch_info.address_size + 8)

        return instrs

    def _all_ones_imm(self, reg):
        return self.immediate((2**reg.size) - 1, reg.size)

    def _negate_reg(self, reg):
        neg = self.temporal(reg.size)
        self.add(self._builder.gen_xor(reg, self._all_ones_imm(reg), neg))
        return neg

    def _and_regs(self, reg1, reg2):
        ret = self.temporal(reg1.size)
        self.add(self._builder.gen_and(reg1, reg2, ret))
        return ret

    def _or_regs(self, reg1, reg2):
        ret = self.temporal(reg1.size)
        self.add(self._builder.gen_or(reg1, reg2, ret))
        return ret

    def _xor_regs(self, reg1, reg2):
        ret = self.temporal(reg1.size)
        self.add(self._builder.gen_xor(reg1, reg2, ret))
        return ret

    def _equal_regs(self, reg1, reg2):
        return self._negate_reg(self._xor_regs(reg1, reg2))

    def _unequal_regs(self, reg1, reg2):
        return self._xor_regs(reg1, reg2)

    def _shift_reg(self, reg, sh):
        ret = self.temporal(reg.size)
        self.add(self._builder.gen_bsh(reg, sh, ret))
        return ret

    def _extract_bit(self, reg, bit):
        assert(bit >= 0 and bit < reg.size)
        tmp = self.temporal(reg.size)
        ret = self.temporal(1)

        self.add(self._builder.gen_bsh(reg, self.immediate(-bit, reg.size), tmp)) # shift to LSB
        self.add(self._builder.gen_and(tmp, self.immediate(1, reg.size), ret)) # filter LSB

        return ret

    # Same as before but the bit number is indicated by a register and it will be resolved at runtime
    def _extract_bit_with_register(self, reg, bit):
        # assert(bit >= 0 and bit < reg.size2) # It is assumed, it is not checked
        tmp = self.temporal(reg.size)
        neg_bit = self.temporal(reg.size)
        ret = self.temporal(1)

        self.add(self._builder.gen_sub(self.immediate(0, bit.size), bit, neg_bit)) # as left bit is indicated by a negative number
        self.add(self._builder.gen_bsh(reg, neg_bit, tmp)) # shift to LSB
        self.add(self._builder.gen_and(tmp, self.immediate(1, reg.size), ret)) # filter LSB

        return ret

    def _extract_msb(self, reg):
        return self._extract_bit(reg, reg.size - 1)

    def _extract_sign_bit(self, reg):
        return self._extract_msb(self, reg)

    def _greater_than_or_equal(self, reg1, reg2):
        assert(reg1.size == reg2.size)
        result = self.temporal(reg1.size * 2)

        self.add(self._builder.gen_sub(reg1, reg2, result))

        sign = self._extract_bit(result, reg1.size - 1)
        overflow = self._overflow_from_sub(reg1, reg2, result)

        return self._equal_regs(sign, overflow)

    def _jump_to(self, target):
        self.add(self._builder.gen_jcc(self.immediate(1, 1), target))

    def _jump_if_zero(self, reg, label):
        is_zero = self.temporal(1)
        self.add(self._builder.gen_bisz(reg, is_zero))
        self.add(self._builder.gen_jcc(is_zero, label))

    def _add_to_reg(self, reg, value):
        res = self.temporal(reg.size)
        self.add(self._builder.gen_add(reg, value, res))

        return res

    def _sub_to_reg(self, reg, value):
        res = self.temporal(reg.size)
        self.add(self._builder.gen_sub(reg, value, res))

        return res

    def _overflow_from_sub(self, oprnd0, oprnd1, result):
        op1_sign = self._extract_bit(oprnd0, oprnd0.size - 1)
        op2_sign = self._extract_bit(oprnd1, oprnd0.size - 1)
        res_sign = self._extract_bit(result, oprnd0.size - 1)

        return self._and_regs(self._unequal_regs(op1_sign, op2_sign), self._unequal_regs(op1_sign, res_sign))