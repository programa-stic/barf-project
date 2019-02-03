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

from barf.core.reil import ReilEmptyOperand
from barf.core.reil import ReilInstruction
from barf.core.reil import ReilMnemonic


class ReilBuilder(object):

    """REIL Instruction Builder. Generate REIL instructions, easily.
    """

    # Arithmetic Instructions
    # ======================================================================== #
    @staticmethod
    def gen_add(src1, src2, dst):
        """Return an ADD instruction.
        """
        assert src1.size == src2.size

        return ReilBuilder.build(ReilMnemonic.ADD, src1, src2, dst)

    @staticmethod
    def gen_sub(src1, src2, dst):
        """Return a SUB instruction.
        """
        assert src1.size == src2.size

        return ReilBuilder.build(ReilMnemonic.SUB, src1, src2, dst)

    @staticmethod
    def gen_mul(src1, src2, dst):
        """Return a MUL instruction.
        """
        assert src1.size == src2.size

        return ReilBuilder.build(ReilMnemonic.MUL, src1, src2, dst)

    @staticmethod
    def gen_div(src1, src2, dst):
        """Return a DIV instruction.
        """
        assert src1.size == src2.size

        return ReilBuilder.build(ReilMnemonic.DIV, src1, src2, dst)

    @staticmethod
    def gen_mod(src1, src2, dst):
        """Return a MOD instruction.
        """
        assert src1.size == src2.size

        return ReilBuilder.build(ReilMnemonic.MOD, src1, src2, dst)

    @staticmethod
    def gen_bsh(src1, src2, dst):
        """Return a BSH instruction.
        """
        assert src1.size == src2.size

        return ReilBuilder.build(ReilMnemonic.BSH, src1, src2, dst)

    # Bitwise Instructions
    # ======================================================================== #
    @staticmethod
    def gen_and(src1, src2, dst):
        """Return an AND instruction.
        """
        assert src1.size == src2.size

        return ReilBuilder.build(ReilMnemonic.AND, src1, src2, dst)

    @staticmethod
    def gen_or(src1, src2, dst):
        """Return an OR instruction.
        """
        assert src1.size == src2.size

        return ReilBuilder.build(ReilMnemonic.OR, src1, src2, dst)

    @staticmethod
    def gen_xor(src1, src2, dst):
        """Return a XOR instruction.
        """
        assert src1.size == src2.size

        return ReilBuilder.build(ReilMnemonic.XOR, src1, src2, dst)

    # Data Transfer Instructions
    # ======================================================================== #
    @staticmethod
    def gen_ldm(src, dst):
        """Return a LDM instruction.
        """
        return ReilBuilder.build(ReilMnemonic.LDM, src, ReilEmptyOperand(), dst)

    @staticmethod
    def gen_stm(src, dst):
        """Return a STM instruction.
        """
        return ReilBuilder.build(ReilMnemonic.STM, src, ReilEmptyOperand(), dst)

    @staticmethod
    def gen_str(src, dst):
        """Return a STR instruction.
        """
        return ReilBuilder.build(ReilMnemonic.STR, src, ReilEmptyOperand(), dst)

    # Conditional Instructions
    # ======================================================================== #
    @staticmethod
    def gen_bisz(src, dst):
        """Return a BISZ instruction.
        """
        return ReilBuilder.build(ReilMnemonic.BISZ, src, ReilEmptyOperand(), dst)

    @staticmethod
    def gen_jcc(src, dst):
        """Return a JCC instruction.
        """
        return ReilBuilder.build(ReilMnemonic.JCC, src, ReilEmptyOperand(), dst)

    # Other Instructions
    # ======================================================================== #
    @staticmethod
    def gen_unkn():
        """Return an UNKN instruction.
        """
        empty_reg = ReilEmptyOperand()

        return ReilBuilder.build(ReilMnemonic.UNKN, empty_reg, empty_reg, empty_reg)

    @staticmethod
    def gen_undef():
        """Return an UNDEF instruction.
        """
        empty_reg = ReilEmptyOperand()

        return ReilBuilder.build(ReilMnemonic.UNDEF, empty_reg, empty_reg, empty_reg)

    @staticmethod
    def gen_nop():
        """Return a NOP instruction.
        """
        empty_reg = ReilEmptyOperand()

        return ReilBuilder.build(ReilMnemonic.NOP, empty_reg, empty_reg, empty_reg)

    # Extensions
    # ======================================================================== #
    @staticmethod
    def gen_sext(src, dst):
        """Return a SEXT instruction.
        """
        assert src.size <= dst.size

        empty_reg = ReilEmptyOperand()

        return ReilBuilder.build(ReilMnemonic.SEXT, src, empty_reg, dst)

    @staticmethod
    def gen_sdiv(src1, src2, dst):
        """Return a SDIV instruction.
        """
        assert src1.size == src2.size

        return ReilBuilder.build(ReilMnemonic.SDIV, src1, src2, dst)

    @staticmethod
    def gen_smod(src1, src2, dst):
        """Return a SMOD instruction.
        """
        assert src1.size == src2.size

        return ReilBuilder.build(ReilMnemonic.SMOD, src1, src2, dst)

    @staticmethod
    def gen_smul(src1, src2, dst):
        """Return a SMUL instruction.
        """
        assert src1.size == src2.size

        return ReilBuilder.build(ReilMnemonic.SMUL, src1, src2, dst)

    # Helpers
    # ======================================================================== #
    @staticmethod
    def build(mnemonic, oprnd1, oprnd2, oprnd3):
        """Return the specified instruction.
        """
        ins = ReilInstruction()

        ins.mnemonic = mnemonic
        ins.operands = [oprnd1, oprnd2, oprnd3]

        return ins
