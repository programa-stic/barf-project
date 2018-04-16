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
from barf.core.reil import ReilInstruction
from barf.core.reil import ReilMnemonic


class ReilBuilder(object):

    """REIL Instruction Builder. Generate REIL instructions, easily.
    """

    # Arithmetic Instructions
    # ======================================================================== #
    def gen_add(self, src1, src2, dst):
        """Return an ADD instruction.
        """
        assert src1.size == src2.size

        return self.build(ReilMnemonic.ADD, src1, src2, dst)

    def gen_sub(self, src1, src2, dst):
        """Return a SUB instruction.
        """
        assert src1.size == src2.size

        return self.build(ReilMnemonic.SUB, src1, src2, dst)

    def gen_mul(self, src1, src2, dst):
        """Return a MUL instruction.
        """
        assert src1.size == src2.size

        return self.build(ReilMnemonic.MUL, src1, src2, dst)

    def gen_div(self, src1, src2, dst):
        """Return a DIV instruction.
        """
        assert src1.size == src2.size

        return self.build(ReilMnemonic.DIV, src1, src2, dst)

    def gen_mod(self, src1, src2, dst):
        """Return a MOD instruction.
        """
        assert src1.size == src2.size

        return self.build(ReilMnemonic.MOD, src1, src2, dst)

    def gen_bsh(self, src1, src2, dst):
        """Return a BSH instruction.
        """
        assert src1.size == src2.size

        return self.build(ReilMnemonic.BSH, src1, src2, dst)

    # Bitwise Instructions
    # ======================================================================== #
    def gen_and(self, src1, src2, dst):
        """Return an AND instruction.
        """
        assert src1.size == src2.size

        return self.build(ReilMnemonic.AND, src1, src2, dst)

    def gen_or(self, src1, src2, dst):
        """Return an OR instruction.
        """
        assert src1.size == src2.size

        return self.build(ReilMnemonic.OR, src1, src2, dst)

    def gen_xor(self, src1, src2, dst):
        """Return a XOR instruction.
        """
        assert src1.size == src2.size

        return self.build(ReilMnemonic.XOR, src1, src2, dst)

    # Data Transfer Instructions
    # ======================================================================== #
    def gen_ldm(self, src, dst):
        """Return a LDM instruction.
        """
        return self.build(ReilMnemonic.LDM, src, ReilEmptyOperand(), dst)

    def gen_stm(self, src, dst):
        """Return a STM instruction.
        """
        return self.build(ReilMnemonic.STM, src, ReilEmptyOperand(), dst)

    def gen_str(self, src, dst):
        """Return a STR instruction.
        """
        return self.build(ReilMnemonic.STR, src, ReilEmptyOperand(), dst)

    # Conditional Instructions
    # ======================================================================== #
    def gen_bisz(self, src, dst):
        """Return a BISZ instruction.
        """
        return self.build(ReilMnemonic.BISZ, src, ReilEmptyOperand(), dst)

    def gen_jcc(self, src, dst):
        """Return a JCC instruction.
        """
        return self.build(ReilMnemonic.JCC, src, ReilEmptyOperand(), dst)

    # Other Instructions
    # ======================================================================== #
    def gen_unkn(self):
        """Return an UNKN instruction.
        """
        empty_reg = ReilEmptyOperand()

        return self.build(ReilMnemonic.UNKN, empty_reg, empty_reg, empty_reg)

    def gen_undef(self):
        """Return an UNDEF instruction.
        """
        empty_reg = ReilEmptyOperand()

        return self.build(ReilMnemonic.UNDEF, empty_reg, empty_reg, empty_reg)

    def gen_nop(self):
        """Return a NOP instruction.
        """
        empty_reg = ReilEmptyOperand()

        return self.build(ReilMnemonic.NOP, empty_reg, empty_reg, empty_reg)

    # Extensions
    # ======================================================================== #
    def gen_sext(self, src, dst):
        """Return a SEXT instruction.
        """
        assert src.size <= dst.size

        empty_reg = ReilEmptyOperand()

        return self.build(ReilMnemonic.SEXT, src, empty_reg, dst)

    def gen_sdiv(self, src1, src2, dst):
        """Return a SDIV instruction.
        """
        assert src1.size == src2.size

        return self.build(ReilMnemonic.SDIV, src1, src2, dst)

    def gen_smod(self, src1, src2, dst):
        """Return a SMOD instruction.
        """
        assert src1.size == src2.size

        return self.build(ReilMnemonic.SMOD, src1, src2, dst)

    # Helpers
    # ======================================================================== #
    def build(self, mnemonic, oprnd1, oprnd2, oprnd3):
        """Return the specified instruction.
        """
        ins = ReilInstruction()

        ins.mnemonic = mnemonic
        ins.operands = [oprnd1, oprnd2, oprnd3]

        return ins
