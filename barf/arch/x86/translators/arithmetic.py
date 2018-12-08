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


# "Binary Arithmetic Instructions"
# ============================================================================ #
def _translate_adc(self, tb, instruction):
    # Flags Affected
    # The OF, SF, ZF, AF, CF, and PF flags are set according to the result.

    oprnd0 = self._reg_acc_translator.read(tb, instruction.operands[0])
    oprnd1 = self._reg_acc_translator.read(tb, instruction.operands[1])

    tmp0 = tb.temporal(oprnd1.size * 2)
    tmp1 = tb.temporal(oprnd1.size * 2)
    tmp2 = tb.temporal(oprnd1.size * 2)

    tb.add(self._builder.gen_add(oprnd0, oprnd1, tmp0))
    tb.add(self._builder.gen_str(self._flags.cf, tmp1))
    tb.add(self._builder.gen_add(tmp0, tmp1, tmp2))

    # Flags : OF, SF, ZF, AF, CF, PF
    self._flag_translator.update_of(tb, oprnd0, oprnd1, tmp2)
    self._flag_translator.update_sf(tb, oprnd0, tmp2)
    self._flag_translator.update_zf(tb, oprnd0, tmp2)
    self._flag_translator.update_af(tb, oprnd0, oprnd1, cf=self._flags.cf)
    self._flag_translator.update_cf(tb, oprnd0, tmp2)
    self._flag_translator.update_pf(tb, tmp2)

    self._reg_acc_translator.write(tb, instruction.operands[0], tmp2)


def _translate_add(self, tb, instruction):
    # Flags Affected
    # The OF, SF, ZF, AF, CF, and PF flags are set according to the
    # result.

    oprnd0 = self._reg_acc_translator.read(tb, instruction.operands[0])
    oprnd1 = self._reg_acc_translator.read(tb, instruction.operands[1])

    tmp0 = tb.temporal(oprnd0.size * 2)

    tb.add(self._builder.gen_add(oprnd0, oprnd1, tmp0))

    # Flags : OF, SF, ZF, AF, CF, PF
    self._flag_translator.update_of(tb, oprnd0, oprnd1, tmp0)
    self._flag_translator.update_sf(tb, oprnd0, tmp0)
    self._flag_translator.update_zf(tb, oprnd0, tmp0)
    self._flag_translator.update_af(tb, oprnd0, oprnd1)
    self._flag_translator.update_cf(tb, oprnd0, tmp0)
    self._flag_translator.update_pf(tb, tmp0)

    self._reg_acc_translator.write(tb, instruction.operands[0], tmp0)


def _translate_cmp(self, tb, instruction):
    # Flags Affected
    # The CF, OF, SF, ZF, AF, and PF flags are set according to the
    # result.

    oprnd0 = self._reg_acc_translator.read(tb, instruction.operands[0])
    oprnd1 = self._reg_acc_translator.read(tb, instruction.operands[1])

    tmp0 = tb.temporal(oprnd0.size * 2)

    tb.add(self._builder.gen_sub(oprnd0, oprnd1, tmp0))

    # Flags : CF, OF, SF, ZF, AF, PF
    self._flag_translator.update_cf(tb, oprnd0, tmp0)
    self._flag_translator.update_of(tb, oprnd0, oprnd1, tmp0, subtraction=True)
    self._flag_translator.update_sf(tb, oprnd0, tmp0)
    self._flag_translator.update_zf(tb, oprnd0, tmp0)
    self._flag_translator.update_af(tb, oprnd0, oprnd1, subtraction=True)
    self._flag_translator.update_pf(tb, tmp0)


def _translate_dec(self, tb, instruction):
    # Flags Affected
    # The CF flag is not affected. The OF, SF, ZF, AF, and PF flags
    # are set according to the result.

    oprnd0 = self._reg_acc_translator.read(tb, instruction.operands[0])

    imm0 = tb.immediate(1, oprnd0.size)

    tmp0 = tb.temporal(oprnd0.size * 2)

    tb.add(self._builder.gen_sub(oprnd0, imm0, tmp0))

    # Flags : OF, SF, ZF, AF, PF
    self._flag_translator.update_of(tb, oprnd0, imm0, tmp0, subtraction=True)
    self._flag_translator.update_sf(tb, oprnd0, tmp0)
    self._flag_translator.update_zf(tb, oprnd0, tmp0)
    self._flag_translator.update_af(tb, oprnd0, imm0, subtraction=True)
    self._flag_translator.update_pf(tb, tmp0)

    self._reg_acc_translator.write(tb, instruction.operands[0], tmp0)


def _translate_div(self, tb, instruction):
    # Flags Affected
    # The CF, OF, SF, ZF, AF, and PF flags are undefined.

    oprnd0 = self._reg_acc_translator.read(tb, instruction.operands[0])
    oprnd1_x86, oprnd2_x86, result_low_x86, result_high_x86 = __get_div_implicit_operands(oprnd0.size)
    oprnd1 = self._reg_acc_translator.read(tb, oprnd1_x86)
    oprnd2 = self._reg_acc_translator.read(tb, oprnd2_x86)

    imm0 = tb.immediate(oprnd0.size, oprnd0.size * 2)

    tmp0 = tb.temporal(oprnd0.size * 2)
    tmp1 = tb.temporal(oprnd0.size * 2)
    tmp2 = tb.temporal(oprnd0.size * 2)
    tmp3 = tb.temporal(oprnd0.size * 2)
    tmp4 = tb.temporal(oprnd0.size * 2)
    tmp5 = tb.temporal(oprnd0.size * 2)
    tmp6 = tb.temporal(oprnd0.size * 2)

    # Extend operands to match their size.
    tb.add(self._builder.gen_str(oprnd0, tmp0))
    tb.add(self._builder.gen_str(oprnd1, tmp1))
    tb.add(self._builder.gen_str(oprnd2, tmp2))

    # Put dividend together.
    tb.add(self._builder.gen_bsh(tmp1, imm0, tmp3))
    tb.add(self._builder.gen_or(tmp3, tmp2, tmp4))

    # Do division.
    tb.add(self._builder.gen_div(tmp4, tmp0, tmp5))
    tb.add(self._builder.gen_mod(tmp4, tmp0, tmp6))

    # Flags : CF, OF, SF, ZF, AF, PF
    self._flag_translator.undefine_flag(tb, self._flags.cf)
    self._flag_translator.undefine_flag(tb, self._flags.of)
    self._flag_translator.undefine_flag(tb, self._flags.sf)
    self._flag_translator.undefine_flag(tb, self._flags.zf)
    self._flag_translator.undefine_flag(tb, self._flags.af)
    self._flag_translator.undefine_flag(tb, self._flags.pf)

    # Store result.
    self._reg_acc_translator.write(tb, result_low_x86, tmp5)
    self._reg_acc_translator.write(tb, result_high_x86, tmp6)


def _translate_idiv(self, tb, instruction):
    # Flags Affected
    # The CF, OF, SF, ZF, AF, and PF flags are undefined.

    oprnd0 = self._reg_acc_translator.read(tb, instruction.operands[0])
    oprnd1_x86, oprnd2_x86, result_low_x86, result_high_x86 = __get_div_implicit_operands(oprnd0.size)
    oprnd1 = self._reg_acc_translator.read(tb, oprnd1_x86)
    oprnd2 = self._reg_acc_translator.read(tb, oprnd2_x86)

    imm0 = tb.immediate(oprnd0.size, oprnd0.size * 2)

    tmp0 = tb.temporal(oprnd0.size * 2)
    tmp1 = tb.temporal(oprnd0.size * 2)
    tmp2 = tb.temporal(oprnd0.size * 2)
    tmp3 = tb.temporal(oprnd0.size * 2)
    tmp4 = tb.temporal(oprnd0.size * 2)
    tmp5 = tb.temporal(oprnd0.size * 2)
    tmp6 = tb.temporal(oprnd0.size * 2)

    # Extend operands to match their size.
    tb.add(self._builder.gen_sext(oprnd0, tmp0))
    tb.add(self._builder.gen_str(oprnd1, tmp1))
    tb.add(self._builder.gen_str(oprnd2, tmp2))

    # Put dividend together.
    tb.add(self._builder.gen_bsh(tmp1, imm0, tmp3))
    tb.add(self._builder.gen_or(tmp3, tmp2, tmp4))

    # Do division.
    tb.add(self._builder.gen_sdiv(tmp4, tmp0, tmp5))
    tb.add(self._builder.gen_smod(tmp4, tmp0, tmp6))

    # Flags : CF, OF, SF, ZF, AF, PF
    self._flag_translator.undefine_flag(tb, self._flags.cf)
    self._flag_translator.undefine_flag(tb, self._flags.of)
    self._flag_translator.undefine_flag(tb, self._flags.sf)
    self._flag_translator.undefine_flag(tb, self._flags.zf)
    self._flag_translator.undefine_flag(tb, self._flags.af)
    self._flag_translator.undefine_flag(tb, self._flags.pf)

    # Store result.
    self._reg_acc_translator.write(tb, result_low_x86, tmp5)
    self._reg_acc_translator.write(tb, result_high_x86, tmp6)


def _translate_imul(self, tb, instruction):
    # Flags Affected
    # For the one operand form of the instruction, the CF and OF flags are
    # set when significant bits are carried into the upper half of the
    # result and cleared when the result fits exactly in the lower half of
    # the result. For the two- and three-operand forms of the instruction,
    # the CF and OF flags are set when the result must be truncated to fit
    # in the destination operand size and cleared when the result fits
    # exactly in the destination operand size. The SF, ZF, AF, and PF flags
    # are undefined.

    # IF (NumberOfOperands = 1)
    #   THEN IF (OperandSize = 8)
    #       THEN
    #           AX <- AL * SRC (* Signed multiplication *)
    #           IF AL = AX
    #               THEN CF <- 0; OF <- 0;
    #               ELSE CF <- 1; OF <- 1; FI;
    #   ELSE IF OperandSize = 16
    #       THEN
    #       DX:AX <- AX * SRC (* Signed multiplication *)
    #       IF sign_extend_to_32 (AX) = DX:AX
    #           THEN CF <- 0; OF <- 0;
    #           ELSE CF <- 1; OF <- 1; FI;
    #   ELSE IF OperandSize = 32
    #       THEN
    #       EDX:EAX <- EAX * SRC (* Signed multiplication *)
    #       IF EAX = EDX:EAX
    #           THEN CF <- 0; OF <- 0;
    #           ELSE CF <- 1; OF <- 1; FI;
    #   ELSE (* OperandSize = 64 *)
    #       RDX:RAX <- RAX * SRC (* Signed multiplication *)
    #       IF RAX = RDX:RAX
    #           THEN CF <- 0; OF <- 0;
    #           ELSE CF <- 1; OF <- 1; FI;
    #   FI;
    # ELSE IF (NumberOfOperands = 2)
    #   THEN
    #       temp <- DEST * SRC (* Signed multiplication; temp is double DEST size *)
    #       DEST <- DEST * SRC (* Signed multiplication *)
    #       IF temp != DEST
    #           THEN CF <- 1; OF <- 1;
    #           ELSE CF <- 0; OF <- 0; FI;
    #   ELSE (* NumberOfOperands = 3 *)
    #       DEST <- SRC1 * SRC2 (* Signed multiplication *)
    #       temp <- SRC1 * SRC2 (* Signed multiplication; temp is double SRC1 size *)
    #       IF temp != DEST
    #           THEN CF <- 1; OF <- 1;
    #           ELSE CF <- 0; OF <- 0; FI;
    #   FI;
    # FI;

    if len(instruction.operands) == 1:
        oprnd0 = self._reg_acc_translator.read(tb, instruction.operands[0])
        oprnd1_x86, result_low_x86, result_high_x86 = __get_mul_implicit_operands(oprnd0.size)
        oprnd1 = self._reg_acc_translator.read(tb, oprnd1_x86)
    elif len(instruction.operands) == 2:
        oprnd0 = self._reg_acc_translator.read(tb, instruction.operands[0])
        oprnd1 = self._reg_acc_translator.read(tb, instruction.operands[1])
    elif len(instruction.operands) == 3:
        oprnd0 = self._reg_acc_translator.read(tb, instruction.operands[1])
        oprnd1 = self._reg_acc_translator.read(tb, instruction.operands[2])

    tmp0 = tb.temporal(2 * oprnd0.size)

    # Do multiplication.
    tb.add(self._builder.gen_smul(oprnd0, oprnd1, tmp0))

    # Flags : OF, CF
    # TODO: Implement CF and OF flags.

    # Flags : SF, ZF, AF, PF
    self._flag_translator.undefine_flag(tb, self._flags.sf)
    self._flag_translator.undefine_flag(tb, self._flags.zf)
    self._flag_translator.undefine_flag(tb, self._flags.af)
    self._flag_translator.undefine_flag(tb, self._flags.pf)

    # Store result.
    if len(instruction.operands) == 1:
        imm0 = tb.immediate(-oprnd0.size, 2 * oprnd0.size)

        tmp1 = tb.temporal(2 * oprnd0.size)

        tb.add(self._builder.gen_bsh(tmp0, imm0, tmp1))

        self._reg_acc_translator.write(tb, result_low_x86, tmp0)
        self._reg_acc_translator.write(tb, result_high_x86, tmp1)
    elif len(instruction.operands) == 2:
        self._reg_acc_translator.write(tb, instruction.operands[0], tmp0)
    elif len(instruction.operands) == 3:
        self._reg_acc_translator.write(tb, instruction.operands[0], tmp0)


def _translate_inc(self, tb, instruction):
    # Flags Affected
    # The CF flag is not affected. The OF, SF, ZF, AF, and PF flags
    # are set according to the result.

    oprnd0 = self._reg_acc_translator.read(tb, instruction.operands[0])

    imm0 = tb.immediate(1, oprnd0.size)

    tmp0 = tb.temporal(oprnd0.size * 2)

    tb.add(self._builder.gen_add(oprnd0, imm0, tmp0))

    # Flags : OF, SF, ZF, AF, PF
    self._flag_translator.update_of(tb, oprnd0, imm0, tmp0)
    self._flag_translator.update_sf(tb, oprnd0, tmp0)
    self._flag_translator.update_zf(tb, oprnd0, tmp0)
    self._flag_translator.update_af(tb, oprnd0, imm0)
    self._flag_translator.update_pf(tb, tmp0)

    self._reg_acc_translator.write(tb, instruction.operands[0], tmp0)


def _translate_mul(self, tb, instruction):
    # Flags Affected
    # The OF and CF flags are set to 0 if the upper half of the
    # result is 0; otherwise, they are set to 1. The SF, ZF, AF, and
    # PF flags are undefined.

    # IF (Byte operation)
    #   THEN
    #       AX <- AL * SRC;
    #   ELSE (* Word or doubleword operation *)
    #       IF OperandSize = 16
    #           THEN
    #               DX:AX <- AX * SRC;
    #           ELSE IF OperandSize = 32
    #               THEN EDX:EAX <- EAX * SRC; FI;
    #           ELSE (* OperandSize = 64 *)
    #               RDX:RAX <- RAX * SRC;
    #           FI;
    # FI;

    oprnd0 = self._reg_acc_translator.read(tb, instruction.operands[0])
    oprnd1_x86, result_low_x86, result_high_x86 = __get_mul_implicit_operands(oprnd0.size)
    oprnd1 = self._reg_acc_translator.read(tb, oprnd1_x86)

    imm0 = tb.immediate(-oprnd0.size, oprnd0.size * 2)

    tmp0 = tb.temporal(2 * oprnd0.size)
    tmp1 = tb.temporal(2 * oprnd0.size)

    tb.add(self._builder.gen_mul(oprnd0, oprnd1, tmp0))
    tb.add(self._builder.gen_bsh(tmp0, imm0, tmp1))

    # Flags : OF, CF
    fimm0 = tb.immediate(1, 1)

    ftmp0 = tb.temporal(oprnd0.size * 2)
    ftmp1 = tb.temporal(1)

    tb.add(self._builder.gen_bsh(tmp0, imm0, ftmp0))
    tb.add(self._builder.gen_bisz(ftmp0, ftmp1))
    tb.add(self._builder.gen_xor(ftmp1, fimm0, self._flags.of))
    tb.add(self._builder.gen_xor(ftmp1, fimm0, self._flags.cf))

    # Flags : SF, ZF, AF, PF
    self._flag_translator.undefine_flag(tb, self._flags.sf)
    self._flag_translator.undefine_flag(tb, self._flags.zf)
    self._flag_translator.undefine_flag(tb, self._flags.af)
    self._flag_translator.undefine_flag(tb, self._flags.pf)

    # Store result.
    self._reg_acc_translator.write(tb, result_low_x86, tmp0)
    self._reg_acc_translator.write(tb, result_high_x86, tmp1)


def _translate_neg(self, tb, instruction):
    # Flags Affected
    # The CF flag set to 0 if the source operand is 0; otherwise it
    # is set to 1. The OF, SF, ZF, AF, and PF flags are set
    # according to the result.

    oprnd0 = self._reg_acc_translator.read(tb, instruction.operands[0])

    imm0 = tb.immediate((2 ** oprnd0.size) - 1, oprnd0.size)
    imm1 = tb.immediate(1, oprnd0.size)
    imm2 = tb.immediate(1, 1)
    zero = tb.immediate(0, oprnd0.size)

    tmp0 = tb.temporal(oprnd0.size)
    tmp1 = tb.temporal(oprnd0.size)
    tmp2 = tb.temporal(1)

    tb.add(self._builder.gen_xor(oprnd0, imm0, tmp0))
    tb.add(self._builder.gen_add(tmp0, imm1, tmp1))

    # Flags : CF
    tb.add(self._builder.gen_bisz(oprnd0, tmp2))
    tb.add(self._builder.gen_xor(tmp2, imm2, self._flags.cf))

    # Flags : OF, SF, ZF, AF, PF
    self._flag_translator.update_of(tb, oprnd0, oprnd0, tmp1, subtraction=True)
    self._flag_translator.update_sf(tb, oprnd0, tmp1)
    self._flag_translator.update_zf(tb, oprnd0, tmp1)
    self._flag_translator.update_af(tb, zero, oprnd0, subtraction=True)
    self._flag_translator.update_pf(tb, tmp1)

    self._reg_acc_translator.write(tb, instruction.operands[0], tmp1)


def _translate_sbb(self, tb, instruction):
    # Flags Affected
    # The OF, SF, ZF, AF, PF, and CF flags are set according to the
    # result.

    oprnd0 = self._reg_acc_translator.read(tb, instruction.operands[0])
    oprnd1 = self._reg_acc_translator.read(tb, instruction.operands[1])

    tmp0 = tb.temporal(oprnd0.size * 2)
    tmp1 = tb.temporal(oprnd0.size * 2)
    tmp2 = tb.temporal(oprnd0.size * 2)
    tmp3 = tb.temporal(oprnd0.size)
    tmp4 = tb.temporal(oprnd0.size)

    tb.add(self._builder.gen_sub(oprnd0, oprnd1, tmp0))
    tb.add(self._builder.gen_str(self._flags.cf, tmp1))
    tb.add(self._builder.gen_sub(tmp0, tmp1, tmp2))
    tb.add(self._builder.gen_str(tmp0, tmp3))
    tb.add(self._builder.gen_str(tmp1, tmp4))

    # Flags : OF, SF, ZF, AF, PF, CF
    self._flag_translator.update_of(tb, oprnd0, oprnd1, tmp2, subtraction=True)
    self._flag_translator.update_sf(tb, tmp3, tmp2)
    self._flag_translator.update_zf(tb, tmp3, tmp2)
    self._flag_translator.update_af(tb, oprnd0, oprnd1, subtraction=True, cf=self._flags.cf)
    self._flag_translator.update_pf(tb, tmp2)
    self._flag_translator.update_cf(tb, tmp3, tmp2)

    self._reg_acc_translator.write(tb, instruction.operands[0], tmp2)


def _translate_sub(self, tb, instruction):
    # Flags Affected
    # The OF, SF, ZF, AF, PF, and CF flags are set according to the
    # result.

    oprnd0 = self._reg_acc_translator.read(tb, instruction.operands[0])
    oprnd1 = self._reg_acc_translator.read(tb, instruction.operands[1])

    tmp0 = tb.temporal(oprnd0.size * 2)

    tb.add(self._builder.gen_sub(oprnd0, oprnd1, tmp0))

    # Flags : OF, SF, ZF, AF, PF, CF
    self._flag_translator.update_of(tb, oprnd0, oprnd1, tmp0, subtraction=True)
    self._flag_translator.update_sf(tb, oprnd0, tmp0)
    self._flag_translator.update_zf(tb, oprnd0, tmp0)
    self._flag_translator.update_af(tb, oprnd0, oprnd1, subtraction=True)
    self._flag_translator.update_pf(tb, tmp0)
    self._flag_translator.update_cf(tb, oprnd0, tmp0)

    self._reg_acc_translator.write(tb, instruction.operands[0], tmp0)


# Auxiliary functions
# ============================================================================ #
def __get_div_implicit_operands(size):
    if size == 8:
        oprnd1 = X86RegisterOperand('ah', 8)
        oprnd2 = X86RegisterOperand('al', 8)
        result_low = X86RegisterOperand('al', 8)
        result_high = X86RegisterOperand('ah', 8)
    elif size == 16:
        oprnd1 = X86RegisterOperand('dx', 16)
        oprnd2 = X86RegisterOperand('ax', 16)
        result_low = X86RegisterOperand('ax', 16)
        result_high = X86RegisterOperand('dx', 16)
    elif size == 32:
        oprnd1 = X86RegisterOperand('edx', 32)
        oprnd2 = X86RegisterOperand('eax', 32)
        result_low = X86RegisterOperand('eax', 32)
        result_high = X86RegisterOperand('edx', 32)
    elif size == 64:
        oprnd1 = X86RegisterOperand('rdx', 64)
        oprnd2 = X86RegisterOperand('rax', 64)
        result_low = X86RegisterOperand('rax', 64)
        result_high = X86RegisterOperand('rdx', 64)

    return oprnd1, oprnd2, result_low, result_high


def __get_mul_implicit_operands(size):
    if size == 8:
        oprnd1 = X86RegisterOperand('al', 8)
        result_low = X86RegisterOperand('al', 8)
        result_high = X86RegisterOperand('ah', 8)
    elif size == 16:
        oprnd1 = X86RegisterOperand('ax', 16)
        result_low = X86RegisterOperand('ax', 16)
        result_high = X86RegisterOperand('dx', 16)
    elif size == 32:
        oprnd1 = X86RegisterOperand('eax', 32)
        result_low = X86RegisterOperand('eax', 32)
        result_high = X86RegisterOperand('edx', 32)
    elif size == 64:
        oprnd1 = X86RegisterOperand('rax', 64)
        result_low = X86RegisterOperand('rax', 64)
        result_high = X86RegisterOperand('rdx', 64)

    return oprnd1, result_low, result_high


dispatcher = {
    'adc': _translate_adc,
    'add': _translate_add,
    'cmp': _translate_cmp,
    'dec': _translate_dec,
    'div': _translate_div,
    'idiv': _translate_idiv,
    'imul': _translate_imul,
    'inc': _translate_inc,
    'mul': _translate_mul,
    'neg': _translate_neg,
    'sbb': _translate_sbb,
    'sub': _translate_sub,
}
