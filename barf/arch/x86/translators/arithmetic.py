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

from barf.arch import ARCH_X86_MODE_64
from barf.core.reil import ReilImmediateOperand
from barf.core.reil import ReilRegisterOperand


# "Binary Arithmetic Instructions"
# ============================================================================ #
def _translate_add(self, tb, instruction):
    # Flags Affected
    # The OF, SF, ZF, AF, CF, and PF flags are set according to the
    # result.

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


def _translate_adc(self, tb, instruction):
    # Flags Affected
    # The OF, SF, ZF, AF, CF, and PF flags are set according to the result.

    oprnd0 = tb.read(instruction.operands[0])
    oprnd1 = tb.read(instruction.operands[1])

    tmp0 = tb.temporal(oprnd1.size * 2)
    tmp1 = tb.temporal(oprnd1.size * 2)
    tmp2 = tb.temporal(oprnd1.size * 2)

    tb.add(self._builder.gen_add(oprnd0, oprnd1, tmp0))
    tb.add(self._builder.gen_str(self._flags["cf"], tmp1))
    tb.add(self._builder.gen_add(tmp0, tmp1, tmp2))

    # Flags : OF, SF, ZF, AF, CF, PF
    self._update_of(tb, oprnd0, oprnd1, tmp2)
    self._update_sf(tb, oprnd0, oprnd1, tmp2)
    self._update_zf(tb, oprnd0, oprnd1, tmp2)
    self._update_af(tb, oprnd0, oprnd1, tmp2)
    self._update_cf(tb, oprnd0, oprnd1, tmp2)
    self._update_pf(tb, oprnd0, oprnd1, tmp2)

    tb.write(instruction.operands[0], tmp2)


def _translate_sub(self, tb, instruction):
    # Flags Affected
    # The OF, SF, ZF, AF, PF, and CF flags are set according to the
    # result.

    oprnd0 = tb.read(instruction.operands[0])
    oprnd1 = tb.read(instruction.operands[1])

    tmp0 = tb.temporal(oprnd0.size * 2)

    tb.add(self._builder.gen_sub(oprnd0, oprnd1, tmp0))

    # Flags : OF, SF, ZF, AF, PF, CF
    self._update_of_sub(tb, oprnd0, oprnd1, tmp0)
    self._update_sf(tb, oprnd0, oprnd1, tmp0)
    self._update_zf(tb, oprnd0, oprnd1, tmp0)
    self._update_af_sub(tb, oprnd0, oprnd1, tmp0)
    self._update_pf(tb, oprnd0, oprnd1, tmp0)
    self._update_cf(tb, oprnd0, oprnd1, tmp0)

    tb.write(instruction.operands[0], tmp0)


def _translate_sbb(self, tb, instruction):
    # Flags Affected
    # The OF, SF, ZF, AF, PF, and CF flags are set according to the
    # result.

    oprnd0 = tb.read(instruction.operands[0])
    oprnd1 = tb.read(instruction.operands[1])

    tmp0 = tb.temporal(oprnd0.size * 2)
    tmp1 = tb.temporal(oprnd0.size * 2)
    tmp2 = tb.temporal(oprnd0.size * 2)
    tmp3 = tb.temporal(oprnd0.size)
    tmp4 = tb.temporal(oprnd0.size)

    tb.add(self._builder.gen_sub(oprnd0, oprnd1, tmp0))
    tb.add(self._builder.gen_str(self._flags["cf"], tmp1))
    tb.add(self._builder.gen_sub(tmp0, tmp1, tmp2))
    tb.add(self._builder.gen_str(tmp0, tmp3))
    tb.add(self._builder.gen_str(tmp1, tmp4))

    # Flags : OF, SF, ZF, AF, PF, CF
    self._update_of_sub(tb, tmp3, tmp4, tmp2)
    self._update_sf(tb, tmp3, tmp4, tmp2)
    self._update_zf(tb, tmp3, tmp4, tmp2)
    self._update_af_sub(tb, tmp3, tmp4, tmp2)
    self._update_pf(tb, tmp3, tmp4, tmp2)
    self._update_cf(tb, tmp3, tmp4, tmp2)

    tb.write(instruction.operands[0], tmp2)


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

    oprnd0 = tb.read(instruction.operands[0])

    if oprnd0.size == 8:
        oprnd1 = ReilRegisterOperand("al", 8)
        tmp0 = tb.temporal(16)
        result_low = ReilRegisterOperand("al", 8)
        result_high = ReilRegisterOperand("ah", 8)
    elif oprnd0.size == 16:
        oprnd1 = ReilRegisterOperand("ax", 16)
        tmp0 = tb.temporal(32)
        result_low = ReilRegisterOperand("ax", 16)
        result_high = ReilRegisterOperand("dx", 16)
    elif oprnd0.size == 32:
        oprnd1 = ReilRegisterOperand("eax", 32)
        tmp0 = tb.temporal(64)
        result_low = ReilRegisterOperand("eax", 32)
        result_high = ReilRegisterOperand("edx", 32)
    elif oprnd0.size == 64:
        oprnd1 = ReilRegisterOperand("rax", 64)
        tmp0 = tb.temporal(128)
        result_low = ReilRegisterOperand("rax", 64)
        result_high = ReilRegisterOperand("rdx", 64)

    imm0 = tb.immediate(-oprnd0.size, oprnd0.size * 2)

    tb.add(self._builder.gen_mul(oprnd0, oprnd1, tmp0))

    # Clean rax and rdx registers.
    if self._arch_info.architecture_mode == ARCH_X86_MODE_64 and oprnd0.size == 32:
        zero = tb.immediate(0, 64)

        tb.add(self._builder.gen_str(zero, ReilRegisterOperand("rdx", 64)))
        tb.add(self._builder.gen_str(zero, ReilRegisterOperand("rax", 64)))

    tb.add(self._builder.gen_bsh(tmp0, imm0, result_high))
    tb.add(self._builder.gen_str(tmp0, result_low))

    # Flags : OF, CF
    fimm0 = tb.immediate(1, 1)

    ftmp0 = tb.temporal(oprnd0.size * 2)
    ftmp1 = tb.temporal(1)

    tb.add(self._builder.gen_bsh(tmp0, imm0, ftmp0))
    tb.add(self._builder.gen_bisz(ftmp0, ftmp1))
    tb.add(self._builder.gen_xor(ftmp1, fimm0, self._flags["of"]))
    tb.add(self._builder.gen_xor(ftmp1, fimm0, self._flags["cf"]))

    # Flags : SF, ZF, AF, PF
    self._undefine_flag(tb, self._flags["sf"])
    self._undefine_flag(tb, self._flags["zf"])
    self._undefine_flag(tb, self._flags["af"])
    self._undefine_flag(tb, self._flags["pf"])


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

    # TODO: Implement CF and OF flags.
    # FIXME: Make this a signed multiply.

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
        oprnd0 = tb.read(instruction.operands[0])

        if oprnd0.size == 8:
            oprnd1 = ReilRegisterOperand("al", 8)

            result_low = ReilRegisterOperand("al", 8)
            result_high = ReilRegisterOperand("ah", 8)
        elif oprnd0.size == 16:
            oprnd1 = ReilRegisterOperand("ax", 16)

            result_low = ReilRegisterOperand("dx", 16)
            result_high = ReilRegisterOperand("ax", 16)
        elif oprnd0.size == 32:
            oprnd1 = ReilRegisterOperand("eax", 32)

            result_low = ReilRegisterOperand("edx", 32)
            result_high = ReilRegisterOperand("eax", 32)
        elif oprnd0.size == 64:
            oprnd1 = ReilRegisterOperand("rax", 64)

            result_low = ReilRegisterOperand("rdx", 64)
            result_high = ReilRegisterOperand("rax", 64)

    elif len(instruction.operands) == 2:

        oprnd0 = tb.read(instruction.operands[0])
        oprnd1 = tb.read(instruction.operands[1])

    elif len(instruction.operands) == 3:

        oprnd0 = tb.read(instruction.operands[1])
        oprnd1 = tb.read(instruction.operands[2])

    imm0 = tb.immediate(-oprnd0.size, 2 * oprnd0.size)

    tmp0 = tb.temporal(2 * oprnd0.size)

    # Do multiplication.
    tb.add(self._builder.gen_mul(oprnd0, oprnd1, tmp0))

    # Save result.
    if len(instruction.operands) == 1:

        tb.add(self._builder.gen_bsh(tmp0, imm0, result_high))
        tb.add(self._builder.gen_str(tmp0, result_low))

    elif len(instruction.operands) == 2:

        tb.write(instruction.operands[0], tmp0)

    elif len(instruction.operands) == 3:

        tb.write(instruction.operands[0], tmp0)

    # Flags : OF, CF
    # TODO: Implement.
    self._undefine_flag(tb, self._flags["sf"])
    self._undefine_flag(tb, self._flags["zf"])
    self._undefine_flag(tb, self._flags["af"])
    self._undefine_flag(tb, self._flags["pf"])


def _translate_div(self, tb, instruction):
    # Flags Affected
    # The CF, OF, SF, ZF, AF, and PF flags are undefined.

    oprnd0 = tb.read(instruction.operands[0])

    if oprnd0.size == 8:
        oprnd1 = ReilRegisterOperand("ah", 8)
        oprnd2 = ReilRegisterOperand("al", 8)
        result_low = ReilRegisterOperand("al", 8)
        result_high = ReilRegisterOperand("ah", 8)
    elif oprnd0.size == 16:
        oprnd1 = ReilRegisterOperand("dx", 16)
        oprnd2 = ReilRegisterOperand("ax", 16)
        result_low = ReilRegisterOperand("ax", 16)
        result_high = ReilRegisterOperand("dx", 16)
    elif oprnd0.size == 32:
        oprnd1 = ReilRegisterOperand("edx", 32)
        oprnd2 = ReilRegisterOperand("eax", 32)
        result_low = ReilRegisterOperand("eax", 32)
        result_high = ReilRegisterOperand("edx", 32)
    elif oprnd0.size == 64:
        oprnd1 = ReilRegisterOperand("rdx", 64)
        oprnd2 = ReilRegisterOperand("rax", 64)
        result_low = ReilRegisterOperand("rax", 64)
        result_high = ReilRegisterOperand("rdx", 64)

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

    # Store result.
    # TODO: Improve this code.
    if self._arch_info.architecture_mode == ARCH_X86_MODE_64 and result_low.size == 32:
        if result_low.name in tb._regs_mapper:
            base_reg, offset = tb._regs_mapper[result_low.name]

            reil_operand_base = ReilRegisterOperand(base_reg, tb._regs_size[base_reg])
            reil_immediate = ReilImmediateOperand(0x0, tb._regs_size[base_reg])

            tb.add(self._builder.gen_str(reil_immediate, reil_operand_base))

    tb.add(self._builder.gen_str(tmp5, result_low))

    # TODO: Improve this code.
    if self._arch_info.architecture_mode == ARCH_X86_MODE_64 and result_high.size == 32:
        if result_high.name in tb._regs_mapper:
            base_reg, offset = tb._regs_mapper[result_high.name]

            reil_operand_base = ReilRegisterOperand(base_reg, tb._regs_size[base_reg])
            reil_immediate = ReilImmediateOperand(0x0, tb._regs_size[base_reg])

            tb.add(self._builder.gen_str(reil_immediate, reil_operand_base))

    tb.add(self._builder.gen_str(tmp6, result_high))

    # Flags : CF, OF, SF, ZF, AF, PF
    self._undefine_flag(tb, self._flags["cf"])
    self._undefine_flag(tb, self._flags["of"])
    self._undefine_flag(tb, self._flags["sf"])
    self._undefine_flag(tb, self._flags["zf"])
    self._undefine_flag(tb, self._flags["af"])
    self._undefine_flag(tb, self._flags["pf"])


def _translate_idiv(self, tb, instruction):
    # Flags Affected
    # The CF, OF, SF, ZF, AF, and PF flags are undefined.

    oprnd0 = tb.read(instruction.operands[0])

    if oprnd0.size == 8:
        oprnd1 = ReilRegisterOperand("ah", 8)
        oprnd2 = ReilRegisterOperand("al", 8)
        result_low = ReilRegisterOperand("al", 8)
        result_high = ReilRegisterOperand("ah", 8)
    elif oprnd0.size == 16:
        oprnd1 = ReilRegisterOperand("dx", 16)
        oprnd2 = ReilRegisterOperand("ax", 16)
        result_low = ReilRegisterOperand("ax", 16)
        result_high = ReilRegisterOperand("dx", 16)
    elif oprnd0.size == 32:
        oprnd1 = ReilRegisterOperand("edx", 32)
        oprnd2 = ReilRegisterOperand("eax", 32)
        result_low = ReilRegisterOperand("eax", 32)
        result_high = ReilRegisterOperand("edx", 32)
    elif oprnd0.size == 64:
        oprnd1 = ReilRegisterOperand("rdx", 64)
        oprnd2 = ReilRegisterOperand("rax", 64)
        result_low = ReilRegisterOperand("rax", 64)
        result_high = ReilRegisterOperand("rdx", 64)

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

    # Store result.
    # TODO: Improve this code.
    if self._arch_info.architecture_mode == ARCH_X86_MODE_64 and result_low.size == 32:
        if result_low.name in tb._regs_mapper:
            base_reg, offset = tb._regs_mapper[result_low.name]

            reil_operand_base = ReilRegisterOperand(base_reg, tb._regs_size[base_reg])
            reil_immediate = ReilImmediateOperand(0x0, tb._regs_size[base_reg])

            tb.add(self._builder.gen_str(reil_immediate, reil_operand_base))

    tb.add(self._builder.gen_str(tmp5, result_low))

    # TODO: Improve this code.
    if self._arch_info.architecture_mode == ARCH_X86_MODE_64 and result_high.size == 32:
        if result_high.name in tb._regs_mapper:
            base_reg, offset = tb._regs_mapper[result_high.name]

            reil_operand_base = ReilRegisterOperand(base_reg, tb._regs_size[base_reg])
            reil_immediate = ReilImmediateOperand(0x0, tb._regs_size[base_reg])

            tb.add(self._builder.gen_str(reil_immediate, reil_operand_base))

    tb.add(self._builder.gen_str(tmp6, result_high))

    # Flags : CF, OF, SF, ZF, AF, PF
    self._undefine_flag(tb, self._flags["cf"])
    self._undefine_flag(tb, self._flags["of"])
    self._undefine_flag(tb, self._flags["sf"])
    self._undefine_flag(tb, self._flags["zf"])
    self._undefine_flag(tb, self._flags["af"])
    self._undefine_flag(tb, self._flags["pf"])


def _translate_inc(self, tb, instruction):
    # Flags Affected
    # The CF flag is not affected. The OF, SF, ZF, AF, and PF flags
    # are set according to the result.

    oprnd0 = tb.read(instruction.operands[0])

    imm0 = tb.immediate(1, oprnd0.size)

    tmp0 = tb.temporal(oprnd0.size * 2)

    tb.add(self._builder.gen_add(oprnd0, imm0, tmp0))

    # Flags : OF, SF, ZF, AF, PF
    self._update_of(tb, oprnd0, imm0, tmp0)
    self._update_sf(tb, oprnd0, imm0, tmp0)
    self._update_zf(tb, oprnd0, imm0, tmp0)
    self._update_af(tb, oprnd0, imm0, tmp0)
    self._update_pf(tb, oprnd0, imm0, tmp0)

    tb.write(instruction.operands[0], tmp0)


def _translate_dec(self, tb, instruction):
    # Flags Affected
    # The CF flag is not affected. The OF, SF, ZF, AF, and PF flags
    # are set according to the result.

    oprnd0 = tb.read(instruction.operands[0])

    imm0 = tb.immediate(1, oprnd0.size)

    tmp0 = tb.temporal(oprnd0.size * 2)

    tb.add(self._builder.gen_sub(oprnd0, imm0, tmp0))

    # Flags : OF, SF, ZF, AF, PF
    self._update_of_sub(tb, oprnd0, imm0, tmp0)
    self._update_sf(tb, oprnd0, imm0, tmp0)
    self._update_zf(tb, oprnd0, imm0, tmp0)
    self._update_af_sub(tb, oprnd0, imm0, tmp0)
    self._update_pf(tb, oprnd0, imm0, tmp0)

    tb.write(instruction.operands[0], tmp0)


def _translate_neg(self, tb, instruction):
    # Flags Affected
    # The CF flag set to 0 if the source operand is 0; otherwise it
    # is set to 1. The OF, SF, ZF, AF, and PF flags are set
    # according to the result.

    oprnd0 = tb.read(instruction.operands[0])

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
    tb.add(self._builder.gen_xor(tmp2, imm2, self._flags["cf"]))

    # Flags : OF, SF, ZF, AF, PF
    self._update_of_sub(tb, oprnd0, oprnd0, tmp1)
    self._update_sf(tb, oprnd0, oprnd0, tmp1)
    self._update_zf(tb, oprnd0, oprnd0, tmp1)
    self._update_af_sub(tb, zero, oprnd0, tmp1)
    self._update_pf(tb, oprnd0, oprnd0, tmp1)

    tb.write(instruction.operands[0], tmp1)


def _translate_cmp(self, tb, instruction):
    # Flags Affected
    # The CF, OF, SF, ZF, AF, and PF flags are set according to the
    # result.

    oprnd0 = tb.read(instruction.operands[0])
    oprnd1 = tb.read(instruction.operands[1])

    tmp0 = tb.temporal(oprnd0.size * 2)

    tb.add(self._builder.gen_sub(oprnd0, oprnd1, tmp0))

    # Flags : CF, OF, SF, ZF, AF, PF
    self._update_cf(tb, oprnd0, oprnd1, tmp0)
    self._update_of_sub(tb, oprnd0, oprnd1, tmp0)
    self._update_sf(tb, oprnd0, oprnd1, tmp0)
    self._update_zf(tb, oprnd0, oprnd1, tmp0)
    self._update_af_sub(tb, oprnd0, oprnd1, tmp0)
    self._update_pf(tb, oprnd0, oprnd1, tmp0)


dispatcher = {
    '_translate_add': _translate_add,
    '_translate_adc': _translate_adc,
    '_translate_sub': _translate_sub,
    '_translate_sbb': _translate_sbb,
    '_translate_mul': _translate_mul,
    '_translate_imul': _translate_imul,
    '_translate_div': _translate_div,
    '_translate_idiv': _translate_idiv,
    '_translate_inc': _translate_inc,
    '_translate_dec': _translate_dec,
    '_translate_neg': _translate_neg,
    '_translate_cmp': _translate_cmp,
}
