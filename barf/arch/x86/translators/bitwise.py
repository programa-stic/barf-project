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

from barf.arch import ARCH_X86_MODE_32
from barf.arch import ARCH_X86_MODE_64
from barf.core.reil import ReilImmediateOperand
from barf.core.reil import ReilLabel


# "Bit and Byte Instructions"
# ============================================================================ #
def _translate_bsf(self, tb, instruction):
    # Flags Affected
    # The ZF flag is set to 1 if all the source operand is 0;
    # otherwise, the ZF flag is cleared. The CF, OF, SF, AF, and PF,
    # flags are undefined.

    # Operation
    # IF SRC = 0
    #     THEN
    #         ZF <- 1;
    #         DEST is undefined;
    #     ELSE
    #         ZF <- 0;
    #         temp <- 0;
    #         WHILE Bit(SRC, temp) = 0
    #         DO
    #             temp <- temp + 1;
    #         OD;
    #         DEST <- temp;
    # FI;

    oprnd0 = self._reg_acc_translator.read(tb, instruction.operands[0])
    oprnd1 = self._reg_acc_translator.read(tb, instruction.operands[1])

    zf = self._flags.zf
    tmp = tb.temporal(oprnd1.size)
    tmp1 = tb.temporal(oprnd1.size)
    bit_curr = tb.temporal(1)
    dst = tb.temporal(oprnd0.size)
    src_is_zero = tb.temporal(1)
    bit_zero = tb.temporal(1)

    src_is_zero_lbl = ReilLabel('src_is_zero_lbl')
    loop_lbl = ReilLabel('loop_lbl')
    end_lbl = ReilLabel('end_lbl')

    tb.add(self._builder.gen_bisz(oprnd1, src_is_zero))
    tb.add(self._builder.gen_jcc(src_is_zero, src_is_zero_lbl))

    # if src != 0 ...
    tb.add(self._builder.gen_str(tb.immediate(0, 1), zf))
    tb.add(self._builder.gen_str(tb.immediate(1, tmp.size), tmp))
    tb.add(self._builder.gen_str(tb.immediate(-1, tmp1.size), tmp1))

    # while bit(src, tmp) == 0 ...
    tb.add(loop_lbl)
    tb.add(self._builder.gen_sub(tmp, tb.immediate(1, tmp.size), tmp))
    tb.add(self._builder.gen_add(tmp1, tb.immediate(1, tmp.size), tmp1))

    tb.add(self._builder.gen_bsh(oprnd1, tmp, bit_curr))
    tb.add(self._builder.gen_bisz(bit_curr, bit_zero))
    tb.add(self._builder.gen_jcc(bit_zero, loop_lbl))

    # Save result.
    tb.add(self._builder.gen_str(tmp1, dst))

    # jump to the end.
    tb.add(self._builder.gen_jcc(tb.immediate(1, 1), end_lbl))

    # If src == 0 ...
    tb.add(src_is_zero_lbl)
    tb.add(self._builder.gen_str(tb.immediate(1, 1), zf))
    # Undefine dst (set the same value).
    tb.add(self._builder.gen_str(oprnd0, dst))

    tb.add(end_lbl)

    # Set flags.
    # Flags : CF, OF, SF, AF, and PF
    self._flag_translator.undefine_flag(tb, self._flags.cf)
    self._flag_translator.undefine_flag(tb, self._flags.of)
    self._flag_translator.undefine_flag(tb, self._flags.sf)
    self._flag_translator.undefine_flag(tb, self._flags.af)
    self._flag_translator.undefine_flag(tb, self._flags.pf)

    self._reg_acc_translator.write(tb, instruction.operands[0], dst)


def _translate_bt(self, tb, instruction):
    # Flags Affected
    # The CF flag contains the value of the selected bit. The ZF
    # flag is unaffected. The OF, SF, AF, and PF flags are
    # undefined.

    oprnd0 = self._reg_acc_translator.read(tb, instruction.operands[0])
    oprnd1 = self._reg_acc_translator.read(tb, instruction.operands[1])

    tmp0 = tb.temporal(oprnd0.size)
    zero = tb.immediate(0, oprnd0.size)
    one = tb.immediate(1, oprnd0.size)
    bit_base_size = tb.immediate(oprnd0.size, oprnd1.size)
    bit_offset_tmp = tb.temporal(oprnd0.size)
    bit_offset = tb.temporal(oprnd0.size)

    # Compute bit offset.
    tb.add(self._builder.gen_mod(oprnd1, bit_base_size, bit_offset_tmp))
    tb.add(self._builder.gen_sub(zero, bit_offset_tmp, bit_offset))  # negate

    # Extract bit.
    tb.add(self._builder.gen_bsh(oprnd0, bit_offset, tmp0))

    # Set CF.
    tb.add(self._builder.gen_and(tmp0, one, self._flags.cf))

    # Set flags.
    # Flags : OF, SF, AF, PF
    self._flag_translator.undefine_flag(tb, self._flags.of)
    self._flag_translator.undefine_flag(tb, self._flags.sf)
    self._flag_translator.undefine_flag(tb, self._flags.af)
    self._flag_translator.undefine_flag(tb, self._flags.pf)


def _translate_bts(self, tb, instruction):
    # Flags Affected
    # The CF flag contains the value of the selected bit before it
    # is set. The ZF flag is unaffected. The OF, SF, AF, and PF
    # flags are undefined.

    # Operation
    # CF <- Bit(BitBase, BitOffset);
    # Bit(BitBase, BitOffset) <- 1;

    # TODO Refactor code into a Bit function (this code is a copy of
    # BT instruction translation.)
    oprnd0 = self._reg_acc_translator.read(tb, instruction.operands[0])
    oprnd1 = self._reg_acc_translator.read(tb, instruction.operands[1])

    zero = tb.immediate(0, oprnd0.size)
    one = tb.immediate(1, oprnd0.size)
    bit_base_size = tb.immediate(oprnd0.size, oprnd1.size)
    bit_offset_tmp = tb.temporal(oprnd0.size)
    bit_offset = tb.temporal(oprnd0.size)

    offset = tb.temporal(oprnd1.size)
    tmp0 = tb.temporal(oprnd0.size)
    dst = tb.temporal(oprnd0.size)

    # Compute bit offset.
    tb.add(self._builder.gen_mod(oprnd1, bit_base_size, bit_offset_tmp))
    tb.add(self._builder.gen_sub(zero, bit_offset_tmp, bit_offset))  # negate

    # Extract bit.
    tb.add(self._builder.gen_bsh(oprnd0, bit_offset, tmp0))

    # Set CF.
    tb.add(self._builder.gen_and(tmp0, one, self._flags.cf))

    # Set bit in dst.
    tb.add(self._builder.gen_mod(oprnd1, bit_base_size, offset))
    tb.add(self._builder.gen_bsh(one, offset, tmp0))

    tb.add(self._builder.gen_or(oprnd0, tmp0, dst))

    # Set flags.
    # Flags : OF, SF, AF, PF
    self._flag_translator.undefine_flag(tb, self._flags.of)
    self._flag_translator.undefine_flag(tb, self._flags.sf)
    self._flag_translator.undefine_flag(tb, self._flags.af)
    self._flag_translator.undefine_flag(tb, self._flags.pf)

    self._reg_acc_translator.write(tb, instruction.operands[0], dst)


def _translate_test(self, tb, instruction):
    # Flags Affected
    # The OF and CF flags are set to 0. The SF, ZF, and PF flags are
    # set according to the result (see the "Operation" section
    # above). The state of the AF flag is undefined.

    oprnd0 = self._reg_acc_translator.read(tb, instruction.operands[0])
    oprnd1 = self._reg_acc_translator.read(tb, instruction.operands[1])

    tmp0 = tb.temporal(oprnd0.size)

    tb.add(self._builder.gen_and(oprnd0, oprnd1, tmp0))

    # Flags : OF, CF
    self._flag_translator.clear_flag(tb, self._flags.of)
    self._flag_translator.clear_flag(tb, self._flags.cf)

    # Flags : SF, ZF, PF
    self._flag_translator.update_sf(tb, oprnd0, tmp0)
    self._flag_translator.update_zf(tb, oprnd0, tmp0)
    self._flag_translator.update_pf(tb, tmp0)

    # Flags : AF
    self._flag_translator.undefine_flag(tb, self._flags.af)


# "Shift and Rotate Instructions"
# ============================================================================ #
def _translate_rcl(self, tb, instruction):
    # Flags Affected
    # The CF flag contains the value of the bit shifted into it.
    # The OF flag is affected only for single-bit rotates (see
    # "Description" above); it is undefined for multi-bit rotates.
    # The SF, ZF, AF, and PF flags are not affected.

    oprnd0 = self._reg_acc_translator.read(tb, instruction.operands[0])
    oprnd1 = self._reg_acc_translator.read(tb, instruction.operands[1])

    tmp_cf_ext = tb.temporal(oprnd0.size * 2)
    tmp_cf_ext_1 = tb.temporal(oprnd0.size * 2)

    oprnd_ext = tb.temporal(oprnd0.size * 2)
    oprnd_ext_1 = tb.temporal(oprnd0.size * 2)
    oprnd_ext_shifted = tb.temporal(oprnd0.size * 2)
    oprnd_ext_shifted_l = tb.temporal(oprnd0.size)
    oprnd_ext_shifted_h = tb.temporal(oprnd0.size)

    result = tb.temporal(oprnd0.size)
    result_msb = tb.temporal(1)

    tmp1 = tb.temporal(1)
    tmp1_zero = tb.temporal(1)

    imm1 = tb.immediate(1, oprnd0.size)
    imm2 = tb.immediate(-(oprnd0.size + 1), oprnd0.size * 2)
    imm4 = tb.immediate(oprnd0.size, oprnd0.size * 2)

    if oprnd0.size == 8:
        count_mask = tb.immediate(0x1f, oprnd0.size)
        tmp0 = tb.temporal(oprnd0.size)
        count = tb.temporal(oprnd0.size)
        temp_count = tb.temporal(oprnd_ext.size)
        mod_amount = tb.immediate(9, oprnd0.size)

        tb.add(self._builder.gen_str(oprnd1, count))
        tb.add(self._builder.gen_and(count, count_mask, tmp0))
        tb.add(self._builder.gen_mod(tmp0, mod_amount, temp_count))
    elif oprnd0.size == 16:
        count_mask = tb.immediate(0x1f, oprnd0.size)
        tmp0 = tb.temporal(oprnd0.size)
        count = tb.temporal(oprnd0.size)
        temp_count = tb.temporal(oprnd_ext.size)
        mod_amount = tb.immediate(17, oprnd0.size)

        tb.add(self._builder.gen_str(oprnd1, count))
        tb.add(self._builder.gen_and(count, count_mask, tmp0))
        tb.add(self._builder.gen_mod(tmp0, mod_amount, temp_count))
    elif oprnd0.size == 32:
        count_mask = tb.immediate(0x1f, oprnd0.size)
        tmp0 = tb.temporal(oprnd0.size)
        count = tb.temporal(oprnd0.size)
        temp_count = tb.temporal(oprnd_ext.size)

        tb.add(self._builder.gen_str(oprnd1, count))
        tb.add(self._builder.gen_and(count, count_mask, tmp0))
        tb.add(self._builder.gen_str(tmp0, temp_count))
    elif oprnd0.size == 64:
        count_mask = tb.immediate(0x3f, oprnd0.size)
        tmp0 = tb.temporal(oprnd0.size)
        count = tb.temporal(oprnd0.size)
        temp_count = tb.temporal(oprnd_ext.size)

        tb.add(self._builder.gen_str(oprnd1, count))
        tb.add(self._builder.gen_and(count, count_mask, tmp0))
        tb.add(self._builder.gen_str(tmp0, temp_count))
    else:
        raise Exception('Invalid operand size: %d', oprnd0.size)

    tb.add(self._builder.gen_str(oprnd0, oprnd_ext_1))

    # Insert CF.
    tb.add(self._builder.gen_str(self._flags.cf, tmp_cf_ext))
    tb.add(self._builder.gen_bsh(tmp_cf_ext, imm4, tmp_cf_ext_1))
    tb.add(self._builder.gen_or(tmp_cf_ext_1, oprnd_ext_1, oprnd_ext))

    tb.add(self._builder.gen_bsh(oprnd_ext, temp_count, oprnd_ext_shifted))
    tb.add(self._builder.gen_bsh(oprnd_ext_shifted, imm2, oprnd_ext_shifted_h))
    tb.add(self._builder.gen_str(oprnd_ext_shifted, oprnd_ext_shifted_l))
    tb.add(self._builder.gen_or(oprnd_ext_shifted_l, oprnd_ext_shifted_h, result))

    # Compute CF.
    tb.add(self._builder.gen_str(result, self._flags.cf))

    # Compute OF.
    undef_of_lbl = tb.label('undef_of_lbl')

    tb.add(self._builder.gen_sub(count, imm1, tmp1))
    tb.add(self._builder.gen_bisz(tmp1, tmp1_zero))
    tb.add(self._builder.gen_jcc(tmp1_zero, undef_of_lbl))

    # Compute.
    imm3_1 = tb.immediate(-(oprnd0.size + 1), result.size)

    tb.add(self._builder.gen_bsh(result, imm3_1, result_msb))
    tb.add(self._builder.gen_xor(result_msb, self._flags.cf, self._flags.of))

    # Undef OF.
    tb.add(undef_of_lbl)
    self._flag_translator.undefine_flag(tb, self._flags.of)

    self._reg_acc_translator.write(tb, instruction.operands[0], result)


def _translate_rcr(self, tb, instruction):
    # Flags Affected
    # The CF flag contains the value of the bit shifted into it.
    # The OF flag is affected only for single-bit rotates (see
    # "Description" above); it is undefined for multi-bit rotates.
    # The SF, ZF, AF, and PF flags are not affected.

    # XXX: Fix OF flag

    oprnd0 = self._reg_acc_translator.read(tb, instruction.operands[0])
    oprnd1 = self._reg_acc_translator.read(tb, instruction.operands[1])

    tmp0_1 = tb.temporal(oprnd0.size)
    zero = tb.immediate(0, oprnd0.size)

    # TODO: Improve this translation. It uses unnecessary large
    # register...
    tmp_cf_ext = tb.temporal(oprnd0.size * 4)

    oprnd_ext = tb.temporal(oprnd0.size * 4)
    oprnd_ext_1 = tb.temporal(oprnd0.size * 4)
    oprnd_ext_2 = tb.temporal(oprnd0.size * 4)
    oprnd_ext_shifted = tb.temporal(oprnd0.size * 4)
    oprnd_ext_shifted_l = tb.temporal(oprnd0.size)
    oprnd_ext_shifted_h = tb.temporal(oprnd0.size)
    oprnd_ext_shifted_h_1 = tb.temporal(oprnd0.size)

    result = tb.temporal(oprnd0.size)
    result_msb = tb.temporal(1)

    tmp1 = tb.temporal(1)
    tmp1_zero = tb.temporal(1)

    imm1 = tb.immediate(1, oprnd0.size)
    imm7 = tb.immediate(-(oprnd0.size - 1), oprnd0.size)

    cf_old = tb.temporal(1)

    if oprnd0.size == 8:
        count_mask = tb.immediate(0x1f, oprnd0.size)
        tmp0 = tb.temporal(oprnd0.size)
        count = tb.temporal(oprnd0.size)
        temp_count = tb.temporal(oprnd_ext.size)
        mod_amount = tb.immediate(9, oprnd0.size)

        tb.add(self._builder.gen_str(oprnd1, count))
        tb.add(self._builder.gen_and(count, count_mask, tmp0_1))
        tb.add(self._builder.gen_mod(tmp0_1, mod_amount, tmp0))
    elif oprnd0.size == 16:
        count_mask = tb.immediate(0x1f, oprnd0.size)
        tmp0 = tb.temporal(oprnd0.size)
        count = tb.temporal(oprnd0.size)
        temp_count = tb.temporal(oprnd_ext.size)
        mod_amount = tb.immediate(17, oprnd0.size)

        tb.add(self._builder.gen_str(oprnd1, count))
        tb.add(self._builder.gen_and(count, count_mask, tmp0_1))
        tb.add(self._builder.gen_mod(tmp0_1, mod_amount, tmp0))
    elif oprnd0.size == 32:
        count_mask = tb.immediate(0x1f, oprnd0.size)
        tmp0 = tb.temporal(oprnd0.size)
        count = tb.temporal(oprnd0.size)
        temp_count = tb.temporal(oprnd_ext.size)

        tb.add(self._builder.gen_str(oprnd1, count))
        tb.add(self._builder.gen_and(count, count_mask, tmp0))
    elif oprnd0.size == 64:
        count_mask = tb.immediate(0x3f, oprnd0.size)
        tmp0 = tb.temporal(oprnd0.size)
        count = tb.temporal(oprnd0.size)
        temp_count = tb.temporal(oprnd_ext.size)

        tb.add(self._builder.gen_str(oprnd1, count))
        tb.add(self._builder.gen_and(count, count_mask, tmp0))
    else:
        raise Exception('Invalid operand size: %d', oprnd0.size)

    tb.add(self._builder.gen_sub(zero, tmp0, temp_count))

    # Backup CF.
    tb.add(self._builder.gen_str(self._flags.cf, cf_old))

    # Insert CF.
    one_1 = tb.immediate(1, oprnd0.size)

    tb.add(self._builder.gen_bsh(oprnd0, one_1, oprnd_ext_1))
    tb.add(self._builder.gen_str(self._flags.cf, tmp_cf_ext))
    tb.add(self._builder.gen_or(tmp_cf_ext, oprnd_ext_1, oprnd_ext_2))

    # Rotate register.
    size_1 = tb.immediate(oprnd0.size, oprnd_ext_2.size)
    msize_1 = tb.immediate(-oprnd0.size, oprnd_ext_shifted.size)
    mone_1 = tb.immediate(-1, oprnd_ext_shifted_h_1.size)

    tb.add(self._builder.gen_bsh(oprnd_ext_2, size_1, oprnd_ext))

    tb.add(self._builder.gen_bsh(oprnd_ext, temp_count, oprnd_ext_shifted))
    tb.add(self._builder.gen_bsh(oprnd_ext_shifted, msize_1, oprnd_ext_shifted_h_1))
    tb.add(self._builder.gen_bsh(oprnd_ext_shifted_h_1, mone_1, oprnd_ext_shifted_h))
    tb.add(self._builder.gen_str(oprnd_ext_shifted, oprnd_ext_shifted_l))
    tb.add(self._builder.gen_or(oprnd_ext_shifted_l, oprnd_ext_shifted_h, result))

    # Compute CF.
    tb.add(self._builder.gen_str(oprnd_ext_shifted_h_1, self._flags.cf))

    # Compute OF.
    undef_of_lbl = tb.label('undef_of_lbl')

    tb.add(self._builder.gen_sub(count, imm1, tmp1))
    tb.add(self._builder.gen_bisz(tmp1, tmp1_zero))
    tb.add(self._builder.gen_jcc(tmp1_zero, undef_of_lbl))

    # Compute.
    tb.add(self._builder.gen_bsh(oprnd0, imm7, result_msb))
    tb.add(self._builder.gen_xor(result_msb, cf_old, self._flags.of))

    # Undef OF.
    tb.add(undef_of_lbl)
    self._flag_translator.undefine_flag(tb, self._flags.of)

    self._reg_acc_translator.write(tb, instruction.operands[0], result)


def _translate_rol(self, tb, instruction):
    # Flags Affected
    # The CF flag contains the value of the bit shifted into it.
    # The OF flag is affected only for single-bit rotates (see
    # "Description" above); it is undefined for multi-bit rotates.
    # The SF, ZF, AF, and PF flags are not affected.

    oprnd0 = self._reg_acc_translator.read(tb, instruction.operands[0])
    oprnd1 = self._reg_acc_translator.read(tb, instruction.operands[1])

    size = tb.immediate(oprnd0.size, oprnd0.size)

    if self._arch_mode == ARCH_X86_MODE_32:
        count_mask = tb.immediate(0x1f, oprnd0.size)
    elif self._arch_mode == ARCH_X86_MODE_64:
        count_mask = tb.immediate(0x3f, oprnd0.size)

    count_masked = tb.temporal(oprnd0.size)
    count = tb.temporal(oprnd0.size)

    oprnd_ext = tb.temporal(oprnd0.size * 2)
    oprnd_ext_shifted = tb.temporal(oprnd0.size * 2)
    oprnd_ext_shifted_l = tb.temporal(oprnd0.size)
    oprnd_ext_shifted_h = tb.temporal(oprnd0.size)

    temp_count = tb.temporal(oprnd_ext.size)

    result = tb.temporal(oprnd0.size)
    result_msb = tb.temporal(1)

    tmp0 = tb.temporal(1)
    tmp0_zero = tb.temporal(1)

    imm0 = tb.immediate(1, oprnd0.size)
    imm1 = tb.immediate(-oprnd0.size, oprnd0.size * 2)
    imm2 = tb.immediate(-(oprnd0.size + 1), oprnd0.size)

    # Compute temp count.
    tb.add(self._builder.gen_str(oprnd1, count))
    tb.add(self._builder.gen_and(count, count_mask, count_masked))
    tb.add(self._builder.gen_mod(count_masked, size, temp_count))

    # Rotate register.
    tb.add(self._builder.gen_str(oprnd0, oprnd_ext))
    tb.add(self._builder.gen_bsh(oprnd_ext, temp_count, oprnd_ext_shifted))
    tb.add(self._builder.gen_bsh(oprnd_ext_shifted, imm1, oprnd_ext_shifted_h))
    tb.add(self._builder.gen_str(oprnd_ext_shifted, oprnd_ext_shifted_l))
    tb.add(self._builder.gen_or(oprnd_ext_shifted_l, oprnd_ext_shifted_h, result))

    # Compute CF.
    tb.add(self._builder.gen_str(result, self._flags.cf))

    # Compute OF.
    undef_of_lbl = tb.label('undef_of_lbl')

    tb.add(self._builder.gen_sub(count_masked, imm0, tmp0))
    tb.add(self._builder.gen_bisz(tmp0, tmp0_zero))
    tb.add(self._builder.gen_jcc(tmp0_zero, undef_of_lbl))

    # Compute.
    tb.add(self._builder.gen_bsh(result, imm2, result_msb))
    tb.add(self._builder.gen_xor(result_msb, self._flags.cf, self._flags.of))

    # Undef OF.
    tb.add(undef_of_lbl)
    self._flag_translator.undefine_flag(tb, self._flags.of)

    self._reg_acc_translator.write(tb, instruction.operands[0], result)


def _translate_ror(self, tb, instruction):
    # Flags Affected
    # The CF flag contains the value of the bit shifted into it.
    # The OF flag is affected only for single-bit rotates (see
    # "Description" above); it is undefined for multi-bit rotates.
    # The SF, ZF, AF, and PF flags are not affected.

    oprnd0 = self._reg_acc_translator.read(tb, instruction.operands[0])
    oprnd1 = self._reg_acc_translator.read(tb, instruction.operands[1])

    size = tb.immediate(oprnd0.size, oprnd0.size)

    if self._arch_mode == ARCH_X86_MODE_32:
        count_mask = tb.immediate(0x1f, oprnd0.size)
    elif self._arch_mode == ARCH_X86_MODE_64:
        count_mask = tb.immediate(0x3f, oprnd0.size)

    count = tb.temporal(oprnd0.size)

    oprnd_ext = tb.temporal(oprnd0.size * 2)
    oprnd_ext_shifted = tb.temporal(oprnd0.size * 2)
    oprnd_ext_shifted_l = tb.temporal(oprnd0.size)
    oprnd_ext_shifted_h = tb.temporal(oprnd0.size)

    temp_count = tb.temporal(oprnd_ext.size)

    result = tb.temporal(oprnd0.size)
    result_msb = tb.temporal(1)
    result_msb_prev = tb.temporal(1)

    tmp0 = tb.temporal(oprnd0.size)
    tmp1 = tb.temporal(1)
    tmp1_zero = tb.temporal(1)
    tmp2 = tb.temporal(oprnd0.size)
    tmp3 = tb.temporal(1)

    zero = tb.immediate(0, oprnd0.size)
    imm1 = tb.immediate(1, oprnd0.size)
    imm2 = tb.immediate(-oprnd0.size, oprnd0.size * 2)
    imm3 = tb.immediate(-(oprnd0.size + 1), oprnd0.size)
    imm4 = tb.immediate(-oprnd0.size + 1, oprnd0.size)
    imm5 = tb.immediate(oprnd0.size - 2, oprnd0.size)

    # Compute temp count.
    tb.add(self._builder.gen_str(oprnd1, count))
    tb.add(self._builder.gen_and(count, count_mask, tmp0))
    tb.add(self._builder.gen_mod(tmp0, size, tmp2))
    tb.add(self._builder.gen_sub(zero, tmp2, temp_count))

    # Rotate register.
    tb.add(self._builder.gen_bsh(oprnd0, size, oprnd_ext))
    tb.add(self._builder.gen_bsh(oprnd_ext, temp_count, oprnd_ext_shifted))
    tb.add(self._builder.gen_bsh(oprnd_ext_shifted, imm2, oprnd_ext_shifted_h))
    tb.add(self._builder.gen_str(oprnd_ext_shifted, oprnd_ext_shifted_l))
    tb.add(self._builder.gen_or(oprnd_ext_shifted_l, oprnd_ext_shifted_h, result))

    # Compute CF.
    tb.add(self._builder.gen_bsh(result, imm4, tmp3))
    tb.add(self._builder.gen_str(tmp3, self._flags.cf))

    # Compute OF.
    undef_of_lbl = tb.label('undef_of_lbl')

    tb.add(self._builder.gen_sub(tmp0, imm1, tmp1))
    tb.add(self._builder.gen_bisz(tmp1, tmp1_zero))
    tb.add(self._builder.gen_jcc(tmp1_zero, undef_of_lbl))

    # Compute.
    tb.add(self._builder.gen_bsh(result, imm3, result_msb))
    tb.add(self._builder.gen_bsh(result, imm5, result_msb_prev))
    tb.add(self._builder.gen_xor(result_msb, result_msb_prev, self._flags.of))

    # Undef OF.
    tb.add(undef_of_lbl)
    self._flag_translator.undefine_flag(tb, self._flags.of)

    self._reg_acc_translator.write(tb, instruction.operands[0], result)


def _translate_sal(self, tb, instruction):
    # Flags Affected
    # The CF flag contains the value of the last bit shifted out
    # of the destination operand; it is undefined for SHL and SHR
    # instructions where the count is greater than or equal to the
    # size (in bits) of the destination operand. The OF flag is
    # affected only for 1-bit shifts (see "Description" above);
    # otherwise, it is undefined. The SF, ZF, and PF flags are set
    # according to the result. If the count is 0, the flags are
    # not affected. For a non-zero count, the AF flag is
    # undefined.

    # TODO: Fix flag translation.

    return _translate_shl(self, tb, instruction)


def _translate_sar(self, tb, instruction):
    # Flags Affected
    # The CF flag contains the value of the last bit shifted out
    # of the destination operand; it is undefined for SHL and SHR
    # instructions where the count is greater than or equal to the
    # size (in bits) of the destination operand. The OF flag is
    # affected only for 1-bit shifts (see "Description" above);
    # otherwise, it is undefined. The SF, ZF, and PF flags are set
    # according to the result. If the count is 0, the flags are
    # not affected. For a non-zero count, the AF flag is
    # undefined.

    # TODO: Fix flag translation.

    oprnd0 = self._reg_acc_translator.read(tb, instruction.operands[0])
    oprnd1 = self._reg_acc_translator.read(tb, instruction.operands[1])

    imm0 = tb.immediate(2 ** (oprnd0.size - 1), oprnd0.size)
    imm1 = tb.immediate(1, oprnd0.size)
    imm2 = tb.immediate(-1, oprnd0.size)

    tmp0 = tb.temporal(oprnd0.size)
    tmp0_zero = tb.temporal(1)
    tmp1 = tb.temporal(oprnd0.size)
    tmp2 = tb.temporal(oprnd0.size)
    tmp3 = tb.temporal(oprnd0.size)
    tmp4 = tb.temporal(oprnd0.size)
    tmp5 = tb.temporal(oprnd0.size)
    tmp6 = tb.temporal(oprnd0.size)

    # Create labels.
    loop_lbl = tb.label('loop')
    skip_lbl = tb.label('skip')
    end_lbl = tb.label('end')

    # Initialize counter
    tb.add(self._builder.gen_str(oprnd1, tmp0))

    # Check counter
    tb.add(self._builder.gen_bisz(tmp0, tmp0_zero))
    tb.add(self._builder.gen_jcc(tmp0_zero, skip_lbl))

    # Copy operand to temporal register
    tb.add(self._builder.gen_str(oprnd0, tmp1))

    # Filter sign bit
    tb.add(self._builder.gen_and(oprnd0, imm0, tmp2))

    tb.add(loop_lbl)

    # Filter lsb bit
    tb.add(self._builder.gen_and(oprnd0, imm1, tmp6))
    tb.add(self._builder.gen_str(tmp6, self._flags.cf))

    # Shift right
    tb.add(self._builder.gen_bsh(tmp1, imm2, tmp3))

    # Propagate sign bit
    tb.add(self._builder.gen_or(tmp3, tmp2, tmp1))

    # Decrement counter
    tb.add(self._builder.gen_sub(tmp0, imm1, tmp0))

    # Compare counter to zero
    tb.add(self._builder.gen_bisz(tmp0, tmp4))

    # Invert stop flag
    tb.add(self._builder.gen_xor(tmp4, imm1, tmp5))

    # Iterate
    tb.add(self._builder.gen_jcc(tmp5, loop_lbl))

    # Save result
    tb.add(self._builder.gen_str(tmp1, tmp6))

    # Flags : OF
    # TODO: Implement translation for OF flag.

    # Flags : SF, ZF, PF
    self._flag_translator.update_sf(tb, oprnd0, tmp6)
    self._flag_translator.update_zf(tb, oprnd0, tmp6)
    self._flag_translator.update_pf(tb, tmp6)

    # Flags : AF
    self._flag_translator.undefine_flag(tb, self._flags.af)

    tb.add(self._builder.gen_jcc(tb.immediate(1, 1), end_lbl))

    # skip
    tb.add(skip_lbl)
    tb.add(self._builder.gen_str(oprnd0, tmp6))

    tb.add(end_lbl)

    self._reg_acc_translator.write(tb, instruction.operands[0], tmp6)


def _translate_shl(self, tb, instruction):
    # Flags Affected
    # The CF flag contains the value of the last bit shifted out
    # of the destination operand; it is undefined for SHL and SHR
    # instructions where the count is greater than or equal to the
    # size (in bits) of the destination operand. The OF flag is
    # affected only for 1-bit shifts (see "Description" above);
    # otherwise, it is undefined. The SF, ZF, and PF flags are set
    # according to the result. If the count is 0, the flags are
    # not affected. For a non-zero count, the AF flag is
    # undefined.

    # TODO: Fix flag translation.

    oprnd0 = self._reg_acc_translator.read(tb, instruction.operands[0])
    oprnd1 = self._reg_acc_translator.read(tb, instruction.operands[1])

    imm0 = tb.immediate(1, oprnd0.size)
    imm1 = tb.immediate(-31, oprnd0.size)

    if oprnd0.size <= 32:
        mask = tb.immediate(0x1f, oprnd1.size)
    elif oprnd0.size == 64:
        mask = tb.immediate(0x3f, oprnd1.size)
    else:
        raise Exception()

    tmp0 = tb.temporal(oprnd0.size)
    tmp1 = tb.temporal(oprnd0.size)
    tmp2 = tb.temporal(oprnd0.size)
    tmp3 = tb.temporal(1)
    tmp4 = tb.temporal(oprnd0.size)

    # Mask the 2nd operand and extend its size to match the size of
    # the 1st operand.
    tb.add(self._builder.gen_and(oprnd1, mask, tmp0))

    # Decrement in 1 shift amount
    tb.add(self._builder.gen_sub(tmp0, imm0, tmp1))

    # Shift left
    tb.add(self._builder.gen_bsh(oprnd0, tmp1, tmp2))

    # Save MSB in CF
    tb.add(self._builder.gen_bsh(tmp2, imm1, tmp3))
    tb.add(self._builder.gen_str(tmp3, self._flags.cf))

    # Shift one more time
    tb.add(self._builder.gen_bsh(tmp2, imm0, tmp4))

    # Flags : OF
    # TODO: Implement translation for OF flag.

    # Flags : SF, ZF, PF
    self._flag_translator.update_sf(tb, oprnd0, tmp4)
    self._flag_translator.update_zf(tb, oprnd0, tmp4)
    self._flag_translator.update_pf(tb, tmp4)

    # Flags : AF
    self._flag_translator.undefine_flag(tb, self._flags.af)

    self._reg_acc_translator.write(tb, instruction.operands[0], tmp4)


def _translate_shld(self, tb, instruction):
    # Flags Affected
    # If the count is 1 or greater, the CF flag is filled with the last
    # bit shifted out of the destination operand and the SF, ZF, and PF
    # flags are set according to the value of the result. For a 1-bit
    # shift, the OF flag is set if a sign change occurred; otherwise, it
    # is cleared. For shifts greater than 1 bit, the OF flag is undefined.
    # If a shift occurs, the AF flag is undefined. If the count operand is
    # 0, the flags are not affected. If the count is greater than the
    # operand size, the flags are undefined.

    # Operation
    # IF (In 64-Bit Mode and REX.W = 1)
    #     THEN COUNT <- COUNT MOD 64;
    #     ELSE COUNT <- COUNT MOD 32;
    # FI
    # SIZE <- OperandSize;
    # IF COUNT = 0
    #     THEN
    #         No operation;
    #     ELSE
    #         IF COUNT > SIZE
    #             THEN (* Bad parameters *)
    #                 DEST is undefined;
    #                 CF, OF, SF, ZF, AF, PF are undefined;
    #             ELSE (* Perform the shift *)
    #                 CF <- BIT[DEST, SIZE - COUNT];
    #                 FOR i <- SIZE - 1 DOWN TO COUNT
    #                     DO
    #                         BIT[DEST, i] <- BIT[DEST, i - COUNT];
    #                     OD;
    #                 FOR i <- COUNT DOWN TO 0
    #                     DO
    #                         BIT[DEST,i] <- BIT[SRC, i - COUNT + SIZE];
    #                     OD;
    #             FI;
    # FI;

    oprnd0 = self._reg_acc_translator.read(tb, instruction.operands[0])
    oprnd1 = self._reg_acc_translator.read(tb, instruction.operands[1])
    oprnd2 = self._reg_acc_translator.read(tb, instruction.operands[2])

    if self._arch_info.architecture_mode == ARCH_X86_MODE_32:
        mod_const = tb.immediate(32, oprnd2.size)
    elif self._arch_info.architecture_mode == ARCH_X86_MODE_64:
        mod_const = tb.immediate(64, oprnd2.size)
    else:
        raise Exception('Invalid architecture mode.')

    size = tb.immediate(self._arch_info.operand_size, oprnd2.size)
    end_addr = ReilImmediateOperand((instruction.address + instruction.size) << 8, self._arch_info.address_size + 8)
    count = tb.temporal(oprnd2.size)
    count_zero = tb.temporal(1)
    count_ext = tb.temporal(oprnd2.size * 2)
    size_ext = tb.temporal(oprnd2.size * 2)
    count_check = tb.temporal(oprnd2.size * 2)
    count_check_sign = tb.temporal(1)
    dst = tb.temporal(oprnd0.size)

    bad_parameters_lbl = ReilLabel('bad_parameters_lbl')
    shift_lbl = ReilLabel('shift_lbl')

    tb.add(self._builder.gen_mod(oprnd2, mod_const, count))
    tb.add(self._builder.gen_bisz(count, count_zero))
    tb.add(self._builder.gen_jcc(count_zero, end_addr))

    tb.add(self._builder.gen_str(count, count_ext))
    tb.add(self._builder.gen_str(size, size_ext))
    tb.add(self._builder.gen_sub(size_ext, count_ext, count_check))  # count_check = size_ext - count_ext

    # count_check_sign == 1 => count > size
    tb.add(self._builder.gen_bsh(count_check, tb.immediate(-count.size, count_check.size), count_check_sign))

    tb.add(self._builder.gen_jcc(count_check_sign, bad_parameters_lbl))
    tb.add(self._builder.gen_jcc(tb.immediate(1, 1), shift_lbl))

    tb.add(bad_parameters_lbl)
    # dst <- undefined
    tb.add(self._builder.gen_str(oprnd0, dst))
    # Set flags: CF, OF, SF, ZF, AF, PF are undefined;
    self._flag_translator.undefine_flag(tb, self._flags.cf)
    self._flag_translator.undefine_flag(tb, self._flags.of)
    self._flag_translator.undefine_flag(tb, self._flags.sf)
    self._flag_translator.undefine_flag(tb, self._flags.zf)
    self._flag_translator.undefine_flag(tb, self._flags.af)
    self._flag_translator.undefine_flag(tb, self._flags.pf)
    tb.add(self._builder.gen_jcc(tb.immediate(1, 1), end_addr))

    tb.add(shift_lbl)
    # (* Perform the shift *)
    # CF <- BIT[DEST, SIZE - COUNT];
    # FOR i <- SIZE - 1 DOWN TO COUNT
    #     DO
    #         BIT[DEST, i] <- BIT[DEST, i - COUNT];
    #     OD;
    # FOR i <- COUNT DOWN TO 0
    #     DO
    #         BIT[DEST,i] <- BIT[SRC, i - COUNT + SIZE];
    #     OD;

    zero = tb.immediate(0, count.size)
    bit_offset = tb.temporal(oprnd0.size)
    bit_offset2 = tb.temporal(oprnd0.size)
    bit_offset2_tmp = tb.temporal(oprnd0.size)
    tmp0 = tb.temporal(1)
    lower = tb.temporal(oprnd0.size * 2)
    upper = tb.temporal(oprnd0.size * 2)
    dst_tmp0 = tb.temporal(oprnd0.size * 2)
    dst_tmp1 = tb.temporal(oprnd0.size * 2)
    dst_count = tb.temporal(oprnd0.size * 2)

    # Compute bit offset.
    tb.add(self._builder.gen_str(count, bit_offset))
    tb.add(self._builder.gen_sub(size, count, bit_offset2_tmp))
    tb.add(self._builder.gen_sub(zero, bit_offset2_tmp, bit_offset2))

    # Extract bit.
    tb.add(self._builder.gen_bsh(oprnd0, bit_offset, tmp0))

    # Set CF.
    tb.add(self._builder.gen_and(tmp0, tb.immediate(1, 1), self._flags.cf))

    tb.add(self._builder.gen_str(oprnd1, lower))
    tb.add(self._builder.gen_bsh(oprnd0, tb.immediate(oprnd0.size, oprnd0.size), upper))
    tb.add(self._builder.gen_or(upper, lower, dst_tmp0))
    tb.add(self._builder.gen_str(count, dst_count))
    tb.add(self._builder.gen_bsh(dst_tmp0, dst_count, dst_tmp1))
    tb.add(self._builder.gen_bsh(dst_tmp1, tb.immediate(-oprnd0.size, dst_tmp1.size), dst))

    # Flags : SF, ZF, PF
    self._flag_translator.update_sf(tb, oprnd0, dst)
    self._flag_translator.update_zf(tb, oprnd0, dst)
    self._flag_translator.update_pf(tb, dst)

    self._reg_acc_translator.write(tb, instruction.operands[0], dst)


def _translate_shr(self, tb, instruction):
    # Flags Affected
    # The CF flag contains the value of the last bit shifted out
    # of the destination operand; it is undefined for SHL and SHR
    # instructions where the count is greater than or equal to the
    # size (in bits) of the destination operand. The OF flag is
    # affected only for 1-bit shifts (see "Description" above);
    # otherwise, it is undefined. The SF, ZF, and PF flags are set
    # according to the result. If the count is 0, the flags are
    # not affected. For a non-zero count, the AF flag is
    # undefined.

    # TODO: Fix flag translation

    oprnd0 = self._reg_acc_translator.read(tb, instruction.operands[0])
    oprnd1 = self._reg_acc_translator.read(tb, instruction.operands[1])

    imm0 = tb.immediate(1, oprnd0.size)
    imm1 = tb.immediate((2 ** oprnd0.size) - 1, oprnd0.size)
    imm2 = tb.immediate(-1, oprnd0.size)

    if oprnd0.size <= 32:
        mask = tb.immediate(0x1f, oprnd1.size)
    elif oprnd0.size == 64:
        mask = tb.immediate(0x3f, oprnd1.size)
    else:
        raise Exception()

    tmp0 = tb.temporal(oprnd0.size)
    tmp1 = tb.temporal(oprnd0.size)
    tmp2 = tb.temporal(oprnd0.size)
    tmp3 = tb.temporal(oprnd0.size)
    tmp4 = tb.temporal(oprnd0.size)
    tmp5 = tb.temporal(oprnd0.size)
    tmp6 = tb.temporal(oprnd0.size)

    # Mask the 2nd operand and extend its size to match the size of
    # the 1st operand.
    tb.add(self._builder.gen_and(oprnd1, mask, tmp0))

    # Decrement in 1 shift amount
    tb.add(self._builder.gen_sub(tmp0, imm0, tmp1))

    # Negate
    tb.add(self._builder.gen_xor(tmp1, imm1, tmp2))
    tb.add(self._builder.gen_add(tmp2, imm0, tmp3))

    # Shift right
    tb.add(self._builder.gen_bsh(oprnd0, tmp3, tmp4))

    # Save LSB in CF
    tb.add(self._builder.gen_and(tmp4, imm0, tmp5))
    tb.add(self._builder.gen_str(tmp5, self._flags.cf))

    # Shift one more time
    tb.add(self._builder.gen_bsh(tmp4, imm2, tmp6))

    # Flags : OF
    # TODO: Implement translation for OF flag.

    # Flags : SF, ZF, PF
    self._flag_translator.update_sf(tb, oprnd0, tmp6)
    self._flag_translator.update_zf(tb, oprnd0, tmp6)
    self._flag_translator.update_pf(tb, tmp6)

    # Flags : AF
    self._flag_translator.undefine_flag(tb, self._flags.af)

    self._reg_acc_translator.write(tb, instruction.operands[0], tmp6)


def _translate_shrd(self, tb, instruction):
    # Flags Affected
    # If the count is 1 or greater, the CF flag is filled with the last
    # bit shifted out of the destination operand and the SF, ZF, and PF
    # flags are set according to the value of the result. For a 1-bit
    # shift, the OF flag is set if a sign change occurred; otherwise, it
    # is cleared. For shifts greater than 1 bit, the OF flag is undefined.
    # If a shift occurs, the AF flag is undefined. If the count operand is
    # 0, the flags are not affected. If the count is greater than the
    # operand size, the flags are undefined.

    # Operation
    # IF (In 64-Bit Mode and REX.W = 1)
    #     THEN COUNT <- COUNT MOD 64;
    #     ELSE COUNT <- COUNT MOD 32;
    # FI
    # SIZE <- OperandSize;
    # IF COUNT = 0
    #     THEN
    #         No operation;
    #     ELSE
    #         IF COUNT > SIZE
    #             THEN (* Bad parameters *)
    #                 DEST is undefined;
    #                 CF, OF, SF, ZF, AF, PF are undefined;
    #             ELSE (* Perform the shift *)
    #                 CF <- BIT[DEST, COUNT - 1]; (* Last bit shifted out on exit *)
    #                 FOR i <- 0 TO SIZE - 1 - COUNT
    #                     DO
    #                         BIT[DEST, i] <- BIT[DEST, i + COUNT];
    #                     OD;
    #                 FOR i <- SIZE - COUNT TO SIZE - 1
    #                     DO
    #                         BIT[DEST,i] <- BIT[SRC, i + COUNT - SIZE];
    #                     OD;
    #             FI;
    # FI;

    oprnd0 = self._reg_acc_translator.read(tb, instruction.operands[0])
    oprnd1 = self._reg_acc_translator.read(tb, instruction.operands[1])
    oprnd2 = self._reg_acc_translator.read(tb, instruction.operands[2])

    if self._arch_info.architecture_mode == ARCH_X86_MODE_32:
        mod_const = tb.immediate(32, oprnd2.size)
    elif self._arch_info.architecture_mode == ARCH_X86_MODE_64:
        mod_const = tb.immediate(64, oprnd2.size)
    else:
        raise Exception('Invalid architecture mode.')

    size = tb.immediate(self._arch_info.operand_size, oprnd2.size)
    end_addr = ReilImmediateOperand((instruction.address + instruction.size) << 8, self._arch_info.address_size + 8)
    count = tb.temporal(oprnd2.size)
    count_zero = tb.temporal(1)
    count_ext = tb.temporal(oprnd2.size * 2)
    size_ext = tb.temporal(oprnd2.size * 2)
    count_check = tb.temporal(oprnd2.size * 2)
    count_check_sign = tb.temporal(1)
    dst = tb.temporal(oprnd0.size)

    bad_parameters_lbl = ReilLabel('bad_parameters_lbl')
    shift_lbl = ReilLabel('shift_lbl')

    tb.add(self._builder.gen_mod(oprnd2, mod_const, count))
    tb.add(self._builder.gen_bisz(count, count_zero))
    tb.add(self._builder.gen_jcc(count_zero, end_addr))

    tb.add(self._builder.gen_str(count, count_ext))
    tb.add(self._builder.gen_str(size, size_ext))
    tb.add(self._builder.gen_sub(size_ext, count_ext, count_check))  # count_check = size_ext - count_ext

    # count_check_sign == 1 => count > size
    tb.add(self._builder.gen_bsh(count_check, tb.immediate(-count.size, count_check.size), count_check_sign))

    tb.add(self._builder.gen_jcc(count_check_sign, bad_parameters_lbl))
    tb.add(self._builder.gen_jcc(tb.immediate(1, 1), shift_lbl))

    tb.add(bad_parameters_lbl)
    # dst <- undefined
    tb.add(self._builder.gen_str(oprnd0, dst))
    # Set flags: CF, OF, SF, ZF, AF, PF are undefined;
    self._flag_translator.undefine_flag(tb, self._flags.cf)
    self._flag_translator.undefine_flag(tb, self._flags.of)
    self._flag_translator.undefine_flag(tb, self._flags.sf)
    self._flag_translator.undefine_flag(tb, self._flags.zf)
    self._flag_translator.undefine_flag(tb, self._flags.af)
    self._flag_translator.undefine_flag(tb, self._flags.pf)
    tb.add(self._builder.gen_jcc(tb.immediate(1, 1), end_addr))

    tb.add(shift_lbl)
    # (* Perform the shift *)
    # CF <- BIT[DEST, COUNT - 1]; (* Last bit shifted out on exit *)
    # FOR i <- 0 TO SIZE - 1 - COUNT
    #     DO
    #         BIT[DEST, i] <- BIT[DEST, i + COUNT];
    #     OD;
    # FOR i <- SIZE - COUNT TO SIZE - 1
    #     DO
    #         BIT[DEST,i] <- BIT[SRC, i + COUNT - SIZE];
    #     OD;

    zero = tb.immediate(0, count.size)
    one = tb.immediate(1, count.size)
    bit_offset = tb.temporal(oprnd0.size)
    bit_offset_tmp = tb.temporal(oprnd0.size)
    tmp0 = tb.temporal(1)
    lower = tb.temporal(oprnd0.size * 2)
    upper = tb.temporal(oprnd0.size * 2)
    dst_tmp0 = tb.temporal(oprnd0.size * 2)
    dst_tmp1 = tb.temporal(oprnd0.size * 2)
    dst_count = tb.temporal(oprnd0.size * 2)
    dst_count0 = tb.temporal(oprnd0.size * 2)

    # Compute bit offset.
    tb.add(self._builder.gen_sub(count, one, bit_offset_tmp))
    tb.add(self._builder.gen_sub(zero, bit_offset_tmp, bit_offset))  # negate

    # Extract bit.
    tb.add(self._builder.gen_bsh(oprnd0, bit_offset, tmp0))

    # Set CF.
    tb.add(self._builder.gen_and(tmp0, tb.immediate(1, 1), self._flags.cf))

    tb.add(self._builder.gen_str(oprnd0, lower))
    tb.add(self._builder.gen_bsh(oprnd1, tb.immediate(oprnd1.size, oprnd1.size), upper))
    tb.add(self._builder.gen_or(upper, lower, dst_tmp0))
    tb.add(self._builder.gen_str(count, dst_count0))
    tb.add(self._builder.gen_sub(tb.immediate(0, dst_count0.size), dst_count0, dst_count))
    tb.add(self._builder.gen_bsh(dst_tmp0, dst_count, dst_tmp1))
    tb.add(self._builder.gen_str(dst_tmp1, dst))

    # Flags : SF, ZF, PF
    self._flag_translator.update_sf(tb, oprnd0, dst)
    self._flag_translator.update_zf(tb, oprnd0, dst)
    self._flag_translator.update_pf(tb, dst)

    self._reg_acc_translator.write(tb, instruction.operands[0], dst)


dispatcher = {
    # "Bit and Byte Instructions"
    'bsf': _translate_bsf,
    'bt': _translate_bt,
    'bts': _translate_bts,
    'test': _translate_test,

    # "Shift and Rotate Instructions"
    'rcl': _translate_rcl,
    'rcr': _translate_rcr,
    'rol': _translate_rol,
    'ror': _translate_ror,
    'sal': _translate_sal,
    'sar': _translate_sar,
    'shl': _translate_shl,
    'shld': _translate_shld,
    'shr': _translate_shr,
    'shrd': _translate_shrd,
}
