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

from barf.core.reil import ReilLabel


# "SIMD Instructions"
# ============================================================================ #
def _translate_lddqu(self, tb, instruction):
    # Flags Affected
    # None.

    # DEST[127:0] <- SRC[127:0]

    oprnd0 = self._reg_acc_translator.read(tb, instruction.operands[0])
    oprnd1 = self._reg_acc_translator.read(tb, instruction.operands[1])

    tmp0 = tb.temporal(oprnd0.size)

    tb.add(self._builder.gen_str(oprnd1, tmp0))

    self._reg_acc_translator.write(tb, instruction.operands[0], tmp0)


def _translate_movaps(self, tb, instruction):
    # Flags Affected
    # None.

    oprnd1 = self._reg_acc_translator.read(tb, instruction.operands[1])

    self._reg_acc_translator.write(tb, instruction.operands[0], oprnd1)


def _translate_movd(self, tb, instruction):
    # Flags Affected
    # None

    # Operation
    # MOVD (when destination operand is MMX technology register)
    # DEST[31:0] <- SRC;
    # DEST[63:32] <- 00000000H;
    #
    # MOVD (when destination operand is XMM register)
    # DEST[31:0] <- SRC;
    # DEST[127:32] <- 000000000000000000000000H;
    # DEST[VLMAX-1:128] (Unmodified)
    #
    # MOVD (when source operand is MMX technology or XMM register)
    # DEST <- SRC[31:0];

    # NOTE Only supports mmx and xmm registers.

    oprnd0 = self._reg_acc_translator.read(tb, instruction.operands[0])
    oprnd1 = self._reg_acc_translator.read(tb, instruction.operands[1])

    tmp0 = tb.temporal(oprnd0.size)

    tb.add(self._builder.gen_str(tb.immediate(0, oprnd0.size), tmp0))
    tb.add(self._builder.gen_str(oprnd1, tmp0))

    self._reg_acc_translator.write(tb, instruction.operands[0], tmp0)


def _translate_movdqa(self, tb, instruction):
    # Flags Affected
    # None.

    # DEST[127:0] <- SRC[127:0]

    # NOTE This implementation ignores the alignment.

    oprnd0 = self._reg_acc_translator.read(tb, instruction.operands[0])
    oprnd1 = self._reg_acc_translator.read(tb, instruction.operands[1])

    tmp0 = tb.temporal(oprnd0.size)

    tb.add(self._builder.gen_str(oprnd1, tmp0))

    self._reg_acc_translator.write(tb, instruction.operands[0], tmp0)


def _translate_movdqu(self, tb, instruction):
    # Flags Affected
    # None.

    # DEST[127:0] <- SRC[127:0]

    oprnd0 = self._reg_acc_translator.read(tb, instruction.operands[0])
    oprnd1 = self._reg_acc_translator.read(tb, instruction.operands[1])

    tmp0 = tb.temporal(oprnd0.size)

    tb.add(self._builder.gen_str(oprnd1, tmp0))

    self._reg_acc_translator.write(tb, instruction.operands[0], tmp0)


def _translate_movhpd(self, tb, instruction):
    # Flags Affected
    # None.

    # Operation
    # MOVHPD (128-bit Legacy SSE load)
    # DEST[63:0] (Unmodified)
    # DEST[127:64] <- SRC[63:0]
    # DEST[MAX_VL-1:128] (Unmodified)

    # NOTE Only supports mmx and xmm registers.

    oprnd0 = self._reg_acc_translator.read(tb, instruction.operands[0])
    oprnd1 = self._reg_acc_translator.read(tb, instruction.operands[1])

    dst_low = tb.temporal(64)
    dst_high = tb.temporal(64)
    dst = tb.temporal(oprnd0.size)
    dst_tmp0 = tb.temporal(oprnd0.size)
    dst_tmp1 = tb.temporal(oprnd0.size)
    dst_low_ext = tb.temporal(oprnd0.size)

    tb.add(self._builder.gen_str(oprnd0, dst_low))
    tb.add(self._builder.gen_str(oprnd1, dst_high))

    tb.add(self._builder.gen_str(dst_high, dst_tmp0))
    tb.add(self._builder.gen_bsh(dst_tmp0, tb.immediate(64, dst_tmp0.size), dst_tmp1))

    tb.add(self._builder.gen_str(dst_low, dst_low_ext))
    tb.add(self._builder.gen_or(dst_low_ext, dst_tmp1, dst))

    self._reg_acc_translator.write(tb, instruction.operands[0], dst)


def _translate_movlpd(self, tb, instruction):
    # Flags Affected
    # None.

    # Operation
    # MOVLPD (128-bit Legacy SSE load)
    # DEST[63:0] <- SRC[63:0]
    # DEST[MAX_VL-1:64] (Unmodified)

    # NOTE Only supports mmx and xmm registers.

    oprnd0 = self._reg_acc_translator.read(tb, instruction.operands[0])
    oprnd1 = self._reg_acc_translator.read(tb, instruction.operands[1])

    dst_low = tb.temporal(64)
    dst_high = tb.temporal(64)
    dst = tb.temporal(oprnd0.size)
    dst_tmp0 = tb.temporal(oprnd0.size)
    dst_low_ext = tb.temporal(oprnd0.size)

    tb.add(self._builder.gen_bsh(oprnd0, tb.immediate(-64, oprnd0.size), dst_high))
    tb.add(self._builder.gen_str(oprnd1, dst_low))

    tb.add(self._builder.gen_bsh(dst_high, tb.immediate(64, dst_high.size), dst_tmp0))
    tb.add(self._builder.gen_str(dst_low, dst_low_ext))

    tb.add(self._builder.gen_or(dst_low_ext, dst_tmp0, dst))

    self._reg_acc_translator.write(tb, instruction.operands[0], dst)


def _translate_movq(self, tb, instruction):
    # Flags Affected
    # None

    # Operation
    # MOVQ (when destination operand is XMM register)
    # DEST[63:0] <- SRC[63:0];
    # DEST[127:64] <- 0000000000000000H;
    # DEST[VLMAX-1:128] (Unmodified)
    #
    # MOVQ (when destination operand is r/m64)
    # DEST[63:0] <- SRC[63:0];
    #
    # MOVQ (when source operand is XMM register or r/m64)
    # DEST <- SRC[63:0];

    # NOTE Only supports mmx and xmm registers.

    oprnd0 = self._reg_acc_translator.read(tb, instruction.operands[0])
    oprnd1 = self._reg_acc_translator.read(tb, instruction.operands[1])

    tmp0 = tb.temporal(oprnd0.size)

    tb.add(self._builder.gen_str(tb.immediate(0, oprnd0.size), tmp0))
    tb.add(self._builder.gen_str(oprnd1, tmp0))

    self._reg_acc_translator.write(tb, instruction.operands[0], tmp0)


def _translate_movsd_sse(self, tb, instruction):
    # Flags Affected
    # None.

    # Operation
    # MOVSD (128-bit Legacy SSE version: MOVSD XMM1, m64)
    # DEST[63:0] <- SRC[63:0]
    # DEST[127:64] <- 0
    # DEST[MAX_VL-1:128] (Unmodified)

    oprnd1 = self._reg_acc_translator.read(tb, instruction.operands[1])

    dst = tb.temporal(64)

    tb.add(self._builder.gen_str(oprnd1, dst))

    self._reg_acc_translator.write(tb, instruction.operands[0], dst)


def _translate_pcmpeqb(self, tb, instruction):
    # Flags Affected
    # None.

    # IF DEST[7:0] = SRC[7:0]
    # THEN DEST[7:0) <- FFH;
    # ELSE DEST[7:0] <- 0; FI;
    # (* Continue comparison of 2nd through 7th bytes in DEST and SRC *)
    # IF DEST[63:56] = SRC[63:56]
    # THEN DEST[63:56] <- FFH;
    # ELSE DEST[63:56] <- 0; FI;

    oprnd0 = self._reg_acc_translator.read(tb, instruction.operands[0])
    oprnd1 = self._reg_acc_translator.read(tb, instruction.operands[1])

    dst = tb.temporal(oprnd0.size)

    tb.add(self._builder.gen_str(tb.immediate(0, dst.size), dst))

    for i in range(oprnd0.size // 8):
        t1 = tb.temporal(8)
        t2 = tb.temporal(8)
        t3 = tb.temporal(8)
        t4 = tb.temporal(8)
        t5 = tb.temporal(8)
        t6 = tb.temporal(oprnd0.size)
        dst_new = tb.temporal(oprnd0.size)

        imm1 = tb.immediate(-(i * 8), oprnd0.size)
        imm2 = tb.immediate(i * 8, 8)

        # Extract i-th bytes.
        tb.add(self._builder.gen_bsh(oprnd0, imm1, t1))
        tb.add(self._builder.gen_bsh(oprnd1, imm1, t2))

        # Compare i-th bytes.
        tb.add(self._builder.gen_sub(t1, t2, t3))

        tb.add(self._builder.gen_bisz(t3, t4))

        # Set result for the i-th byte.
        tb.add(self._builder.gen_mul(t4, tb.immediate(0xff, 8), t5))

        # Store the i-th result.
        tb.add(self._builder.gen_bsh(t5, imm2, t6))
        tb.add(self._builder.gen_or(dst, t6, dst_new))

        dst = dst_new

    self._reg_acc_translator.write(tb, instruction.operands[0], dst)


def _translate_pminub(self, tb, instruction):
    # Flags Affected
    # None.

    # Operation
    # PMINUB (for 64-bit operands)
    # IF DEST[7:0] < SRC[7:0] THEN
    #     DEST[7:0] <- DEST[7:0];
    # ELSE
    #     DEST[7:0] <- SRC[7:0]; FI;
    # (* Repeat operation for 2nd through 7th bytes in source and destination operands *)
    # IF DEST[63:56] < SRC[63:56] THEN
    #     DEST[63:56] <- DEST[63:56];
    # ELSE
    #     DEST[63:56] <- SRC[63:56]; FI;

    # PMINUB instruction for 128-bit operands:
    # IF DEST[7:0] < SRC[7:0] THEN
    #     DEST[7:0] <- DEST[7:0];
    # ELSE
    #     DEST[15:0] <- SRC[7:0]; FI;
    # (* Repeat operation for 2nd through 15th bytes in source and destination operands *)
    # IF DEST[127:120] < SRC[127:120] THEN
    #     DEST[127:120] <- DEST[127:120];
    # ELSE
    #     DEST[127:120] <- SRC[127:120]; FI;
    # DEST[MAX_VL-1:128] (Unmodified)

    oprnd0 = self._reg_acc_translator.read(tb, instruction.operands[0])
    oprnd1 = self._reg_acc_translator.read(tb, instruction.operands[1])

    dst = tb.temporal(oprnd0.size)

    tb.add(self._builder.gen_str(tb.immediate(0, dst.size), dst))

    for i in range(oprnd0.size // 8):
        t1 = tb.temporal(8)
        t1_ext = tb.temporal(16)
        t1_mul = tb.temporal(8)
        t2 = tb.temporal(8)
        t2_ext = tb.temporal(16)
        t2_mul = tb.temporal(8)
        t3 = tb.temporal(16)
        sign = tb.temporal(1)
        not_sign = tb.temporal(1)
        sign_ext = tb.temporal(8)
        not_sign_ext = tb.temporal(8)
        t5 = tb.temporal(8)
        t6 = tb.temporal(oprnd0.size)
        dst_new = tb.temporal(oprnd0.size)

        imm1 = tb.immediate(-(i * 8), oprnd0.size)
        imm2 = tb.immediate(i * 8, 8)

        # Extract i-th bytes.
        tb.add(self._builder.gen_bsh(oprnd0, imm1, t1))
        tb.add(self._builder.gen_bsh(oprnd1, imm1, t2))

        # Compare i-th bytes.
        tb.add(self._builder.gen_str(t1, t1_ext))
        tb.add(self._builder.gen_str(t2, t2_ext))
        tb.add(self._builder.gen_sub(t1_ext, t2_ext, t3))

        tb.add(self._builder.gen_bsh(t3, tb.immediate(-8, t3.size), sign))
        tb.add(self._builder.gen_xor(sign, tb.immediate(1, 1), not_sign))

        tb.add(self._builder.gen_str(sign, sign_ext))
        tb.add(self._builder.gen_str(not_sign, not_sign_ext))

        # Set result for the i-th byte.
        tb.add(self._builder.gen_mul(t1, sign_ext, t1_mul))
        tb.add(self._builder.gen_mul(t2, not_sign_ext, t2_mul))

        tb.add(self._builder.gen_or(t1_mul, t2_mul, t5))

        # Store the i-th result.
        tb.add(self._builder.gen_bsh(t5, imm2, t6))
        tb.add(self._builder.gen_or(dst, t6, dst_new))

        dst = dst_new

    self._reg_acc_translator.write(tb, instruction.operands[0], dst)


def _translate_pmovmskb(self, tb, instruction):
    # Flags Affected
    # None.

    # PMOVMSKB (with 64-bit source operand and r32)
    # r32[0] <- SRC[7];
    # r32[1] <- SRC[15];
    # (* Repeat operation for bytes 2 through 6 *)
    # r32[7] <- SRC[63];
    # r32[31:8] <- ZERO_FILL;

    oprnd1 = self._reg_acc_translator.read(tb, instruction.operands[1])

    dst = tb.temporal(instruction.operands[0].size)

    tb.add(self._builder.gen_str(tb.immediate(0, dst.size), dst))

    j = 0

    for i in range(oprnd1.size // 8):
        t1 = tb.temporal(1)
        t2 = tb.temporal(dst.size)
        t3 = tb.temporal(dst.size)

        dst_new = tb.temporal(dst.size)

        imm1 = tb.immediate(-(i * 8 + 7), oprnd1.size)
        imm2 = tb.immediate(j, dst.size)

        tb.add(self._builder.gen_bsh(oprnd1, imm1, t1))

        tb.add(self._builder.gen_str(t1, t2))

        tb.add(self._builder.gen_bsh(t2, imm2, t3))
        tb.add(self._builder.gen_or(dst, t3, dst_new))

        j += 1

        dst = dst_new

    self._reg_acc_translator.write(tb, instruction.operands[0], dst)


def _translate_por(self, tb, instruction):
    # Flags Affected
    # None.

    # Operation
    # POR (64-bit operand)
    # DEST <- DEST OR SRC

    # POR (128-bit Legacy SSE version)
    # DEST <- DEST OR SRC
    # DEST[VLMAX-1:128] (Unmodified)

    # NOTE Only supports mmx and xmm registers.

    oprnd0 = self._reg_acc_translator.read(tb, instruction.operands[0])
    oprnd1 = self._reg_acc_translator.read(tb, instruction.operands[1])

    tmp0 = tb.temporal(oprnd0.size)

    tb.add(self._builder.gen_or(oprnd0, oprnd1, tmp0))

    self._reg_acc_translator.write(tb, instruction.operands[0], tmp0)


def _translate_pshufd(self, tb, instruction):
    # Flags Affected
    # None.

    # Operation
    # PSHUFD (128-bit Legacy SSE version)
    # DEST[31:0] <- (SRC >> (ORDER[1:0] * 32))[31:0];
    # DEST[63:32] <- (SRC >> (ORDER[3:2] * 32))[31:0];
    # DEST[95:64] <- (SRC >> (ORDER[5:4] * 32))[31:0];
    # DEST[127:96] <- (SRC >> (ORDER[7:6] * 32))[31:0];
    # DEST[VLMAX-1:128] (Unmodified)

    oprnd0 = self._reg_acc_translator.read(tb, instruction.operands[0])
    oprnd1 = self._reg_acc_translator.read(tb, instruction.operands[1])
    oprnd2 = self._reg_acc_translator.read(tb, instruction.operands[2])

    dst = tb.temporal(oprnd0.size)

    tb.add(self._builder.gen_str(tb.immediate(0, dst.size), dst))

    for i in range(oprnd0.size // 32):
        t1 = tb.temporal(8)
        t2 = tb.temporal(8)
        t3 = tb.temporal(oprnd1.size)
        t4 = tb.temporal(oprnd1.size)

        tmp0 = tb.temporal(32)
        tmp1 = tb.temporal(oprnd0.size)

        dst_new = tb.temporal(oprnd0.size)

        imm1 = tb.immediate(-(i * 2), oprnd2.size)
        imm2 = tb.immediate(i * 32, 32)

        # Extract i-th dword order.
        tb.add(self._builder.gen_bsh(oprnd2, imm1, t1))
        tb.add(self._builder.gen_and(t1, tb.immediate(0x3, t1.size), t2))
        tb.add(self._builder.gen_mul(t2, tb.immediate(32, t2.size), t3))
        tb.add(self._builder.gen_sub(tb.immediate(0, t3.size), t3, t4))

        tb.add(self._builder.gen_bsh(oprnd1, t4, tmp0))
        tb.add(self._builder.gen_bsh(tmp0, imm2, tmp1))

        # Store the i-th result.
        tb.add(self._builder.gen_or(dst, tmp1, dst_new))

        dst = dst_new

    self._reg_acc_translator.write(tb, instruction.operands[0], dst)


def _translate_pslldq(self, tb, instruction):
    # Flags Affected
    # None.

    # TEMP <- COUNT
    # IF (TEMP > 15) THEN TEMP <- 16; FI
    # DEST <- DEST << (TEMP * 8)
    # DEST[VLMAX-1:128] (Unmodified)

    # NOTE Only supports xmm registers.

    oprnd0 = self._reg_acc_translator.read(tb, instruction.operands[0])
    oprnd1 = self._reg_acc_translator.read(tb, instruction.operands[1])

    count = tb.temporal(oprnd0.size)
    count_tmp = tb.temporal(oprnd1.size)
    tmp0 = tb.temporal(oprnd1.size)
    cmp_result = tb.temporal(1)
    dst = tb.temporal(oprnd0.size)

    imm0 = tb.immediate(~0x7fff, oprnd1.size)

    # Create labels.
    count_ok_lbl = ReilLabel('count_ok_lbl')

    # Check if count <= 16
    tb.add(self._builder.gen_str(oprnd1, count_tmp))
    tb.add(self._builder.gen_and(count_tmp, imm0, tmp0))
    tb.add(self._builder.gen_bisz(tmp0, cmp_result))
    tb.add(self._builder.gen_jcc(cmp_result, count_ok_lbl))

    # Set count to 16.
    tb.add(self._builder.gen_str(imm0, count_tmp))

    # Count ok.
    tb.add(count_ok_lbl)

    # Extend count to the size of oprnd0 and multiply by 8.
    tb.add(self._builder.gen_mul(count_tmp, tb.immediate(8, oprnd1.size), count))

    # Do the shift.
    tb.add(self._builder.gen_bsh(oprnd0, count, dst))

    # Save the result.
    self._reg_acc_translator.write(tb, instruction.operands[0], dst)


def _translate_psrldq(self, tb, instruction):
    # Flags Affected
    # None.

    # Operation
    # PSRLDQ(128-bit Legacy SSE version)
    # TEMP <- COUNT
    # IF (TEMP > 15) THEN TEMP <- 16; FI
    # DEST <- DEST >> (TEMP * 8)
    # DEST[MAX_VL-1:128] (Unmodified)

    # NOTE Only supports xmm registers.

    oprnd0 = self._reg_acc_translator.read(tb, instruction.operands[0])
    oprnd1 = self._reg_acc_translator.read(tb, instruction.operands[1])

    count = tb.temporal(oprnd0.size)
    count_tmp = tb.temporal(oprnd1.size)
    count_tmp_2 = tb.temporal(oprnd1.size)
    tmp0 = tb.temporal(oprnd1.size)
    cmp_result = tb.temporal(1)
    dst = tb.temporal(oprnd0.size)

    imm0 = tb.immediate(~0x7fff, oprnd1.size)

    # Create labels.
    count_ok_lbl = ReilLabel('count_ok_lbl')

    # Check if count <= 16
    tb.add(self._builder.gen_str(oprnd1, count_tmp))
    tb.add(self._builder.gen_and(count_tmp, imm0, tmp0))
    tb.add(self._builder.gen_bisz(tmp0, cmp_result))
    tb.add(self._builder.gen_jcc(cmp_result, count_ok_lbl))

    # Set count to 16.
    tb.add(self._builder.gen_str(imm0, count_tmp))

    # Count ok.
    tb.add(count_ok_lbl)

    # Extend count to the size of oprnd0 and multiply by 8.
    tb.add(self._builder.gen_mul(count_tmp, tb.immediate(8, oprnd1.size), count_tmp_2))

    # Negate
    tb.add(self._builder.gen_sub(tb.immediate(0, oprnd1.size), count_tmp_2, count))

    # Do the shift.
    tb.add(self._builder.gen_bsh(oprnd0, count, dst))

    # Save the result.
    self._reg_acc_translator.write(tb, instruction.operands[0], dst)


def _translate_psubb(self, tb, instruction):
    # Flags Affected
    # None.

    # PSUBB (128-bit Legacy SSE version)
    # DEST[7:0] <- DEST[7:0]-SRC[7:0]
    # DEST[15:8] <- DEST[15:8]-SRC[15:8]
    # DEST[23:16] <- DEST[23:16]-SRC[23:16]
    # DEST[31:24] <- DEST[31:24]-SRC[31:24]
    # DEST[39:32] <- DEST[39:32]-SRC[39:32]
    # DEST[47:40] <- DEST[47:40]-SRC[47:40]
    # DEST[55:48] <- DEST[55:48]-SRC[55:48]
    # DEST[63:56] <- DEST[63:56]-SRC[63:56]
    # DEST[71:64] <- DEST[71:64]-SRC[71:64]
    # DEST[79:72] <- DEST[79:72]-SRC[79:72]
    # DEST[87:80] <- DEST[87:80]-SRC[87:80]
    # DEST[95:88] <- DEST[95:88]-SRC[95:88]
    # DEST[103:96] <- DEST[103:96]-SRC[103:96]
    # DEST[111:104] <- DEST[111:104]-SRC[111:104]
    # DEST[119:112] <- DEST[119:112]-SRC[119:112]
    # DEST[127:120] <- DEST[127:120]-SRC[127:120]
    # DEST[MAX_VL-1:128] (Unmodified)

    # NOTE Only supports xmm registers.

    oprnd0 = self._reg_acc_translator.read(tb, instruction.operands[0])
    oprnd1 = self._reg_acc_translator.read(tb, instruction.operands[1])

    dst = tb.temporal(oprnd0.size)

    tb.add(self._builder.gen_str(tb.immediate(0, dst.size), dst))

    for i in range(oprnd0.size // 8):
        t1 = tb.temporal(8)
        t2 = tb.temporal(8)
        t3 = tb.temporal(8)
        t4 = tb.temporal(oprnd0.size)
        dst_new = tb.temporal(oprnd0.size)

        imm1 = tb.immediate(-(i * 8), oprnd0.size)
        imm2 = tb.immediate(i * 8, 8)

        # Extract i-th bytes.
        tb.add(self._builder.gen_bsh(oprnd0, imm1, t1))
        tb.add(self._builder.gen_bsh(oprnd1, imm1, t2))

        # Do subtraction between i-th bytes.
        tb.add(self._builder.gen_sub(t1, t2, t3))

        # Store the i-th result.
        tb.add(self._builder.gen_bsh(t3, imm2, t4))
        tb.add(self._builder.gen_or(dst, t4, dst_new))

        dst = dst_new

    self._reg_acc_translator.write(tb, instruction.operands[0], dst)


def _translate_punpcklbw(self, tb, instruction):
    # Flags Affected
    # None.

    # Operation
    # PUNPCKLBW instruction with 64-bit operands:
    # DEST[63:56] <- SRC[31:24];
    # DEST[55:48] <- DEST[31:24];
    # DEST[47:40] <- SRC[23:16];
    # DEST[39:32] <- DEST[23:16];
    # DEST[31:24] <- SRC[15:8];
    # DEST[23:16] <- DEST[15:8];
    # DEST[15:8] <- SRC[7:0];
    # DEST[7:0] <- DEST[7:0];

    oprnd0 = self._reg_acc_translator.read(tb, instruction.operands[0])
    oprnd1 = self._reg_acc_translator.read(tb, instruction.operands[1])

    dst = tb.temporal(oprnd0.size)

    tb.add(self._builder.gen_str(tb.immediate(0, dst.size), dst))

    j = 0

    for i in range(oprnd0.size // 8):
        t1 = tb.temporal(8)
        t2 = tb.temporal(8)
        t1_ext = tb.temporal(oprnd0.size)
        t2_ext = tb.temporal(oprnd0.size)
        dst_tmp0 = tb.temporal(oprnd0.size)
        dst_new = tb.temporal(oprnd0.size)

        imm1 = tb.immediate(-(i * 8), oprnd0.size)
        imm2 = tb.immediate(j * 8, 8)
        imm3 = tb.immediate((j + 1) * 8, 8)

        # Extract i-th bytes.
        tb.add(self._builder.gen_bsh(oprnd0, imm1, t1))
        tb.add(self._builder.gen_bsh(oprnd1, imm1, t2))

        # Shift and extend to the size of the dst operand.
        tb.add(self._builder.gen_bsh(t1, imm2, t1_ext))
        tb.add(self._builder.gen_bsh(t2, imm3, t2_ext))

        # Store the i-th result.
        tb.add(self._builder.gen_or(dst, t1_ext, dst_tmp0))
        tb.add(self._builder.gen_or(dst_tmp0, t2_ext, dst_new))

        j += 2

        dst = dst_new

    self._reg_acc_translator.write(tb, instruction.operands[0], dst)


def _translate_punpcklqdq(self, tb, instruction):
    # Flags Affected
    # None.

    # Operation
    # PUNPCKLQDQ
    # DEST[127:0] <- INTERLEAVE_QWORDS(DEST, SRC)
    # DEST[MAX_VL-1:128] (Unmodified)

    oprnd0 = self._reg_acc_translator.read(tb, instruction.operands[0])
    oprnd1 = self._reg_acc_translator.read(tb, instruction.operands[1])

    dst = tb.temporal(oprnd0.size)

    tb.add(self._builder.gen_str(tb.immediate(0, dst.size), dst))

    j = 0

    word = 16
    qword = 4 * word
    dqword = 2 * qword

    size_src = qword
    size_dst = dqword

    for i in range(oprnd0.size // size_dst):
        t1 = tb.temporal(size_src)
        t2 = tb.temporal(size_src)
        t1_ext = tb.temporal(oprnd0.size)
        t2_ext = tb.temporal(oprnd0.size)
        dst_tmp0 = tb.temporal(oprnd0.size)
        dst_new = tb.temporal(oprnd0.size)

        imm1 = tb.immediate(-(i * size_src), oprnd0.size)
        imm2 = tb.immediate(j * size_src, size_src)
        imm3 = tb.immediate((j + 1) * size_src, size_src)

        # Extract i-th bytes.
        tb.add(self._builder.gen_bsh(oprnd0, imm1, t1))
        tb.add(self._builder.gen_bsh(oprnd1, imm1, t2))

        # Shift and extend to the size of the dst operand.
        tb.add(self._builder.gen_bsh(t1, imm2, t1_ext))
        tb.add(self._builder.gen_bsh(t2, imm3, t2_ext))

        # Store the i-th result.
        tb.add(self._builder.gen_or(dst, t1_ext, dst_tmp0))
        tb.add(self._builder.gen_or(dst_tmp0, t2_ext, dst_new))

        j += 2

        dst = dst_new

    self._reg_acc_translator.write(tb, instruction.operands[0], dst)


def _translate_punpcklwd(self, tb, instruction):
    # Flags Affected
    # None.

    # Operation
    # PUNPCKLWD instruction with 64-bit operands:
    # DEST[63:48] <- SRC[31:16];
    # DEST[47:32] <- DEST[31:16];
    # DEST[31:16] <- SRC[15:0];
    # DEST[15:0] <- DEST[15:0];

    oprnd0 = self._reg_acc_translator.read(tb, instruction.operands[0])
    oprnd1 = self._reg_acc_translator.read(tb, instruction.operands[1])

    dst = tb.temporal(oprnd0.size)

    tb.add(self._builder.gen_str(tb.immediate(0, dst.size), dst))

    j = 0

    for i in range(oprnd0.size // 16):
        t1 = tb.temporal(16)
        t2 = tb.temporal(16)
        t1_ext = tb.temporal(oprnd0.size)
        t2_ext = tb.temporal(oprnd0.size)
        dst_tmp0 = tb.temporal(oprnd0.size)
        dst_new = tb.temporal(oprnd0.size)

        imm1 = tb.immediate(-(i * 16), oprnd0.size)
        imm2 = tb.immediate(j * 16, 16)
        imm3 = tb.immediate((j + 1) * 16, 16)

        # Extract i-th bytes.
        tb.add(self._builder.gen_bsh(oprnd0, imm1, t1))
        tb.add(self._builder.gen_bsh(oprnd1, imm1, t2))

        # Shift and extend to the size of the dst operand.
        tb.add(self._builder.gen_bsh(t1, imm2, t1_ext))
        tb.add(self._builder.gen_bsh(t2, imm3, t2_ext))

        # Store the i-th result.
        tb.add(self._builder.gen_or(dst, t1_ext, dst_tmp0))
        tb.add(self._builder.gen_or(dst_tmp0, t2_ext, dst_new))

        j += 2

        dst = dst_new

    self._reg_acc_translator.write(tb, instruction.operands[0], dst)


def _translate_pxor(self, tb, instruction):
    # Flags Affected
    # None.

    # DEST <- DEST XOR SRC

    oprnd0 = self._reg_acc_translator.read(tb, instruction.operands[0])
    oprnd1 = self._reg_acc_translator.read(tb, instruction.operands[1])

    tmp0 = tb.temporal(oprnd0.size)

    tb.add(self._builder.gen_xor(oprnd0, oprnd1, tmp0))

    self._reg_acc_translator.write(tb, instruction.operands[0], tmp0)


def _translate_vmovdqa(self, tb, instruction):
    _translate_movdqa(self, tb, instruction)


dispatcher = {
    'lddqu': _translate_lddqu,
    'movaps': _translate_movaps,
    'movd': _translate_movd,
    'movdqa': _translate_movdqa,
    'movdqu': _translate_movdqu,
    'movhpd': _translate_movhpd,
    'movlpd': _translate_movlpd,
    'movq': _translate_movq,
    'movsd_sse': _translate_movsd_sse,
    'pcmpeqb': _translate_pcmpeqb,
    'pminub': _translate_pminub,
    'pmovmskb': _translate_pmovmskb,
    'por': _translate_por,
    'pshufd': _translate_pshufd,
    'pslldq': _translate_pslldq,
    'psrldq': _translate_psrldq,
    'psubb': _translate_psubb,
    'punpcklbw': _translate_punpcklbw,
    'punpcklqdq': _translate_punpcklqdq,
    'punpcklwd': _translate_punpcklwd,
    'pxor': _translate_pxor,
    'vmovdqa': _translate_vmovdqa,
}
