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

from barf.arch import ARCH_X86_MODE_32, ARCH_X86_MODE_64
from barf.arch.translator import Label
from barf.core.reil import ReilImmediateOperand, ReilRegisterOperand


# "String Instructions"
# ============================================================================ #
def _update_strings_src(self, tb, src, size, instruction):
    _update_strings_dst(self, tb, src, size, instruction)


def _update_strings_srcs(self, tb, src1, src2, size):
    _update_strings_src_and_dst(self, tb, src1, src2, size)


def _update_strings_dst(self, tb, dst, size, instruction):
    # Create labels.
    forward_lbl = Label('forward')
    backward_lbl = Label('backward')

    end_addr = ReilImmediateOperand((instruction.address + instruction.size) << 8, self._arch_info.address_size + 8)

    # Define immediate registers.
    imm_one = tb.immediate(1, 1)

    # Define temporary registers.
    df_zero = tb.temporal(1)
    imm_tmp = tb.immediate(size / 8, dst.size)
    dst_tmp = tb.temporal(dst.size)

    # Update destination pointer.
    tb.add(self._builder.gen_bisz(self._flags["df"], df_zero))
    tb.add(self._builder.gen_jcc(df_zero, forward_lbl))

    # Update backwards.
    tb.add(backward_lbl)
    tb.add(self._builder.gen_sub(dst, imm_tmp, dst_tmp))
    tb.add(self._builder.gen_str(dst_tmp, dst))

    # Jump to next instruction.
    tb.add(self._builder.gen_jcc(imm_one, end_addr))

    # Update forwards.
    tb.add(forward_lbl)
    tb.add(self._builder.gen_add(dst, imm_tmp, dst_tmp))
    tb.add(self._builder.gen_str(dst_tmp, dst))


def _update_strings_src_and_dst(self, tb, src, dst, size):
    # Create labels.
    forward_lbl = Label('forward')
    backward_lbl = Label('backward')
    continue_lbl = Label('continue')

    # Define immediate registers.
    imm_one = tb.immediate(1, 1)

    # Define temporary registers.
    df_zero = tb.temporal(1)
    imm_tmp = tb.immediate(size / 8, src.size)
    src_tmp = tb.temporal(src.size)
    dst_tmp = tb.temporal(dst.size)

    # Update destination pointer.
    tb.add(self._builder.gen_bisz(self._flags["df"], df_zero))
    tb.add(self._builder.gen_jcc(df_zero, forward_lbl))

    # Update backwards.
    tb.add(backward_lbl)
    # src
    tb.add(self._builder.gen_sub(src, imm_tmp, src_tmp))
    tb.add(self._builder.gen_str(src_tmp, src))
    # dst
    tb.add(self._builder.gen_sub(dst, imm_tmp, dst_tmp))
    tb.add(self._builder.gen_str(dst_tmp, dst))

    # Jump to next instruction.
    tb.add(self._builder.gen_jcc(imm_one, continue_lbl))

    # Update forwards.
    tb.add(forward_lbl)
    # src
    tb.add(self._builder.gen_add(src, imm_tmp, src_tmp))
    tb.add(self._builder.gen_str(src_tmp, src))
    # dst
    tb.add(self._builder.gen_add(dst, imm_tmp, dst_tmp))
    tb.add(self._builder.gen_str(dst_tmp, dst))

    # Continuation label.
    tb.add(continue_lbl)


def _translate_cmps(self, tb, instruction):
    _translate_cmpsb(self, tb, instruction)


def _translate_cmpsb(self, tb, instruction):
    _translate_cmps_suffix(self, tb, instruction, "b")


def _translate_cmpsw(self, tb, instruction):
    _translate_cmps_suffix(self, tb, instruction, "w")


def _translate_cmpsd(self, tb, instruction):
    _translate_cmps_suffix(self, tb, instruction, "d")


def _translate_cmpsq(self, tb, instruction):
    _translate_cmps_suffix(self, tb, instruction, "q")


def _translate_cmps_suffix(self, tb, instruction, suffix):
    # Flags Affected
    # The CF, OF, SF, ZF, AF, and PF flags are set according to the
    # temporary result of the comparison.

    # temp <- SRC1 - SRC2;
    # SetStatusFlags(temp);
    #
    # IF (Byte comparison)
    #   THEN
    #       IF DF = 0
    #           THEN
    #           (R|E)SI <- (R|E)SI + sizeof(SRC);
    #           (R|E)DI <- (R|E)DI + sizeof(SRC);
    #       ELSE
    #           (R|E)SI <- (R|E)SI - sizeof(SRC);
    #           (R|E)DI <- (R|E)DI - sizeof(SRC);
    #       FI;
    # FI;

    # Define data size.
    if suffix == 'b':
        data_size = 8
    elif suffix == 'w':
        data_size = 16
    elif suffix == 'd':
        data_size = 32
    elif suffix == 'q':
        data_size = 64
    else:
        raise Exception("Invalid instruction suffix: %s" % suffix)

    # Define source1 register.
    if self._arch_mode == ARCH_X86_MODE_32:
        src1 = ReilRegisterOperand("esi", 32)
    elif self._arch_mode == ARCH_X86_MODE_64:
        src1 = ReilRegisterOperand("rsi", 64)
    else:
        raise Exception("Invalid architecture mode: %d", self._arch_mode)

    # Define source2 register.
    if self._arch_mode == ARCH_X86_MODE_32:
        src2 = ReilRegisterOperand("edi", 32)
    elif self._arch_mode == ARCH_X86_MODE_64:
        src2 = ReilRegisterOperand("rdi", 64)
    else:
        raise Exception("Invalid architecture mode: %d", self._arch_mode)

    # Define temporary registers
    src1_data = tb.temporal(data_size)
    src2_data = tb.temporal(data_size)
    tmp0 = tb.temporal(data_size * 2)

    if instruction.prefix:
        counter, loop_start_lbl = _rep_prefix_begin(self, tb, instruction)

    # Instruction
    # -------------------------------------------------------------------- #
    # Move data.
    tb.add(self._builder.gen_ldm(src1, src1_data))
    tb.add(self._builder.gen_ldm(src2, src2_data))

    tb.add(self._builder.gen_sub(src1_data, src2_data, tmp0))

    # Flags : CF, OF, SF, ZF, AF, PF
    self._update_cf(self, tb, src1_data, src2_data, tmp0)
    self._update_of_sub(self, tb, src1_data, src2_data, tmp0)
    self._update_sf(self, tb, src1_data, src2_data, tmp0)
    self._update_zf(self, tb, src1_data, src2_data, tmp0)
    self._update_af_sub(self, tb, src1_data, src2_data, tmp0)
    self._update_pf(self, tb, src1_data, src2_data, tmp0)

    # Update source pointers.
    _update_strings_srcs(self, tb, src1, src2, data_size)
    # -------------------------------------------------------------------- #

    if instruction.prefix:
        _rep_prefix_end(self, tb, instruction, counter, loop_start_lbl)


def _translate_lods(self, tb, instruction):
    _translate_lodsb(self, tb, instruction)


def _translate_lodsb(self, tb, instruction):
    _translate_lods_suffix(self, tb, instruction, "b")


def _translate_lodsw(self, tb, instruction):
    _translate_lods_suffix(self, tb, instruction, "w")


def _translate_lodsd(self, tb, instruction):
    _translate_lods_suffix(self, tb, instruction, "d")


def _translate_lodsq(self, tb, instruction):
    _translate_lods_suffix(self, tb, instruction, "q")


def _translate_lods_suffix(self, tb, instruction, suffix):
    # Flags Affected
    # None.

    # DEST <- SRC;
    # IF DF = 0
    #     THEN (E)DI <- (E)DI + sizeof(SRC);
    #     ELSE (E)DI <- (E)DI - sizeof(SRC);
    # FI;

    # Define source register.
    if self._arch_mode == ARCH_X86_MODE_32:
        src = ReilRegisterOperand("esi", 32)
    elif self._arch_mode == ARCH_X86_MODE_64:
        src = ReilRegisterOperand("rsi", 64)
    else:
        raise Exception("Invalid architecture mode: %d", self._arch_mode)

    # Define destination register.
    if suffix == 'b':
        dst = ReilRegisterOperand("al", 8)
    elif suffix == 'w':
        dst = ReilRegisterOperand("ax", 16)
    elif suffix == 'd':
        dst = ReilRegisterOperand("eax", 32)
    elif suffix == 'q':
        dst = ReilRegisterOperand("rax", 64)
    else:
        raise Exception("Invalid instruction suffix: %s" % suffix)

    if instruction.prefix:
        counter, loop_start_lbl = _rep_prefix_begin(self, tb, instruction)

    # Instruction
    # -------------------------------------------------------------------- #
    # Move data.
    tb.add(self._builder.gen_ldm(src, dst))

    # Update destination pointer.
    _update_strings_src(self, tb, src, dst.size, instruction)
    # -------------------------------------------------------------------- #

    if instruction.prefix:
        _rep_prefix_end(self, tb, instruction, counter, loop_start_lbl)


def _translate_movs(self, tb, instruction):
    _translate_movsb(self, tb, instruction)


def _translate_movsb(self, tb, instruction):
    _translate_movs_suffix(self, tb, instruction, "b")


def _translate_movsw(self, tb, instruction):
    _translate_movs_suffix(self, tb, instruction, "w")


def _translate_movsd(self, tb, instruction):
    _translate_movs_suffix(self, tb, instruction, "d")


def _translate_movsq(self, tb, instruction):
    _translate_movs_suffix(self, tb, instruction, "q")


def _translate_movs_suffix(self, tb, instruction, suffix):
    # Flags Affected
    # None.

    # DEST <- SRC;
    # IF DF = 0
    #     THEN (E)DI <- (E)DI + sizeof(SRC);
    #     ELSE (E)DI <- (E)DI - sizeof(SRC);
    # FI;

    # Define source and destination registers.
    if self._arch_mode == ARCH_X86_MODE_32:
        src = ReilRegisterOperand("esi", 32)
        dst = ReilRegisterOperand("edi", 32)
    elif self._arch_mode == ARCH_X86_MODE_64:
        src = ReilRegisterOperand("rsi", 64)
        dst = ReilRegisterOperand("rdi", 64)
    else:
        raise Exception("Invalid architecture mode: %d", self._arch_mode)

    # Define destination register.
    if suffix == 'b':
        data_size = 8
    elif suffix == 'w':
        data_size = 16
    elif suffix == 'd':
        data_size = 32
    elif suffix == 'q':
        data_size = 64
    else:
        raise Exception("Invalid instruction suffix: %s" % suffix)

    if instruction.prefix:
        counter, loop_start_lbl = _rep_prefix_begin(self, tb, instruction)

    # Define temporal registers.
    tmp0 = tb.temporal(data_size)

    # Instruction
    # -------------------------------------------------------------------- #
    # Move data.
    tb.add(self._builder.gen_ldm(src, tmp0))
    tb.add(self._builder.gen_stm(tmp0, dst))

    # Update destination pointer.
    _update_strings_src_and_dst(self, tb, src, dst, data_size)
    # -------------------------------------------------------------------- #

    if instruction.prefix:
        _rep_prefix_end(self, tb, instruction, counter, loop_start_lbl)


def _translate_scas(self, tb, instruction):
    _translate_scasb(self, tb, instruction)


def _translate_scasb(self, tb, instruction):
    _translate_scas_suffix(self, tb, instruction, "b")


def _translate_scasw(self, tb, instruction):
    _translate_scas_suffix(self, tb, instruction, "w")


def _translate_scasd(self, tb, instruction):
    _translate_scas_suffix(self, tb, instruction, "d")


def _translate_scasq(self, tb, instruction):
    _translate_scas_suffix(self, tb, instruction, "q")


def _translate_scas_suffix(self, tb, instruction, suffix):
    # Flags Affected
    # The OF, SF, ZF, AF, PF, and CF flags are set according to the
    # temporary result of the comparison.

    # temp <- SRC1 - SRC2;
    # SetStatusFlags(temp);
    #
    # IF (Byte comparison)
    #   THEN
    #       IF DF = 0
    #           THEN
    #           (R|E)SI <- (R|E)SI + sizeof(SRC);
    #           (R|E)DI <- (R|E)DI + sizeof(SRC);
    #       ELSE
    #           (R|E)SI <- (R|E)SI - sizeof(SRC);
    #           (R|E)DI <- (R|E)DI - sizeof(SRC);
    #       FI;
    # FI;

    # Define source1 register.
    if suffix == 'b':
        src1_data = ReilRegisterOperand("al", 8)
        data_size = 8
    elif suffix == 'w':
        src1_data = ReilRegisterOperand("ax", 16)
        data_size = 16
    elif suffix == 'd':
        src1_data = ReilRegisterOperand("eax", 32)
        data_size = 32
    elif suffix == 'q':
        src1_data = ReilRegisterOperand("rax", 64)
        data_size = 64
    else:
        raise Exception("Invalid instruction suffix: %s" % suffix)

    # Define source2 register.
    if self._arch_mode == ARCH_X86_MODE_32:
        src2 = ReilRegisterOperand("edi", 32)
    elif self._arch_mode == ARCH_X86_MODE_64:
        src2 = ReilRegisterOperand("rdi", 64)
    else:
        raise Exception("Invalid architecture mode: %d", self._arch_mode)

    # Define temporary registers
    src2_data = tb.temporal(data_size)
    tmp0 = tb.temporal(data_size * 2)

    if instruction.prefix:
        counter, loop_start_lbl = _rep_prefix_begin(self, tb, instruction)

    # Instruction
    # -------------------------------------------------------------------- #
    # Move data.
    tb.add(self._builder.gen_ldm(src2, src2_data))

    tb.add(self._builder.gen_sub(src1_data, src2_data, tmp0))

    # Flags : CF, OF, SF, ZF, AF, PF
    self._update_cf(self, tb, src1_data, src2_data, tmp0)
    self._update_of_sub(self, tb, src1_data, src2_data, tmp0)
    self._update_sf(self, tb, src1_data, src2_data, tmp0)
    self._update_zf(self, tb, src1_data, src2_data, tmp0)
    self._update_af_sub(self, tb, src1_data, src2_data, tmp0)
    self._update_pf(self, tb, src1_data, src2_data, tmp0)

    # Update source pointers.
    _update_strings_dst(self, tb, src2, data_size, instruction)
    # -------------------------------------------------------------------- #

    if instruction.prefix:
        _rep_prefix_end(self, tb, instruction, counter, loop_start_lbl)


def _translate_stos(self, tb, instruction):
    _translate_stosb(self, tb, instruction)


def _translate_stosb(self, tb, instruction):
    _translate_stos_suffix(self, tb, instruction, "b")


def _translate_stosw(self, tb, instruction):
    _translate_stos_suffix(self, tb, instruction, "w")


def _translate_stosd(self, tb, instruction):
    _translate_stos_suffix(self, tb, instruction, "d")


def _translate_stosq(self, tb, instruction):
    _translate_stos_suffix(self, tb, instruction, "q")


def _translate_stos_suffix(self, tb, instruction, suffix):
    # Flags Affected
    # None.

    # DEST <- SRC;
    # IF DF = 0
    #     THEN (E)DI <- (E)DI + sizeof(SRC);
    #     ELSE (E)DI <- (E)DI - sizeof(SRC);
    # FI;

    # Define source register.
    if suffix == 'b':
        src = ReilRegisterOperand("al", 8)
    elif suffix == 'w':
        src = ReilRegisterOperand("ax", 16)
    elif suffix == 'd':
        src = ReilRegisterOperand("eax", 32)
    elif suffix == 'q':
        src = ReilRegisterOperand("rax", 64)
    else:
        raise Exception("Invalid instruction suffix: %s" % suffix)

    # Define destination register.
    if self._arch_mode == ARCH_X86_MODE_32:
        dst = ReilRegisterOperand("edi", 32)
    elif self._arch_mode == ARCH_X86_MODE_64:
        dst = ReilRegisterOperand("rdi", 64)
    else:
        raise Exception("Invalid architecture mode: %d", self._arch_mode)

    if instruction.prefix:
        counter, loop_start_lbl = _rep_prefix_begin(self, tb, instruction)

    # Instruction
    # -------------------------------------------------------------------- #
    # Move data.
    tb.add(self._builder.gen_stm(src, dst))

    # Update destination pointer.
    _update_strings_dst(self, tb, dst, src.size, instruction)
    # -------------------------------------------------------------------- #

    if instruction.prefix:
        _rep_prefix_end(self, tb, instruction, counter, loop_start_lbl)


def _rep_prefix_begin(self, tb, instruction):
    # Define counter register.
    if self._arch_info.address_size == 16:
        counter = ReilRegisterOperand("cx", 16)
    elif self._arch_info.address_size == 32:
        counter = ReilRegisterOperand("ecx", 32)
    elif self._arch_info.address_size == 64:
        counter = ReilRegisterOperand("rcx", 64)
    else:
        raise Exception("Invalid address size: %d", self._arch_info.address_size)

    # Create labels.
    loop_start_lbl = Label('loop_start')

    # Define immediate registers.
    end_addr = ReilImmediateOperand((instruction.address + instruction.size) << 8, self._arch_info.address_size + 8)

    # Define temporary registers.
    counter_zero = tb.temporal(1)

    tb.add(loop_start_lbl)

    tb.add(self._builder.gen_bisz(counter, counter_zero))
    tb.add(self._builder.gen_jcc(counter_zero, end_addr))

    return counter, loop_start_lbl


def _rep_prefix_end(self, tb, instruction, counter, loop_start_lbl):
    # Define immediate registers
    imm_one = tb.immediate(1, 1)
    counter_imm_one = tb.immediate(1, counter.size)
    end_addr = ReilImmediateOperand((instruction.address + instruction.size) << 8, self._arch_info.address_size + 8)

    # Define temporary registers.
    counter_tmp = tb.temporal(counter.size)
    counter_zero = tb.temporal(1)
    zf_zero = tb.temporal(1)

    # Termination Condition 1: RCX or (E)CX = 0.
    tb.add(self._builder.gen_sub(counter, counter_imm_one, counter_tmp))
    tb.add(self._builder.gen_str(counter_tmp, counter))
    tb.add(self._builder.gen_bisz(counter, counter_zero))
    tb.add(self._builder.gen_jcc(counter_zero, end_addr))

    prefix = instruction.prefix

    if prefix in ["rep"]:
        # Termination Condition 2: None.
        pass
    elif prefix in ["repz", "repe"]:
        # Termination Condition 2: ZF = 0.
        tb.add(self._builder.gen_xor(self._flags["zf"], imm_one, zf_zero))
        tb.add(self._builder.gen_jcc(zf_zero, end_addr))
    elif prefix in ["repnz", "repne"]:
        # Termination Condition 2: ZF = 1.
        tb.add(self._builder.gen_str(self._flags["zf"], zf_zero))
        tb.add(self._builder.gen_jcc(zf_zero, end_addr))
    else:
        raise Exception("Invalid prefix: %s" % prefix)

    tb.add(self._builder.gen_jcc(imm_one, loop_start_lbl))


dispatcher = {
    'cmpsb': _translate_cmpsb,
    'cmpsw': _translate_cmpsw,
    'cmpsd': _translate_cmpsd,
    'cmpsq': _translate_cmpsq,
    'lods': _translate_lods,
    'lodsb': _translate_lodsb,
    'lodsw': _translate_lodsw,
    'lodsd': _translate_lodsd,
    'lodsq': _translate_lodsq,
    'movs': _translate_movs,
    'movsb': _translate_movsb,
    'movsw': _translate_movsw,
    'movsd': _translate_movsd,
    'movsq': _translate_movsq,
    'scas': _translate_scas,
    'scasb': _translate_scasb,
    'scasw': _translate_scasw,
    'scasd': _translate_scasd,
    'scasq': _translate_scasq,
    'stos': _translate_stos,
    'stosb': _translate_stosb,
    'stosw': _translate_stosw,
    'stosd': _translate_stosd,
    'stosq': _translate_stosq,
}
