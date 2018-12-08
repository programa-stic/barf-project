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

import logging

from barf.arch import ARCH_X86_MODE_32
from barf.arch import ARCH_X86_MODE_64
from barf.arch.helper import extract_bit
from barf.arch.helper import extract_sign_bit
from barf.arch.translator import FlagTranslator
from barf.arch.translator import InstructionTranslator
from barf.arch.translator import RegisterTranslator
from barf.arch.translator import TranslationBuilder
from barf.arch.x86 import X86ArchitectureInformation
from barf.arch.x86 import X86ImmediateOperand
from barf.arch.x86 import X86MemoryOperand
from barf.arch.x86 import X86RegisterOperand
from barf.arch.x86.translators import dispatcher
from barf.core.reil import ReilImmediateOperand
from barf.core.reil import ReilRegisterOperand
from barf.core.reil.builder import ReilBuilder

logger = logging.getLogger(__name__)


class X86FlagTranslator(object):

    def __init__(self, flags):
        # NOTE: it needs: a) a translation builder (to store the instructions),
        # and b) a REIL builder to build the instructions.

        self._flags = flags

    def update_af(self, tb, oprnd0, oprnd1, subtraction=False, cf=None):
        assert oprnd0.size == oprnd1.size

        tmp0 = tb.temporal(8)
        tmp1 = tb.temporal(8)
        tmp2 = tb.temporal(8)
        tmp3 = tb.temporal(8)
        tmp4 = tb.temporal(8)
        tmp5 = tb.temporal(8)
        tmp6 = tb.temporal(8)
        tmp7 = tb.temporal(8)
        tmp8 = tb.temporal(8)

        zero = tb.immediate(0, 8)

        imm4 = tb.immediate(4, 8)
        immn4 = tb.immediate(-4, 8)

        # Extract lower byte.
        tb.add(tb._builder.gen_str(oprnd0, tmp0))
        tb.add(tb._builder.gen_str(oprnd1, tmp1))

        # Zero-extend lower 4 bits.
        tb.add(tb._builder.gen_bsh(tmp0, imm4, tmp2))
        tb.add(tb._builder.gen_bsh(tmp2, immn4, tmp4))

        tb.add(tb._builder.gen_bsh(tmp1, imm4, tmp3))
        tb.add(tb._builder.gen_bsh(tmp3, immn4, tmp5))

        if cf:
            tb.add(tb._builder.gen_str(cf, tmp7))
        else:
            tb.add(tb._builder.gen_str(zero, tmp7))

        if subtraction:
            tb.add(tb._builder.gen_sub(tmp4, tmp5, tmp6))
            tb.add(tb._builder.gen_sub(tmp6, tmp7, tmp8))
        else:
            tb.add(tb._builder.gen_add(tmp4, tmp5, tmp6))
            tb.add(tb._builder.gen_add(tmp6, tmp7, tmp8))

        # Move bit 4 to AF flag.
        tb.add(tb._builder.gen_bsh(tmp8, immn4, self._flags.af))

    def update_pf(self, tb, result):
        tmp0 = tb.temporal(result.size)
        tmp1 = tb.temporal(result.size)
        tmp2 = tb.temporal(result.size)
        tmp3 = tb.temporal(result.size)
        tmp4 = tb.temporal(result.size)
        tmp5 = tb.temporal(result.size)

        imm1 = tb.immediate(1, result.size)
        immn1 = tb.immediate(-1, result.size)
        immn2 = tb.immediate(-2, result.size)
        immn4 = tb.immediate(-4, result.size)

        # tmp1 =  result ^ (result >> 4)
        tb.add(tb._builder.gen_bsh(result, immn4, tmp0))
        tb.add(tb._builder.gen_xor(result, tmp0, tmp1))

        # tmp3 =  tmp1 ^ (tmp1 >> 2)
        tb.add(tb._builder.gen_bsh(tmp1, immn2, tmp2))
        tb.add(tb._builder.gen_xor(tmp2, tmp1, tmp3))

        # tmp5 = tmp3 ^ (tmp3 >> 1)
        tb.add(tb._builder.gen_bsh(tmp3, immn1, tmp4))
        tb.add(tb._builder.gen_xor(tmp4, tmp3, tmp5))

        # Invert and save result.
        tb.add(tb._builder.gen_xor(tmp5, imm1, self._flags.pf))

    def update_sf(self, tb, oprnd0, result):
        tmp0 = tb.temporal(result.size)

        mask0 = tb.immediate(2**(oprnd0.size-1), result.size)
        shift0 = tb.immediate(-(oprnd0.size-1), result.size)

        tb.add(tb._builder.gen_and(result, mask0, tmp0))            # filter sign bit
        tb.add(tb._builder.gen_bsh(tmp0, shift0, self._flags.sf))   # extract sign bit

    def update_of(self, tb, oprnd0, oprnd1, result, subtraction=False):
        assert oprnd0.size == oprnd1.size

        imm0 = tb.immediate(1, 1)

        tmp0 = tb.temporal(1)
        tmp1 = tb.temporal(1)
        tmp2 = tb.temporal(1)
        tmp3 = tb.temporal(1)

        # Extract sign bit.
        oprnd0_sign = extract_sign_bit(tb, oprnd0)
        if subtraction:
            oprnd1_sign = tb.temporal(1)
            oprnd1_sign_tmp = extract_sign_bit(tb, oprnd1)
            # Invert sign bit of oprnd2.
            tb.add(tb._builder.gen_xor(oprnd1_sign_tmp, imm0, oprnd1_sign))
        else:
            oprnd1_sign = extract_sign_bit(tb, oprnd1)
        result_sign = extract_bit(tb, result, oprnd0.size - 1)

        # Compute OF.
        # (sign bit oprnd0 ^ sign bit oprnd1)
        tb.add(tb._builder.gen_xor(oprnd0_sign, oprnd1_sign, tmp0))
        # (sign bit oprnd0 ^ sign bit oprnd1 ^ 1)
        tb.add(tb._builder.gen_xor(tmp0, imm0, tmp1))
        # (sign bit oprnd0 ^ sign bit result)
        tb.add(tb._builder.gen_xor(oprnd0_sign, result_sign, tmp2))
        # (sign bit oprnd0 ^ sign bit oprnd1 ^ 1) & (sign bit oprnd0 ^ sign bit result)
        tb.add(tb._builder.gen_and(tmp1, tmp2, tmp3))

        # Save result.
        tb.add(tb._builder.gen_str(tmp3, self._flags.of))

    def update_cf(self, tb, oprnd0, result):
        imm0 = tb.immediate(2**oprnd0.size, result.size)
        imm1 = tb.immediate(-oprnd0.size, result.size)

        tmp0 = tb.temporal(result.size)

        tb.add(tb._builder.gen_and(result, imm0, tmp0))   # filter carry bit
        tb.add(tb._builder.gen_bsh(tmp0, imm1, self._flags.cf))

    def update_zf(self, tb, oprnd0, result):
        imm0 = tb.immediate((2**oprnd0.size)-1, result.size)

        tmp0 = tb.temporal(oprnd0.size)

        tb.add(tb._builder.gen_and(result, imm0, tmp0))  # filter low part of result
        tb.add(tb._builder.gen_bisz(tmp0, self._flags.zf))

    def undefine_flag(self, tb, flag):
        # NOTE: In every test I've made, each time a flag is leave
        # undefined it is always set to 0.

        imm = tb.immediate(0, flag.size)

        tb.add(tb._builder.gen_str(imm, flag))

    def clear_flag(self, tb, flag):
        imm = tb.immediate(0, flag.size)

        tb.add(tb._builder.gen_str(imm, flag))

    def set_flag(self, tb, flag):
        imm = tb.immediate(1, flag.size)

        tb.add(tb._builder.gen_str(imm, flag))


class X86OperandAccessTranslator(object):

    def __init__(self, arch_info):
        # NOTE: it needs: a) a translation context (to store the instructions),
        # and b) a REIL builder to build the instructions.

        self._arch_info = arch_info

        self._regs_mapper = self._arch_info.alias_mapper

        self._regs_size = self._arch_info.registers_size

    def read(self, tb, x86_operand):
        if isinstance(x86_operand, X86ImmediateOperand):
            reil_operand = ReilImmediateOperand(x86_operand.immediate, x86_operand.size)
        elif isinstance(x86_operand, X86RegisterOperand):
            reil_operand = ReilRegisterOperand(x86_operand.name, x86_operand.size)
        elif isinstance(x86_operand, X86MemoryOperand):
            reil_operand = tb.temporal(x86_operand.size)
            addr = self.resolve_memory_access(tb, x86_operand)
            tb.add(tb._builder.gen_ldm(addr, reil_operand))
        else:
            raise Exception('Invalid operand type')

        return reil_operand

    def write(self, tb, x86_operand, value):
        if isinstance(x86_operand, X86RegisterOperand):
            reil_operand = ReilRegisterOperand(x86_operand.name, x86_operand.size)

            if self._arch_info.architecture_mode == ARCH_X86_MODE_64 and x86_operand.size == 32:
                if x86_operand.name in self._regs_mapper:
                    base_reg, offset = self._regs_mapper[x86_operand.name]

                    reil_operand_base = ReilRegisterOperand(base_reg, self._regs_size[base_reg])
                    reil_immediate = ReilImmediateOperand(0x0, self._regs_size[base_reg])

                    tb.add(tb._builder.gen_str(reil_immediate, reil_operand_base))

            tb.add(tb._builder.gen_str(value, reil_operand))
        elif isinstance(x86_operand, X86MemoryOperand):
            addr = self.resolve_memory_access(tb, x86_operand)

            if value.size != x86_operand.size:
                tmp = tb.temporal(x86_operand.size)

                tb.add(tb._builder.gen_str(value, tmp))
                tb.add(tb._builder.gen_stm(tmp, addr))
            else:
                tb.add(tb._builder.gen_stm(value, addr))
        else:
            raise Exception('Invalid operand type')

    def resolve_memory_access(self, tb, x86_mem_operand):
        """Return operand memory access translation.
        """
        size = self.__get_memory_access_size(x86_mem_operand)

        addr = None

        if x86_mem_operand.base:
            addr = ReilRegisterOperand(x86_mem_operand.base, size)

        if x86_mem_operand.index and x86_mem_operand.scale != 0x0:
            index = ReilRegisterOperand(x86_mem_operand.index, size)
            scale = ReilImmediateOperand(x86_mem_operand.scale, size)
            scaled_index = tb.temporal(size)

            tb.add(tb._builder.gen_mul(index, scale, scaled_index))

            if addr:
                tmp = tb.temporal(size)

                tb.add(tb._builder.gen_add(addr, scaled_index, tmp))

                addr = tmp
            else:
                addr = scaled_index

        if x86_mem_operand.displacement != 0x0:
            disp = ReilImmediateOperand(x86_mem_operand.displacement, size)

            if addr:
                tmp = tb.temporal(size)

                tb.add(tb._builder.gen_add(addr, disp, tmp))

                addr = tmp
            else:
                addr = disp
        else:
            if not addr:
                disp = ReilImmediateOperand(x86_mem_operand.displacement, size)

                addr = disp

        # TODO Improve this code and add support for the rest of the segments.
        if x86_mem_operand.segment in ["gs", "fs"]:
            seg_base_addr_map = {
                "gs": "gs_base_addr",
                "fs": "fs_base_addr",
            }

            seg_base = ReilRegisterOperand(seg_base_addr_map[x86_mem_operand.segment], size)

            if addr:
                tmp = tb.temporal(size)

                tb.add(tb._builder.gen_add(addr, seg_base, tmp))

                addr = tmp
            else:
                addr = seg_base

        return addr

    # Auxiliary functions
    # ======================================================================== #
    def __get_memory_access_size(self, x86_mem_operand):
        if x86_mem_operand.base:
            size = self._regs_size[x86_mem_operand.base]
        elif x86_mem_operand.index:
            size = self._regs_size[x86_mem_operand.index]
        else:
            size = self._arch_info.architecture_size

        return size


class X86Translator(InstructionTranslator):

    """x86 to IR Translator."""

    def __init__(self, architecture_mode):
        super(X86Translator, self).__init__()

        # Set *Architecture Mode*. The translation of each instruction
        # into the REIL language is based on this.
        self._arch_mode = architecture_mode

        # An instance of *ArchitectureInformation*.
        self._arch_info = X86ArchitectureInformation(architecture_mode)

        self._builder = ReilBuilder()

        self._registers = RegisterTranslator(self._arch_info)

        self._reg_acc_translator = X86OperandAccessTranslator(self._arch_info)

        self._flags = FlagTranslator(self._arch_info)

        self._flag_translator = X86FlagTranslator(self._flags)

        # Special registers.
        if self._arch_mode == ARCH_X86_MODE_32:
            self._sp = self._registers.esp
            self._bp = self._registers.ebp
            self._ip = self._registers.eip

        if self._arch_mode == ARCH_X86_MODE_64:
            self._sp = self._registers.rsp
            self._bp = self._registers.rbp
            self._ip = self._registers.rip

        # Word size.
        self._ws = ReilImmediateOperand(self._arch_info.address_size // 8,
                                        self._arch_info.address_size)

    def _translate(self, instruction):
        mnemonic = instruction.mnemonic

        # Check whether it refers to the strings instruction or the sse
        # instruction.
        if instruction.mnemonic in ["movsd"]:
            if instruction.bytes[0] not in ["\xa4", "\xa5"]:
                mnemonic += "_sse"

        tb = TranslationBuilder(self._ir_name_generator, self._arch_info)

        if mnemonic in dispatcher:
            dispatcher[mnemonic](self, tb, instruction)
        else:
            tb.add(self._builder.gen_unkn())

            self._log_not_supported_instruction(instruction)

        return tb.instanciate(instruction.address)
