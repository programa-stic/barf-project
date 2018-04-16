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

import logging

import barf.arch.x86.translators as translators

from barf.arch import ARCH_X86_MODE_32
from barf.arch import ARCH_X86_MODE_64
from barf.arch.translator import TranslationBuilder
from barf.arch.translator import Translator
from barf.arch.x86 import X86ArchitectureInformation
from barf.arch.x86 import X86ImmediateOperand
from barf.arch.x86 import X86MemoryOperand
from barf.arch.x86 import X86RegisterOperand
from barf.core.reil import ReilImmediateOperand
from barf.core.reil import ReilRegisterOperand
from barf.core.reil import check_operands_size
from barf.core.reil.builder import ReilBuilder
from barf.utils.utils import VariableNamer

logger = logging.getLogger(__name__)


class X86TranslationBuilder(TranslationBuilder):

    def __init__(self, ir_name_generator, architecture_mode):
        super(X86TranslationBuilder, self).__init__(ir_name_generator, X86ArchitectureInformation(architecture_mode))

        self._regs_mapper = self._arch_info.alias_mapper

        self._regs_size = self._arch_info.registers_size

    def read(self, x86_operand):

        if isinstance(x86_operand, X86ImmediateOperand):

            reil_operand = ReilImmediateOperand(x86_operand.immediate, x86_operand.size)

        elif isinstance(x86_operand, X86RegisterOperand):

            reil_operand = ReilRegisterOperand(x86_operand.name, x86_operand.size)

        elif isinstance(x86_operand, X86MemoryOperand):

            addr = self._compute_memory_address(x86_operand)

            reil_operand = self.temporal(x86_operand.size)

            self.add(self._builder.gen_ldm(addr, reil_operand))

        else:
            raise Exception()

        return reil_operand

    def write(self, x86_operand, value):

        if isinstance(x86_operand, X86RegisterOperand):

            reil_operand = ReilRegisterOperand(x86_operand.name, x86_operand.size)

            if self._arch_info.architecture_mode == ARCH_X86_MODE_64 and x86_operand.size == 32:
                if x86_operand.name in self._regs_mapper:
                    base_reg, offset = self._regs_mapper[x86_operand.name]

                    reil_operand_base = ReilRegisterOperand(base_reg, self._regs_size[base_reg])
                    reil_immediate = ReilImmediateOperand(0x0, self._regs_size[base_reg])

                    self.add(self._builder.gen_str(reil_immediate, reil_operand_base))

            self.add(self._builder.gen_str(value, reil_operand))

        elif isinstance(x86_operand, X86MemoryOperand):

            addr = self._compute_memory_address(x86_operand)

            if value.size != x86_operand.size:
                tmp = self.temporal(x86_operand.size)

                self.add(self._builder.gen_str(value, tmp))

                self.add(self._builder.gen_stm(tmp, addr))
            else:
                self.add(self._builder.gen_stm(value, addr))

        else:
            raise Exception()

    def _compute_memory_address(self, mem_operand):
        """Return operand memory access translation.
        """
        if mem_operand.base:
            size = self._regs_size[mem_operand.base]
        elif mem_operand.index:
            size = self._regs_size[mem_operand.index]
        else:
            size = self._arch_info.architecture_size

        addr = None

        if mem_operand.base:
            addr = ReilRegisterOperand(mem_operand.base, size)

        if mem_operand.index and mem_operand.scale != 0x0:
            index = ReilRegisterOperand(mem_operand.index, size)
            scale = ReilImmediateOperand(mem_operand.scale, size)
            scaled_index = self.temporal(size)

            self.add(self._builder.gen_mul(index, scale, scaled_index))

            if addr:
                tmp = self.temporal(size)

                self.add(self._builder.gen_add(addr, scaled_index, tmp))

                addr = tmp
            else:
                addr = scaled_index

        if mem_operand.displacement != 0x0:
            disp = ReilImmediateOperand(mem_operand.displacement, size)

            if addr:
                tmp = self.temporal(size)

                self.add(self._builder.gen_add(addr, disp, tmp))

                addr = tmp
            else:
                addr = disp
        else:
            if not addr:
                disp = ReilImmediateOperand(mem_operand.displacement, size)

                addr = disp

        # TODO Improve this code and add support for the rest of the segments.
        if mem_operand.segment in ["gs", "fs"]:
            seg_base_addr_map = {
                "gs": "gs_base_addr",
                "fs": "fs_base_addr",
            }

            seg_base = ReilRegisterOperand(seg_base_addr_map[mem_operand.segment], size)

            if addr:
                tmp = self.temporal(size)

                self.add(self._builder.gen_add(addr, seg_base, tmp))

                addr = tmp
            else:
                addr = seg_base

        return addr


class X86Translator(Translator):

    """x86 to IR Translator."""

    def __init__(self, architecture_mode):

        super(X86Translator, self).__init__()

        # Set *Architecture Mode*. The translation of each instruction
        # into the REIL language is based on this.
        self._arch_mode = architecture_mode

        # An instance of *ArchitectureInformation*.
        self._arch_info = X86ArchitectureInformation(architecture_mode)

        # An instance of a *VariableNamer*. This is used so all the
        # temporary REIL registers are unique.
        self._ir_name_generator = VariableNamer("t", separator="")

        self._builder = ReilBuilder()

        self._flags = {
            "af": ReilRegisterOperand("af", 1),
            "cf": ReilRegisterOperand("cf", 1),
            "df": ReilRegisterOperand("df", 1),
            "of": ReilRegisterOperand("of", 1),
            "pf": ReilRegisterOperand("pf", 1),
            "sf": ReilRegisterOperand("sf", 1),
            "zf": ReilRegisterOperand("zf", 1),
        }

        if self._arch_mode == ARCH_X86_MODE_32:
            self._sp = ReilRegisterOperand("esp", 32)
            self._bp = ReilRegisterOperand("ebp", 32)
            self._ip = ReilRegisterOperand("eip", 32)

            self._ws = ReilImmediateOperand(4, 32)  # word size
        elif self._arch_mode == ARCH_X86_MODE_64:
            self._sp = ReilRegisterOperand("rsp", 64)
            self._bp = ReilRegisterOperand("rbp", 64)
            self._ip = ReilRegisterOperand("rip", 64)

            self._ws = ReilImmediateOperand(8, 64)  # word size

    def translate(self, instruction):
        """Return IR representation of an instruction.
        """
        try:
            trans_instrs = self._translate(instruction)
        except NotImplementedError:
            unkn_instr = self._builder.gen_unkn()
            unkn_instr.address = instruction.address << 8 | (0x0 & 0xff)
            trans_instrs = [unkn_instr]

            self._log_not_supported_instruction(instruction)
        except:
            self._log_translation_exception(instruction)

            raise

        # Some sanity check....
        for instr in trans_instrs:
            try:
                check_operands_size(instr, self._arch_info.architecture_size)
            except:
                logger.error("Invalid operand size: %s (%s)", instr, instruction)

                raise

        return trans_instrs

    def _translate(self, instruction):
        """Translate a x86 instruction into REIL language.

        :param instruction: a x86 instruction
        :type instruction: X86Instruction
        """
        # Retrieve translation function.
        if instruction.mnemonic in ["movsd"]:
            # Check if it refers to the strings instruction or the sse
            # instruction.
            if not instruction.bytes:
                # Assume strings by default.
                translator_name = "_translate_" + instruction.mnemonic
            elif instruction.bytes[0] not in ["\xa4", "\xa5"]:
                translator_name = "_translate_" + instruction.mnemonic + "_sse"
            else:
                translator_name = "_translate_" + instruction.mnemonic
        else:
            translator_name = "_translate_" + instruction.mnemonic

        # Translate instruction.
        tb = X86TranslationBuilder(self._ir_name_generator, self._arch_mode)

        if translator_name in translators.dispatcher:
            translator_fn = translators.dispatcher[translator_name]

            translator_fn(self, tb, instruction)
        else:
            raise NotImplementedError("Instruction Not Implemented")

        return tb.instanciate(instruction.address)

    def reset(self):
        """Restart IR register name generator.
        """
        self._ir_name_generator.reset()

    def _log_not_supported_instruction(self, instruction):
        bytes_str = " ".join("%02x" % ord(b) for b in instruction.bytes)

        logger.info(
            "Instruction not supported: %s (%s [%s])",
            instruction.mnemonic,
            instruction,
            bytes_str
        )

    def _log_translation_exception(self, instruction):
        bytes_str = " ".join("%02x" % ord(b) for b in instruction.bytes)

        logger.error(
            "Failed to translate x86 to REIL: %s (%s)",
            instruction,
            bytes_str,
            exc_info=True
        )

    # ======================================================================== #
    def _extract_bit(self, tb, reg, bit):
        assert(0 <= bit < reg.size)

        tmp = tb.temporal(reg.size)
        ret = tb.temporal(1)

        tb.add(self._builder.gen_bsh(reg, tb.immediate(-bit, reg.size), tmp))   # shift to LSB
        tb.add(self._builder.gen_and(tmp, tb.immediate(1, reg.size), ret))      # filter LSB

        return ret

    def _extract_msb(self, tb, reg):
        return self._extract_bit(tb, reg, reg.size - 1)

    def _extract_sign_bit(self, tb, reg):
        return self._extract_msb(tb, reg)

    # Flag translation.
    # ======================================================================== #
    def _update_af(self, tb, oprnd0, oprnd1, result):
        assert oprnd0.size == oprnd1.size

        tmp0 = tb.temporal(8)
        tmp1 = tb.temporal(8)
        tmp2 = tb.temporal(8)
        tmp3 = tb.temporal(8)
        tmp4 = tb.temporal(8)
        tmp5 = tb.temporal(8)
        tmp6 = tb.temporal(8)

        imm4 = tb.immediate(4, 8)
        immn4 = tb.immediate(-4, 8)

        af = self._flags["af"]

        # Extract lower byte.
        tb.add(self._builder.gen_str(oprnd0, tmp0))
        tb.add(self._builder.gen_str(oprnd1, tmp1))

        # Zero-extend lower 4 bits.
        tb.add(self._builder.gen_bsh(tmp0, imm4, tmp2))
        tb.add(self._builder.gen_bsh(tmp2, immn4, tmp4))

        tb.add(self._builder.gen_bsh(tmp1, imm4, tmp3))
        tb.add(self._builder.gen_bsh(tmp3, immn4, tmp5))

        # Add up.
        tb.add(self._builder.gen_add(tmp4, tmp5, tmp6))

        # Move bit 4 to AF flag.
        tb.add(self._builder.gen_bsh(tmp6, immn4, af))

    def _update_af_sub(self, tb, oprnd0, oprnd1, result):
        assert oprnd0.size == oprnd1.size

        tmp0 = tb.temporal(8)
        tmp1 = tb.temporal(8)
        tmp2 = tb.temporal(8)
        tmp3 = tb.temporal(8)
        tmp4 = tb.temporal(8)
        tmp5 = tb.temporal(8)
        tmp6 = tb.temporal(8)

        imm4 = tb.immediate(4, 8)
        immn4 = tb.immediate(-4, 8)

        af = self._flags["af"]

        # Extract lower byte.
        tb.add(self._builder.gen_str(oprnd0, tmp0))
        tb.add(self._builder.gen_str(oprnd1, tmp1))

        # Zero-extend lower 4 bits.
        tb.add(self._builder.gen_bsh(tmp0, imm4, tmp2))
        tb.add(self._builder.gen_bsh(tmp2, immn4, tmp4))

        tb.add(self._builder.gen_bsh(tmp1, imm4, tmp3))
        tb.add(self._builder.gen_bsh(tmp3, immn4, tmp5))

        # Subtract
        tb.add(self._builder.gen_sub(tmp4, tmp5, tmp6))

        # Move bit 4 to AF flag.
        tb.add(self._builder.gen_bsh(tmp6, immn4, af))

    def _update_pf(self, tb, oprnd0, oprnd1, result):
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

        pf = self._flags["pf"]

        # tmp1 =  result ^ (result >> 4)
        tb.add(self._builder.gen_bsh(result, immn4, tmp0))
        tb.add(self._builder.gen_xor(result, tmp0, tmp1))

        # tmp3 =  tmp1 ^ (tmp1 >> 2)
        tb.add(self._builder.gen_bsh(tmp1, immn2, tmp2))
        tb.add(self._builder.gen_xor(tmp2, tmp1, tmp3))

        # tmp5 = tmp3 ^ (tmp3 >> 1)
        tb.add(self._builder.gen_bsh(tmp3, immn1, tmp4))
        tb.add(self._builder.gen_xor(tmp4, tmp3, tmp5))

        # Invert and save result.
        tb.add(self._builder.gen_xor(tmp5, imm1, pf))

    def _update_sf(self, tb, oprnd0, oprnd1, result):
        # Create temporal variables.
        tmp0 = tb.temporal(result.size)

        mask0 = tb.immediate(2**(oprnd0.size-1), result.size)
        shift0 = tb.immediate(-(oprnd0.size-1), result.size)

        sf = self._flags["sf"]

        tb.add(self._builder.gen_and(result, mask0, tmp0))  # filter sign bit
        tb.add(self._builder.gen_bsh(tmp0, shift0, sf))     # extract sign bit

    def _update_of(self, tb, oprnd0, oprnd1, result):
        assert oprnd0.size == oprnd1.size

        of = self._flags["of"]

        imm0 = tb.immediate(1, 1)

        tmp0 = tb.temporal(1)
        tmp1 = tb.temporal(1)
        tmp2 = tb.temporal(1)
        tmp3 = tb.temporal(1)

        # Extract sign bit.
        oprnd0_sign = self._extract_sign_bit(tb, oprnd0)
        oprnd1_sign = self._extract_sign_bit(tb, oprnd1)
        result_sign = self._extract_bit(tb, result, oprnd0.size - 1)

        # Compute OF.
        tb.add(self._builder.gen_xor(oprnd0_sign, oprnd1_sign, tmp0))   # (sign bit oprnd0 ^ sign bit oprnd1)
        tb.add(self._builder.gen_xor(tmp0, imm0, tmp1))                 # (sign bit oprnd0 ^ sign bit oprnd1 ^ 1)
        tb.add(self._builder.gen_xor(oprnd0_sign, result_sign, tmp2))   # (sign bit oprnd0 ^ sign bit result)
        tb.add(self._builder.gen_and(tmp1, tmp2, tmp3))                 # (sign bit oprnd0 ^ sign bit oprnd1 ^ 1) & (sign bit oprnd0 ^ sign bit result)

        # Save result.
        tb.add(self._builder.gen_str(tmp3, of))

    def _update_of_sub(self, tb, oprnd0, oprnd1, result):
        assert oprnd0.size == oprnd1.size

        of = self._flags["of"]

        imm0 = tb.immediate(1, 1)

        tmp0 = tb.temporal(1)
        tmp1 = tb.temporal(1)
        tmp2 = tb.temporal(1)
        tmp3 = tb.temporal(1)

        oprnd1_sign = tb.temporal(1)

        # Extract sign bit.
        oprnd0_sign = self._extract_sign_bit(tb, oprnd0)
        oprnd1_sign_tmp = self._extract_sign_bit(tb, oprnd1)
        result_sign = self._extract_bit(tb, result, oprnd0.size - 1)

        # Invert sign bit of oprnd2.
        tb.add(self._builder.gen_xor(oprnd1_sign_tmp, imm0, oprnd1_sign))

        # Compute OF.
        tb.add(self._builder.gen_xor(oprnd0_sign, oprnd1_sign, tmp0))   # (sign bit oprnd0 ^ sign bit oprnd1)
        tb.add(self._builder.gen_xor(tmp0, imm0, tmp1))                 # (sign bit oprnd0 ^ sign bit oprnd1 ^ 1)
        tb.add(self._builder.gen_xor(oprnd0_sign, result_sign, tmp2))   # (sign bit oprnd0 ^ sign bit result)
        tb.add(self._builder.gen_and(tmp1, tmp2, tmp3))                 # (sign bit oprnd0 ^ sign bit oprnd1 ^ 1) & (sign bit oprnd0 ^ sign bit result)

        # Save result.
        tb.add(self._builder.gen_str(tmp3, of))

    def _update_cf(self, tb, oprnd0, oprnd1, result):
        cf = self._flags["cf"]

        imm0 = tb.immediate(2**oprnd0.size, result.size)
        imm1 = tb.immediate(-oprnd0.size, result.size)

        tmp0 = tb.temporal(result.size)

        tb.add(self._builder.gen_and(result, imm0, tmp0))   # filter carry bit
        tb.add(self._builder.gen_bsh(tmp0, imm1, cf))

    def _update_zf(self, tb, oprnd0, oprnd1, result):
        zf = self._flags["zf"]

        imm0 = tb.immediate((2**oprnd0.size)-1, result.size)

        tmp0 = tb.temporal(oprnd0.size)

        tb.add(self._builder.gen_and(result, imm0, tmp0))  # filter low part of result
        tb.add(self._builder.gen_bisz(tmp0, zf))

    def _undefine_flag(self, tb, flag):
        # NOTE: In every test I've made, each time a flag is leave
        # undefined it is always set to 0.

        imm = tb.immediate(0, flag.size)

        tb.add(self._builder.gen_str(imm, flag))

    def _clear_flag(self, tb, flag):
        imm = tb.immediate(0, flag.size)

        tb.add(self._builder.gen_str(imm, flag))

    def _set_flag(self, tb, flag):
        imm = tb.immediate(1, flag.size)

        tb.add(self._builder.gen_str(imm, flag))

    # Helpers.
    # ======================================================================== #
    def _evaluate_a(self, tb):
        return tb._and_regs(tb._negate_reg(self._flags["cf"]), tb._negate_reg(self._flags["zf"]))
        # above (CF=0 and ZF=0).

    def _evaluate_ae(self, tb):
        # above or equal (CF=0)
        return tb._negate_reg(self._flags["cf"])

    def _evaluate_b(self, tb):
        # below (CF=1)
        return self._flags["cf"]

    def _evaluate_be(self, tb):
        # below or equal (CF=1 or ZF=1)
        return tb._or_regs(self._flags["cf"], self._flags["zf"])

    def _evaluate_c(self, tb):
        # carry (CF=1)
        return self._flags["cf"]

    def _evaluate_e(self, tb):
        # equal (ZF=1)
        return self._flags["zf"]

    def _evaluate_g(self, tb):
        # greater (ZF=0 and SF=OF)
        return tb._and_regs(tb._negate_reg(self._flags["zf"]), tb._equal_regs(self._flags["sf"], self._flags["of"]))

    def _evaluate_ge(self, tb):
        # greater or equal (SF=OF)
        return tb._equal_regs(self._flags["sf"], self._flags["of"])

    def _evaluate_l(self, tb):
        # less (SF != OF)
        return tb._unequal_regs(self._flags["sf"], self._flags["of"])

    def _evaluate_le(self, tb):
        # less or equal (ZF=1 or SF != OF)
        return tb._or_regs(self._flags["zf"], tb._unequal_regs(self._flags["sf"], self._flags["of"]))

    def _evaluate_na(self, tb):
        # not above (CF=1 or ZF=1).
        return tb._or_regs(self._flags["cf"], self._flags["zf"])

    def _evaluate_nae(self, tb):
        # not above or equal (CF=1)
        return self._flags["cf"]

    def _evaluate_nb(self, tb):
        # not below (CF=0)
        return tb._negate_reg(self._flags["cf"])

    def _evaluate_nbe(self, tb):
        # not below or equal (CF=0 and ZF=0)
        return tb._and_regs(tb._negate_reg(self._flags["cf"]), tb._negate_reg(self._flags["zf"]))

    def _evaluate_nc(self, tb):
        # not carry (CF=0)
        return tb._negate_reg(self._flags["cf"])

    def _evaluate_ne(self, tb):
        # not equal (ZF=0)
        return tb._negate_reg(self._flags["zf"])

    def _evaluate_ng(self, tb):
        # not greater (ZF=1 or SF != OF)
        return tb._or_regs(self._flags["zf"], tb._unequal_regs(self._flags["sf"], self._flags["of"]))

    def _evaluate_nge(self, tb):
        # not greater or equal (SF != OF)
        return tb._unequal_regs(self._flags["sf"], self._flags["of"])

    def _evaluate_nl(self, tb):
        # not less (SF=OF)
        return tb._equal_regs(self._flags["sf"], self._flags["of"])

    def _evaluate_nle(self, tb):
        # not less or equal (ZF=0 and SF=OF)
        return tb._and_regs(tb._negate_reg(self._flags["zf"]), tb._equal_regs(self._flags["sf"], self._flags["of"]))

    def _evaluate_no(self, tb):
        # not overflow (OF=0)
        return tb._negate_reg(self._flags["of"])

    def _evaluate_np(self, tb):
        # not parity (PF=0)
        return tb._negate_reg(self._flags["pf"])

    def _evaluate_ns(self, tb):
        # not sign (SF=0)
        return tb._negate_reg(self._flags["sf"])

    def _evaluate_nz(self, tb):
        # not zero (ZF=0)
        return tb._negate_reg(self._flags["zf"])

    def _evaluate_o(self, tb):
        # overflow (OF=1)
        return self._flags["of"]

    def _evaluate_p(self, tb):
        # parity (PF=1)
        return self._flags["pf"]

    def _evaluate_pe(self, tb):
        # parity even (PF=1)
        return self._flags["pf"]

    def _evaluate_po(self, tb):
        # parity odd (PF=0)
        return tb._negate_reg(self._flags["pf"])

    def _evaluate_s(self, tb):
        # sign (SF=1)
        return self._flags["sf"]

    def _evaluate_z(self, tb):
        # zero (ZF=1)
        return self._flags["zf"]
