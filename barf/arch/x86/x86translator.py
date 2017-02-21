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

import barf

from barf.arch.translator import Label
from barf.arch.translator import Translator
from barf.arch.translator import TranslationBuilder

from barf.arch import ARCH_X86_MODE_32
from barf.arch import ARCH_X86_MODE_64
from barf.arch.x86.x86base import X86ArchitectureInformation
from barf.arch.x86.x86base import X86RegisterOperand
from barf.core.reil import ReilImmediateOperand
from barf.core.reil import ReilInstructionBuilder
from barf.core.reil import ReilRegisterOperand
from barf.core.reil import check_operands_size
from barf.utils.utils import VariableNamer

FULL_TRANSLATION = 0
LITE_TRANSLATION = 1

logger = logging.getLogger(__name__)


class X86TranslationBuilder(TranslationBuilder):

    def __init__(self, ir_name_generator, architecture_mode):
        super(X86TranslationBuilder, self).__init__(ir_name_generator, architecture_mode)

        self._arch_info = X86ArchitectureInformation(architecture_mode)

        self._regs_mapper = self._arch_info.alias_mapper

        self._regs_size = self._arch_info.registers_size

    def read(self, x86_operand):

        if isinstance(x86_operand, barf.arch.x86.x86base.X86ImmediateOperand):

            reil_operand = ReilImmediateOperand(x86_operand.immediate, x86_operand.size)

        elif isinstance(x86_operand, barf.arch.x86.x86base.X86RegisterOperand):

            reil_operand = ReilRegisterOperand(x86_operand.name, x86_operand.size)

        elif isinstance(x86_operand, barf.arch.x86.x86base.X86MemoryOperand):

            addr = self._compute_memory_address(x86_operand)

            reil_operand = self.temporal(x86_operand.size)

            self.add(self._builder.gen_ldm(addr, reil_operand))

        else:
            raise Exception()

        return reil_operand

    def write(self, x86_operand, value):

        if isinstance(x86_operand, barf.arch.x86.x86base.X86RegisterOperand):

            reil_operand = ReilRegisterOperand(x86_operand.name, x86_operand.size)

            if self._arch_info.architecture_mode == ARCH_X86_MODE_64 and x86_operand.size == 32:
                if x86_operand.name in self._regs_mapper:
                    base_reg, offset = self._regs_mapper[x86_operand.name]

                    reil_operand_base = ReilRegisterOperand(base_reg, self._regs_size[base_reg])
                    reil_immediate = ReilImmediateOperand(0x0, self._regs_size[base_reg])

                    self.add(self._builder.gen_str(reil_immediate, reil_operand_base))

            self.add(self._builder.gen_str(value, reil_operand))

        elif isinstance(x86_operand, barf.arch.x86.x86base.X86MemoryOperand):

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

    def __init__(self, architecture_mode=ARCH_X86_MODE_32, translation_mode=FULL_TRANSLATION):

        super(X86Translator, self).__init__()

        # Set *Architecture Mode*. The translation of each instruction
        # into the REIL language is based on this.
        self._arch_mode = architecture_mode

        # An instance of *ArchitectureInformation*.
        self._arch_info = X86ArchitectureInformation(architecture_mode)

        # Set *Translation Mode*.
        self._translation_mode = translation_mode

        # An instance of a *VariableNamer*. This is used so all the
        # temporary REIL registers are unique.
        self._ir_name_generator = VariableNamer("t", separator="")

        self._builder = ReilInstructionBuilder()

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
                logger.error(
                    "Invalid operand size: %s (%s)",
                    instr,
                    instruction
                )

                raise

        return trans_instrs

    def _translate(self, instruction):
        """Translate a x86 instruction into REIL language.

        :param instruction: a x86 instruction
        :type instruction: X86Instruction
        """
        # Retrieve translation function.
        translator_name = "_translate_" + instruction.mnemonic
        translator_fn = getattr(self, translator_name, self._not_implemented)

        # Translate instruction.
        tb = X86TranslationBuilder(self._ir_name_generator, self._arch_mode)

        translator_fn(tb, instruction)

        return tb.instanciate(instruction.address)

    def reset(self):
        """Restart IR register name generator.
        """
        self._ir_name_generator.reset()

    @property
    def translation_mode(self):
        """Get translation mode.
        """
        return self._translation_mode

    @translation_mode.setter
    def translation_mode(self, value):
        """Set translation mode.
        """
        self._translation_mode = value

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

# ============================================================================ #

    def _not_implemented(self, tb, instruction):
        raise NotImplementedError("Instruction Not Implemented")

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

# Translators
# ============================================================================ #
# ============================================================================ #

# "Flags"
# ============================================================================ #
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

    # above (CF=0 and ZF=0).
    def _evaluate_a(self, tb):
        return tb._and_regs(tb._negate_reg(self._flags["cf"]), tb._negate_reg(self._flags["zf"]))

    # above or equal (CF=0)
    def _evaluate_ae(self, tb):
        return tb._negate_reg(self._flags["cf"])

    # below (CF=1)
    def _evaluate_b(self, tb):
        return self._flags["cf"]

    # below or equal (CF=1 or ZF=1)
    def _evaluate_be(self, tb):
        return tb._or_regs(self._flags["cf"], self._flags["zf"])

    # carry (CF=1)
    def _evaluate_c(self, tb):
        return self._flags["cf"]

    # equal (ZF=1)
    def _evaluate_e(self, tb):
        return self._flags["zf"]

    # greater (ZF=0 and SF=OF)
    def _evaluate_g(self, tb):
        return tb._and_regs(tb._negate_reg(self._flags["zf"]), tb._equal_regs(self._flags["sf"], self._flags["of"]))

    # greater or equal (SF=OF)
    def _evaluate_ge(self, tb):
        return tb._equal_regs(self._flags["sf"], self._flags["of"])

    # less (SF != OF)
    def _evaluate_l(self, tb):
        return tb._unequal_regs(self._flags["sf"], self._flags["of"])

    # less or equal (ZF=1 or SF != OF)
    def _evaluate_le(self, tb):
        return tb._or_regs(self._flags["zf"], tb._unequal_regs(self._flags["sf"], self._flags["of"]))

    # not above (CF=1 or ZF=1).
    def _evaluate_na(self, tb):
        return tb._or_regs(self._flags["cf"], self._flags["zf"])

    # not above or equal (CF=1)
    def _evaluate_nae(self, tb):
        return self._flags["cf"]

    # not below (CF=0)
    def _evaluate_nb(self, tb):
        return tb._negate_reg(self._flags["cf"])

    # not below or equal (CF=0 and ZF=0)
    def _evaluate_nbe(self, tb):
        return tb._and_regs(tb._negate_reg(self._flags["cf"]), tb._negate_reg(self._flags["zf"]))

    # not carry (CF=0)
    def _evaluate_nc(self, tb):
        return tb._negate_reg(self._flags["cf"])

    # not equal (ZF=0)
    def _evaluate_ne(self, tb):
        return tb._negate_reg(self._flags["zf"])

    # not greater (ZF=1 or SF != OF)
    def _evaluate_ng(self, tb):
        return tb._or_regs(self._flags["zf"], tb._unequal_regs(self._flags["sf"], self._flags["of"]))

    # not greater or equal (SF != OF)
    def _evaluate_nge(self, tb):
        return tb._unequal_regs(self._flags["sf"], self._flags["of"])

    # not less (SF=OF)
    def _evaluate_nl(self, tb):
        return tb._equal_regs(self._flags["sf"], self._flags["of"])

    # not less or equal (ZF=0 and SF=OF)
    def _evaluate_nle(self, tb):
        return tb._and_regs(tb._negate_reg(self._flags["zf"]), tb._equal_regs(self._flags["sf"], self._flags["of"]))

    # not overflow (OF=0)
    def _evaluate_no(self, tb):
        return tb._negate_reg(self._flags["of"])

    # not parity (PF=0)
    def _evaluate_np(self, tb):
        return tb._negate_reg(self._flags["pf"])

    # not sign (SF=0)
    def _evaluate_ns(self, tb):
        return tb._negate_reg(self._flags["sf"])

    # not zero (ZF=0)
    def _evaluate_nz(self, tb):
        return tb._negate_reg(self._flags["zf"])

    # overflow (OF=1)
    def _evaluate_o(self, tb):
        return self._flags["of"]

    # parity (PF=1)
    def _evaluate_p(self, tb):
        return self._flags["pf"]

    # parity even (PF=1)
    def _evaluate_pe(self, tb):
        return self._flags["pf"]

    # parity odd (PF=0)
    def _evaluate_po(self, tb):
        return tb._negate_reg(self._flags["pf"])

    # sign (SF=1)
    def _evaluate_s(self, tb):
        return self._flags["sf"]

    # zero (ZF=1)
    def _evaluate_z(self, tb):
        return self._flags["zf"]


# "Data Transfer Instructions"
# ============================================================================ #
    def _translate_bswap(self, tb, instruction):
        # Flags Affected
        # None.
        oprnd0 = tb.read(instruction.operands[0])

        dst = tb.temporal(oprnd0.size)

        tb.add(self._builder.gen_str(tb.immediate(0, dst.size), dst))

        for i in xrange(oprnd0.size / 8):
            t1 = tb.temporal(8)
            t2 = tb.temporal(oprnd0.size)
            t3 = tb.temporal(oprnd0.size)

            dst_new = tb.temporal(oprnd0.size)

            imm1 = tb.immediate(-(i * 8), oprnd0.size)
            imm2 = tb.immediate(8, oprnd0.size)

            tb.add(self._builder.gen_bsh(oprnd0, imm1, t1))
            tb.add(self._builder.gen_str(t1, t2))
            tb.add(self._builder.gen_bsh(dst, imm2, t3))
            tb.add(self._builder.gen_or(t3, t2, dst_new))

            dst = dst_new

        tb.write(instruction.operands[0], dst)

    def _translate_cdq(self, tb, instruction):
        # Flags Affected
        # None.
        eax = X86RegisterOperand("eax", 32)
        edx = X86RegisterOperand("edx", 32)

        oprnd1 = tb.read(eax)

        tmp0 = tb.temporal(64)
        tmp1 = tb.temporal(32)
        imm32 = tb.immediate(-32, 64)

        tb.add(self._builder.gen_sext(oprnd1, tmp0))
        tb.add(self._builder.gen_bsh(tmp0, imm32, tmp1))

        tb.write(edx, tmp1)     # if in 64 bit mode, it zeros the upper half of rdx.

    def _translate_cdqe(self, tb, instruction):
        # Flags Affected
        # None.
        oprnd1 = ReilRegisterOperand("eax", 32)
        oprnd2 = ReilRegisterOperand("rax", 64)

        tmp0 = tb.temporal(oprnd1.size)

        tb.add(self._builder.gen_sext(oprnd1, tmp0))
        tb.add(self._builder.gen_sext(tmp0, oprnd2))

    def _translate_mov(self, tb, instruction):
        # Flags Affected
        # None.

        oprnd1 = tb.read(instruction.operands[1])

        # For cases such as: mov rax, rax
        tmp0 = tb.temporal(oprnd1.size)
        tb.add(self._builder.gen_str(oprnd1, tmp0))

        tb.write(instruction.operands[0], tmp0)

    def _translate_movabs(self, tb, instruction):
        # Alias for mov with 64bit operands.

        self._translate_mov(tb, instruction)

    def _translate_movsx(self, tb, instruction):
        # Flags Affected
        # None.

        oprnd1 = tb.read(instruction.operands[1])

        tmp0 = tb.temporal(instruction.operands[0].size)

        tb.add(self._builder.gen_sext(oprnd1, tmp0))

        tb.write(instruction.operands[0], tmp0)

    def _translate_movsxd(self, tb, instruction):
        # Flags Affected
        # None.

        self._translate_movsx(tb, instruction)

    def _translate_movzx(self, tb, instruction):
        # Flags Affected
        # None.

        oprnd1 = tb.read(instruction.operands[1])

        # For cases such as: movzx eax, al
        tmp0 = tb.temporal(oprnd1.size)
        tb.add(self._builder.gen_str(oprnd1, tmp0))

        tb.write(instruction.operands[0], tmp0)

    def _translate_cmov(self, tb, instruction, cmov_cond):
        # Move if condition (cmov_cond) is met.
        # Flags Affected
        # None.

        eval_cond_fn_name = "_evaluate_" + cmov_cond
        eval_cond_fn = getattr(self, eval_cond_fn_name, self._not_implemented)

        # NOTE: CMOV pseudocode (not its description) specifies that in 32 bit registers, even
        # if the condition is not met, the high 32 bits of the destiny are set to zero (DEST[63:32] <- 0).
        # So op0 (dest) is assigned to itself, in 32 bits that doesn't change anything, in 64 it sets high bits
        # to zero. Then if the condition is met the mov is performed and the previous assignment has no effect.
        # op0 <- op0:
        oprnd0 = tb.read(instruction.operands[0])
        tmp = tb.temporal(oprnd0.size)
        tb.add(self._builder.gen_str(oprnd0, tmp))
        tb.write(instruction.operands[0], tmp)

        cmov_cond_not_met = Label('cmov_cond_not_met')

        neg_cond = tb._negate_reg(eval_cond_fn(tb))

        tb.add(self._builder.gen_jcc(neg_cond, cmov_cond_not_met))

        oprnd1 = tb.read(instruction.operands[1])

        tb.write(instruction.operands[0], oprnd1)

        tb.add(cmov_cond_not_met)
        tb.add(self._builder.gen_nop())

    def _translate_cmova(self, tb, instruction):
        self._translate_cmov(tb, instruction, 'a')

    def _translate_cmovae(self, tb, instruction):
        self._translate_cmov(tb, instruction, 'ae')

    def _translate_cmovb(self, tb, instruction):
        self._translate_cmov(tb, instruction, 'b')

    def _translate_cmovbe(self, tb, instruction):
        self._translate_cmov(tb, instruction, 'be')

    def _translate_cmovc(self, tb, instruction):
        self._translate_cmov(tb, instruction, 'c')

    def _translate_cmove(self, tb, instruction):
        self._translate_cmov(tb, instruction, 'e')

    def _translate_cmovg(self, tb, instruction):
        self._translate_cmov(tb, instruction, 'g')

    def _translate_cmovge(self, tb, instruction):
        self._translate_cmov(tb, instruction, 'ge')

    def _translate_cmovl(self, tb, instruction):
        self._translate_cmov(tb, instruction, 'l')

    def _translate_cmovle(self, tb, instruction):
        self._translate_cmov(tb, instruction, 'le')

    def _translate_cmovna(self, tb, instruction):
        self._translate_cmov(tb, instruction, 'na')

    def _translate_cmovnae(self, tb, instruction):
        self._translate_cmov(tb, instruction, 'nae')

    def _translate_cmovnb(self, tb, instruction):
        self._translate_cmov(tb, instruction, 'nb')

    def _translate_cmovnbe(self, tb, instruction):
        self._translate_cmov(tb, instruction, 'nbe')

    def _translate_cmovnc(self, tb, instruction):
        self._translate_cmov(tb, instruction, 'nc')

    def _translate_cmovne(self, tb, instruction):
        self._translate_cmov(tb, instruction, 'ne')

    def _translate_cmovng(self, tb, instruction):
        self._translate_cmov(tb, instruction, 'ng')

    def _translate_cmovnge(self, tb, instruction):
        self._translate_cmov(tb, instruction, 'nge')

    def _translate_cmovnl(self, tb, instruction):
        self._translate_cmov(tb, instruction, 'nl')

    def _translate_cmovnle(self, tb, instruction):
        self._translate_cmov(tb, instruction, 'nle')

    def _translate_cmovno(self, tb, instruction):
        self._translate_cmov(tb, instruction, 'no')

    def _translate_cmovnp(self, tb, instruction):
        self._translate_cmov(tb, instruction, 'np')

    def _translate_cmovns(self, tb, instruction):
        self._translate_cmov(tb, instruction, 'ns')

    def _translate_cmovnz(self, tb, instruction):
        self._translate_cmov(tb, instruction, 'nz')

    def _translate_cmovo(self, tb, instruction):
        self._translate_cmov(tb, instruction, 'o')

    def _translate_cmovp(self, tb, instruction):
        self._translate_cmov(tb, instruction, 'p')

    def _translate_cmovpe(self, tb, instruction):
        self._translate_cmov(tb, instruction, 'pe')

    def _translate_cmovpo(self, tb, instruction):
        self._translate_cmov(tb, instruction, 'po')

    def _translate_cmovs(self, tb, instruction):
        self._translate_cmov(tb, instruction, 's')

    def _translate_cmovz(self, tb, instruction):
        self._translate_cmov(tb, instruction, 'z')

    def _translate_set(self, tb, instruction, set_cond):
        # Set if condition (set_cond) is met.
        # Flags Affected
        # None.

        eval_cond_fn_name = "_evaluate_" + set_cond
        eval_cond_fn = getattr(self, eval_cond_fn_name, self._not_implemented)

        tb.write(instruction.operands[0], tb.immediate(0, 1))

        set_cond_not_met = Label('set_cond_not_met')

        neg_cond = tb._negate_reg(eval_cond_fn(tb))

        tb.add(self._builder.gen_jcc(neg_cond, set_cond_not_met))

        tb.write(instruction.operands[0], tb.immediate(1, 1))

        tb.add(set_cond_not_met)
        tb.add(self._builder.gen_nop())

    def _translate_seta(self, tb, instruction):
        self._translate_set(tb, instruction, 'a')

    def _translate_setae(self, tb, instruction):
        self._translate_set(tb, instruction, 'ae')

    def _translate_setb(self, tb, instruction):
        self._translate_set(tb, instruction, 'b')

    def _translate_setbe(self, tb, instruction):
        self._translate_set(tb, instruction, 'be')

    def _translate_setc(self, tb, instruction):
        self._translate_set(tb, instruction, 'c')

    def _translate_sete(self, tb, instruction):
        self._translate_set(tb, instruction, 'e')

    def _translate_setg(self, tb, instruction):
        self._translate_set(tb, instruction, 'g')

    def _translate_setge(self, tb, instruction):
        self._translate_set(tb, instruction, 'ge')

    def _translate_setl(self, tb, instruction):
        self._translate_set(tb, instruction, 'l')

    def _translate_setle(self, tb, instruction):
        self._translate_set(tb, instruction, 'le')

    def _translate_setna(self, tb, instruction):
        self._translate_set(tb, instruction, 'na')

    def _translate_setnae(self, tb, instruction):
        self._translate_set(tb, instruction, 'nae')

    def _translate_setnb(self, tb, instruction):
        self._translate_set(tb, instruction, 'nb')

    def _translate_setnbe(self, tb, instruction):
        self._translate_set(tb, instruction, 'nbe')

    def _translate_setnc(self, tb, instruction):
        self._translate_set(tb, instruction, 'nc')

    def _translate_setne(self, tb, instruction):
        self._translate_set(tb, instruction, 'ne')

    def _translate_setng(self, tb, instruction):
        self._translate_set(tb, instruction, 'ng')

    def _translate_setnge(self, tb, instruction):
        self._translate_set(tb, instruction, 'nge')

    def _translate_setnl(self, tb, instruction):
        self._translate_set(tb, instruction, 'nl')

    def _translate_setnle(self, tb, instruction):
        self._translate_set(tb, instruction, 'nle')

    def _translate_setno(self, tb, instruction):
        self._translate_set(tb, instruction, 'no')

    def _translate_setnp(self, tb, instruction):
        self._translate_set(tb, instruction, 'np')

    def _translate_setns(self, tb, instruction):
        self._translate_set(tb, instruction, 'ns')

    def _translate_setnz(self, tb, instruction):
        self._translate_set(tb, instruction, 'nz')

    def _translate_seto(self, tb, instruction):
        self._translate_set(tb, instruction, 'o')

    def _translate_setp(self, tb, instruction):
        self._translate_set(tb, instruction, 'p')

    def _translate_setpe(self, tb, instruction):
        self._translate_set(tb, instruction, 'pe')

    def _translate_setpo(self, tb, instruction):
        self._translate_set(tb, instruction, 'po')

    def _translate_sets(self, tb, instruction):
        self._translate_set(tb, instruction, 's')

    def _translate_setz(self, tb, instruction):
        self._translate_set(tb, instruction, 'z')

    def _translate_xchg(self, tb, instruction):
        # Flags Affected
        # None.

        oprnd0 = tb.read(instruction.operands[0])
        oprnd1 = tb.read(instruction.operands[1])

        tmp0 = tb.temporal(oprnd1.size)

        tb.add(self._builder.gen_str(oprnd0, tmp0))

        tb.write(instruction.operands[0], oprnd1)
        tb.write(instruction.operands[1], tmp0)

    def _translate_push(self, tb, instruction):
        # Flags Affected
        # None.

        oprnd0 = tb.read(instruction.operands[0])

        tmp0 = tb.temporal(self._sp.size)

        tb.add(self._builder.gen_sub(self._sp, self._ws, tmp0))
        tb.add(self._builder.gen_str(tmp0, self._sp))
        tb.add(self._builder.gen_stm(oprnd0, self._sp))

    def _translate_pop(self, tb, instruction):
        # Flags Affected
        # None.

        oprnd0 = tb.read(instruction.operands[0])

        tmp0 = tb.temporal(self._sp.size)

        tb.add(self._builder.gen_ldm(self._sp, oprnd0))
        tb.add(self._builder.gen_add(self._sp, self._ws, tmp0))
        tb.add(self._builder.gen_str(tmp0, self._sp))

    def _translate_cmpxchg(self, tb, instruction):
        # Flags Affected
        # The ZF flag is set if the values in the destination operand
        # and register AL, AX, or EAX are equal; otherwise it is
        # cleared. The CF, PF, AF, SF, and OF flags are set according
        # to the results of the comparison operation.

        # Accumulator = AL, AX, EAX, or RAX depending on whether a byte,
        # word, doubleword, or quadword comparison is being performed
        # IF accumulator = DEST
        # THEN
        #   ZF <- 1;
        #   DEST <- SRC;
        # ELSE
        #   ZF <- 0;
        #   accumulator <- DEST;
        # FI;

        oprnd0 = tb.read(instruction.operands[0])
        oprnd1 = tb.read(instruction.operands[1])

        # Define immediate registers
        end_addr = ReilImmediateOperand((instruction.address + instruction.size) << 8, self._arch_info.address_size + 8)

        # Define accum register.
        if oprnd0.size == 8:
            accum = ReilRegisterOperand("al", 8)
            accum_x86 = X86RegisterOperand("al", 8)
        elif oprnd0.size == 16:
            accum = ReilRegisterOperand("ax", 16)
            accum_x86 = X86RegisterOperand("ax", 16)
        elif oprnd0.size == 32:
            accum = ReilRegisterOperand("eax", 32)
            accum_x86 = X86RegisterOperand("eax", 32)
        elif oprnd0.size == 64:
            accum = ReilRegisterOperand("rax", 64)
            accum_x86 = X86RegisterOperand("rax", 64)
        else:
            raise Exception("Invalid operand size: %s" % oprnd0)

        tmp0 = tb.temporal(oprnd0.size*2)

        one = tb.immediate(1, 1)

        change_dst_lbl = Label('change_dst')
        change_accum_lbl = Label('change_accum')

        # Compare.
        tb.add(self._builder.gen_sub(accum, oprnd0, tmp0))

        # Update flags : CF, OF, SF, ZF, AF, PF
        self._update_cf(tb, accum, oprnd0, tmp0)
        self._update_of_sub(tb, accum, oprnd0, tmp0)
        self._update_sf(tb, accum, oprnd0, tmp0)
        self._update_zf(tb, accum, oprnd0, tmp0)
        self._update_af_sub(tb, accum, oprnd0, tmp0)
        self._update_pf(tb, accum, oprnd0, tmp0)

        # Exchange
        tb.add(self._builder.gen_jcc(tmp0, change_accum_lbl))
        tb.add(change_dst_lbl)
        tb.write(instruction.operands[0], oprnd1)
        tb.add(self._builder.gen_jcc(one, end_addr))
        tb.add(change_accum_lbl)
        # tb.add(self._builder.gen_str(oprnd0, accum))
        tb.write(accum_x86, oprnd0)

# "Binary Arithmetic Instructions"
# ============================================================================ #
    def _translate_add(self, tb, instruction):
        # Flags Affected
        # The OF, SF, ZF, AF, CF, and PF flags are set according to the
        # result.

        oprnd0 = tb.read(instruction.operands[0])
        oprnd1 = tb.read(instruction.operands[1])

        tmp0 = tb.temporal(oprnd0.size*2)

        tb.add(self._builder.gen_add(oprnd0, oprnd1, tmp0))

        if self._translation_mode == FULL_TRANSLATION:
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

        tmp0 = tb.temporal(oprnd1.size*2)
        tmp1 = tb.temporal(oprnd1.size*2)
        tmp2 = tb.temporal(oprnd1.size*2)

        tb.add(self._builder.gen_add(oprnd0, oprnd1, tmp0))
        tb.add(self._builder.gen_str(self._flags["cf"], tmp1))
        tb.add(self._builder.gen_add(tmp0, tmp1, tmp2))

        if self._translation_mode == FULL_TRANSLATION:
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

        tmp0 = tb.temporal(oprnd0.size*2)

        tb.add(self._builder.gen_sub(oprnd0, oprnd1, tmp0))

        if self._translation_mode == FULL_TRANSLATION:
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

        tmp0 = tb.temporal(oprnd0.size*2)
        tmp1 = tb.temporal(oprnd0.size*2)
        tmp2 = tb.temporal(oprnd0.size*2)
        tmp3 = tb.temporal(oprnd0.size)
        tmp4 = tb.temporal(oprnd0.size)

        tb.add(self._builder.gen_sub(oprnd0, oprnd1, tmp0))
        tb.add(self._builder.gen_str(self._flags["cf"], tmp1))
        tb.add(self._builder.gen_sub(tmp0, tmp1, tmp2))
        tb.add(self._builder.gen_str(tmp0, tmp3))
        tb.add(self._builder.gen_str(tmp1, tmp4))

        if self._translation_mode == FULL_TRANSLATION:
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

        imm0 = tb.immediate(-oprnd0.size, oprnd0.size*2)

        tb.add(self._builder.gen_mul(oprnd0, oprnd1, tmp0))

        # Clean rax and rdx registers.
        if self._arch_info.architecture_mode == ARCH_X86_MODE_64 and oprnd0.size == 32:

            zero = tb.immediate(0, 64)

            tb.add(self._builder.gen_str(zero, ReilRegisterOperand("rdx", 64)))
            tb.add(self._builder.gen_str(zero, ReilRegisterOperand("rax", 64)))

        tb.add(self._builder.gen_bsh(tmp0, imm0, result_high))
        tb.add(self._builder.gen_str(tmp0, result_low))

        if self._translation_mode == FULL_TRANSLATION:
            # Flags : OF, CF
            fimm0 = tb.immediate(1, 1)

            ftmp0 = tb.temporal(oprnd0.size*2)
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

        imm0 = tb.immediate(-oprnd0.size, 2*oprnd0.size)

        tmp0 = tb.temporal(2*oprnd0.size)

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

        if self._translation_mode == FULL_TRANSLATION:
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

        imm0 = tb.immediate(oprnd0.size, oprnd0.size*2)

        tmp0 = tb.temporal(oprnd0.size*2)
        tmp1 = tb.temporal(oprnd0.size*2)
        tmp2 = tb.temporal(oprnd0.size*2)

        tmp3 = tb.temporal(oprnd0.size*2)
        tmp4 = tb.temporal(oprnd0.size*2)
        tmp5 = tb.temporal(oprnd0.size*2)
        tmp6 = tb.temporal(oprnd0.size*2)

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

        if self._translation_mode == FULL_TRANSLATION:
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

        imm0 = tb.immediate(oprnd0.size, oprnd0.size*2)

        tmp0 = tb.temporal(oprnd0.size*2)
        tmp1 = tb.temporal(oprnd0.size*2)
        tmp2 = tb.temporal(oprnd0.size*2)

        tmp3 = tb.temporal(oprnd0.size*2)
        tmp4 = tb.temporal(oprnd0.size*2)
        tmp5 = tb.temporal(oprnd0.size*2)
        tmp6 = tb.temporal(oprnd0.size*2)

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

        if self._translation_mode == FULL_TRANSLATION:
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

        tmp0 = tb.temporal(oprnd0.size*2)

        tb.add(self._builder.gen_add(oprnd0, imm0, tmp0))

        if self._translation_mode == FULL_TRANSLATION:
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

        tmp0 = tb.temporal(oprnd0.size*2)

        tb.add(self._builder.gen_sub(oprnd0, imm0, tmp0))

        if self._translation_mode == FULL_TRANSLATION:
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

        imm0 = tb.immediate((2**oprnd0.size)-1, oprnd0.size)
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

        if self._translation_mode == FULL_TRANSLATION:
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

        tmp0 = tb.temporal(oprnd0.size*2)

        tb.add(self._builder.gen_sub(oprnd0, oprnd1, tmp0))

        # Flags : CF, OF, SF, ZF, AF, PF
        self._update_cf(tb, oprnd0, oprnd1, tmp0)
        self._update_of_sub(tb, oprnd0, oprnd1, tmp0)
        self._update_sf(tb, oprnd0, oprnd1, tmp0)
        self._update_zf(tb, oprnd0, oprnd1, tmp0)
        self._update_af_sub(tb, oprnd0, oprnd1, tmp0)
        self._update_pf(tb, oprnd0, oprnd1, tmp0)

# "Decimal Arithmetic Instructions"
# ============================================================================ #

# "Logical Instructions"
# ============================================================================ #
    def _translate_and(self, tb, instruction):
        # Flags Affected
        # The OF and CF flags are cleared; the SF, ZF, and PF flags are
        # set according to the result. The state of the AF flag is
        # undefined.

        oprnd0 = tb.read(instruction.operands[0])
        oprnd1 = tb.read(instruction.operands[1])

        tmp0 = tb.temporal(oprnd0.size*2)

        tb.add(self._builder.gen_and(oprnd0, oprnd1, tmp0))

        if self._translation_mode == FULL_TRANSLATION:
            # Flags : OF, CF
            self._clear_flag(tb, self._flags["of"])
            self._clear_flag(tb, self._flags["cf"])

            # Flags : SF, ZF, PF
            self._update_sf(tb, oprnd0, oprnd1, tmp0)
            self._update_zf(tb, oprnd0, oprnd1, tmp0)
            self._update_pf(tb, oprnd0, oprnd1, tmp0)

            # Flags : AF
            self._undefine_flag(tb, self._flags["af"])

        tb.write(instruction.operands[0], tmp0)

    def _translate_or(self, tb, instruction):
        # Flags Affected
        # The OF and CF flags are cleared; the SF, ZF, and PF flags are
        # set according to the result. The state of the AF flag is
        # undefined.

        oprnd0 = tb.read(instruction.operands[0])
        oprnd1 = tb.read(instruction.operands[1])

        tmp0 = tb.temporal(oprnd0.size*2)

        tb.add(self._builder.gen_or(oprnd0, oprnd1, tmp0))

        if self._translation_mode == FULL_TRANSLATION:
            # Flags : OF, CF
            self._clear_flag(tb, self._flags["of"])
            self._clear_flag(tb, self._flags["cf"])

            # Flags : SF, ZF, PF
            self._update_sf(tb, oprnd0, oprnd1, tmp0)
            self._update_zf(tb, oprnd0, oprnd1, tmp0)
            self._update_pf(tb, oprnd0, oprnd1, tmp0)

            # Flags : AF
            self._undefine_flag(tb, self._flags["af"])

        tb.write(instruction.operands[0], tmp0)

    def _translate_xor(self, tb, instruction):
        # Flags Affected
        # The OF and CF flags are cleared; the SF, ZF, and PF flags are set
        # according to the result. The state of the AF flag is
        # undefined.

        oprnd0 = tb.read(instruction.operands[0])
        oprnd1 = tb.read(instruction.operands[1])

        tmp0 = tb.temporal(oprnd0.size*2)

        tb.add(self._builder.gen_xor(oprnd0, oprnd1, tmp0))

        if self._translation_mode == FULL_TRANSLATION:
            # Flags : OF, CF
            self._clear_flag(tb, self._flags["of"])
            self._clear_flag(tb, self._flags["cf"])

            # Flags : SF, ZF, PF
            self._update_sf(tb, oprnd0, oprnd1, tmp0)
            self._update_zf(tb, oprnd0, oprnd1, tmp0)
            self._update_pf(tb, oprnd0, oprnd1, tmp0)

            # Flags : AF
            self._undefine_flag(tb, self._flags["af"])

        tb.write(instruction.operands[0], tmp0)

    def _translate_not(self, tb, instruction):
        # Flags Affected
        # None.

        oprnd0 = tb.read(instruction.operands[0])

        tmp0 = tb.temporal(oprnd0.size*2)

        imm0 = tb.immediate((2**oprnd0.size)-1, oprnd0.size)

        tb.add(self._builder.gen_xor(oprnd0, imm0, tmp0))

        tb.write(instruction.operands[0], tmp0)

# "Shift and Rotate Instructions"
# ============================================================================ #
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

        oprnd0 = tb.read(instruction.operands[0])
        oprnd1 = tb.read(instruction.operands[1])
        oprnd2 = tb.read(instruction.operands[2])

        if self._arch_info.architecture_mode == ARCH_X86_MODE_32:
            mod_const = tb.immediate(32, oprnd2.size)
        elif self._arch_info.architecture_mode == ARCH_X86_MODE_64:
            mod_const = tb.immediate(64, oprnd2.size)
        else:
            raise Exception("Invalid architecture mode.")

        size = tb.immediate(self._arch_info.operand_size, oprnd2.size)
        end_addr = ReilImmediateOperand((instruction.address + instruction.size) << 8, self._arch_info.address_size + 8)
        count = tb.temporal(oprnd2.size)
        count_zero = tb.temporal(1)
        count_ext = tb.temporal(oprnd2.size*2)
        size_ext = tb.temporal(oprnd2.size * 2)
        count_check = tb.temporal(oprnd2.size * 2)
        count_check_sign = tb.temporal(1)
        dst = tb.temporal(oprnd0.size)

        bad_parameters_lbl = Label("bad_parameters_lbl")
        shift_lbl = Label("shift_lbl")

        tb.add(self._builder.gen_mod(oprnd2, mod_const, count))
        tb.add(self._builder.gen_bisz(count, count_zero))
        tb.add(self._builder.gen_jcc(count_zero, end_addr))

        tb.add(self._builder.gen_str(count, count_ext))
        tb.add(self._builder.gen_str(size, size_ext))
        tb.add(self._builder.gen_sub(size_ext, count_ext, count_check)) # count_check = size_ext - count_ext

        tb.add(self._builder.gen_bsh(count_check, tb.immediate(-count.size, count_check.size), count_check_sign)) # count_check_sign == 1 => count > size

        tb.add(self._builder.gen_jcc(count_check_sign, bad_parameters_lbl))
        tb.add(self._builder.gen_jcc(tb.immediate(1, 1), shift_lbl))

        tb.add(bad_parameters_lbl)
        # dst <- undefined
        tb.add(self._builder.gen_str(oprnd0, dst))
        # Set flags: CF, OF, SF, ZF, AF, PF are undefined;
        if self._translation_mode == FULL_TRANSLATION:
            self._undefine_flag(tb, self._flags["cf"])
            self._undefine_flag(tb, self._flags["of"])
            self._undefine_flag(tb, self._flags["sf"])
            self._undefine_flag(tb, self._flags["zf"])
            self._undefine_flag(tb, self._flags["af"])
            self._undefine_flag(tb, self._flags["pf"])
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

        zero = tb.temporal(count.size)
        bit_offset = tb.temporal(oprnd0.size)
        tmp0 = tb.temporal(1)
        lower = tb.temporal(oprnd0.size*2)
        upper = tb.temporal(oprnd0.size * 2)
        dst_tmp0 = tb.temporal(oprnd0.size * 2)
        dst_tmp1 = tb.temporal(oprnd0.size * 2)
        dst_count = tb.temporal(oprnd0.size * 2)
        dst_count0 = tb.temporal(oprnd0.size * 2)

        # Compute bit offset.
        tb.add(self._builder.gen_sub(zero, count, bit_offset))     # negate

        # Extract bit.
        tb.add(self._builder.gen_bsh(oprnd0, bit_offset, tmp0))

        # Set CF.
        tb.add(self._builder.gen_and(tmp0, tb.immediate(1, 1), self._flags["cf"]))

        tb.add(self._builder.gen_str(oprnd0, lower))
        tb.add(self._builder.gen_bsh(oprnd1, tb.immediate(oprnd1.size, oprnd1.size), upper))
        tb.add(self._builder.gen_or(upper, lower, dst_tmp0))
        tb.add(self._builder.gen_str(count, dst_count0))
        tb.add(self._builder.gen_sub(tb.immediate(0, dst_count0.size), dst_count0, dst_count))
        tb.add(self._builder.gen_bsh(dst_tmp0, dst_count, dst_tmp1))
        tb.add(self._builder.gen_str(dst_tmp1, dst))

        # TODO Set flags accordingly.

        tb.write(instruction.operands[0], dst)

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

        oprnd0 = tb.read(instruction.operands[0])
        oprnd1 = tb.read(instruction.operands[1])

        imm0 = tb.immediate(1, oprnd0.size)
        imm1 = tb.immediate((2**oprnd0.size)-1, oprnd0.size)
        imm2 = tb.immediate(-1, oprnd0.size)

        # if self._arch_info.architecture_mode == ARCH_X86_MODE_32:
        #     mask = tb.immediate(0x1f, oprnd1.size)
        # elif self._arch_info.architecture_mode == ARCH_X86_MODE_64:
        #     mask = tb.immediate(0x3f, oprnd1.size)
        # else:
        #     raise Exception()

        if (oprnd0.name, oprnd0.size) in self._arch_info.regs_32:
            mask = tb.immediate(0x1f, oprnd1.size)
        elif (oprnd0.name, oprnd0.size) in self._arch_info.regs_64:
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
        tb.add(self._builder.gen_str(tmp5, self._flags["cf"]))

        # Shift one more time
        tb.add(self._builder.gen_bsh(tmp4, imm2, tmp6))

        if self._translation_mode == FULL_TRANSLATION:
            # Flags : OF
            # TODO: Implement translation for OF flag.

            # Flags : SF, ZF, PF
            self._update_sf(tb, oprnd0, oprnd0, tmp6)
            self._update_zf(tb, oprnd0, oprnd0, tmp6)
            self._update_pf(tb, oprnd0, oprnd0, tmp6)

            # Flags : AF
            self._undefine_flag(tb, self._flags["af"])

        tb.write(instruction.operands[0], tmp6)

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

        oprnd0 = tb.read(instruction.operands[0])
        oprnd1 = tb.read(instruction.operands[1])

        imm0 = tb.immediate(1, oprnd0.size)
        imm1 = tb.immediate(-31, oprnd0.size)

        # if self._arch_info.architecture_mode == ARCH_X86_MODE_32:
        #     mask = tb.immediate(0x1f, oprnd1.size)
        # elif self._arch_info.architecture_mode == ARCH_X86_MODE_64:
        #     mask = tb.immediate(0x3f, oprnd1.size)
        # else:
        #     raise Exception()

        if (oprnd0.name, oprnd0.size) in self._arch_info.regs_32:
            mask = tb.immediate(0x1f, oprnd1.size)
        elif (oprnd0.name, oprnd0.size) in self._arch_info.regs_64:
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
        tb.add(self._builder.gen_str(tmp3, self._flags["cf"]))

        # Shift one more time
        tb.add(self._builder.gen_bsh(tmp2, imm0, tmp4))

        if self._translation_mode == FULL_TRANSLATION:
            # Flags : OF
            # TODO: Implement translation for OF flag.

            # Flags : SF, ZF, PF
            self._update_sf(tb, oprnd0, oprnd0, tmp4)
            self._update_zf(tb, oprnd0, oprnd0, tmp4)
            self._update_pf(tb, oprnd0, oprnd0, tmp4)

            # Flags : AF
            self._undefine_flag(tb, self._flags["af"])

        tb.write(instruction.operands[0], tmp4)

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

        return self._translate_shl(tb, instruction)

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

        oprnd0 = tb.read(instruction.operands[0])
        oprnd1 = tb.read(instruction.operands[1])

        imm0 = tb.immediate(2**(oprnd0.size-1), oprnd0.size)
        imm1 = tb.immediate(1, oprnd0.size)
        imm2 = tb.immediate(-1, oprnd0.size)

        tmp0 = tb.temporal(oprnd0.size)
        tmp1 = tb.temporal(oprnd0.size)
        tmp2 = tb.temporal(oprnd0.size)
        tmp3 = tb.temporal(oprnd0.size)
        tmp4 = tb.temporal(oprnd0.size)
        tmp5 = tb.temporal(oprnd0.size)
        tmp6 = tb.temporal(oprnd0.size)

        # Create labels.
        loop_lbl = tb.label('loop')

        # Initialize counter
        tb.add(self._builder.gen_str(oprnd1, tmp0))

        # Copy operand to temporal register
        tb.add(self._builder.gen_str(oprnd0, tmp1))

        # Filter sign bit
        tb.add(self._builder.gen_and(oprnd0, imm0, tmp2))

        tb.add(loop_lbl)

        # Filter lsb bit
        tb.add(self._builder.gen_and(oprnd0, imm1, tmp6))
        tb.add(self._builder.gen_str(tmp6, self._flags["cf"]))

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

        if self._translation_mode == FULL_TRANSLATION:
            # Flags : OF
            # TODO: Implement translation for OF flag.

            # Flags : SF, ZF, PF
            self._update_sf(tb, oprnd0, oprnd0, tmp6)
            self._update_zf(tb, oprnd0, oprnd0, tmp6)
            self._update_pf(tb, oprnd0, oprnd0, tmp6)

            # Flags : AF
            self._undefine_flag(tb, self._flags["af"])

        tb.write(instruction.operands[0], tmp6)

    def _translate_rol(self, tb, instruction):
        # Flags Affected
        # The CF flag contains the value of the bit shifted into it.
        # The OF flag is affected only for single-bit rotates (see
        # "Description" above); it is undefined for multi-bit rotates.
        # The SF, ZF, AF, and PF flags are not affected.

        oprnd0 = tb.read(instruction.operands[0])
        oprnd1 = tb.read(instruction.operands[1])

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
        tb.add(self._builder.gen_str(result, self._flags["cf"]))

        # Compute OF.
        undef_of_lbl = tb.label('undef_of_lbl')

        tb.add(self._builder.gen_sub(count_masked, imm0, tmp0))
        tb.add(self._builder.gen_bisz(tmp0, tmp0_zero))
        tb.add(self._builder.gen_jcc(tmp0_zero, undef_of_lbl))

        # Compute.
        tb.add(self._builder.gen_bsh(result, imm2, result_msb))
        tb.add(self._builder.gen_xor(result_msb, self._flags["cf"], self._flags["of"]))

        # Undef OF.
        tb.add(undef_of_lbl)
        self._undefine_flag(tb, self._flags["of"])

        tb.write(instruction.operands[0], result)

    def _translate_ror(self, tb, instruction):
        # Flags Affected
        # The CF flag contains the value of the bit shifted into it.
        # The OF flag is affected only for single-bit rotates (see
        # "Description" above); it is undefined for multi-bit rotates.
        # The SF, ZF, AF, and PF flags are not affected.

        oprnd0 = tb.read(instruction.operands[0])
        oprnd1 = tb.read(instruction.operands[1])

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
        tb.add(self._builder.gen_str(tmp3, self._flags["cf"]))

        # Compute OF.
        undef_of_lbl = tb.label('undef_of_lbl')

        tb.add(self._builder.gen_sub(tmp0, imm1, tmp1))
        tb.add(self._builder.gen_bisz(tmp1, tmp1_zero))
        tb.add(self._builder.gen_jcc(tmp1_zero, undef_of_lbl))

        # Compute.
        tb.add(self._builder.gen_bsh(result, imm3, result_msb))
        tb.add(self._builder.gen_bsh(result, imm5, result_msb_prev))
        tb.add(self._builder.gen_xor(result_msb, result_msb_prev, self._flags["of"]))

        # Undef OF.
        tb.add(undef_of_lbl)
        self._undefine_flag(tb, self._flags["of"])

        tb.write(instruction.operands[0], result)

    def _translate_rcl(self, tb, instruction):
        # Flags Affected
        # The CF flag contains the value of the bit shifted into it.
        # The OF flag is affected only for single-bit rotates (see
        # "Description" above); it is undefined for multi-bit rotates.
        # The SF, ZF, AF, and PF flags are not affected.

        oprnd0 = tb.read(instruction.operands[0])
        oprnd1 = tb.read(instruction.operands[1])

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
            raise Exception("Invalid operand size: %d", oprnd0.size)

        tb.add(self._builder.gen_str(oprnd0, oprnd_ext_1))

        # Insert CF.
        tb.add(self._builder.gen_str(self._flags["cf"], tmp_cf_ext))
        tb.add(self._builder.gen_bsh(tmp_cf_ext, imm4, tmp_cf_ext_1))
        tb.add(self._builder.gen_or(tmp_cf_ext_1, oprnd_ext_1, oprnd_ext))

        tb.add(self._builder.gen_bsh(oprnd_ext, temp_count, oprnd_ext_shifted))
        tb.add(self._builder.gen_bsh(oprnd_ext_shifted, imm2, oprnd_ext_shifted_h))
        tb.add(self._builder.gen_str(oprnd_ext_shifted, oprnd_ext_shifted_l))
        tb.add(self._builder.gen_or(oprnd_ext_shifted_l, oprnd_ext_shifted_h, result))

        # Compute CF.
        tb.add(self._builder.gen_str(result, self._flags["cf"]))

        # Compute OF.
        undef_of_lbl = tb.label('undef_of_lbl')

        tb.add(self._builder.gen_sub(count, imm1, tmp1))
        tb.add(self._builder.gen_bisz(tmp1, tmp1_zero))
        tb.add(self._builder.gen_jcc(tmp1_zero, undef_of_lbl))

        # Compute.
        imm3_1 = tb.immediate(-(oprnd0.size + 1), result.size)

        tb.add(self._builder.gen_bsh(result, imm3_1, result_msb))
        tb.add(self._builder.gen_xor(result_msb, self._flags["cf"], self._flags["of"]))

        # Undef OF.
        tb.add(undef_of_lbl)
        self._undefine_flag(tb, self._flags["of"])

        tb.write(instruction.operands[0], result)

    def _translate_rcr(self, tb, instruction):
        # Flags Affected
        # The CF flag contains the value of the bit shifted into it.
        # The OF flag is affected only for single-bit rotates (see
        # "Description" above); it is undefined for multi-bit rotates.
        # The SF, ZF, AF, and PF flags are not affected.

        # XXX: Fix OF flag

        oprnd0 = tb.read(instruction.operands[0])
        oprnd1 = tb.read(instruction.operands[1])

        tmp0_1 = tb.temporal(oprnd0.size)
        zero = tb.immediate(0, oprnd0.size)

        # TODO: Improve this translation. It uses unecessary large
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
            raise Exception("Invalid operand size: %d", oprnd0.size)

        tb.add(self._builder.gen_sub(zero, tmp0, temp_count))

        # Backup CF.
        tb.add(self._builder.gen_str(self._flags["cf"], cf_old))

        # Insert CF.
        one_1 = tb.immediate(1, oprnd0.size)

        tb.add(self._builder.gen_bsh(oprnd0, one_1, oprnd_ext_1))
        tb.add(self._builder.gen_str(self._flags["cf"], tmp_cf_ext))
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
        tb.add(self._builder.gen_str(oprnd_ext_shifted_h_1, self._flags["cf"]))

        # Compute OF.
        undef_of_lbl = tb.label('undef_of_lbl')

        tb.add(self._builder.gen_sub(count, imm1, tmp1))
        tb.add(self._builder.gen_bisz(tmp1, tmp1_zero))
        tb.add(self._builder.gen_jcc(tmp1_zero, undef_of_lbl))

        # Compute.
        tb.add(self._builder.gen_bsh(oprnd0, imm7, result_msb))
        tb.add(self._builder.gen_xor(result_msb, cf_old, self._flags["of"]))

        # Undef OF.
        tb.add(undef_of_lbl)
        self._undefine_flag(tb, self._flags["of"])

        tb.write(instruction.operands[0], result)

# "Bit and Byte Instructions"
# ============================================================================ #
    def _translate_bt(self, tb, instruction):
        # Flags Affected
        # The CF flag contains the value of the selected bit. The ZF
        # flag is unaffected. The OF, SF, AF, and PF flags are
        # undefined.

        oprnd0 = tb.read(instruction.operands[0])
        oprnd1 = tb.read(instruction.operands[1])

        tmp0 = tb.temporal(oprnd0.size)
        zero = tb.immediate(0, oprnd0.size)
        one = tb.immediate(1, oprnd0.size)
        bit_base_size = tb.immediate(oprnd0.size, oprnd1.size)
        bit_offset_tmp = tb.temporal(oprnd0.size)
        bit_offset = tb.temporal(oprnd0.size)

        # Compute bit offset.
        tb.add(self._builder.gen_mod(oprnd1, bit_base_size, bit_offset_tmp))
        tb.add(self._builder.gen_sub(zero, bit_offset_tmp, bit_offset))     # negate

        # Extract bit.
        tb.add(self._builder.gen_bsh(oprnd0, bit_offset, tmp0))

        # Set CF.
        tb.add(self._builder.gen_and(tmp0, one, self._flags["cf"]))

        # Set flags.
        if self._translation_mode == FULL_TRANSLATION:
            # Flags : OF, SF, AF, PF
            self._undefine_flag(tb, self._flags["of"])
            self._undefine_flag(tb, self._flags["sf"])
            self._undefine_flag(tb, self._flags["af"])
            self._undefine_flag(tb, self._flags["pf"])

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
        oprnd0 = tb.read(instruction.operands[0])
        oprnd1 = tb.read(instruction.operands[1])

        tmp0 = tb.temporal(oprnd0.size)
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
        tb.add(self._builder.gen_sub(zero, bit_offset_tmp, bit_offset))     # negate

        # Extract bit.
        tb.add(self._builder.gen_bsh(oprnd0, bit_offset, tmp0))

        # Set CF.
        tb.add(self._builder.gen_and(tmp0, one, self._flags["cf"]))

        # Set bit in dst.
        tb.add(self._builder.gen_mod(oprnd1, bit_base_size, offset))
        tb.add(self._builder.gen_bsh(one, offset, tmp0))

        tb.add(self._builder.gen_or(oprnd0, tmp0, dst))

        # Set flags.
        if self._translation_mode == FULL_TRANSLATION:
            # Flags : OF, SF, AF, PF
            self._undefine_flag(tb, self._flags["of"])
            self._undefine_flag(tb, self._flags["sf"])
            self._undefine_flag(tb, self._flags["af"])
            self._undefine_flag(tb, self._flags["pf"])

        tb.write(instruction.operands[0], dst)

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

        oprnd0 = tb.read(instruction.operands[0])
        oprnd1 = tb.read(instruction.operands[1])

        zf = self._flags["zf"]
        tmp = tb.temporal(oprnd1.size)
        tmp1 = tb.temporal(oprnd1.size)
        bit_curr = tb.temporal(1)
        dst = tb.temporal(oprnd0.size)
        src_is_zero = tb.temporal(1)
        bit_zero = tb.temporal(1)

        src_is_zero_lbl = Label("src_is_zero_lbl")
        loop_lbl = Label("loop_lbl")
        end_lbl = Label("end_lbl")

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
        if self._translation_mode == FULL_TRANSLATION:
            # Flags : CF, OF, SF, AF, and PF
            self._undefine_flag(tb, self._flags["cf"])
            self._undefine_flag(tb, self._flags["of"])
            self._undefine_flag(tb, self._flags["sf"])
            self._undefine_flag(tb, self._flags["af"])
            self._undefine_flag(tb, self._flags["pf"])

        tb.write(instruction.operands[0], dst)

    def _translate_test(self, tb, instruction):
        # Flags Affected
        # The OF and CF flags are set to 0. The SF, ZF, and PF flags are
        # set according to the result (see the "Operation" section
        # above). The state of the AF flag is undefined.

        oprnd0 = tb.read(instruction.operands[0])
        oprnd1 = tb.read(instruction.operands[1])

        tmp0 = tb.temporal(oprnd0.size)

        tb.add(self._builder.gen_and(oprnd0, oprnd1, tmp0))

        # Flags : OF, CF
        self._clear_flag(tb, self._flags["of"])
        self._clear_flag(tb, self._flags["cf"])

        # Flags : SF, ZF, PF
        self._update_sf(tb, oprnd0, oprnd1, tmp0)
        self._update_zf(tb, oprnd0, oprnd1, tmp0)
        self._update_pf(tb, oprnd0, oprnd1, tmp0)

        # Flags : AF
        self._undefine_flag(tb, self._flags["af"])

# "Control Transfer Instructions"
# ============================================================================ #
    def _translate_address(self, tb, oprnd):
        addr_oprnd_size = oprnd.size + 8

        if isinstance(oprnd, ReilRegisterOperand):
            oprnd_tmp = tb.temporal(addr_oprnd_size)
            addr_oprnd = tb.temporal(addr_oprnd_size)
            imm = ReilImmediateOperand(8, addr_oprnd_size)

            tb.add(self._builder.gen_str(oprnd, oprnd_tmp))
            tb.add(self._builder.gen_bsh(oprnd_tmp, imm, addr_oprnd))
        elif isinstance(oprnd, ReilImmediateOperand):
            addr_oprnd = ReilImmediateOperand(oprnd.immediate << 8, addr_oprnd_size)

        return addr_oprnd

    def _translate_jmp(self, tb, instruction):
        # Flags Affected
        # All flags are affected if a task switch occurs; no flags are
        # affected if a task switch does not occur.

        oprnd0 = tb.read(instruction.operands[0])

        addr_oprnd = self._translate_address(tb, oprnd0)

        imm0 = tb.immediate(1, 1)

        tb.add(self._builder.gen_jcc(imm0, addr_oprnd))

    def _translate_jcc(self, tb, instruction, jcc_cond):
        # Jump if condition (jcc_cond) is met.
        # Flags Affected
        # None.

        eval_cond_fn_name = "_evaluate_" + jcc_cond
        eval_cond_fn = getattr(self, eval_cond_fn_name, self._not_implemented)

        oprnd0 = tb.read(instruction.operands[0])

        addr_oprnd = self._translate_address(tb, oprnd0)

        tb.add(self._builder.gen_jcc(eval_cond_fn(tb), addr_oprnd))

    def _translate_ja(self, tb, instruction):
        self._translate_jcc(tb, instruction, 'a')

    def _translate_jae(self, tb, instruction):
        self._translate_jcc(tb, instruction, 'ae')

    def _translate_jb(self, tb, instruction):
        self._translate_jcc(tb, instruction, 'b')

    def _translate_jbe(self, tb, instruction):
        self._translate_jcc(tb, instruction, 'be')

    def _translate_jc(self, tb, instruction):
        self._translate_jcc(tb, instruction, 'c')

    def _translate_je(self, tb, instruction):
        self._translate_jcc(tb, instruction, 'e')

    def _translate_jg(self, tb, instruction):
        self._translate_jcc(tb, instruction, 'g')

    def _translate_jge(self, tb, instruction):
        self._translate_jcc(tb, instruction, 'ge')

    def _translate_jl(self, tb, instruction):
        self._translate_jcc(tb, instruction, 'l')

    def _translate_jle(self, tb, instruction):
        self._translate_jcc(tb, instruction, 'le')

    def _translate_jna(self, tb, instruction):
        self._translate_jcc(tb, instruction, 'na')

    def _translate_jnae(self, tb, instruction):
        self._translate_jcc(tb, instruction, 'nae')

    def _translate_jnb(self, tb, instruction):
        self._translate_jcc(tb, instruction, 'nb')

    def _translate_jnbe(self, tb, instruction):
        self._translate_jcc(tb, instruction, 'nbe')

    def _translate_jnc(self, tb, instruction):
        self._translate_jcc(tb, instruction, 'nc')

    def _translate_jne(self, tb, instruction):
        self._translate_jcc(tb, instruction, 'ne')

    def _translate_jng(self, tb, instruction):
        self._translate_jcc(tb, instruction, 'ng')

    def _translate_jnge(self, tb, instruction):
        self._translate_jcc(tb, instruction, 'nge')

    def _translate_jnl(self, tb, instruction):
        self._translate_jcc(tb, instruction, 'nl')

    def _translate_jnle(self, tb, instruction):
        self._translate_jcc(tb, instruction, 'nle')

    def _translate_jno(self, tb, instruction):
        self._translate_jcc(tb, instruction, 'no')

    def _translate_jnp(self, tb, instruction):
        self._translate_jcc(tb, instruction, 'np')

    def _translate_jns(self, tb, instruction):
        self._translate_jcc(tb, instruction, 'ns')

    def _translate_jnz(self, tb, instruction):
        self._translate_jcc(tb, instruction, 'nz')

    def _translate_jo(self, tb, instruction):
        self._translate_jcc(tb, instruction, 'o')

    def _translate_jp(self, tb, instruction):
        self._translate_jcc(tb, instruction, 'p')

    def _translate_jpe(self, tb, instruction):
        self._translate_jcc(tb, instruction, 'pe')

    def _translate_jpo(self, tb, instruction):
        self._translate_jcc(tb, instruction, 'po')

    def _translate_js(self, tb, instruction):
        self._translate_jcc(tb, instruction, 's')

    def _translate_jz(self, tb, instruction):
        self._translate_jcc(tb, instruction, 'z')

    def _translate_jecxz(self, tb, instruction):
        # Jump short if ECX register is 0.

        oprnd0 = tb.read(instruction.operands[0])

        addr_oprnd = self._translate_address(tb, oprnd0)

        tmp0 = tb.temporal(1)

        ecx = ReilRegisterOperand("ecx", 32)

        tb.add(self._builder.gen_bisz(ecx, tmp0))
        tb.add(self._builder.gen_jcc(tmp0, addr_oprnd))

    def _translate_call(self, tb, instruction):
        # Flags Affected
        # All flags are affected if a task switch occurs; no flags are
        # affected if a task switch does not occur.

        oprnd0 = tb.read(instruction.operands[0])

        addr_oprnd = self._translate_address(tb, oprnd0)

        imm1 = tb.immediate(1, 1)

        tmp0 = tb.temporal(self._sp.size)

        end_addr = ReilImmediateOperand((instruction.address + instruction.size), self._arch_info.address_size)

        tb.add(self._builder.gen_sub(self._sp, self._ws, tmp0))
        tb.add(self._builder.gen_str(tmp0, self._sp))
        tb.add(self._builder.gen_stm(end_addr, self._sp))
        tb.add(self._builder.gen_jcc(imm1, addr_oprnd))

    def _translate_ret(self, tb, instruction):
        # Flags Affected
        # None.

        imm1 = tb.immediate(1, 1)
        imm8 = tb.immediate(8, self._sp.size)

        tmp0 = tb.temporal(self._sp.size)
        tmp1 = tb.temporal(self._sp.size)
        tmp2 = tb.temporal(self._sp.size + 8)

        tb.add(self._builder.gen_ldm(self._sp, tmp1))
        tb.add(self._builder.gen_add(self._sp, self._ws, tmp0))
        tb.add(self._builder.gen_str(tmp0, self._sp))

        # Free stack.
        if len(instruction.operands) > 0:
            oprnd0 = tb.read(instruction.operands[0])

            imm0 = tb.immediate(oprnd0.immediate & (2**self._sp.size - 1), self._sp.size)

            tmp3 = tb.temporal(self._sp.size)

            tb.add(self._builder.gen_add(self._sp, imm0, tmp3))
            tb.add(self._builder.gen_str(tmp3, self._sp))

        tb.add(self._builder.gen_bsh(tmp1, imm8, tmp2))
        tb.add(self._builder.gen_jcc(imm1, tmp2))

    def _translate_loop(self, tb, instruction):
        # Flags Affected
        # None.

        if self._arch_mode == ARCH_X86_MODE_32:
            counter = ReilRegisterOperand("ecx", 32)
        elif self._arch_mode == ARCH_X86_MODE_64:
            counter = ReilRegisterOperand("rcx", 64)

        oprnd0 = tb.read(instruction.operands[0])

        addr_oprnd = self._translate_address(tb, oprnd0)

        tmp0 = tb.temporal(counter.size)

        imm0 = tb.immediate(1, counter.size)

        tb.add(self._builder.gen_str(counter, tmp0))
        tb.add(self._builder.gen_sub(tmp0, imm0, counter))
        tb.add(self._builder.gen_jcc(counter, addr_oprnd))  # keep looping

    def _translate_loopne(self, tb, instruction):
        # Flags Affected
        # None.

        if self._arch_mode == ARCH_X86_MODE_32:
            counter = ReilRegisterOperand("ecx", 32)
        elif self._arch_mode == ARCH_X86_MODE_64:
            counter = ReilRegisterOperand("rcx", 64)

        oprnd0 = tb.read(instruction.operands[0])

        addr_oprnd = self._translate_address(tb, oprnd0)

        end_addr = ReilImmediateOperand((instruction.address + instruction.size) << 8, self._arch_info.address_size + 8)

        tmp0 = tb.temporal(counter.size)

        counter_zero = tb.temporal(1)
        counter_not_zero = tb.temporal(1)
        zf_zero = tb.temporal(1)
        branch_cond = tb.temporal(1)

        imm0 = tb.immediate(1, counter.size)
        imm1 = tb.immediate(1, 1)

        keep_looping_lbl = tb.label('keep_looping')

        tb.add(self._builder.gen_str(counter, tmp0))
        tb.add(self._builder.gen_sub(tmp0, imm0, counter))
        tb.add(self._builder.gen_bisz(counter, counter_zero))
        tb.add(self._builder.gen_bisz(self._flags["zf"], zf_zero))
        tb.add(self._builder.gen_xor(counter_zero, imm1, counter_not_zero))
        tb.add(self._builder.gen_and(counter_not_zero, zf_zero, branch_cond))
        tb.add(self._builder.gen_jcc(branch_cond, keep_looping_lbl))
        tb.add(self._builder.gen_jcc(imm0, end_addr))   # exit loop
        tb.add(keep_looping_lbl)
        tb.add(self._builder.gen_jcc(imm0, addr_oprnd))

    def _translate_loopnz(self, tb, instruction):
        return self._translate_loopne(tb, instruction)

    def _translate_loope(self, tb, instruction):
        # Flags Affected
        # None.

        if self._arch_mode == ARCH_X86_MODE_32:
            counter = ReilRegisterOperand("ecx", 32)
        elif self._arch_mode == ARCH_X86_MODE_64:
            counter = ReilRegisterOperand("rcx", 64)

        oprnd0 = tb.read(instruction.operands[0])

        addr_oprnd = self._translate_address(tb, oprnd0)

        end_addr = ReilImmediateOperand((instruction.address + instruction.size) << 8, self._arch_info.address_size + 8)

        tmp0 = tb.temporal(counter.size)

        counter_zero = tb.temporal(1)
        counter_not_zero = tb.temporal(1)
        zf_zero = tb.temporal(1)
        zf_not_zero = tb.temporal(1)
        branch_cond = tb.temporal(1)

        imm0 = tb.immediate(1, counter.size)
        imm1 = tb.immediate(1, 1)

        keep_looping_lbl = tb.label('keep_looping')

        tb.add(self._builder.gen_str(counter, tmp0))
        tb.add(self._builder.gen_sub(tmp0, imm0, counter))
        tb.add(self._builder.gen_bisz(counter, counter_zero))
        tb.add(self._builder.gen_bisz(self._flags["zf"], zf_zero))
        tb.add(self._builder.gen_xor(zf_zero, imm1, zf_not_zero))
        tb.add(self._builder.gen_xor(counter_zero, imm1, counter_not_zero))
        tb.add(self._builder.gen_and(counter_not_zero, zf_not_zero, branch_cond))
        tb.add(self._builder.gen_jcc(branch_cond, keep_looping_lbl))
        tb.add(self._builder.gen_jcc(imm0, end_addr))   # exit loop
        tb.add(keep_looping_lbl)
        tb.add(self._builder.gen_jcc(imm0, addr_oprnd))

    def _translate_loopz(self, tb, instruction):
        return self._translate_loope(tb, instruction)

# "String Instructions"
# ============================================================================ #
    def _update_strings_src(self, tb, src, size, instruction):
        self._update_strings_dst(tb, src, size, instruction)

    def _update_strings_srcs(self, tb, src1, src2, size):
        self._update_strings_src_and_dst(tb, src1, src2, size)

    def _update_strings_dst(self, tb, dst, size, instruction):
        # Create labels.
        forward_lbl = Label('forward')
        backward_lbl = Label('backward')

        end_addr = ReilImmediateOperand((instruction.address + instruction.size) << 8, self._arch_info.address_size + 8)

        # Define immediate registers.
        imm_one = tb.immediate(1, 1)

        # Define temporary registers.
        df_zero = tb.temporal(1)
        imm_tmp = tb.immediate(size/8, dst.size)
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
        imm_tmp = tb.immediate(size/8, src.size)
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
        self._translate_cmpsb(tb, instruction)

    def _translate_cmpsb(self, tb, instruction):
        self._translate_cmps_suffix(tb, instruction, "b")

    def _translate_cmpsw(self, tb, instruction):
        self._translate_cmps_suffix(tb, instruction, "w")

    def _translate_cmpsd(self, tb, instruction):
        self._translate_cmps_suffix(tb, instruction, "d")

    def _translate_cmpsq(self, tb, instruction):
        self._translate_cmps_suffix(tb, instruction, "q")

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
        tmp0 = tb.temporal(data_size*2)

        if instruction.prefix:
            counter, loop_start_lbl = self._rep_prefix_begin(tb, instruction)

        # Instruction
        # -------------------------------------------------------------------- #
        # Move data.
        tb.add(self._builder.gen_ldm(src1, src1_data))
        tb.add(self._builder.gen_ldm(src2, src2_data))

        tb.add(self._builder.gen_sub(src1_data, src2_data, tmp0))

        # Flags : CF, OF, SF, ZF, AF, PF
        self._update_cf(tb, src1_data, src2_data, tmp0)
        self._update_of_sub(tb, src1_data, src2_data, tmp0)
        self._update_sf(tb, src1_data, src2_data, tmp0)
        self._update_zf(tb, src1_data, src2_data, tmp0)
        self._update_af_sub(tb, src1_data, src2_data, tmp0)
        self._update_pf(tb, src1_data, src2_data, tmp0)

        # Update source pointers.
        self._update_strings_srcs(tb, src1, src2, data_size)
        # -------------------------------------------------------------------- #

        if instruction.prefix:
            self._rep_prefix_end(tb, instruction, counter, loop_start_lbl)

    def _translate_lods(self, tb, instruction):
        self._translate_lodsb(tb, instruction)

    def _translate_lodsb(self, tb, instruction):
        self._translate_lods_suffix(tb, instruction, "b")

    def _translate_lodsw(self, tb, instruction):
        self._translate_lods_suffix(tb, instruction, "w")

    def _translate_lodsd(self, tb, instruction):
        self._translate_lods_suffix(tb, instruction, "d")

    def _translate_lodsq(self, tb, instruction):
        self._translate_lods_suffix(tb, instruction, "q")

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
            counter, loop_start_lbl = self._rep_prefix_begin(tb, instruction)

        # Instruction
        # -------------------------------------------------------------------- #
        # Move data.
        tb.add(self._builder.gen_ldm(src, dst))

        # Update destination pointer.
        self._update_strings_src(tb, src, dst.size, instruction)
        # -------------------------------------------------------------------- #

        if instruction.prefix:
            self._rep_prefix_end(tb, instruction, counter, loop_start_lbl)

    def _translate_movs(self, tb, instruction):
        self._translate_movsb(tb, instruction)

    def _translate_movsb(self, tb, instruction):
        self._translate_movs_suffix(tb, instruction, "b")

    def _translate_movsw(self, tb, instruction):
        self._translate_movs_suffix(tb, instruction, "w")

    def _translate_movsd(self, tb, instruction):
        self._translate_movs_suffix(tb, instruction, "d")

    def _translate_movsq(self, tb, instruction):
        self._translate_movs_suffix(tb, instruction, "q")

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
            counter, loop_start_lbl = self._rep_prefix_begin(tb, instruction)

        # Define temporal registers.
        tmp0 = tb.temporal(data_size)

        # Instruction
        # -------------------------------------------------------------------- #
        # Move data.
        tb.add(self._builder.gen_ldm(src, tmp0))
        tb.add(self._builder.gen_stm(tmp0, dst))

        # Update destination pointer.
        self._update_strings_src_and_dst(tb, src, dst, data_size)
        # -------------------------------------------------------------------- #

        if instruction.prefix:
            self._rep_prefix_end(tb, instruction, counter, loop_start_lbl)

    def _translate_scas(self, tb, instruction):
        self._translate_scasb(tb, instruction)

    def _translate_scasb(self, tb, instruction):
        self._translate_scas_suffix(tb, instruction, "b")

    def _translate_scasw(self, tb, instruction):
        self._translate_scas_suffix(tb, instruction, "w")

    def _translate_scasd(self, tb, instruction):
        self._translate_scas_suffix(tb, instruction, "d")

    def _translate_scasq(self, tb, instruction):
        self._translate_scas_suffix(tb, instruction, "q")

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
        tmp0 = tb.temporal(data_size*2)

        if instruction.prefix:
            counter, loop_start_lbl = self._rep_prefix_begin(tb, instruction)

        # Instruction
        # -------------------------------------------------------------------- #
        # Move data.
        tb.add(self._builder.gen_ldm(src2, src2_data))

        tb.add(self._builder.gen_sub(src1_data, src2_data, tmp0))

        # Flags : CF, OF, SF, ZF, AF, PF
        self._update_cf(tb, src1_data, src2_data, tmp0)
        self._update_of_sub(tb, src1_data, src2_data, tmp0)
        self._update_sf(tb, src1_data, src2_data, tmp0)
        self._update_zf(tb, src1_data, src2_data, tmp0)
        self._update_af_sub(tb, src1_data, src2_data, tmp0)
        self._update_pf(tb, src1_data, src2_data, tmp0)

        # Update source pointers.
        self._update_strings_dst(tb, src2, data_size, instruction)
        # -------------------------------------------------------------------- #

        if instruction.prefix:
            self._rep_prefix_end(tb, instruction, counter, loop_start_lbl)

    def _translate_stos(self, tb, instruction):
        self._translate_stosb(tb, instruction)

    def _translate_stosb(self, tb, instruction):
        self._translate_stos_suffix(tb, instruction, "b")

    def _translate_stosw(self, tb, instruction):
        self._translate_stos_suffix(tb, instruction, "w")

    def _translate_stosd(self, tb, instruction):
        self._translate_stos_suffix(tb, instruction, "d")

    def _translate_stosq(self, tb, instruction):
        self._translate_stos_suffix(tb, instruction, "q")

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
            counter, loop_start_lbl = self._rep_prefix_begin(tb, instruction)

        # Instruction
        # -------------------------------------------------------------------- #
        # Move data.
        tb.add(self._builder.gen_stm(src, dst))

        # Update destination pointer.
        self._update_strings_dst(tb, dst, src.size, instruction)
        # -------------------------------------------------------------------- #

        if instruction.prefix:
            self._rep_prefix_end(tb, instruction, counter, loop_start_lbl)

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

# "I/O Instructions"
# ============================================================================ #

# "Enter and Leave Instructions"
# ============================================================================ #
    def _translate_leave(self, tb, instruction):
        # Flags Affected
        # None.

        tmp0 = tb.temporal(self._sp.size)

        tb.add(self._builder.gen_str(self._bp, self._sp))
        tb.add(self._builder.gen_ldm(self._sp, self._bp))
        tb.add(self._builder.gen_add(self._sp, self._ws, tmp0))
        tb.add(self._builder.gen_str(tmp0, self._sp))

# "Flag Control (EFLAG) Instructions"
# ============================================================================ #
    def _translate_cld(self, tb, instruction):
        # Flags Affected
        # The DF flag is set to 0. The CF, OF, ZF, SF, AF, and PF flags
        # are unaffected.

        self._clear_flag(tb, self._flags["df"])

    def _translate_clc(self, tb, instruction):
        # Flags Affected
        # The CF flag is set to 0. The OF, ZF, SF, AF, and PF flags are
        # unaffected.

        self._clear_flag(tb, self._flags["cf"])

    def _translate_stc(self, tb, instruction):
        # Flags Affected
        # The CF flag is set. The OF, ZF, SF, AF, and PF flags are
        # unaffected.

        self._set_flag(tb, self._flags["cf"])

    def _translate_std(self, tb, instruction):
        # Flags Affected
        # The DF flag is set. The CF, OF, ZF, SF, AF, and PF flags are
        # unaffected.

        self._set_flag(tb, self._flags["df"])

    def _translate_sahf(self, tb, instruction):
        # Flags Affected
        # The SF, ZF, AF, PF, and CF flags are loaded with values from
        # the AH register. Bits 1, 3, and 5 of the EFLAGS register are
        # unaffected, with the values remaining 1, 0, and 0,
        # respectively.

        oprnd0 = ReilRegisterOperand("ah", 8)

        tmp0 = tb.temporal(oprnd0.size)
        tmp1 = tb.temporal(oprnd0.size)
        tmp2 = tb.temporal(oprnd0.size)
        tmp3 = tb.temporal(oprnd0.size)

        shl_two = tb.immediate(-2, 8)
        shl_one = tb.immediate(-1, 8)

        tb.add(self._builder.gen_str(oprnd0, self._flags["cf"]))
        tb.add(self._builder.gen_bsh(oprnd0, shl_two, tmp0))

        tb.add(self._builder.gen_str(tmp0, self._flags["pf"]))
        tb.add(self._builder.gen_bsh(tmp0, shl_two, tmp1))

        tb.add(self._builder.gen_str(tmp1, self._flags["af"]))
        tb.add(self._builder.gen_bsh(tmp1, shl_two, tmp2))

        tb.add(self._builder.gen_str(tmp2, self._flags["zf"]))
        tb.add(self._builder.gen_bsh(tmp2, shl_one, tmp3))

        tb.add(self._builder.gen_str(tmp3, self._flags["sf"]))

    def _translate_pushf(self, tb, instruction):
        # Flags Affected
        # None.

        tmp0 = tb.temporal(self._sp.size)
        tmp1 = tb.temporal(self._sp.size)

        shr_one = tb.immediate(1, self._sp.size)
        shr_two = tb.immediate(2, self._sp.size)
        shr_three = tb.immediate(3, self._sp.size)

        tb.add(self._builder.gen_str(self._flags["of"], tmp1))
        tb.add(self._builder.gen_bsh(tmp1, shr_one, tmp1))
        tb.add(self._builder.gen_str(self._flags["df"], tmp1))
        tb.add(self._builder.gen_bsh(tmp1, shr_three, tmp1))
        tb.add(self._builder.gen_str(self._flags["sf"], tmp1))
        tb.add(self._builder.gen_bsh(tmp1, shr_one, tmp1))
        tb.add(self._builder.gen_str(self._flags["zf"], tmp1))
        tb.add(self._builder.gen_bsh(tmp1, shr_two, tmp1))
        tb.add(self._builder.gen_str(self._flags["af"], tmp1))
        tb.add(self._builder.gen_bsh(tmp1, shr_two, tmp1))
        tb.add(self._builder.gen_str(self._flags["pf"], tmp1))
        tb.add(self._builder.gen_bsh(tmp1, shr_two, tmp1))
        tb.add(self._builder.gen_str(self._flags["cf"], tmp1))

        tb.add(self._builder.gen_sub(self._sp, self._ws, tmp0))
        tb.add(self._builder.gen_str(tmp0, self._sp))
        tb.add(self._builder.gen_stm(tmp1, self._sp))

    def _translate_pushfd(self, tb, instruction):
        # Flags Affected
        # None.

        self._translate_pushf(tb, instruction)

    def _translate_pushfq(self, tb, instruction):
        # Flags Affected
        # None.

        self._translate_pushf(tb, instruction)

    def _translate_popf(self, tb, instruction):
        # Flags Affected
        # All flags may be affected; see the Operation section for
        # details.

        tmp1 = tb.temporal(self._sp.size)

        shl_one = tb.immediate(-1, self._sp.size)
        shl_two = tb.immediate(-2, self._sp.size)
        shl_three = tb.immediate(-3, self._sp.size)

        tmp0 = tb.temporal(self._sp.size)

        tb.add(self._builder.gen_ldm(self._sp, tmp1))
        tb.add(self._builder.gen_add(self._sp, self._ws, tmp0))
        tb.add(self._builder.gen_str(tmp0, self._sp))

        tb.add(self._builder.gen_str(tmp1, self._flags["cf"]))
        tb.add(self._builder.gen_bsh(tmp1, shl_two, tmp1))
        tb.add(self._builder.gen_str(tmp1, self._flags["pf"]))
        tb.add(self._builder.gen_bsh(tmp1, shl_two, tmp1))
        tb.add(self._builder.gen_str(tmp1, self._flags["af"]))
        tb.add(self._builder.gen_bsh(tmp1, shl_two, tmp1))
        tb.add(self._builder.gen_str(tmp1, self._flags["zf"]))
        tb.add(self._builder.gen_bsh(tmp1, shl_one, tmp1))
        tb.add(self._builder.gen_str(tmp1, self._flags["sf"]))
        tb.add(self._builder.gen_bsh(tmp1, shl_three, tmp1))
        tb.add(self._builder.gen_str(tmp1, self._flags["df"]))
        tb.add(self._builder.gen_bsh(tmp1, shl_one, tmp1))
        tb.add(self._builder.gen_str(tmp1, self._flags["of"]))

    def _translate_popfd(self, tb, instruction):
        # Flags Affected
        # None.

        self._translate_popf(tb, instruction)

    def _translate_popfq(self, tb, instruction):
        # Flags Affected
        # None.

        self._translate_popf(tb, instruction)

# "Segment Register Instructions"
# ============================================================================ #

# "Miscellaneous Instructions"
# ============================================================================ #
    def _translate_lea(self, tb, instruction):
        # Flags Affected
        # None.

        oprnd1 = tb._compute_memory_address(instruction.operands[1])

        tb.write(instruction.operands[0], oprnd1)

    def _translate_nop(self, tb, instruction):
        # Flags Affected
        # None.

        tb.add(self._builder.gen_nop())

# "Random Number Generator Instruction"
# ============================================================================ #

# "Misc"
# ============================================================================ #
    def _translate_hlt(self, tb, instruction):
        # Flags Affected
        # None.

        tb.add(self._builder.gen_unkn())

# "SIMD Instructions"
# ============================================================================ #
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
        # TODO Check.

        oprnd0 = tb.read(instruction.operands[0])
        oprnd1 = tb.read(instruction.operands[1])

        tmp0 = tb.temporal(oprnd0.size)

        tb.add(self._builder.gen_str(tb.immediate(0, oprnd0.size), tmp0))
        tb.add(self._builder.gen_str(oprnd1, tmp0))

        tb.write(instruction.operands[0], tmp0)

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
        # TODO Check.

        oprnd0 = tb.read(instruction.operands[0])
        oprnd1 = tb.read(instruction.operands[1])

        tmp0 = tb.temporal(oprnd0.size)

        tb.add(self._builder.gen_str(tb.immediate(0, oprnd0.size), tmp0))
        tb.add(self._builder.gen_str(oprnd1, tmp0))

        tb.write(instruction.operands[0], tmp0)

    def _translate_movdqa(self, tb, instruction):
        # Flags Affected
        # None.

        # DEST[127:0] <- SRC[127:0]

        # NOTE This implementation ignores the alignment.

        oprnd0 = tb.read(instruction.operands[0])
        oprnd1 = tb.read(instruction.operands[1])

        tmp0 = tb.temporal(oprnd0.size)

        tb.add(self._builder.gen_str(oprnd1, tmp0))

        tb.write(instruction.operands[0], tmp0)

    def _translate_movdqu(self, tb, instruction):
        # Flags Affected
        # None.

        # DEST[127:0] <- SRC[127:0]

        oprnd0 = tb.read(instruction.operands[0])
        oprnd1 = tb.read(instruction.operands[1])

        tmp0 = tb.temporal(oprnd0.size)

        tb.add(self._builder.gen_str(oprnd1, tmp0))

        tb.write(instruction.operands[0], tmp0)

    def _translate_movhpd(self, tb, instruction):
        # Flags Affected
        # None.

        # Operation
        # MOVHPD (128-bit Legacy SSE load)
        # DEST[63:0] (Unmodified)
        # DEST[127:64] <- SRC[63:0]
        # DEST[MAX_VL-1:128] (Unmodified)

        # NOTE Only supports mmx and xmm registers.

        oprnd0 = tb.read(instruction.operands[0])
        oprnd1 = tb.read(instruction.operands[1])

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

        tb.write(instruction.operands[0], dst)

    def _translate_movlpd(self, tb, instruction):
        # Flags Affected
        # None.

        # Operation
        # MOVLPD (128-bit Legacy SSE load)
        # DEST[63:0] <- SRC[63:0]
        # DEST[MAX_VL-1:64] (Unmodified)

        # NOTE Only supports mmx and xmm registers.

        oprnd0 = tb.read(instruction.operands[0])
        oprnd1 = tb.read(instruction.operands[1])

        dst_low = tb.temporal(64)
        dst_high = tb.temporal(64)
        dst = tb.temporal(oprnd0.size)
        dst_tmp0 = tb.temporal(oprnd0.size)
        dst_tmp1 = tb.temporal(oprnd0.size)
        dst_low_ext = tb.temporal(oprnd0.size)

        tb.add(self._builder.gen_bsh(oprnd0, tb.immediate(-64, oprnd0.size), dst_high))
        tb.add(self._builder.gen_str(oprnd1, dst_low))

        tb.add(self._builder.gen_bsh(dst_high, tb.immediate(64, dst_high.size), dst_tmp0))
        tb.add(self._builder.gen_str(dst_low, dst_low_ext))

        tb.add(self._builder.gen_or(dst_low_ext, dst_tmp0, dst))

        tb.write(instruction.operands[0], dst)

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

        oprnd0 = tb.read(instruction.operands[0])
        oprnd1 = tb.read(instruction.operands[1])

        tmp0 = tb.temporal(oprnd0.size)

        tb.add(self._builder.gen_or(oprnd0, oprnd1, tmp0))

        tb.write(instruction.operands[0], tmp0)

    def _translate_pxor(self, tb, instruction):
        # Flags Affected
        # None.

        # DEST <- DEST XOR SRC

        oprnd0 = tb.read(instruction.operands[0])
        oprnd1 = tb.read(instruction.operands[1])

        tmp0 = tb.temporal(oprnd0.size)

        tb.add(self._builder.gen_xor(oprnd0, oprnd1, tmp0))

        tb.write(instruction.operands[0], tmp0)

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

        oprnd0 = tb.read(instruction.operands[0])
        oprnd1 = tb.read(instruction.operands[1])

        dst = tb.temporal(oprnd0.size)

        tb.add(self._builder.gen_str(tb.immediate(0, dst.size), dst))

        for i in xrange(oprnd0.size / 8):
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

        tb.write(instruction.operands[0], dst)

    def _translate_pmovmskb(self, tb, instruction):
        # Flags Affected
        # None.

        # PMOVMSKB (with 64-bit source operand and r32)
        # r32[0] <- SRC[7];
        # r32[1] <- SRC[15];
        # (* Repeat operation for bytes 2 through 6 *)
        # r32[7] <- SRC[63];
        # r32[31:8] <- ZERO_FILL;

        oprnd1 = tb.read(instruction.operands[1])

        dst = tb.temporal(instruction.operands[0].size)

        tb.add(self._builder.gen_str(tb.immediate(0, dst.size), dst))

        j = 0

        for i in xrange(oprnd1.size / 8):
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

        tb.write(instruction.operands[0], dst)

    def _translate_pslldq(self, tb, instruction):
        # Flags Affected
        # None.

        # TEMP <- COUNT
        # IF (TEMP > 15) THEN TEMP <- 16; FI
        # DEST <- DEST << (TEMP * 8)
        # DEST[VLMAX-1:128] (Unmodified)

        # NOTE Only supports xmm registers.

        oprnd0 = tb.read(instruction.operands[0])
        oprnd1 = tb.read(instruction.operands[1])

        count = tb.temporal(oprnd0.size)
        count_tmp = tb.temporal(oprnd1.size)
        tmp0 = tb.temporal(oprnd1.size)
        cmp_result = tb.temporal(1)
        dst = tb.temporal(oprnd0.size)

        imm0 = tb.immediate(~0x7fff, oprnd1.size)

        # Create labels.
        count_ok_lbl = Label('count_ok_lbl')

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
        tb.write(instruction.operands[0], dst)

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

        oprnd0 = tb.read(instruction.operands[0])
        oprnd1 = tb.read(instruction.operands[1])

        count = tb.temporal(oprnd0.size)
        count_tmp = tb.temporal(oprnd1.size)
        count_tmp_2 = tb.temporal(oprnd1.size)
        tmp0 = tb.temporal(oprnd1.size)
        cmp_result = tb.temporal(1)
        dst = tb.temporal(oprnd0.size)

        imm0 = tb.immediate(~0x7fff, oprnd1.size)

        # Create labels.
        count_ok_lbl = Label('count_ok_lbl')

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
        tb.write(instruction.operands[0], dst)

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

        oprnd0 = tb.read(instruction.operands[0])
        oprnd1 = tb.read(instruction.operands[1])

        dst = tb.temporal(oprnd0.size)

        tb.add(self._builder.gen_str(tb.immediate(0, dst.size), dst))

        for i in xrange(oprnd0.size / 8):
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

        tb.write(instruction.operands[0], dst)

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

        oprnd0 = tb.read(instruction.operands[0])
        oprnd1 = tb.read(instruction.operands[1])

        dst = tb.temporal(oprnd0.size)

        tb.add(self._builder.gen_str(tb.immediate(0, dst.size), dst))

        j = 0

        for i in xrange(oprnd0.size / 8):
            t1 = tb.temporal(8)
            t2 = tb.temporal(8)
            t1_ext = tb.temporal(oprnd0.size)
            t2_ext = tb.temporal(oprnd0.size)
            dst_tmp0 = tb.temporal(oprnd0.size)
            dst_tmp1 = tb.temporal(oprnd0.size)
            dst_new = tb.temporal(oprnd0.size)

            imm1 = tb.immediate(-(i * 8), oprnd0.size)
            imm2 = tb.immediate(j * 8, 8)
            imm3 = tb.immediate((j+1) * 8, 8)
            imm4 = tb.immediate(16, oprnd0.size)

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

        tb.write(instruction.operands[0], dst)

    def _translate_punpcklwd(self, tb, instruction):
        # Flags Affected
        # None.

        # Operation
        # PUNPCKLWD instruction with 64-bit operands:
        # DEST[63:48] <- SRC[31:16];
        # DEST[47:32] <- DEST[31:16];
        # DEST[31:16] <- SRC[15:0];
        # DEST[15:0] <- DEST[15:0];

        oprnd0 = tb.read(instruction.operands[0])
        oprnd1 = tb.read(instruction.operands[1])

        dst = tb.temporal(oprnd0.size)

        tb.add(self._builder.gen_str(tb.immediate(0, dst.size), dst))

        j = 0

        for i in xrange(oprnd0.size / 16):
            t1 = tb.temporal(16)
            t2 = tb.temporal(16)
            t1_ext = tb.temporal(oprnd0.size)
            t2_ext = tb.temporal(oprnd0.size)
            dst_tmp0 = tb.temporal(oprnd0.size)
            dst_tmp1 = tb.temporal(oprnd0.size)
            dst_new = tb.temporal(oprnd0.size)

            imm1 = tb.immediate(-(i * 16), oprnd0.size)
            imm2 = tb.immediate(j * 16, 16)
            imm3 = tb.immediate((j+1) * 16, 16)
            imm4 = tb.immediate(32, oprnd0.size)

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

        tb.write(instruction.operands[0], dst)

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

        oprnd0 = tb.read(instruction.operands[0])
        oprnd1 = tb.read(instruction.operands[1])
        oprnd2 = tb.read(instruction.operands[2])

        dst = tb.temporal(oprnd0.size)

        tb.add(self._builder.gen_str(tb.immediate(0, dst.size), dst))

        j = 0

        for i in xrange(oprnd0.size / 32):

            t1 = tb.temporal(8)
            t2 = tb.temporal(8)
            t3 = tb.temporal(oprnd1.size)
            t4 = tb.temporal(oprnd1.size)

            tmp0 = tb.temporal(32)
            tmp1 = tb.temporal(oprnd0.size)

            t1_ext = tb.temporal(oprnd0.size)
            t2_ext = tb.temporal(oprnd0.size)
            dst_tmp0 = tb.temporal(oprnd0.size)
            dst_tmp1 = tb.temporal(oprnd0.size)
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

        tb.write(instruction.operands[0], dst)

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

        oprnd0 = tb.read(instruction.operands[0])
        oprnd1 = tb.read(instruction.operands[1])

        dst = tb.temporal(oprnd0.size)

        tb.add(self._builder.gen_str(tb.immediate(0, dst.size), dst))

        for i in xrange(oprnd0.size / 8):
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

        tb.write(instruction.operands[0], dst)
