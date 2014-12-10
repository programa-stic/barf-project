# coding=latin-1

import copy

from functools import wraps

import barf.arch.x86.x86instructiontranslator

from barf.arch import ARCH_X86_MODE_32
from barf.arch import ARCH_X86_MODE_64
from barf.arch.x86.x86base import X86ArchitectureInformation
from barf.core.reil import ReilEmptyOperand
from barf.core.reil import ReilImmediateOperand
from barf.core.reil import ReilMnemonic
from barf.core.reil import ReilParser
from barf.core.reil import ReilRegisterOperand
from barf.core.reil import ReilInstructionBuilder

FULL_TRANSLATION = 0
LITE_TRANSLATION = 1

size_str = {
    128 : "dqword",
    72  : "pointer",
    64  : "qword",
    40  : "pointer",
    32  : "dword",
    16  : "word",
    8   : "byte",
    1   : "bit",
}

class Label(object):

    def __init__(self, name):
        self.name = name

class TranslationBuilder(object):

    def __init__(self, ir_name_generator):
        self._instructions = []

        self._ir_name_generator = ir_name_generator

        self._loops = False

    def add(self, instr):
        if isinstance(instr, Label):
            self._loops = True

        self._instructions.append(instr)

    def temporal(self, size):
        oprnd = ReilRegisterOperand(self._ir_name_generator.get_next(), size)

        return oprnd

    def immediate(self, value, size):
        oprnd = ReilImmediateOperand(value, size)

        return oprnd

    def label(self, name):
        return Label(name)

    def _resolve_loops(self, instrs):
        labels_by_idx = {}
        idx_by_labels = {}

        # Collect labels.
        for index, instr in enumerate(instrs):
            if isinstance(instr, Label):
                labels_by_idx[index] = instr
                idx_by_labels[instr.name] = index

        # Delete labels.
        for index in labels_by_idx:
            del instrs[index]

        # Resolve instruction addresses and JCC targets.
        for index, instr in enumerate(instrs):
            instr.address |= index

            if instr.mnemonic == ReilMnemonic.JCC:
                target = instr.operands[2]

                if isinstance(target, Label):
                    instr.operands[2] = ReilImmediateOperand((instr.address & ~0xff) | idx_by_labels[target.name], 40)

    def instanciate(self, address):
        # Set instructions address.
        instrs = self._instructions

        for instr in instrs:
            instr.address = address << 8

        self._resolve_loops(instrs)

        return instrs

def check_operands_type(instr):
    # Arithmetic and Bitwise instructions
    if instr.mnemonic in [ReilMnemonic.ADD, ReilMnemonic.SUB,
                          ReilMnemonic.MUL, ReilMnemonic.DIV,
                          ReilMnemonic.MOD, ReilMnemonic.BSH,
                          ReilMnemonic.AND, ReilMnemonic.OR,
                          ReilMnemonic.XOR]:

        assert  isinstance(instr.operands[0], ReilRegisterOperand) or \
                isinstance(instr.operands[0], ReilImmediateOperand)
        assert  isinstance(instr.operands[1], ReilRegisterOperand) or \
                isinstance(instr.operands[1], ReilImmediateOperand)
        assert  isinstance(instr.operands[2], ReilRegisterOperand)

    # Data transfer instructions
    elif instr.mnemonic == ReilMnemonic.LDM:

        assert  isinstance(instr.operands[0], ReilRegisterOperand) or \
                isinstance(instr.operands[0], ReilImmediateOperand)
        assert  isinstance(instr.operands[1], ReilEmptyOperand)
        assert  isinstance(instr.operands[2], ReilRegisterOperand)

    elif instr.mnemonic == ReilMnemonic.STM:

        assert  isinstance(instr.operands[0], ReilRegisterOperand) or \
                isinstance(instr.operands[0], ReilImmediateOperand)
        assert  isinstance(instr.operands[1], ReilEmptyOperand)
        assert  isinstance(instr.operands[2], ReilRegisterOperand) or \
                isinstance(instr.operands[2], ReilImmediateOperand)

    elif instr.mnemonic == ReilMnemonic.STR:

        assert  isinstance(instr.operands[0], ReilRegisterOperand) or \
                isinstance(instr.operands[0], ReilImmediateOperand)
        assert  isinstance(instr.operands[1], ReilEmptyOperand)
        assert  isinstance(instr.operands[2], ReilRegisterOperand)

    # Conditional instructions
    elif instr.mnemonic == ReilMnemonic.BISZ:

        assert  isinstance(instr.operands[0], ReilRegisterOperand) or \
                isinstance(instr.operands[0], ReilImmediateOperand)
        assert  isinstance(instr.operands[1], ReilEmptyOperand)
        assert  isinstance(instr.operands[2], ReilRegisterOperand)

    elif instr.mnemonic == ReilMnemonic.JCC:

        assert  isinstance(instr.operands[0], ReilRegisterOperand) or \
                isinstance(instr.operands[0], ReilImmediateOperand)
        assert  isinstance(instr.operands[1], ReilEmptyOperand)
        assert  isinstance(instr.operands[2], ReilRegisterOperand) or \
                isinstance(instr.operands[2], ReilImmediateOperand)

    # Other instructions
    elif instr.mnemonic == ReilMnemonic.UNDEF:

        assert  isinstance(instr.operands[0], ReilEmptyOperand)
        assert  isinstance(instr.operands[1], ReilEmptyOperand)
        assert  isinstance(instr.operands[2], ReilRegisterOperand)

    elif instr.mnemonic in [ReilMnemonic.UNKN, ReilMnemonic.NOP]:

        assert  isinstance(instr.operands[0], ReilEmptyOperand)
        assert  isinstance(instr.operands[1], ReilEmptyOperand)
        assert  isinstance(instr.operands[2], ReilEmptyOperand)

    elif instr.mnemonic in [ReilMnemonic.RET]:

        assert  isinstance(instr.operands[0], ReilEmptyOperand)
        assert  isinstance(instr.operands[1], ReilEmptyOperand)
        assert  isinstance(instr.operands[2], ReilEmptyOperand)

    else:
        raise TypeError("Unknon instruction mnemonic : ", instr.mnemonic)

def check_operands_size(instr):
    error_msg = "Operand size error : %s" % instr

    for operand in instr.operands:
        if not isinstance(operand, ReilEmptyOperand):
            assert operand.size in [1, 8, 16, 32, 40, 64, 72, 128], error_msg

def set_operands_size(instr, reg_size):
    for operand in instr.operands:
        if isinstance(operand, ReilRegisterOperand):
            if not operand.size:
                operand.size = reg_size.get(operand.name, None)

            if operand.size and operand.name not in reg_size:
                reg_size[operand.name] = operand.size

def infer_operands_size(instr, arch_size):
    if instr.mnemonic in [  ReilMnemonic.ADD, ReilMnemonic.SUB,
                            ReilMnemonic.MUL, ReilMnemonic.DIV,
                            ReilMnemonic.MOD, ReilMnemonic.BSH,
                            ReilMnemonic.AND, ReilMnemonic.OR,
                            ReilMnemonic.XOR]:

        if instr.operands[0].size and not instr.operands[1].size:
            instr.operands[1].size = instr.operands[0].size

        if instr.operands[1].size and not instr.operands[0].size:
            instr.operands[0].size = instr.operands[1].size

        # Check that source operand have the same size.
        assert instr.operands[0].size == instr.operands[1].size

    elif instr.mnemonic in [ReilMnemonic.LDM]:
        # operand0 : address (Literal or Register)
        # operand1 : empty
        # operand2 : destination register

        if not instr.operands[0].size:
            instr.operands[0].size = arch_size

        assert instr.operands[0].size == arch_size

    elif instr.mnemonic in [ReilMnemonic.STM]:
        # operand0 : value to store (Literal or Register)
        # operand1 : empty
        # operand2 : destination address (Literal or Register)

        if not instr.operands[2].size:
            instr.operands[2].size = arch_size

        assert instr.operands[2].size == arch_size

    elif instr.mnemonic in [ReilMnemonic.STR]:
        # operand0 : value to store (Literal or Register)
        # operand1 : empty
        # operand2 : destination register

        if not instr.operands[0].size and \
            isinstance(instr.operands[0], ReilImmediateOperand):
                instr.operands[0].size = arch_size

        # Default size of destination register is the same as
        # source size
        if instr.operands[0].size and not instr.operands[2].size:
            instr.operands[2].size = instr.operands[0].size

    elif instr.mnemonic in [ReilMnemonic.BISZ]:

        pass

    elif instr.mnemonic in [ReilMnemonic.JCC]:

        # Note: operand3.size should be arch_size + 1 byte

        pass

def add_register_size(old_method):
    @wraps(old_method)
    def new_method(self, *args, **kw_args):
        instrs = old_method(self, *args, **kw_args)

        arch_size = self.arch_info.architecture_size
        reg_size = dict(self.arch_info.register_size)

        for instr in instrs:
            # print "<", instr

            # Check that each operand has the correct type for the
            # instruction it is in. Just for debugging purposes.
            check_operands_type(instr)

            # Set each operand size.
            set_operands_size(instr, reg_size)
            # 'Infer' operand size base on other operands.
            infer_operands_size(instr, arch_size)
            # Set each operand size, again (in case, the 'infer' process
            # was successful.)
            set_operands_size(instr, reg_size)

            # Check that each operand size. It should be set and it has
            # to be a valid one.
            check_operands_size(instr)

            # print ">", instr

        return instrs
    return new_method

class X86InstructionTranslator(object):

    """x86 Instruction Translator."""

    def __init__(self, ir_name_generator, architecture_mode=ARCH_X86_MODE_32, translation_mode=FULL_TRANSLATION):

        # An instance of a *VariableNamer*. This is used so all the
        # temporary REIL registers are unique.
        self.ir_name_generator = ir_name_generator

        # Set *Architecture Mode*. The translation of each instruction
        # into the REIL language is based on this.
        self.architecture_mode = architecture_mode

        # Set *Translation Mode*.
        self._translation_mode = translation_mode

        # A *ReilParser*. This is used to do all the instruction
        # translations.
        self._ir_parser = ReilParser()

        # An instruction translation cache.
        self.translation_cache = {}

        # An instance of *ArchitectureInformation*.
        self.arch_info = X86ArchitectureInformation(architecture_mode)

    def translate(self, instruction, in_operands, out_operands):
        """Translate a x86 instruction into REIL language.

        :param instruction: a x86 instruction
        :type instruction: X86Instruction

        :param in_operands: a list of the instruction's source operands
        :type in_operands: list of X86Operand

        :param out_operands: a list of the instruction's destination operands
        :type out_operands: list of X86Operand
        """
        # Retrieve translation function.
        translator_name = "_translate_" + instruction.mnemonic
        translator_fn = getattr(self, translator_name, self._not_implemented)

        # Translate instruction.
        instrs = translator_fn(instruction, in_operands, out_operands)

        return instrs

    @property
    def translation_mode(self):
        return self._translation_mode

    @translation_mode.setter
    def translation_mode(self, value):
        self._translation_mode = value

# ============================================================================ #

    def _not_implemented(self, instruction, in_operands, out_operands):
        raise NotImplementedError("Instruction Not Implemented")

# Translators
# ============================================================================ #
# ============================================================================ #

# "Flags"
# ============================================================================ #
    def _translate_af(self, oprnd1, oprnd2, result, tmpl, builder):
        # TODO: Implement
        return tmpl

    def _translate_pf(self, oprnd1, oprnd2, result, tmpl, builder):
        # TODO: Implement
        return tmpl

    def _translate_sf(self, oprnd1, oprnd2, result, tmpl, builder):
        # Create temporal variables.
        tmp0 = tmpl.temporal(result.size)

        mask0 = tmpl.immediate(2**result.size-1, result.size)
        shift0 = tmpl.immediate(-(result.size-1), result.size)

        sf = ReilRegisterOperand("sf", 1)

        tmpl.add(builder.gen_and(result, mask0,  tmp0))  # filter sign bit
        tmpl.add(builder.gen_bsh(tmp0, shift0,  sf))     # extract sign bit

        return tmpl

    def _translate_of(self, oprnd1, oprnd2, result, tmpl, builder):
        of = ReilRegisterOperand("of", 1)

        imm0 = tmpl.immediate(2**(oprnd1.size-1), oprnd1.size)
        imm1 = tmpl.immediate(1, oprnd1.size)
        imm3 = tmpl.immediate(-(oprnd1.size-1), oprnd1.size)
        imm4 = tmpl.immediate(2**(oprnd1.size-1), result.size)

        tmp0 = tmpl.temporal(oprnd1.size)
        tmp1 = tmpl.temporal(oprnd2.size)
        tmp2 = tmpl.temporal(oprnd1.size)
        tmp3 = tmpl.temporal(oprnd1.size)
        tmp4 = tmpl.temporal(oprnd1.size)
        tmp5 = tmpl.temporal(oprnd1.size)
        tmp6 = tmpl.temporal(oprnd1.size)

        tmpl.add(builder.gen_and(oprnd1, imm0, tmp0))   # filter sign bit oprnd 1
        tmpl.add(builder.gen_and(oprnd2, imm0, tmp1))   # filter sign bit oprnd 2
        tmpl.add(builder.gen_and(result, imm4, tmp2))   # filter sign bit result
        tmpl.add(builder.gen_xor(tmp0, tmp1, tmp3))     # sign bit oprnd1 ^ sign bit oprnd2
        tmpl.add(builder.gen_xor(tmp3, imm1, tmp4))     # sign bit oprnd1 ^ sign bit oprnd2 ^ 1
        tmpl.add(builder.gen_xor(tmp0, tmp2, tmp5))     # sign bit oprnd1 ^ sign bit result
        tmpl.add(builder.gen_and(tmp4, tmp5, tmp6))     # (sign bit oprnd1 ^ sign bit oprnd2 ^ 1) & (sign bit oprnd1 ^ sign bit result)
        tmpl.add(builder.gen_bsh(tmp6, imm3, of))

        return tmpl

    def _translate_cf(self, oprnd1, oprnd2, result, tmpl, builder):
        cf = ReilRegisterOperand("cf", 1)

        imm0 = tmpl.immediate(2**oprnd1.size, result.size)
        imm1 = tmpl.immediate(-oprnd1.size, result.size)
        imm2 = tmpl.immediate(-oprnd1.size, oprnd1.size)

        tmp0 = tmpl.temporal(oprnd1.size)

        tmpl.add(builder.gen_and(result, imm0, tmp0))   # filter carry bit
        tmpl.add(builder.gen_bsh(tmp0, imm2, cf))

        return tmpl

    def _translate_zf(self, oprnd1, oprnd2, result, tmpl, builder):
        zf = ReilRegisterOperand("zf", 1)

        imm0 = tmpl.immediate((2**oprnd1.size)-1, result.size)

        tmp0 = tmpl.temporal(oprnd1.size)

        tmpl.add(builder.gen_and(result, imm0, tmp0))  # filter low part of result
        tmpl.add(builder.gen_bisz(tmp0, zf))

        return tmpl

    def _undefine_flag(self, flag, tmpl, builder):
        imm = tmpl.immediate(0, flag.size)

        tmpl.add(builder.gen_str(imm, flag))

        return tmpl

    def _clear_flag(self, flag, tmpl, builder):
        imm = tmpl.immediate(0, flag.size)

        tmpl.add(builder.gen_str(imm, flag))

        return tmpl


# "Data Transfer Instructions"
# ============================================================================ #
    def _translate_mov(self, instruction, in_operands=None, out_operands=None):
        # Flags Affected
        # None.

        tb = TranslationBuilder(self.ir_name_generator)

        builder = ReilInstructionBuilder()

        oprnd1 = in_operands[0]
        oprnd2 = out_operands[0]

        assert oprnd1.size and oprnd2.size
        assert oprnd1.size == oprnd2.size

        tb.add(builder.gen_str(oprnd1, oprnd2))

        return tb.instanciate(instruction.address)

    def _translate_movzx(self, instruction, in_operands=None, out_operands=None):
        # Flags Affected
        # None.

        tb = TranslationBuilder(self.ir_name_generator)

        builder = ReilInstructionBuilder()

        oprnd1 = in_operands[0]
        oprnd2 = out_operands[0]

        assert oprnd1.size and oprnd2.size
        assert oprnd2.size > oprnd1.size

        tb.add(builder.gen_str(oprnd1, oprnd2))

        return tb.instanciate(instruction.address)

    def _translate_xchg(self, instruction, in_operands=None, out_operands=None):
        # Flags Affected
        # None.

        tb = TranslationBuilder(self.ir_name_generator)

        builder = ReilInstructionBuilder()

        oprnd1 = in_operands[0]
        oprnd2 = in_operands[1]
        oprnd3 = out_operands[0]
        oprnd4 = out_operands[1]

        assert oprnd1.size and oprnd2.size
        assert oprnd1.size == oprnd2.size and oprnd3.size == oprnd4.size

        tmp0 = tb.temporal(oprnd1.size)
        tmp1 = tb.temporal(oprnd2.size)

        tb.add(builder.gen_str(oprnd1, tmp0))
        tb.add(builder.gen_str(oprnd2, tmp1))
        tb.add(builder.gen_str(tmp1, oprnd3))
        tb.add(builder.gen_str(tmp0, oprnd4))

        return tb.instanciate(instruction.address)

    def _translate_push(self, instruction, in_operands=None, out_operands=None):
        # Flags Affected
        # None.

        tb = TranslationBuilder(self.ir_name_generator)

        builder = ReilInstructionBuilder()

        oprnd1 = in_operands[0]

        assert oprnd1.size
        assert oprnd1.size in [32, 64]

        if self.architecture_mode == ARCH_X86_MODE_32:
            sp = ReilRegisterOperand("esp", 32)
            imm = ReilImmediateOperand(4, 32)
        elif self.architecture_mode == ARCH_X86_MODE_64:
            sp = ReilRegisterOperand("rsp", 64)
            imm = ReilImmediateOperand(8, 64)

        tmp0 = tb.temporal(sp.size)

        tb.add(builder.gen_sub(sp, imm, tmp0))
        tb.add(builder.gen_str(tmp0, sp))
        tb.add(builder.gen_stm(oprnd1, sp))

        return tb.instanciate(instruction.address)

    def _translate_pop(self, instruction, in_operands=None, out_operands=None):
        # Flags Affected
        # None.

        tb = TranslationBuilder(self.ir_name_generator)

        builder = ReilInstructionBuilder()

        oprnd1 = out_operands[0]

        assert oprnd1.size
        assert oprnd1.size in [32, 64]

        if self.architecture_mode == ARCH_X86_MODE_32:
            sp = ReilRegisterOperand("esp", 32)
            imm = ReilImmediateOperand(4, 32)
        elif self.architecture_mode == ARCH_X86_MODE_64:
            sp = ReilRegisterOperand("rsp", 64)
            imm = ReilImmediateOperand(8, 64)

        tmp0 = tb.temporal(sp.size)

        tb.add(builder.gen_ldm(sp, oprnd1))
        tb.add(builder.gen_add(sp, imm, tmp0))
        tb.add(builder.gen_str(tmp0, sp))

        return tb.instanciate(instruction.address)

# "Binary Arithmetic Instructions"
# ============================================================================ #
    def _translate_add(self, instruction, in_operands=None, out_operands=None):
        # Flags Affected
        # The OF, SF, ZF, AF, CF, and PF flags are set according to the
        # result.

        tb = TranslationBuilder(self.ir_name_generator)

        builder = ReilInstructionBuilder()

        oprnd1 = in_operands[0]
        oprnd2 = in_operands[1]
        oprnd3 = out_operands[0]

        assert oprnd1.size and oprnd2.size
        assert oprnd1.size == oprnd2.size

        tmp0 = tb.temporal(oprnd1.size*2)

        tb.add(builder.gen_add(oprnd1, oprnd2, tmp0))

        if self._translation_mode == FULL_TRANSLATION:
            # Flags : OF, SF, ZF, AF, CF, PF
            tb = self._translate_of(oprnd1, oprnd2, oprnd1, tb, builder)
            tb = self._translate_sf(oprnd1, oprnd2, oprnd1, tb, builder)
            tb = self._translate_zf(oprnd1, oprnd2, oprnd1, tb, builder)
            tb = self._translate_af(oprnd1, oprnd2, oprnd1, tb, builder)
            tb = self._translate_cf(oprnd1, oprnd2, oprnd1, tb, builder)
            tb = self._translate_pf(oprnd1, oprnd2, oprnd1, tb, builder)

        tb.add(builder.gen_str(tmp0, oprnd3))

        return tb.instanciate(instruction.address)

    def _translate_adc(self, instruction, in_operands=None, out_operands=None):
        # Flags Affected
        # The OF, SF, ZF, AF, CF, and PF flags are set according to the result.

        tb = TranslationBuilder(self.ir_name_generator)

        builder = ReilInstructionBuilder()

        oprnd1 = in_operands[0]
        oprnd2 = in_operands[1]
        oprnd3 = out_operands[0]

        assert oprnd1.size and oprnd2.size
        assert oprnd1.size == oprnd2.size

        cf = ReilRegisterOperand("cf", 1)

        tmp0 = tb.temporal(oprnd1.size*2)
        tmp1 = tb.temporal(oprnd1.size*2)
        tmp2 = tb.temporal(oprnd1.size*2)

        tb.add(builder.gen_add(oprnd1, oprnd2, tmp0))
        tb.add(builder.gen_str(cf, tmp1))
        tb.add(builder.gen_add(tmp0, tmp1, tmp2))

        if self._translation_mode == FULL_TRANSLATION:
            # Flags : OF, SF, ZF, AF, CF, PF
            tb = self._translate_of(oprnd1, oprnd2, tmp2, tb, builder)
            tb = self._translate_sf(oprnd1, oprnd2, tmp2, tb, builder)
            tb = self._translate_zf(oprnd1, oprnd2, tmp2, tb, builder)
            tb = self._translate_af(oprnd1, oprnd2, tmp2, tb, builder)
            tb = self._translate_cf(oprnd1, oprnd2, tmp2, tb, builder)
            tb = self._translate_pf(oprnd1, oprnd2, tmp2, tb, builder)

        tb.add(builder.gen_str(tmp2, oprnd3))

        return tb.instanciate(instruction.address)

    def _translate_sub(self, instruction, in_operands=None, out_operands=None):
        # Flags Affected
        # The OF, SF, ZF, AF, PF, and CF flags are set according to the
        # result.

        tb = TranslationBuilder(self.ir_name_generator)

        builder = ReilInstructionBuilder()

        oprnd1 = in_operands[0]
        oprnd2 = in_operands[1]
        oprnd3 = out_operands[0]

        assert oprnd1.size and oprnd2.size
        assert oprnd1.size == oprnd2.size

        tmp0 = tb.temporal(oprnd1.size*2)

        tb.add(builder.gen_sub(oprnd1, oprnd2, tmp0))

        if self._translation_mode == FULL_TRANSLATION:
            # Flags : OF, SF, ZF, AF, PF, CF
            tb = self._translate_of(oprnd1, oprnd2, oprnd1, tb, builder)
            tb = self._translate_sf(oprnd1, oprnd2, oprnd1, tb, builder)
            tb = self._translate_zf(oprnd1, oprnd2, oprnd1, tb, builder)
            tb = self._translate_af(oprnd1, oprnd2, oprnd1, tb, builder)
            tb = self._translate_pf(oprnd1, oprnd2, oprnd1, tb, builder)
            tb = self._translate_cf(oprnd1, oprnd2, oprnd1, tb, builder)

        tb.add(builder.gen_str(tmp0, oprnd3))

        return tb.instanciate(instruction.address)

    def _translate_sbb(self, instruction, in_operands=None, out_operands=None):
        # Flags Affected
        # The OF, SF, ZF, AF, PF, and CF flags are set according to the
        # result.

        tb = TranslationBuilder(self.ir_name_generator)

        builder = ReilInstructionBuilder()

        oprnd1 = in_operands[0]
        oprnd2 = in_operands[1]
        oprnd3 = out_operands[0]

        assert oprnd1.size and oprnd2.size
        assert oprnd1.size == oprnd2.size

        cf = ReilRegisterOperand("cf", 1)

        tmp0 = tb.temporal(oprnd1.size*2)
        tmp1 = tb.temporal(oprnd1.size*2)
        tmp2 = tb.temporal(oprnd1.size*2)

        tb.add(builder.gen_sub(oprnd1, oprnd2, tmp0))
        tb.add(builder.gen_str(cf, tmp1))
        tb.add(builder.gen_sub(oprnd1, oprnd2, tmp2))

        if self._translation_mode == FULL_TRANSLATION:
            # Flags : OF, SF, ZF, AF, PF, CF
            tb = self._translate_of(oprnd1, oprnd2, tmp2, tb, builder)
            tb = self._translate_sf(oprnd1, oprnd2, tmp2, tb, builder)
            tb = self._translate_zf(oprnd1, oprnd2, tmp2, tb, builder)
            tb = self._translate_af(oprnd1, oprnd2, tmp2, tb, builder)
            tb = self._translate_pf(oprnd1, oprnd2, tmp2, tb, builder)
            tb = self._translate_cf(oprnd1, oprnd2, tmp2, tb, builder)

        tb.add(builder.gen_str(tmp2, oprnd3))

        return tb.instanciate(instruction.address)

    def _translate_mul(self, instruction, in_operands=None, out_operands=None):
        # Flags Affected
        # The OF and CF flags are set to 0 if the upper half of the
        # result is 0; otherwise, they are set to 1. The SF, ZF, AF, and
        # PF flags are undefined.

        tb = TranslationBuilder(self.ir_name_generator)

        builder = ReilInstructionBuilder()

        oprnd1 = in_operands[0]
        oprnd2 = in_operands[1]
        oprnd3 = out_operands[0]
        oprnd4 = out_operands[1]

        assert oprnd1.size and oprnd2.size
        assert oprnd1.size == oprnd2.size

        oprnd_size = oprnd1.size
        result_size = 2*oprnd_size

        oprnd_size_str  = size_str[oprnd_size]
        result_size_str = size_str[result_size]

        imm0 = tb.immediate(-oprnd1.size, oprnd1.size*2)

        tmp0 = tb.temporal(oprnd1.size*2)

        tb.add(builder.gen_mul(oprnd1, oprnd2, tmp0))
        tb.add(builder.gen_bsh(tmp0, imm0, oprnd3))
        tb.add(builder.gen_str(tmp0, oprnd4))

        if self._translation_mode == FULL_TRANSLATION:
            cf = ReilRegisterOperand("cf", 1)
            zf = ReilRegisterOperand("zf", 1)
            af = ReilRegisterOperand("af", 1)
            pf = ReilRegisterOperand("pf", 1)
            of = ReilRegisterOperand("of", 1)
            sf = ReilRegisterOperand("sf", 1)

            # Flags : OF, CF
            fimm0 = tb.immediate(1, 1)

            ftmp0 = tb.temporal(oprnd1.size*2)
            ftmp1 = tb.temporal(1)

            tb.add(builder.gen_bsh(tmp0, imm0, ftmp0))
            tb.add(builder.gen_bisz(ftmp0, ftmp1))
            tb.add(builder.gen_xor(ftmp1, fimm0, of))
            tb.add(builder.gen_xor(ftmp1, fimm0, cf))

            # Flags : SF, ZF, AF, PF
            tb = self._undefine_flag(sf, tb, builder)
            tb = self._undefine_flag(zf, tb, builder)
            tb = self._undefine_flag(af, tb, builder)
            tb = self._undefine_flag(pf, tb, builder)

        return tb.instanciate(instruction.address)

    def _translate_imul(self, instruction, in_operands=None, out_operands=None):
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

        tb = TranslationBuilder(self.ir_name_generator)

        builder = ReilInstructionBuilder()

        oprnd1 = in_operands[0]
        oprnd2 = in_operands[1]

        oprnd3 = out_operands[0]


        result = out_operands[0]

        assert oprnd1.size and oprnd2.size and result.size
        assert oprnd1.size == oprnd2.size
        assert oprnd1.size == result.size

        imm0 = tb.immediate(-oprnd1.size, 2*oprnd1.size)

        tmp0 = tb.temporal(2*oprnd1.size)
        tmp1 = tb.temporal(2*oprnd1.size)

        # Extend second source operand to match the size of the first one.
        tb.add(builder.gen_str(oprnd1, tmp0))

        # Do multiplication.
        tb.add(builder.gen_mul(oprnd1, oprnd2, tmp1))

        # Save result.
        if len(out_operands) == 1:
            tb.add(builder.gen_str(tmp1, oprnd3))

        elif len(out_operands) == 2:
            oprnd4 = out_operands[1]

            tb.add(builder.gen_bsh(tmp1, imm0, oprnd3)) # save high part
            tb.add(builder.gen_str(tmp1, oprnd4))       # save low part
        else:
            raise Exeption()

        if self._translation_mode == FULL_TRANSLATION:
            zf = ReilRegisterOperand("zf", 1)
            af = ReilRegisterOperand("af", 1)
            pf = ReilRegisterOperand("pf", 1)
            sf = ReilRegisterOperand("sf", 1)

            # Flags : OF, CF
            # TODO: Implement.
            tb = self._undefine_flag(sf, tb, builder)
            tb = self._undefine_flag(zf, tb, builder)
            tb = self._undefine_flag(af, tb, builder)
            tb = self._undefine_flag(pf, tb, builder)

        return tb.instanciate(instruction.address)

    def _translate_div(self, instruction, in_operands=None, out_operands=None):
        # Flags Affected
        # The CF, OF, SF, ZF, AF, and PF flags are undefined.

        tb = TranslationBuilder(self.ir_name_generator)

        builder = ReilInstructionBuilder()

        oprnd1 = in_operands[0]
        oprnd2 = in_operands[1]
        oprnd3 = in_operands[2]

        oprnd4 = out_operands[0]
        oprnd5 = out_operands[1]

        assert oprnd1.size and oprnd2.size
        assert oprnd1.size == oprnd2.size == oprnd3.size

        oprnd1_size = oprnd1.size
        oprnd2_size = oprnd2.size
        oprnd3_size = oprnd3.size

        oprnd_size = oprnd1.size * 2
        result_size = oprnd1_size

        oprnd1_size_str = size_str[oprnd1_size]
        oprnd2_size_str = size_str[oprnd2_size]
        oprnd3_size_str = size_str[oprnd2_size]

        oprnd_size_str  = size_str[oprnd_size]
        result_size_str = size_str[result_size]

        imm0 = tb.immediate(oprnd1.size, oprnd1.size*2)

        tmp0 = tb.temporal(oprnd1.size*2)
        tmp1 = tb.temporal(oprnd1.size*2)
        tmp2 = tb.temporal(oprnd1.size*2)

        tmp3 = tb.temporal(oprnd1.size*2)
        tmp4 = tb.temporal(oprnd1.size*2)
        tmp5 = tb.temporal(oprnd1.size*2)
        tmp6 = tb.temporal(oprnd1.size*2)

        # Extend operands to match their size.
        tb.add(builder.gen_str(oprnd1, tmp0))
        tb.add(builder.gen_str(oprnd2, tmp1))
        tb.add(builder.gen_str(oprnd3, tmp2))

        # Put dividend together.
        tb.add(builder.gen_bsh(tmp0, imm0, tmp3))
        tb.add(builder.gen_or(tmp3, tmp1, tmp4))

        # Do division
        tb.add(builder.gen_div(tmp4, tmp2, tmp5))
        tb.add(builder.gen_mod(tmp4, tmp2, tmp6))
        tb.add(builder.gen_str(tmp5, oprnd5))
        tb.add(builder.gen_str(tmp6, oprnd4))

        if self._translation_mode == FULL_TRANSLATION:
            cf = ReilRegisterOperand("cf", 1)
            of = ReilRegisterOperand("of", 1)
            sf = ReilRegisterOperand("sf", 1)
            zf = ReilRegisterOperand("zf", 1)
            af = ReilRegisterOperand("af", 1)
            pf = ReilRegisterOperand("pf", 1)

            # Flags : CF, OF, SF, ZF, AF, PF
            tb = self._undefine_flag(cf, tb, builder)
            tb = self._undefine_flag(of, tb, builder)
            tb = self._undefine_flag(sf, tb, builder)
            tb = self._undefine_flag(zf, tb, builder)
            tb = self._undefine_flag(af, tb, builder)
            tb = self._undefine_flag(pf, tb, builder)

        return tb.instanciate(instruction.address)

    def _translate_inc(self, instruction, in_operands=None, out_operands=None):
        # Flags Affected
        # The CF flag is not affected. The OF, SF, ZF, AF, and PF flags
        # are set according to the result.

        tb = TranslationBuilder(self.ir_name_generator)

        builder = ReilInstructionBuilder()

        oprnd1 = in_operands[0]

        oprnd2 = out_operands[0]

        assert oprnd1.size

        oprnd_size = oprnd1.size
        result_size = 2*oprnd_size

        oprnd_size_str  = size_str[oprnd_size]
        result_size_str = size_str[result_size]

        imm0 = tb.immediate(1, oprnd1.size)

        tmp0 = tb.temporal(oprnd1.size*2)

        tb.add(builder.gen_add(oprnd1, imm0, tmp0))

        if self._translation_mode == FULL_TRANSLATION:
            cf = ReilRegisterOperand("cf", 1)
            of = ReilRegisterOperand("of", 1)
            sf = ReilRegisterOperand("sf", 1)
            zf = ReilRegisterOperand("zf", 1)
            af = ReilRegisterOperand("af", 1)
            pf = ReilRegisterOperand("pf", 1)

            # Flags : OF, SF, ZF, AF, PF
            tb = self._translate_of(oprnd1, oprnd1, tmp0, tb, builder)
            tb = self._translate_sf(oprnd1, oprnd1, tmp0, tb, builder)
            tb = self._translate_zf(oprnd1, oprnd1, tmp0, tb, builder)
            tb = self._translate_af(oprnd1, oprnd1, tmp0, tb, builder)
            tb = self._translate_pf(oprnd1, oprnd1, tmp0, tb, builder)

        tb.add(builder.gen_str(tmp0, oprnd2))

        return tb.instanciate(instruction.address)

    def _translate_dec(self, instruction, in_operands=None, out_operands=None):
        # Flags Affected
        # The CF flag is not affected. The OF, SF, ZF, AF, and PF flags
        # are set according to the result.

        tb = TranslationBuilder(self.ir_name_generator)

        builder = ReilInstructionBuilder()

        oprnd1 = in_operands[0]

        oprnd2 = out_operands[0]

        assert oprnd1.size

        oprnd_size = oprnd1.size
        result_size = 2*oprnd_size

        oprnd_size_str  = size_str[oprnd_size]
        result_size_str = size_str[result_size]

        imm0 = tb.immediate(1, oprnd1.size)

        tmp0 = tb.temporal(oprnd1.size*2)

        # trans  = ["sub [{0} $0, {0} 1, {1} %0]".format(oprnd_size_str, result_size_str)]
        tb.add(builder.gen_sub(oprnd1, imm0, tmp0)) # [{0} $0, {0} 1, {1} %0]".format(oprnd_size_str, result_size_str)]

        if self._translation_mode == FULL_TRANSLATION:
            # Flags : OF, SF, ZF, AF, PF
            # trans += self._translate_of("$0", "$0", oprnd_size, "%0", result_size)
            # trans += self._translate_sf("$0", "$0", oprnd_size, "%0", result_size)
            # trans += self._translate_zf("$0", "$0", oprnd_size, "%0", result_size)
            # trans += self._translate_af("$0", "$0", oprnd_size, "%0", result_size)
            # trans += self._translate_pf("$0", "$0", oprnd_size, "%0", result_size)

            tb = self._translate_of(oprnd1, oprnd1, tmp0, tb, builder) # "$0", "$0", oprnd_size, "%0", result_size)
            tb = self._translate_sf(oprnd1, oprnd1, tmp0, tb, builder) # "$0", "$0", oprnd_size, "%0", result_size)
            tb = self._translate_zf(oprnd1, oprnd1, tmp0, tb, builder) # "$0", "$0", oprnd_size, "%0", result_size)
            tb = self._translate_af(oprnd1, oprnd1, tmp0, tb, builder) # "$0", "$0", oprnd_size, "%0", result_size)
            tb = self._translate_pf(oprnd1, oprnd1, tmp0, tb, builder) # "$0", "$0", oprnd_size, "%0", result_size)

        # trans += ["str [%0, EMPTY, #0]"]
        tb.add(builder.gen_str(tmp0, oprnd2)) # [%0, EMPTY, #0]"]

        return tb.instanciate(instruction.address)

    def _translate_neg(self, instruction, in_operands=None, out_operands=None):
        # Flags Affected
        # The CF flag set to 0 if the source operand is 0; otherwise it
        # is set to 1. The OF, SF, ZF, AF, and PF flags are set
        # according to the result.

        tb = TranslationBuilder(self.ir_name_generator)

        builder = ReilInstructionBuilder()

        oprnd1 = in_operands[0]

        oprnd2 = out_operands[0]

        assert oprnd1.size

        oprnd_size = oprnd1.size
        result_size = oprnd_size

        oprnd_size_str  = size_str[oprnd_size]
        result_size_str = size_str[result_size]

        imm0 = tb.immediate((2**oprnd1.size)-1, oprnd1.size)
        imm1 = tb.immediate(1, oprnd1.size)
        imm2 = tb.immediate(1, 1)

        tmp0 = tb.temporal(oprnd1.size)
        tmp1 = tb.temporal(1)

        tb.add(builder.gen_xor(oprnd1, imm0, tmp0))
        tb.add(builder.gen_add(tmp0, imm1, oprnd2))

        # Flags : CF
        cf = ReilRegisterOperand("cf", 1)

        tb.add(builder.gen_bisz(oprnd1, tmp1))
        tb.add(builder.gen_xor(tmp1, imm2, cf))

        if self._translation_mode == FULL_TRANSLATION:
            # Flags : OF, SF, ZF, AF, PF
            tb = self._translate_of(oprnd1, oprnd1, oprnd2, tb, builder)
            tb = self._translate_sf(oprnd1, oprnd1, oprnd2, tb, builder)
            tb = self._translate_zf(oprnd1, oprnd1, oprnd2, tb, builder)
            tb = self._translate_af(oprnd1, oprnd1, oprnd2, tb, builder)
            tb = self._translate_pf(oprnd1, oprnd1, oprnd2, tb, builder)

        return tb.instanciate(instruction.address)

    def _translate_cmp(self, instruction, in_operands=None, out_operands=None):
        # Flags Affected
        # The CF, OF, SF, ZF, AF, and PF flags are set according to the
        # result.

        tb = TranslationBuilder(self.ir_name_generator)

        builder = ReilInstructionBuilder()

        oprnd1 = in_operands[0]
        oprnd2 = in_operands[1]

        assert oprnd1.size and oprnd2.size
        assert oprnd1.size == oprnd2.size

        oprnd_size = oprnd1.size
        result_size = 2*oprnd_size

        oprnd_size_str  = size_str[oprnd_size]
        result_size_str = size_str[result_size]

        tmp0 = tb.temporal(oprnd1.size*2)

        tb.add(builder.gen_sub(oprnd1, oprnd2, tmp0)) # [{0} $0, {0} $1, {1} %0]".format(oprnd_size_str, result_size_str)]

        # Flags : CF, OF, SF, ZF, AF, PF
        tb = self._translate_cf(oprnd1, oprnd2, tmp0, tb, builder)
        tb = self._translate_of(oprnd1, oprnd2, tmp0, tb, builder)
        tb = self._translate_sf(oprnd1, oprnd2, tmp0, tb, builder)
        tb = self._translate_zf(oprnd1, oprnd2, tmp0, tb, builder)
        tb = self._translate_af(oprnd1, oprnd2, tmp0, tb, builder)
        tb = self._translate_pf(oprnd1, oprnd2, tmp0, tb, builder)

        return tb.instanciate(instruction.address)

# "Decimal Arithmetic Instructions"
# ============================================================================ #

# "Logical Instructions"
# ============================================================================ #
    def _translate_and(self, instruction, in_operands=None, out_operands=None):
        # Flags Affected
        # The OF and CF flags are cleared; the SF, ZF, and PF flags are
        # set according to the result. The state of the AF flag is
        # undefined.

        tb = TranslationBuilder(self.ir_name_generator)

        builder = ReilInstructionBuilder()

        oprnd1 = in_operands[0]
        oprnd2 = in_operands[1]

        oprnd3 = out_operands[0]

        assert oprnd1.size and oprnd2.size
        assert oprnd1.size == oprnd2.size

        oprnd_size = oprnd1.size
        result_size = oprnd_size

        oprnd_size_str  = size_str[oprnd_size]
        result_size_str = size_str[result_size]

        tb.add(builder.gen_and(oprnd1, oprnd2, oprnd3))

        if self._translation_mode == FULL_TRANSLATION:
            # Flags : OF, CF
            of = ReilRegisterOperand("of", 1)
            cf = ReilRegisterOperand("cf", 1)

            tb = self._clear_flag(of, tb, builder)
            tb = self._clear_flag(cf, tb, builder)

            # Flags : SF, ZF, PF
            tb = self._translate_sf(oprnd1, oprnd2, oprnd3, tb, builder)
            tb = self._translate_zf(oprnd1, oprnd2, oprnd3, tb, builder)
            tb = self._translate_pf(oprnd1, oprnd2, oprnd3, tb, builder)

            # Flags : AF
            af = ReilRegisterOperand("af", 1)

            tb = self._undefine_flag(af, tb, builder)

        return tb.instanciate(instruction.address)

    def _translate_or(self, instruction, in_operands=None, out_operands=None):
        # Flags Affected
        # The OF and CF flags are cleared; the SF, ZF, and PF flags are
        # set according to the result. The state of the AF flag is
        # undefined.

        tb = TranslationBuilder(self.ir_name_generator)

        builder = ReilInstructionBuilder()

        oprnd1 = in_operands[0]
        oprnd2 = in_operands[1]

        oprnd3 = out_operands[0]

        assert oprnd1.size and oprnd2.size
        assert oprnd1.size == oprnd2.size

        # print "_translate_or", oprnd1, oprnd1.size, id(oprnd1)
        # print "_translate_or", oprnd2, oprnd2.immediate, oprnd2.size, id(oprnd2)

        oprnd_size = oprnd1.size
        result_size = oprnd_size

        oprnd_size_str  = size_str[oprnd_size]
        result_size_str = size_str[result_size]

        # trans  = ["or [{0} $0, {0} $1, {1} #0]".format(oprnd_size_str, result_size_str)]
        tb.add(builder.gen_or(oprnd1, oprnd2, oprnd3)) # [{0} $0, {0} $1, {1} #0]".format(oprnd_size_str, result_size_str)]

        if self._translation_mode == FULL_TRANSLATION:
            # Flags : OF, CF
            of = ReilRegisterOperand("of", 1)
            cf = ReilRegisterOperand("cf", 1)

            tb = self._clear_flag(of, tb, builder)
            tb = self._clear_flag(cf, tb, builder)

            # Flags : SF, ZF, PF
            tb = self._translate_sf(oprnd1, oprnd2, oprnd3, tb, builder)
            tb = self._translate_zf(oprnd1, oprnd2, oprnd3, tb, builder)
            tb = self._translate_pf(oprnd1, oprnd2, oprnd3, tb, builder)

            # Flags : AF
            af = ReilRegisterOperand("af", 1)

            tb = self._undefine_flag(af, tb, builder)

        return tb.instanciate(instruction.address)

    def _translate_xor(self, instruction, in_operands=None, out_operands=None):
        # Flags Affected
        # The OF and CF flags are cleared; the SF, ZF, and PF flags are set
        # according to the result. The state of the AF flag is
        # undefined.

        tb = TranslationBuilder(self.ir_name_generator)

        builder = ReilInstructionBuilder()

        oprnd1 = in_operands[0]
        oprnd2 = in_operands[1]

        oprnd3 = out_operands[0]

        assert oprnd1.size and oprnd2.size
        assert oprnd1.size == oprnd2.size

        oprnd_size = oprnd1.size
        result_size = oprnd_size

        oprnd_size_str  = size_str[oprnd_size]
        result_size_str = size_str[result_size]

        # trans  = ["xor [{0} $0, {0} $1, {1} #0]".format(oprnd_size_str, result_size_str)]
        tb.add(builder.gen_xor(oprnd1, oprnd2, oprnd3)) # [{0} $0, {0} $1, {1} #0]".format(oprnd_size_str, result_size_str)]

        if self._translation_mode == FULL_TRANSLATION:
            # Flags : OF, CF
            of = ReilRegisterOperand("of", 1)
            cf = ReilRegisterOperand("cf", 1)

            tb = self._clear_flag(of, tb, builder)
            tb = self._clear_flag(cf, tb, builder)

            # Flags : SF, ZF, PF
            tb = self._translate_sf(oprnd1, oprnd2, oprnd3, tb, builder) # "$0", "$1", oprnd_size, "#0", result_size)
            tb = self._translate_zf(oprnd1, oprnd2, oprnd3, tb, builder) # "$0", "$1", oprnd_size, "#0", result_size)
            tb = self._translate_pf(oprnd1, oprnd2, oprnd3, tb, builder) # "$0", "$1", oprnd_size, "#0", result_size)

            # Flags : AF
            af = ReilRegisterOperand("af", 1)

            tb = self._undefine_flag(af, tb, builder)

        return tb.instanciate(instruction.address)

    def _translate_not(self, instruction, in_operands=None, out_operands=None):
        # Flags Affected
        # None.

        tb = TranslationBuilder(self.ir_name_generator)

        builder = ReilInstructionBuilder()

        oprnd1 = in_operands[0]

        oprnd2 = out_operands[0]

        assert oprnd1.size

        oprnd_size = oprnd1.size
        result_size = oprnd_size

        oprnd_size_str  = size_str[oprnd_size]
        result_size_str = size_str[result_size]

        imm0 = tb.immediate((2**oprnd1.size)-1, oprnd1.size)

        tb.add(builder.gen_xor(oprnd1, imm0, oprnd2))

        return tb.instanciate(instruction.address)

# "Shift and Rotate Instructions"
# ============================================================================ #
    def _translate_shr(self, instruction, in_operands=None, out_operands=None):
        # Flags Affected
        # The CF flag contains the value of the last bit shifted out
        # of the destination operand; it is undefined for SHL and SHR
        # instructions where the count is greater than or equal to the
        # size (in bits) of the destination operand. The OF flag is
        # affected only for 1-bit shifts (see “Description” above);
        # otherwise, it is undefined. The SF, ZF, and PF flags are set
        # according to the result. If the count is 0, the flags are
        # not affected. For a non-zero count, the AF flag is
        # undefined.

        # TODO: Fix flag translation

        tb = TranslationBuilder(self.ir_name_generator)

        builder = ReilInstructionBuilder()

        oprnd1 = in_operands[0]
        oprnd2 = in_operands[1]

        oprnd3 = out_operands[0]

        assert oprnd1.size and oprnd2.size

        oprnd1_size = oprnd1.size
        oprnd2_size = oprnd2.size

        oprnd_size  = oprnd1.size
        result_size = oprnd_size

        oprnd1_size_str = size_str[oprnd1_size]
        oprnd2_size_str = size_str[oprnd2_size]
        oprnd_size_str  = size_str[oprnd_size]
        result_size_str = size_str[result_size]

        imm0 = tb.immediate(1, oprnd1.size)
        imm1 = tb.immediate((2**oprnd1.size)-1, oprnd1.size)
        imm2 = tb.immediate(-1, oprnd1.size)

        tmp0 = tb.temporal(oprnd1.size)
        tmp1 = tb.temporal(oprnd1.size)
        tmp2 = tb.temporal(oprnd1.size)
        tmp3 = tb.temporal(oprnd1.size)
        tmp4 = tb.temporal(oprnd1.size)
        tmp5 = tb.temporal(oprnd1.size)

        cf = ReilRegisterOperand("cf", 1)

        # Extend 2nd operand to 1st operand size
        tb.add(builder.gen_str(oprnd2, tmp0))

        # Decrement in 1 shift amount
        tb.add(builder.gen_sub(tmp0, imm0, tmp1))

        # Negate
        tb.add(builder.gen_xor(tmp1, imm1, tmp2))
        tb.add(builder.gen_add(tmp2, imm0, tmp3))

        # Shift right
        tb.add(builder.gen_bsh(oprnd1, tmp3, tmp4))

        # Save LSB in CF
        tb.add(builder.gen_and(tmp4, imm0, tmp5))
        tb.add(builder.gen_str(tmp5, cf))

        # Shift one more time
        tb.add(builder.gen_bsh(tmp4, imm2, oprnd3))

        if self._translation_mode == FULL_TRANSLATION:
            # Flags : OF
            # TODO: Implement translation for OF flag.

            # Flags : SF, ZF, PF
            tb = self._translate_sf(oprnd1, oprnd1, oprnd3, tb, builder)
            tb = self._translate_zf(oprnd1, oprnd1, oprnd3, tb, builder)
            tb = self._translate_pf(oprnd1, oprnd1, oprnd3, tb, builder)

            # Flags : AF
            af = ReilRegisterOperand("af", 1)

            tb = self._undefine_flag(af, tb, builder)

        return tb.instanciate(instruction.address)

    def _translate_shl(self, instruction, in_operands=None, out_operands=None):
        # Flags Affected
        # The CF flag contains the value of the last bit shifted out
        # of the destination operand; it is undefined for SHL and SHR
        # instructions where the count is greater than or equal to the
        # size (in bits) of the destination operand. The OF flag is
        # affected only for 1-bit shifts (see “Description” above);
        # otherwise, it is undefined. The SF, ZF, and PF flags are set
        # according to the result. If the count is 0, the flags are
        # not affected. For a non-zero count, the AF flag is
        # undefined.

        # TODO: Fix flag translation.

        tb = TranslationBuilder(self.ir_name_generator)

        builder = ReilInstructionBuilder()

        oprnd1 = in_operands[0]
        oprnd2 = in_operands[1]

        oprnd3 = out_operands[0]

        assert oprnd1.size and oprnd2.size
        # assert oprnd2.size == 8

        oprnd1_size = oprnd1.size
        oprnd2_size = oprnd2.size

        oprnd_size  = oprnd1.size
        result_size = oprnd_size

        oprnd1_size_str = size_str[oprnd1_size]
        oprnd2_size_str = size_str[oprnd2_size]
        oprnd_size_str  = size_str[oprnd_size]
        result_size_str = size_str[result_size]

        imm0 = tb.immediate(1, oprnd1.size)

        tmp0 = tb.temporal(oprnd1.size)
        tmp1 = tb.temporal(oprnd1.size)
        tmp2 = tb.temporal(oprnd1.size)
        tmp3 = tb.temporal(oprnd1.size)

        cf = ReilRegisterOperand("cf", 1)

        # Extend 2nd operand to 1st operand size
        tb.add(builder.gen_str(oprnd2, tmp0))

        # Decrement in 1 shift amount
        tb.add(builder.gen_sub(tmp0, imm0, tmp1))

        # Shift left
        tb.add(builder.gen_bsh(oprnd1, tmp1, tmp2))

        # Save LSB in CF
        tb.add(builder.gen_and(tmp2, imm0, tmp3))
        tb.add(builder.gen_str(tmp3, cf))

        # Shift one more time
        tb.add(builder.gen_bsh(tmp2, imm0, oprnd3))

        if self._translation_mode == FULL_TRANSLATION:
            # Flags : OF
            # TODO: Implement translation for OF flag.

            # Flags : SF, ZF, PF
            tb = self._translate_sf(oprnd1, oprnd1, oprnd3, tb, builder)
            tb = self._translate_zf(oprnd1, oprnd1, oprnd3, tb, builder)
            tb = self._translate_pf(oprnd1, oprnd1, oprnd3, tb, builder)

            # Flags : AF
            af = ReilRegisterOperand("af", 1)

            tb = self._undefine_flag(af, tb, builder)

        return tb.instanciate(instruction.address)

    def _translate_sal(self, instruction, in_operands=None, out_operands=None):
        # Flags Affected
        # The CF flag contains the value of the last bit shifted out
        # of the destination operand; it is undefined for SHL and SHR
        # instructions where the count is greater than or equal to the
        # size (in bits) of the destination operand. The OF flag is
        # affected only for 1-bit shifts (see “Description” above);
        # otherwise, it is undefined. The SF, ZF, and PF flags are set
        # according to the result. If the count is 0, the flags are
        # not affected. For a non-zero count, the AF flag is
        # undefined.

        # TODO: Fix flag translation.

        return self._translate_shl(instruction, in_operands, out_operands)

    def _translate_sar(self, instruction, in_operands=None, out_operands=None):
        # Flags Affected
        # The CF flag contains the value of the last bit shifted out
        # of the destination operand; it is undefined for SHL and SHR
        # instructions where the count is greater than or equal to the
        # size (in bits) of the destination operand. The OF flag is
        # affected only for 1-bit shifts (see “Description” above);
        # otherwise, it is undefined. The SF, ZF, and PF flags are set
        # according to the result. If the count is 0, the flags are
        # not affected. For a non-zero count, the AF flag is
        # undefined.

        # TODO: Fix flag translation.

        tb = TranslationBuilder(self.ir_name_generator)

        builder = ReilInstructionBuilder()

        oprnd1 = in_operands[0]
        oprnd2 = in_operands[1]

        oprnd3 = out_operands[0]

        assert oprnd1.size and oprnd2.size

        oprnd1_size = oprnd1.size
        oprnd2_size = oprnd2.size

        oprnd_size  = oprnd1.size
        result_size = oprnd_size

        oprnd1_size_str = size_str[oprnd1_size]
        oprnd2_size_str = size_str[oprnd2_size]
        oprnd_size_str  = size_str[oprnd_size]
        result_size_str = size_str[result_size]

        imm0 = tb.immediate(2**(oprnd1.size-1), oprnd1.size)
        imm1 = tb.immediate(1, oprnd1.size)
        imm2 = tb.immediate(-1, oprnd1.size)

        tmp0 = tb.temporal(oprnd1.size)
        tmp1 = tb.temporal(oprnd1.size)
        tmp2 = tb.temporal(oprnd1.size)
        tmp6 = tb.temporal(oprnd1.size)
        tmp3 = tb.temporal(oprnd1.size)
        tmp4 = tb.temporal(oprnd1.size)
        tmp5 = tb.temporal(oprnd1.size)

        cf = ReilRegisterOperand("cf", 1)

        # Create labels.
        loop_lbl = tb.label('loop')

        # Initialize counter
        tb.add(builder.gen_str(oprnd2, tmp0))

        # Copy operand to temporal register
        tb.add(builder.gen_str(oprnd1, tmp1))

        # Filter sign bit
        tb.add(builder.gen_and(oprnd1, imm0, tmp2))

        tb.add(loop_lbl)

        # Filter lsb bit
        tb.add(builder.gen_and(oprnd1, imm1, tmp6))
        tb.add(builder.gen_str(tmp6, cf))

        # Shift right
        tb.add(builder.gen_bsh(tmp1, imm2, tmp3))

        # Propagate sign bit
        tb.add(builder.gen_or(tmp3, tmp2, tmp1))

        # Decrement counter
        tb.add(builder.gen_sub(tmp0, imm1, tmp0))

        # Compare counter to zero
        tb.add(builder.gen_bisz(tmp0, tmp4))

        # Invert stop flag
        tb.add(builder.gen_xor(tmp4, imm1, tmp5))

        # Iterate
        tb.add(builder.gen_jcc(tmp5, loop_lbl))

        # Save result
        tb.add(builder.gen_str(tmp1, oprnd3))

        if self._translation_mode == FULL_TRANSLATION:
            # Flags : OF
            # TODO: Implement translation for OF flag.

            # Flags : SF, ZF, PF
            tb = self._translate_sf(oprnd1, oprnd1, oprnd3, tb, builder)
            tb = self._translate_zf(oprnd1, oprnd1, oprnd3, tb, builder)
            tb = self._translate_pf(oprnd1, oprnd1, oprnd3, tb, builder)

            # Flags : AF
            af = ReilRegisterOperand("af", 1)

            tb = self._undefine_flag(af, tb, builder)

        return tb.instanciate(instruction.address)

# "Bit and Byte Instructions"
# ============================================================================ #
    def _translate_test(self, instruction, in_operands=None, out_operands=None):
        # Flags Affected
        # The OF and CF flags are set to 0. The SF, ZF, and PF flags are
        # set according to the result (see the “Operation” section
        # above). The state of the AF flag is undefined.

        tb = TranslationBuilder(self.ir_name_generator)

        builder = ReilInstructionBuilder()

        oprnd1 = in_operands[0]
        oprnd2 = in_operands[0]

        assert oprnd1.size and oprnd2.size
        assert oprnd1.size == oprnd2.size

        oprnd_size = oprnd1.size
        result_size = oprnd_size

        oprnd_size_str  = size_str[oprnd_size]
        result_size_str = size_str[result_size]

        tmp0 = tb.temporal(oprnd1.size)

        tb.add(builder.gen_and(oprnd1, oprnd2, tmp0)) # [{0} $0, {0} $1, {1} %0]".format(oprnd_size_str, result_size_str)]

        # Flags : OF, CF
        of = ReilRegisterOperand("of", 1)
        cf = ReilRegisterOperand("cf", 1)

        tb = self._clear_flag(of, tb, builder)
        tb = self._clear_flag(cf, tb, builder)

        # Flags : SF, ZF, PF
        tb = self._translate_sf(oprnd1, oprnd2, tmp0, tb, builder)
        tb = self._translate_zf(oprnd1, oprnd2, tmp0, tb, builder)
        tb = self._translate_pf(oprnd1, oprnd2, tmp0, tb, builder)

        # Flags : AF
        af = ReilRegisterOperand("af", 1)

        tb = self._undefine_flag(af, tb, builder)

        return tb.instanciate(instruction.address)

# "Control Transfer Instructions"
# ============================================================================ #
    def _translate_jmp(self, instruction, in_operands=None, out_operands=None):
        # Flags Affected
        # All flags are affected if a task switch occurs; no flags are
        # affected if a task switch does not occur.

        tb = TranslationBuilder(self.ir_name_generator)

        builder = ReilInstructionBuilder()

        oprnd1 = in_operands[0]

        assert oprnd1.size
        assert oprnd1.size in [32, 64]

        if isinstance(in_operands[0], ReilImmediateOperand):
            in_operands[0] = ReilImmediateOperand(in_operands[0].immediate << 8, in_operands[0].size + 8)

        oprnd1 = in_operands[0]

        imm0 = tb.immediate(1, 1)

        tb.add(builder.gen_jcc(imm0, oprnd1))

        return tb.instanciate(instruction.address)

    def _translate_ja(self, instruction, in_operands=None, out_operands=None):
        # Jump near if above (CF=0 and ZF=0).

        tb = TranslationBuilder(self.ir_name_generator)

        builder = ReilInstructionBuilder()

        oprnd1 = in_operands[0]

        assert oprnd1.size
        assert oprnd1.size in [32, 64]

        if isinstance(in_operands[0], ReilImmediateOperand):
            in_operands[0] = ReilImmediateOperand(in_operands[0].immediate << 8, in_operands[0].size + 8)

        oprnd1 = in_operands[0]

        cf = ReilRegisterOperand("cf", 1)
        zf = ReilRegisterOperand("zf", 1)

        imm0 = tb.immediate(1, 1)

        tmp0 = tb.temporal(1)
        tmp1 = tb.temporal(1)
        tmp2 = tb.temporal(1)

        tb.add(builder.gen_xor(cf, imm0, tmp0))
        tb.add(builder.gen_xor(zf, imm0, tmp1))
        tb.add(builder.gen_and(tmp0, tmp1, tmp2))
        tb.add(builder.gen_jcc(tmp2, oprnd1))

        return tb.instanciate(instruction.address)

    def _translate_jo(self, instruction, in_operands=None, out_operands=None):
        # Jump near if overflow (OF=1).

        tb = TranslationBuilder(self.ir_name_generator)

        builder = ReilInstructionBuilder()

        oprnd1 = in_operands[0]

        assert oprnd1.size
        assert oprnd1.size in [32, 64]

        if isinstance(in_operands[0], ReilImmediateOperand):
            in_operands[0] = ReilImmediateOperand(in_operands[0].immediate << 8, in_operands[0].size + 8)

        oprnd1 = in_operands[0]

        # trans  = ["jcc [BYTE of, EMPTY, $0]"]

        of = ReilRegisterOperand("of", 1)

        tb.add(builder.gen_jcc(of, oprnd1)) # [BYTE of, EMPTY, $0]"]

        return tb.instanciate(instruction.address)

    def _translate_jbe(self, instruction, in_operands=None, out_operands=None):
        # Jump near if below or equal (CF=1 or ZF=1).

        tb = TranslationBuilder(self.ir_name_generator)

        builder = ReilInstructionBuilder()

        oprnd1 = in_operands[0]

        assert oprnd1.size
        assert oprnd1.size in [32, 64]

        if isinstance(in_operands[0], ReilImmediateOperand):
            in_operands[0] = ReilImmediateOperand(in_operands[0].immediate << 8, in_operands[0].size + 8)

        oprnd1 = in_operands[0]

        # trans  = ["or  [BIT cf, BIT zf, BIT %0]"]
        # trans += ["jcc [BIT %0,  EMPTY,     $0]"]

        tmp0 = tb.temporal(1)

        cf = ReilRegisterOperand("cf", 1)
        zf = ReilRegisterOperand("zf", 1)

        tb.add(builder.gen_or(cf, zf, tmp0))  # [BIT cf, BIT zf, BIT %0]"]
        tb.add(builder.gen_jcc(tmp0, oprnd1)) # [BIT %0,  EMPTY,     $0]"]

        return tb.instanciate(instruction.address)

    def _translate_jl(self, instruction, in_operands=None, out_operands=None):
        # Jump near if less (SF!=OF).

        tb = TranslationBuilder(self.ir_name_generator)

        builder = ReilInstructionBuilder()

        oprnd1 = in_operands[0]

        assert oprnd1.size
        assert oprnd1.size in [32, 64]

        if isinstance(in_operands[0], ReilImmediateOperand):
            in_operands[0] = ReilImmediateOperand(in_operands[0].immediate << 8, in_operands[0].size + 8)

        oprnd1 = in_operands[0]

        # trans  = ["sub  [BIT  sf, BIT  OF, BYTE %0]"]
        # trans += ["bisz [BYTE %0,   EMPTY, BYTE %1]"]
        # trans += ["xor  [BYTE %1,  BYTE 1, BYTE %2]"]
        # trans += ["jcc  [BYTE %2,   EMPTY,      $0]"]

        imm0 = tb.immediate(1, 1)

        tmp0 = tb.temporal(8)
        tmp1 = tb.temporal(1)
        tmp2 = tb.temporal(1)

        sf = ReilRegisterOperand("sf", 1)
        of = ReilRegisterOperand("of", 1)

        tb.add(builder.gen_sub(sf, of, tmp0))       # [BIT  sf, BIT  OF, BYTE %0]"]
        tb.add(builder.gen_bisz(tmp0, tmp1))        # [BYTE %0,   EMPTY, BYTE %1]"]
        tb.add(builder.gen_xor(tmp1, imm0, tmp2))   # [BYTE %1,  BYTE 1, BYTE %2]"]
        tb.add(builder.gen_jcc(tmp2, oprnd1))       # [BYTE %2,   EMPTY,      $0]"]

        return tb.instanciate(instruction.address)

    def _translate_je(self, instruction, in_operands=None, out_operands=None):
        # Jump near if equal (ZF=1).

        tb = TranslationBuilder(self.ir_name_generator)

        builder = ReilInstructionBuilder()

        oprnd1 = in_operands[0]

        assert oprnd1.size
        assert oprnd1.size in [32, 64]

        if isinstance(in_operands[0], ReilImmediateOperand):
            in_operands[0] = ReilImmediateOperand(in_operands[0].immediate << 8, in_operands[0].size + 8)

        oprnd1 = in_operands[0]

        # trans = ["jcc [BIT  zf, EMPTY, $0]"]

        zf = ReilRegisterOperand("zf", 1)

        tb.add(builder.gen_jcc(zf, oprnd1)) # [BIT  zf, EMPTY, $0]"]

        return tb.instanciate(instruction.address)

    def _translate_js(self, instruction, in_operands=None, out_operands=None):
        # Jump near if sign (SF=1).

        tb = TranslationBuilder(self.ir_name_generator)

        builder = ReilInstructionBuilder()

        oprnd1 = in_operands[0]

        assert oprnd1.size
        assert oprnd1.size in [32, 64]

        if isinstance(in_operands[0], ReilImmediateOperand):
            in_operands[0] = ReilImmediateOperand(in_operands[0].immediate << 8, in_operands[0].size + 8)

        oprnd1 = in_operands[0]

        sf = ReilRegisterOperand("sf", 1)

        # trans = ["jcc [BIT  sf, EMPTY, $0]"]
        tb.add(builder.gen_jcc(sf, oprnd1)) # [BIT  sf, EMPTY, $0]"]

        return tb.instanciate(instruction.address)

    def _translate_jg(self, instruction, in_operands=None, out_operands=None):
        # Jump near if greater (ZF=0 and SF=OF).

        tb = TranslationBuilder(self.ir_name_generator)

        builder = ReilInstructionBuilder()

        oprnd1 = in_operands[0]

        assert oprnd1.size
        assert oprnd1.size in [32, 64]

        if isinstance(in_operands[0], ReilImmediateOperand):
            in_operands[0] = ReilImmediateOperand(in_operands[0].immediate << 8, in_operands[0].size + 8)

        oprnd1 = in_operands[0]

        # trans  = ["sub  [BIT  sf, BIT  of, BYTE %0]"]
        # trans += ["bisz [BYTE %0,   EMPTY, BYTE %1]"]
        # trans += ["xor  [BIT  zf,  BIT 1,  BYTE %2]"]
        # trans += ["and  [BYTE %1, BYTE %2, BYTE %3]"]
        # trans += ["jcc  [BYTE %3,   EMPTY,      $0]"]

        imm0 = tb.immediate(1, 1)

        tmp0 = tb.temporal(8)
        tmp1 = tb.temporal(1)
        tmp2 = tb.temporal(1)
        tmp3 = tb.temporal(1)

        sf = ReilRegisterOperand("sf", 1)
        of = ReilRegisterOperand("of", 1)
        zf = ReilRegisterOperand("zf", 1)

        tb.add(builder.gen_sub(sf, of, tmp0))       # [BIT  sf, BIT  of, BYTE %0]"]
        tb.add(builder.gen_bisz(tmp0, tmp1))        # [BYTE %0,   EMPTY, BYTE %1]"]
        tb.add(builder.gen_xor(zf, imm0, tmp2))     # [BIT  zf,  BIT 1,  BYTE %2]"]
        tb.add(builder.gen_and(tmp1, tmp2, tmp3))   # [BYTE %1, BYTE %2, BYTE %3]"]
        tb.add(builder.gen_jcc(tmp3, oprnd1))       # [BYTE %3,   EMPTY,      $0]"]

        return tb.instanciate(instruction.address)

    def _translate_jge(self, instruction, in_operands=None, out_operands=None):
        # Jump near if greater or equal (SF=OF).

        tb = TranslationBuilder(self.ir_name_generator)

        builder = ReilInstructionBuilder()

        oprnd1 = in_operands[0]

        assert oprnd1.size
        assert oprnd1.size in [32, 64]

        if isinstance(in_operands[0], ReilImmediateOperand):
            in_operands[0] = ReilImmediateOperand(in_operands[0].immediate << 8, in_operands[0].size + 8)

        oprnd1 = in_operands[0]

        # trans  = ["sub  [BIT  sf, BIT  of, BYTE %0]"]
        # trans += ["bisz [BYTE %0,   EMPTY, BYTE %1]"]
        # trans += ["jcc  [BYTE %1,   EMPTY,      $0]"]

        tmp0 = tb.temporal(8)
        tmp1 = tb.temporal(1)

        sf = ReilRegisterOperand("sf", 1)
        of = ReilRegisterOperand("of", 1)

        tb.add(builder.gen_sub(sf, of, tmp0))   # [BIT  sf, BIT  of, BYTE %0]"]
        tb.add(builder.gen_bisz(tmp0, tmp1))    # [BYTE %0,   EMPTY, BYTE %1]"]
        tb.add(builder.gen_jcc(tmp1, oprnd1))   # [BYTE %1,   EMPTY,      $0]"]

        return tb.instanciate(instruction.address)

    def _translate_jae(self, instruction, in_operands=None, out_operands=None):
        # Jump near if above or equal (CF=0).

        tb = TranslationBuilder(self.ir_name_generator)

        builder = ReilInstructionBuilder()

        oprnd1 = in_operands[0]

        assert oprnd1.size
        assert oprnd1.size in [32, 64]

        if isinstance(in_operands[0], ReilImmediateOperand):
            in_operands[0] = ReilImmediateOperand(in_operands[0].immediate << 8, in_operands[0].size + 8)

        oprnd1 = in_operands[0]

        # trans  = ["bisz [BIT  cf, EMPTY, BYTE %0]"]
        # trans += ["jcc  [BYTE %0, EMPTY,      $0]"]

        tmp0 = tb.temporal(1)

        cf = ReilRegisterOperand("cf", 1)

        tb.add(builder.gen_bisz(cf, tmp0))      # [BIT  cf, EMPTY, BYTE %0]"]
        tb.add(builder.gen_jcc(tmp0, oprnd1))   # [BYTE %0, EMPTY,      $0]"]

        return tb.instanciate(instruction.address)

    def _translate_jno(self, instruction, in_operands=None, out_operands=None):
        # Jump near if not overflow (OF=0).

        tb = TranslationBuilder(self.ir_name_generator)

        builder = ReilInstructionBuilder()

        oprnd1 = in_operands[0]

        assert oprnd1.size
        assert oprnd1.size in [32, 64]

        if isinstance(in_operands[0], ReilImmediateOperand):
            in_operands[0] = ReilImmediateOperand(in_operands[0].immediate << 8, in_operands[0].size + 8)

        oprnd1 = in_operands[0]

        # trans  = ["bisz [BIT  of, EMPTY, BYTE %0]"]
        # trans += ["jcc  [BYTE %0, EMPTY,      $0]"]

        tmp0 = tb.temporal(1)

        of = ReilRegisterOperand("of", 1)

        tb.add(builder.gen_bisz(of, tmp0))      # [BIT  of, EMPTY, BYTE %0]"]
        tb.add(builder.gen_jcc(tmp0, oprnd1))   # [BYTE %0, EMPTY,      $0]"]

        return tb.instanciate(instruction.address)

    def _translate_jns(self, instruction, in_operands=None, out_operands=None):
        # Jump near if not sign (SF=0).

        tb = TranslationBuilder(self.ir_name_generator)

        builder = ReilInstructionBuilder()

        oprnd1 = in_operands[0]

        assert oprnd1.size
        assert oprnd1.size in [32, 64]

        if isinstance(in_operands[0], ReilImmediateOperand):
            in_operands[0] = ReilImmediateOperand(in_operands[0].immediate << 8, in_operands[0].size + 8)

        oprnd1 = in_operands[0]

        # trans  = ["bisz [BIT  sf, EMPTY, BYTE %0]"]
        # trans += ["jcc  [BYTE %0, EMPTY,      $0]"]

        tmp0 = tb.temporal(1)

        sf = ReilRegisterOperand("sf", 1)

        tb.add(builder.gen_bisz(sf, tmp0))      # [BIT  sf, EMPTY, BYTE %0]"]
        tb.add(builder.gen_jcc(tmp0, oprnd1))   # [BYTE %0, EMPTY,      $0]"]

        return tb.instanciate(instruction.address)

    def _translate_jb(self, instruction, in_operands=None, out_operands=None):
        # Jump near if below (CF=1).

        tb = TranslationBuilder(self.ir_name_generator)

        builder = ReilInstructionBuilder()

        oprnd1 = in_operands[0]

        assert oprnd1.size
        assert oprnd1.size in [32, 64]

        if isinstance(in_operands[0], ReilImmediateOperand):
            in_operands[0] = ReilImmediateOperand(in_operands[0].immediate << 8, in_operands[0].size + 8)

        oprnd1 = in_operands[0]

        cf = ReilRegisterOperand("cf", 1)

        tb.add(builder.gen_jcc(cf, oprnd1)) # [BIT  cf, EMPTY, $0]"]
        # trans  = ["jcc [BIT  cf, EMPTY, $0]"]

        return tb.instanciate(instruction.address)

    def _translate_jle(self, instruction, in_operands=None, out_operands=None):
        # Jump near if less or equal (ZF=1 or SF!=OF).

        tb = TranslationBuilder(self.ir_name_generator)

        builder = ReilInstructionBuilder()

        oprnd1 = in_operands[0]

        assert oprnd1.size
        assert oprnd1.size in [32, 64]

        if isinstance(in_operands[0], ReilImmediateOperand):
            in_operands[0] = ReilImmediateOperand(in_operands[0].immediate << 8, in_operands[0].size + 8)

        oprnd1 = in_operands[0]

        # trans  = ["sub  [BIT  sf, BIT  of, BYTE %0]"]
        # trans += ["bisz [BYTE %0,   EMPTY, BYTE %1]"]
        # trans += ["xor  [BYTE %1,  BYTE 1, BIT  %2]"]
        # trans += ["or   [BIT  %2, BIT  zf, BYTE %3]"]
        # trans += ["jcc  [BYTE %3,   EMPTY,      $0]"]

        imm0 = tb.immediate(1, 1)

        tmp0 = tb.temporal(8)
        tmp1 = tb.temporal(1)
        tmp2 = tb.temporal(1)
        tmp3 = tb.temporal(1)

        sf = ReilRegisterOperand("sf", 1)
        of = ReilRegisterOperand("of", 1)
        zf = ReilRegisterOperand("zf", 1)

        tb.add(builder.gen_sub(sf, of, tmp0))       # [BIT  sf, BIT  of, BYTE %0]"]
        tb.add(builder.gen_bisz(tmp0, tmp1))        # [BYTE %0,   EMPTY, BYTE %1]"]
        tb.add(builder.gen_xor(tmp1, imm0, tmp2))   # [BYTE %1,  BYTE 1, BIT  %2]"]
        tb.add(builder.gen_or(tmp2, zf, tmp3))      # [BIT  %2, BIT  zf, BYTE %3]"]
        tb.add(builder.gen_jcc(tmp3, oprnd1))       # [BYTE %3,   EMPTY,      $0]"]

        return tb.instanciate(instruction.address)

    def _translate_jz(self, instruction, in_operands=None, out_operands=None):
        # Jump near if 0 (ZF=1).

        tb = TranslationBuilder(self.ir_name_generator)

        builder = ReilInstructionBuilder()

        oprnd1 = in_operands[0]

        assert oprnd1.size
        assert oprnd1.size in [32, 64]

        if isinstance(in_operands[0], ReilImmediateOperand):
            in_operands[0] = ReilImmediateOperand(in_operands[0].immediate << 8, in_operands[0].size + 8)

        oprnd1 = in_operands[0]

        zf = ReilRegisterOperand("zf", 1)

        # trans = ["jcc [BIT  zf, EMPTY, $0]"]
        tb.add(builder.gen_jcc(zf, oprnd1)) # [BIT  zf, EMPTY, $0]"]

        return tb.instanciate(instruction.address)

    def _translate_jne(self, instruction, in_operands=None, out_operands=None):
        # Jump near if not equal (ZF=0).

        tb = TranslationBuilder(self.ir_name_generator)

        builder = ReilInstructionBuilder()

        oprnd1 = in_operands[0]

        assert oprnd1.size
        assert oprnd1.size in [32, 64]

        if isinstance(in_operands[0], ReilImmediateOperand):
            in_operands[0] = ReilImmediateOperand(in_operands[0].immediate << 8, in_operands[0].size + 8)

        oprnd1 = in_operands[0]

        # trans  = ["xor [BIT zf, BIT 0x1, BIT %0]"]
        # trans += ["jcc [BIT %0,   EMPTY,     $0]"]

        imm0 = tb.immediate(1, 1)

        tmp0 = tb.temporal(1)

        zf = ReilRegisterOperand("zf", 1)

        tb.add(builder.gen_xor(zf, imm0, tmp0)) # [BIT zf, BIT 0x1, BIT %0]"]
        tb.add(builder.gen_jcc(tmp0, oprnd1))   # [BIT %0,   EMPTY,     $0]"]

        return tb.instanciate(instruction.address)

    def _translate_jnz(self, instruction, in_operands=None, out_operands=None):
        # Jump near if not zero (ZF=0).

        tb = TranslationBuilder(self.ir_name_generator)

        builder = ReilInstructionBuilder()

        oprnd1 = in_operands[0]

        assert oprnd1.size
        assert oprnd1.size in [32, 64]

        if isinstance(in_operands[0], ReilImmediateOperand):
            in_operands[0] = ReilImmediateOperand(in_operands[0].immediate << 8, in_operands[0].size + 8)

        oprnd1 = in_operands[0]

        # trans  = ["xor [BIT zf, BIT 1, BIT %0]"]
        # trans += ["jcc [BIT %0, EMPTY, $0]"]

        imm0 = tb.immediate(1, 1)

        tmp0 = tb.temporal(1)

        zf = ReilRegisterOperand("zf", 1)

        tb.add(builder.gen_xor(zf, imm0, tmp0)) # [BIT zf, BIT 1, BIT %0]"]
        tb.add(builder.gen_jcc(tmp0, oprnd1))   # [BIT %0, EMPTY, $0]"]

        return tb.instanciate(instruction.address)

    def _translate_jnbe(self, instruction, in_operands=None, out_operands=None):
        # Jump near if not below or equal (CF=0 and ZF=0).

        tb = TranslationBuilder(self.ir_name_generator)

        builder = ReilInstructionBuilder()

        oprnd1 = in_operands[0]

        assert oprnd1.size
        assert oprnd1.size in [32, 64]

        if isinstance(in_operands[0], ReilImmediateOperand):
            in_operands[0] = ReilImmediateOperand(in_operands[0].immediate << 8, in_operands[0].size + 8)

        oprnd1 = in_operands[0]

        # trans  = ["xor [BIT  cf,  BIT  1, BYTE %0]"]
        # trans += ["xor [BIT  zf,  BIT  1, BYTE %1]"]
        # trans += ["and [BYTE %0, BYTE %1, BYTE %2]"]
        # trans += ["jcc [BYTE %2,   EMPTY,      $0]"]

        imm0 = tb.immediate(1, 1)

        tmp0 = tb.temporal(1)
        tmp1 = tb.temporal(1)
        tmp2 = tb.temporal(1)

        cf = ReilRegisterOperand("cf", 1)
        zf = ReilRegisterOperand("zf", 1)

        tb.add(builder.gen_xor(cf, imm0, tmp0))     # [BIT  cf,  BIT  1, BYTE %0]"]
        tb.add(builder.gen_xor(zf, imm0, tmp1))     # [BIT  zf,  BIT  1, BYTE %1]"]
        tb.add(builder.gen_and(tmp0, tmp1, tmp2))   # [BYTE %0, BYTE %1, BYTE %2]"]
        tb.add(builder.gen_jcc(tmp2, oprnd1))       # [BYTE %2,   EMPTY,      $0]"]

        return tb.instanciate(instruction.address)

    def _translate_jc(self, instruction, in_operands=None, out_operands=None):
        # Jump near if carry (CF=1).

        tb = TranslationBuilder(self.ir_name_generator)

        builder = ReilInstructionBuilder()

        oprnd1 = in_operands[0]

        assert oprnd1.size
        assert oprnd1.size in [32, 64]

        if isinstance(in_operands[0], ReilImmediateOperand):
            in_operands[0] = ReilImmediateOperand(in_operands[0].immediate << 8, in_operands[0].size + 8)

        oprnd1 = in_operands[0]

        # trans = ["jcc [BIT  cf, EMPTY, $0]"]

        cf = ReilRegisterOperand("cf", 1)

        tb.add(builder.gen_jcc(cf, oprnd1)) # [BIT  cf, EMPTY, $0]"]

        return tb.instanciate(instruction.address)

    def _translate_jnc(self, instruction, in_operands=None, out_operands=None):
        # Jump near if not carry (CF=0).

        tb = TranslationBuilder(self.ir_name_generator)

        builder = ReilInstructionBuilder()

        oprnd1 = in_operands[0]

        assert oprnd1.size
        assert oprnd1.size in [32, 64]

        if isinstance(in_operands[0], ReilImmediateOperand):
            in_operands[0] = ReilImmediateOperand(in_operands[0].immediate << 8, in_operands[0].size + 8)

        oprnd1 = in_operands[0]

        # trans  = ["xor [BIT  cf, BIT  1, BYTE %0]"]
        # trans += ["jcc [BYTE %0,  EMPTY,      $0]"]

        imm0 = tb.immediate(1, 1)

        tmp0 = tb.temporal(1)

        cf = ReilRegisterOperand("cf", 1)

        tb.add(builder.gen_xor(cf, imm0, tmp0)) # [BIT  cf, BIT  1, BYTE %0]"]
        tb.add(builder.gen_jcc(tmp0, oprnd1))   # [BYTE %0,  EMPTY,      $0]"]

        return tb.instanciate(instruction.address)

    def _translate_jecxz(self, instruction, in_operands=None, out_operands=None):
        # Jump short if ECX register is 0.

        tb = TranslationBuilder(self.ir_name_generator)

        builder = ReilInstructionBuilder()

        oprnd1 = in_operands[0]

        assert oprnd1.size
        assert oprnd1.size in [32, 64]

        if isinstance(in_operands[0], ReilImmediateOperand):
            in_operands[0] = ReilImmediateOperand(in_operands[0].immediate << 8, in_operands[0].size + 8)

        oprnd1 = in_operands[0]

        # trans  = ["bisz [DWORD ecx, EMPTY, BYTE %0]"]
        # trans += ["jcc  [BYTE   %0, EMPTY,      $0]"]

        tmp0 = tb.temporal(1)

        ecx = ReilRegisterOperand("ecx", 32)

        tb.add(builder.gen_bisz(ecx, tmp0))     # [DWORD ecx, EMPTY, BYTE %0]"]
        tb.add(builder.gen_jcc(tmp0, oprnd1))   # [BYTE   %0, EMPTY,      $0]"]

        return tb.instanciate(instruction.address)

    def _translate_call(self, instruction, in_operands=None, out_operands=None):
        # Flags Affected
        # All flags are affected if a task switch occurs; no flags are
        # affected if a task switch does not occur.

        tb = TranslationBuilder(self.ir_name_generator)

        builder = ReilInstructionBuilder()

        oprnd1 = in_operands[0]

        assert oprnd1.size
        assert oprnd1.size in [32, 64]

        if isinstance(in_operands[0], ReilImmediateOperand):
            in_operands[0] = ReilImmediateOperand(in_operands[0].immediate << 8, in_operands[0].size + 8)

        oprnd1 = in_operands[0]

        # if self.architecture_mode == ARCH_X86_MODE_32:
        #     trans  = ["sub [DWORD esp, DWORD   4, DWORD  %0]"]
        #     trans += ["str [DWORD  %0,     EMPTY, DWORD esp]"]
        #     trans += ["add [DWORD eip, DWORD {0}, DWORD  %1]".format(instruction.size)]
        #     trans += ["stm [DWORD  %1,     EMPTY, DWORD esp]"]
        #     trans += ["jcc [BYTE    1,     EMPTY, DWORD  $0]"]
        # elif self.architecture_mode == ARCH_X86_MODE_64:
        #     trans  = ["sub [QWORD rsp, QWORD   8, QWORD  %0]"]
        #     trans += ["str [QWORD  %0,     EMPTY, QWORD rsp]"]
        #     trans += ["add [QWORD rip, QWORD {0}, QWORD  %1]".format(instruction.size)]
        #     trans += ["stm [QWORD  %1,     EMPTY, QWORD rsp]"]
        #     trans += ["jcc [BYTE    1,     EMPTY, QWORD  $0]"]

        if self.architecture_mode == ARCH_X86_MODE_32:
            sp = ReilRegisterOperand("esp", 32)
            ip = ReilRegisterOperand("eip", 32)
            imm0 = ReilImmediateOperand(4, 32)
        elif self.architecture_mode == ARCH_X86_MODE_64:
            sp = ReilRegisterOperand("rsp", 64)
            ip = ReilRegisterOperand("rip", 64)
            imm0 = ReilImmediateOperand(8, 64)

        imm1 = tb.immediate(1, 1)
        size = tb.immediate(instruction.size, sp.size)

        tmp0 = tb.temporal(sp.size)
        tmp1 = tb.temporal(sp.size)

        tb.add(builder.gen_sub(sp, imm0, tmp0)) # [DWORD esp, DWORD   4, DWORD  %0]"]
        tb.add(builder.gen_str(tmp0, sp))       # [DWORD  %0,     EMPTY, DWORD esp]"]
        tb.add(builder.gen_add(ip, size, tmp1)) # [DWORD eip, DWORD {0}, DWORD  %1]".format(instruction.size)]
        tb.add(builder.gen_stm(tmp1, sp))       # [DWORD  %1,     EMPTY, DWORD esp]"]
        tb.add(builder.gen_jcc(imm1, oprnd1))   # [BYTE    1,     EMPTY, DWORD  $0]"]

        return tb.instanciate(instruction.address)

    def _translate_ret(self, instruction, in_operands=None, out_operands=None):
        # Flags Affected
        # None.

        tb = TranslationBuilder(self.ir_name_generator)

        builder = ReilInstructionBuilder()

        # trans = []

        # Pop return address
        # if self.architecture_mode == ARCH_X86_MODE_32:
        #     trans  = ["ldm [DWORD esp,   EMPTY, DWORD  %0]"]
        #     trans += ["add [DWORD esp, DWORD 4, DWORD  %1]"]
        #     trans += ["str [DWORD  %1,   EMPTY, DWORD esp]"]
        # elif self.architecture_mode == ARCH_X86_MODE_64:
        #     trans  = ["ldm [QWORD rsp,   EMPTY, QWORD  %0]"]
        #     trans += ["add [QWORD rsp, QWORD 8, QWORD  %1]"]
        #     trans += ["str [QWORD  %1,   EMPTY, QWORD rsp]"]

        if self.architecture_mode == ARCH_X86_MODE_32:
            sp = ReilRegisterOperand("esp", 32)
            imm = ReilImmediateOperand(4, 32)
        elif self.architecture_mode == ARCH_X86_MODE_64:
            sp = ReilRegisterOperand("rsp", 64)
            imm = ReilImmediateOperand(8, 64)

        tmp0 = tb.temporal(sp.size)
        tmp1 = tb.temporal(sp.size)

        tb.add(builder.gen_ldm(sp, tmp1))
        tb.add(builder.gen_add(sp, imm, tmp0))
        tb.add(builder.gen_str(tmp0, sp))

        # Free stack.
        if len(in_operands) > 0:
            oprnd1 = in_operands[0]

            assert oprnd1.size
            assert oprnd1.size == 16
            assert isinstance(oprnd1, ReilImmediateOperand)

            # if self.architecture_mode == ARCH_X86_MODE_32:
            #     trans += ["add [DWORD esp, DWORD {0},  DWORD %2]".format(oprnd1.immediate & (2**32 -1))]
            #     trans += ["str [DWORD  %2,     EMPTY, DWORD esp]"]
            # elif self.architecture_mode == ARCH_X86_MODE_64:
            #     trans += ["add [QWORD rsp, QWORD {0}, QWORD  %2]".format(oprnd1.immediate & (2**64 -1))]
            #     trans += ["str [QWORD  %2,     EMPTY, QWORD rsp]"]

            imm0 = tb.immediate(oprnd1.immediate & (2**sp.size -1), sp.size)

            tmp2 = tb.temporal(sp.size)

            tb.add(builder.gen_add(sp, imm0, tmp2))   # [DWORD esp, DWORD {0},  DWORD %2]".format(oprnd1.immediate & (2**32 -1))]
            tb.add(builder.gen_str(tmp2, sp))   # [DWORD  %2,     EMPTY, DWORD esp]"]

		# TODO: Replace RET instruction with JCC [BYTE 0x1, EMPTY, {D,Q}WORD %0]
        # trans += ["ret [EMPTY, EMPTY, EMPTY]"]
        tb.add(builder.gen_ret()) # [EMPTY, EMPTY, EMPTY]"]

        return tb.instanciate(instruction.address)

# "String Instructions"
# ============================================================================ #
    # def _translate_movsb(self, instruction, in_operands=None, out_operands=None):

    #     # print map(str, in_operands)
    #     # print map(str, out_operands)
    #     # print instruction.prefix

    #     # TODO: Finish implementation.

    #     trans = []

    #     trans += ["jcc  [DWORD ecx, EMPTY, POINTER {0}]".format(0)] # exit

    #     if instruction.prefix.startswith('rep'):

    #         # Operation
    #         trans += ["ldm  [DWORD $0, EMPTY, DWORD %0]"]
    #         trans += ["str  [DWORD %0, EMPTY, DWORD #0]"]

    #         # Increment pointers
    #         # TODO: Take DF into account.
    #         trans += ["add  [DWORD $0, DWORD 1, DWORD $0]"]
    #         trans += ["add  [DWORD #0, DWORD 1, DWORD #0]"]

    #         # Decrement counter
    #         trans += ["sub  [DWORD ecx, DWORD 1, DWORD ecx]".format(0)]

    #         trans += ["bisz [DWORD ecx, EMPTY, DWORD ?rep.0]"]
    #         trans += ["jcc  [DWORD ?rep.0, EMPTY, POINTER {0}]".format(0)] #exit

    #         if instruction.prefix in ['repz', 'repe']:

    #             trans += ["bisz [BYTE zf, EMPTY, DWORD ?rep.1]"]
    #             trans += ["jcc  [DWORD ?rep.1, EMPTY, POINTER {0}]".format(0)] #exit

    #         elif instruction.prefix in ['repnz', 'repne']:

    #             trans += ["jcc  [byte zf, EMPTY, POINTER {0}]".format(0)] #exit

    #     return self._ir_parser.parse(trans, False)

# "I/O Instructions"
# ============================================================================ #

# "Enter and Leave Instructions"
# ============================================================================ #
    def _translate_leave(self, instruction, in_operands=None, out_operands=None):
        # Flags Affected
        # None.

        tb = TranslationBuilder(self.ir_name_generator)

        builder = ReilInstructionBuilder()

        if self.architecture_mode == ARCH_X86_MODE_32:
            sp = ReilRegisterOperand("esp", 32)
            bp = ReilRegisterOperand("ebp", 32)
            imm = ReilImmediateOperand(4, 32)
        elif self.architecture_mode == ARCH_X86_MODE_64:
            sp = ReilRegisterOperand("rsp", 64)
            bp = ReilRegisterOperand("rbp", 64)
            imm = ReilImmediateOperand(8, 64)

        tmp0 = tb.temporal(sp.size)

        tb.add(builder.gen_str(bp, sp))         # [DWORD ebp,   EMPTY, DWORD esp]"]
        tb.add(builder.gen_ldm(sp, bp))         # [DWORD esp,   EMPTY, DWORD ebp]"]
        tb.add(builder.gen_add(sp, imm, tmp0))  # [DWORD esp, DWORD 4, DWORD  %0]"]
        tb.add(builder.gen_str(tmp0, sp))       # [DWORD  %0,   EMPTY, DWORD esp]"]

        # if self.architecture_mode == ARCH_X86_MODE_32:
        #     # leave == mov esp, ebp ; pop ebp ->
        #     # leave == mov esp, ebp ; mov ebp, [esp] ; add esp, 4
        #     trans  = ["str [DWORD ebp,   EMPTY, DWORD esp]"]
        #     trans += ["ldm [DWORD esp,   EMPTY, DWORD ebp]"]
        #     trans += ["add [DWORD esp, DWORD 4, DWORD  %0]"]
        #     trans += ["str [DWORD  %0,   EMPTY, DWORD esp]"]
        # elif self.architecture_mode == ARCH_X86_MODE_64:
        #     # leave == mov rsp, rbp ; pop rbp ->
        #     # leave == mov rsp, rbp ; mov rbp, [rsp] ; add rsp, 8

        #     trans  = ["str [QWORD rbp,   EMPTY, QWORD rsp]"]
        #     trans += ["ldm [QWORD rsp,   EMPTY, QWORD rbp]"]
        #     trans += ["add [QWORD rsp, QWORD 8, QWORD  %0]"]
        #     trans += ["str [QWORD  %0,   EMPTY, QWORD rsp]"]

        return tb.instanciate(instruction.address)

# "Flag Control (EFLAG) Instructions"
# ============================================================================ #
    def _translate_cld(self, instruction, in_operands=None, out_operands=None):
        # Flags Affected
        # The DF flag is set to 0. The CF, OF, ZF, SF, AF, and PF flags
        # are unaffected.

        tb = TranslationBuilder(self.ir_name_generator)

        builder = ReilInstructionBuilder()

        imm0 = tb.immediate(0, 1)

        df = ReilRegisterOperand("df", 1)

        # trans = ["str [BIT 0, EMPTY, BIT df]"]
        tb.add(builder.gen_str(imm0, df)) # [BIT 0, EMPTY, BIT df]"]

        return tb.instanciate(instruction.address)

    def _translate_clc(self, instruction, in_operands=None, out_operands=None):
        # Flags Affected
        # The CF flag is set to 0. The OF, ZF, SF, AF, and PF flags are
        # unaffected.

        tb = TranslationBuilder(self.ir_name_generator)

        builder = ReilInstructionBuilder()

        imm0 = tb.immediate(0, 1)

        cf = ReilRegisterOperand("cf", 1)

        # trans = ["str [BIT 0, EMPTY, BIT cf]"]
        tb.add(builder.gen_str(imm0, cf)) # [BIT 0, EMPTY, BIT cf]"]

        return tb.instanciate(instruction.address)

    def _translate_stc(self, instruction, in_operands=None, out_operands=None):
        # Flags Affected
        # The CF flag is set. The OF, ZF, SF, AF, and PF flags are
        # unaffected.

        tb = TranslationBuilder(self.ir_name_generator)

        builder = ReilInstructionBuilder()

        imm0 = tb.immediate(1, 1)

        cf = ReilRegisterOperand("cf", 1)

        # trans = ["str [BIT 1, EMPTY, BIT cf]"]
        tb.add(builder.gen_str(imm0, cf)) # [BIT 1, EMPTY, BIT cf]"]

        return tb.instanciate(instruction.address)

# "Segment Register Instructions"
# ============================================================================ #

# "Miscellaneous Instructions"
# ============================================================================ #
    def _translate_lea(self, instruction, in_operands=None, out_operands=None):
        # Flags Affected
        # None.

        tb = TranslationBuilder(self.ir_name_generator)

        builder = ReilInstructionBuilder()

        oprnd1 = in_operands[0]
        oprnd2 = out_operands[0]

        assert oprnd1.size and oprnd2.size
        assert oprnd1.size == oprnd2.size

        # trans = ["str [$0, EMPTY, #0]"]
        tb.add(builder.gen_str(oprnd1, oprnd2)) # [$0, EMPTY, #0]"]

        return tb.instanciate(instruction.address)

    def _translate_nop(self, instruction, in_operands=None, out_operands=None):
        # Flags Affected
        # None.

        tb = TranslationBuilder(self.ir_name_generator)

        builder = ReilInstructionBuilder()

        # trans = ["nop [EMPTY, EMPTY, EMPTY]"]
        tb.add(builder.gen_nop()) # [EMPTY, EMPTY, EMPTY]"]

        return tb.instanciate(instruction.address)

# "Random Number Generator Instruction"
# ============================================================================ #

# "Misc"
# ============================================================================ #
    def _translate_hlt(self, instruction, in_operands=None, out_operands=None):
        # Flags Affected
        # None.

        tb = TranslationBuilder(self.ir_name_generator)

        builder = ReilInstructionBuilder()

        # trans = ["unkn [EMPTY, EMPTY, EMPTY]"]
        tb.add(builder.gen_unkn()) # [EMPTY, EMPTY, EMPTY]"]

        return tb.instanciate(instruction.address)
