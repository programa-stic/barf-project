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

        self._flags = {
            "af" : ReilRegisterOperand("af", 1),
            "cf" : ReilRegisterOperand("cf", 1),
            "df" : ReilRegisterOperand("df", 1),
            "of" : ReilRegisterOperand("of", 1),
            "pf" : ReilRegisterOperand("pf", 1),
            "sf" : ReilRegisterOperand("sf", 1),
            "zf" : ReilRegisterOperand("zf", 1),
        }

        if self.architecture_mode == ARCH_X86_MODE_32:
            self._sp = ReilRegisterOperand("esp", 32)
            self._bp = ReilRegisterOperand("ebp", 32)
            self._ip = ReilRegisterOperand("eip", 32)

            self._ws = ReilImmediateOperand(4, 32) # word size
        elif self.architecture_mode == ARCH_X86_MODE_64:
            self._sp = ReilRegisterOperand("rsp", 64)
            self._bp = ReilRegisterOperand("rbp", 64)
            self._ip = ReilRegisterOperand("rip", 64)

            self._ws = ReilImmediateOperand(8, 64) # word size

        self._builder = ReilInstructionBuilder()

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
        tb = TranslationBuilder(self.ir_name_generator)

        instrs = translator_fn(tb, instruction, in_operands, out_operands)

        return instrs

    @property
    def translation_mode(self):
        return self._translation_mode

    @translation_mode.setter
    def translation_mode(self, value):
        self._translation_mode = value

# ============================================================================ #

    def _not_implemented(self, tb, instruction, in_operands, out_operands):
        raise NotImplementedError("Instruction Not Implemented")

# Translators
# ============================================================================ #
# ============================================================================ #

# "Flags"
# ============================================================================ #
    def _translate_af(self, tb, oprnd1, oprnd2, result):
        # TODO: Implement
        pass

    def _translate_pf(self, tb, oprnd1, oprnd2, result):
        # TODO: Implement
        pass

    def _translate_sf(self, tb, oprnd1, oprnd2, result):
        # Create temporal variables.
        tmp0 = tb.temporal(result.size)

        mask0 = tb.immediate(2**result.size-1, result.size)
        shift0 = tb.immediate(-(result.size-1), result.size)

        sf = self._flags["sf"]

        tb.add(self._builder.gen_and(result, mask0, tmp0))  # filter sign bit
        tb.add(self._builder.gen_bsh(tmp0, shift0, sf))     # extract sign bit

    def _translate_of(self, tb, oprnd1, oprnd2, result):
        of = self._flags["of"]

        imm0 = tb.immediate(2**(oprnd1.size-1), oprnd1.size)
        imm1 = tb.immediate(1, oprnd1.size)
        imm3 = tb.immediate(-(oprnd1.size-1), oprnd1.size)
        imm4 = tb.immediate(2**(oprnd1.size-1), result.size)

        tmp0 = tb.temporal(oprnd1.size)
        tmp1 = tb.temporal(oprnd2.size)
        tmp2 = tb.temporal(oprnd1.size)
        tmp3 = tb.temporal(oprnd1.size)
        tmp4 = tb.temporal(oprnd1.size)
        tmp5 = tb.temporal(oprnd1.size)
        tmp6 = tb.temporal(oprnd1.size)

        tb.add(self._builder.gen_and(oprnd1, imm0, tmp0))   # filter sign bit oprnd 1
        tb.add(self._builder.gen_and(oprnd2, imm0, tmp1))   # filter sign bit oprnd 2
        tb.add(self._builder.gen_and(result, imm4, tmp2))   # filter sign bit result
        tb.add(self._builder.gen_xor(tmp0, tmp1, tmp3))     # sign bit oprnd1 ^ sign bit oprnd2
        tb.add(self._builder.gen_xor(tmp3, imm1, tmp4))     # sign bit oprnd1 ^ sign bit oprnd2 ^ 1
        tb.add(self._builder.gen_xor(tmp0, tmp2, tmp5))     # sign bit oprnd1 ^ sign bit result
        tb.add(self._builder.gen_and(tmp4, tmp5, tmp6))     # (sign bit oprnd1 ^ sign bit oprnd2 ^ 1) & (sign bit oprnd1 ^ sign bit result)
        tb.add(self._builder.gen_bsh(tmp6, imm3, of))

    def _translate_cf(self, tb, oprnd1, oprnd2, result):
        cf = self._flags["cf"]

        imm0 = tb.immediate(2**oprnd1.size, result.size)
        imm1 = tb.immediate(-oprnd1.size, result.size)
        imm2 = tb.immediate(-oprnd1.size, oprnd1.size)

        tmp0 = tb.temporal(oprnd1.size)

        tb.add(self._builder.gen_and(result, imm0, tmp0))   # filter carry bit
        tb.add(self._builder.gen_bsh(tmp0, imm2, cf))

    def _translate_zf(self, tb, oprnd1, oprnd2, result):
        zf = self._flags["zf"]

        imm0 = tb.immediate((2**oprnd1.size)-1, result.size)

        tmp0 = tb.temporal(oprnd1.size)

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

# "Data Transfer Instructions"
# ============================================================================ #
    def _translate_mov(self, tb, instruction, in_operands=None, out_operands=None):
        # Flags Affected
        # None.

        oprnd1 = in_operands[0]
        oprnd2 = out_operands[0]

        assert oprnd1.size and oprnd2.size
        assert oprnd1.size == oprnd2.size

        tb.add(self._builder.gen_str(oprnd1, oprnd2))

        return tb.instanciate(instruction.address)

    def _translate_movzx(self, tb, instruction, in_operands=None, out_operands=None):
        # Flags Affected
        # None.

        oprnd1 = in_operands[0]
        oprnd2 = out_operands[0]

        assert oprnd1.size and oprnd2.size
        assert oprnd2.size > oprnd1.size

        tb.add(self._builder.gen_str(oprnd1, oprnd2))

        return tb.instanciate(instruction.address)

    def _translate_xchg(self, tb, instruction, in_operands=None, out_operands=None):
        # Flags Affected
        # None.

        oprnd1 = in_operands[0]
        oprnd2 = in_operands[1]
        oprnd3 = out_operands[0]
        oprnd4 = out_operands[1]

        assert oprnd1.size and oprnd2.size
        assert oprnd1.size == oprnd2.size and oprnd3.size == oprnd4.size

        tmp0 = tb.temporal(oprnd1.size)
        tmp1 = tb.temporal(oprnd2.size)

        tb.add(self._builder.gen_str(oprnd1, tmp0))
        tb.add(self._builder.gen_str(oprnd2, tmp1))
        tb.add(self._builder.gen_str(tmp1, oprnd3))
        tb.add(self._builder.gen_str(tmp0, oprnd4))

        return tb.instanciate(instruction.address)

    def _translate_push(self, tb, instruction, in_operands=None, out_operands=None):
        # Flags Affected
        # None.

        oprnd1 = in_operands[0]

        assert oprnd1.size
        assert oprnd1.size in [32, 64]

        tmp0 = tb.temporal(self._sp.size)

        tb.add(self._builder.gen_sub(self._sp, self._ws, tmp0))
        tb.add(self._builder.gen_str(tmp0, self._sp))
        tb.add(self._builder.gen_stm(oprnd1, self._sp))

        return tb.instanciate(instruction.address)

    def _translate_pop(self, tb, instruction, in_operands=None, out_operands=None):
        # Flags Affected
        # None.

        oprnd1 = out_operands[0]

        assert oprnd1.size
        assert oprnd1.size in [32, 64]

        tmp0 = tb.temporal(self._sp.size)

        tb.add(self._builder.gen_ldm(self._sp, oprnd1))
        tb.add(self._builder.gen_add(self._sp, self._ws, tmp0))
        tb.add(self._builder.gen_str(tmp0, self._sp))

        return tb.instanciate(instruction.address)

# "Binary Arithmetic Instructions"
# ============================================================================ #
    def _translate_add(self, tb, instruction, in_operands=None, out_operands=None):
        # Flags Affected
        # The OF, SF, ZF, AF, CF, and PF flags are set according to the
        # result.

        oprnd1 = in_operands[0]
        oprnd2 = in_operands[1]
        oprnd3 = out_operands[0]

        assert oprnd1.size and oprnd2.size
        assert oprnd1.size == oprnd2.size

        tmp0 = tb.temporal(oprnd1.size*2)

        tb.add(self._builder.gen_add(oprnd1, oprnd2, tmp0))

        if self._translation_mode == FULL_TRANSLATION:
            # Flags : OF, SF, ZF, AF, CF, PF
            self._translate_of(tb, oprnd1, oprnd2, oprnd1)
            self._translate_sf(tb, oprnd1, oprnd2, oprnd1)
            self._translate_zf(tb, oprnd1, oprnd2, oprnd1)
            self._translate_af(tb, oprnd1, oprnd2, oprnd1)
            self._translate_cf(tb, oprnd1, oprnd2, oprnd1)
            self._translate_pf(tb, oprnd1, oprnd2, oprnd1)

        tb.add(self._builder.gen_str(tmp0, oprnd3))

        return tb.instanciate(instruction.address)

    def _translate_adc(self, tb, instruction, in_operands=None, out_operands=None):
        # Flags Affected
        # The OF, SF, ZF, AF, CF, and PF flags are set according to the result.

        oprnd1 = in_operands[0]
        oprnd2 = in_operands[1]
        oprnd3 = out_operands[0]

        assert oprnd1.size and oprnd2.size
        assert oprnd1.size == oprnd2.size

        tmp0 = tb.temporal(oprnd1.size*2)
        tmp1 = tb.temporal(oprnd1.size*2)
        tmp2 = tb.temporal(oprnd1.size*2)

        tb.add(self._builder.gen_add(oprnd1, oprnd2, tmp0))
        tb.add(self._builder.gen_str(self._flags["cf"], tmp1))
        tb.add(self._builder.gen_add(tmp0, tmp1, tmp2))

        if self._translation_mode == FULL_TRANSLATION:
            # Flags : OF, SF, ZF, AF, CF, PF
            self._translate_of(tb, oprnd1, oprnd2, tmp2)
            self._translate_sf(tb, oprnd1, oprnd2, tmp2)
            self._translate_zf(tb, oprnd1, oprnd2, tmp2)
            self._translate_af(tb, oprnd1, oprnd2, tmp2)
            self._translate_cf(tb, oprnd1, oprnd2, tmp2)
            self._translate_pf(tb, oprnd1, oprnd2, tmp2)

        tb.add(self._builder.gen_str(tmp2, oprnd3))

        return tb.instanciate(instruction.address)

    def _translate_sub(self, tb, instruction, in_operands=None, out_operands=None):
        # Flags Affected
        # The OF, SF, ZF, AF, PF, and CF flags are set according to the
        # result.

        oprnd1 = in_operands[0]
        oprnd2 = in_operands[1]
        oprnd3 = out_operands[0]

        assert oprnd1.size and oprnd2.size
        assert oprnd1.size == oprnd2.size

        tmp0 = tb.temporal(oprnd1.size*2)

        tb.add(self._builder.gen_sub(oprnd1, oprnd2, tmp0))

        if self._translation_mode == FULL_TRANSLATION:
            # Flags : OF, SF, ZF, AF, PF, CF
            self._translate_of(tb, oprnd1, oprnd2, oprnd1)
            self._translate_sf(tb, oprnd1, oprnd2, oprnd1)
            self._translate_zf(tb, oprnd1, oprnd2, oprnd1)
            self._translate_af(tb, oprnd1, oprnd2, oprnd1)
            self._translate_pf(tb, oprnd1, oprnd2, oprnd1)
            self._translate_cf(tb, oprnd1, oprnd2, oprnd1)

        tb.add(self._builder.gen_str(tmp0, oprnd3))

        return tb.instanciate(instruction.address)

    def _translate_sbb(self, tb, instruction, in_operands=None, out_operands=None):
        # Flags Affected
        # The OF, SF, ZF, AF, PF, and CF flags are set according to the
        # result.

        oprnd1 = in_operands[0]
        oprnd2 = in_operands[1]
        oprnd3 = out_operands[0]

        assert oprnd1.size and oprnd2.size
        assert oprnd1.size == oprnd2.size

        tmp0 = tb.temporal(oprnd1.size*2)
        tmp1 = tb.temporal(oprnd1.size*2)
        tmp2 = tb.temporal(oprnd1.size*2)

        tb.add(self._builder.gen_sub(oprnd1, oprnd2, tmp0))
        tb.add(self._builder.gen_str(self._flags["cf"], tmp1))
        tb.add(self._builder.gen_sub(oprnd1, oprnd2, tmp2))

        if self._translation_mode == FULL_TRANSLATION:
            # Flags : OF, SF, ZF, AF, PF, CF
            self._translate_of(tb, oprnd1, oprnd2, tmp2)
            self._translate_sf(tb, oprnd1, oprnd2, tmp2)
            self._translate_zf(tb, oprnd1, oprnd2, tmp2)
            self._translate_af(tb, oprnd1, oprnd2, tmp2)
            self._translate_pf(tb, oprnd1, oprnd2, tmp2)
            self._translate_cf(tb, oprnd1, oprnd2, tmp2)

        tb.add(self._builder.gen_str(tmp2, oprnd3))

        return tb.instanciate(instruction.address)

    def _translate_mul(self, tb, instruction, in_operands=None, out_operands=None):
        # Flags Affected
        # The OF and CF flags are set to 0 if the upper half of the
        # result is 0; otherwise, they are set to 1. The SF, ZF, AF, and
        # PF flags are undefined.

        oprnd1 = in_operands[0]
        oprnd2 = in_operands[1]
        oprnd3 = out_operands[0]
        oprnd4 = out_operands[1]

        assert oprnd1.size and oprnd2.size
        assert oprnd1.size == oprnd2.size

        imm0 = tb.immediate(-oprnd1.size, oprnd1.size*2)

        tmp0 = tb.temporal(oprnd1.size*2)

        tb.add(self._builder.gen_mul(oprnd1, oprnd2, tmp0))
        tb.add(self._builder.gen_bsh(tmp0, imm0, oprnd3))
        tb.add(self._builder.gen_str(tmp0, oprnd4))

        if self._translation_mode == FULL_TRANSLATION:
            # Flags : OF, CF
            fimm0 = tb.immediate(1, 1)

            ftmp0 = tb.temporal(oprnd1.size*2)
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

        return tb.instanciate(instruction.address)

    def _translate_imul(self, tb, instruction, in_operands=None, out_operands=None):
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
        tb.add(self._builder.gen_str(oprnd1, tmp0))

        # Do multiplication.
        tb.add(self._builder.gen_mul(oprnd1, oprnd2, tmp1))

        # Save result.
        if len(out_operands) == 1:
            tb.add(self._builder.gen_str(tmp1, oprnd3))

        elif len(out_operands) == 2:
            oprnd4 = out_operands[1]

            tb.add(self._builder.gen_bsh(tmp1, imm0, oprnd3)) # save high part
            tb.add(self._builder.gen_str(tmp1, oprnd4))       # save low part
        else:
            raise Exeption()

        if self._translation_mode == FULL_TRANSLATION:
            # Flags : OF, CF
            # TODO: Implement.
            self._undefine_flag(tb, self._flags["sf"])
            self._undefine_flag(tb, self._flags["zf"])
            self._undefine_flag(tb, self._flags["af"])
            self._undefine_flag(tb, self._flags["pf"])

        return tb.instanciate(instruction.address)

    def _translate_div(self, tb, instruction, in_operands=None, out_operands=None):
        # Flags Affected
        # The CF, OF, SF, ZF, AF, and PF flags are undefined.

        oprnd1 = in_operands[0]
        oprnd2 = in_operands[1]
        oprnd3 = in_operands[2]

        oprnd4 = out_operands[0]
        oprnd5 = out_operands[1]

        assert oprnd1.size and oprnd2.size
        assert oprnd1.size == oprnd2.size == oprnd3.size

        imm0 = tb.immediate(oprnd1.size, oprnd1.size*2)

        tmp0 = tb.temporal(oprnd1.size*2)
        tmp1 = tb.temporal(oprnd1.size*2)
        tmp2 = tb.temporal(oprnd1.size*2)

        tmp3 = tb.temporal(oprnd1.size*2)
        tmp4 = tb.temporal(oprnd1.size*2)
        tmp5 = tb.temporal(oprnd1.size*2)
        tmp6 = tb.temporal(oprnd1.size*2)

        # Extend operands to match their size.
        tb.add(self._builder.gen_str(oprnd1, tmp0))
        tb.add(self._builder.gen_str(oprnd2, tmp1))
        tb.add(self._builder.gen_str(oprnd3, tmp2))

        # Put dividend together.
        tb.add(self._builder.gen_bsh(tmp0, imm0, tmp3))
        tb.add(self._builder.gen_or(tmp3, tmp1, tmp4))

        # Do division
        tb.add(self._builder.gen_div(tmp4, tmp2, tmp5))
        tb.add(self._builder.gen_mod(tmp4, tmp2, tmp6))
        tb.add(self._builder.gen_str(tmp5, oprnd5))
        tb.add(self._builder.gen_str(tmp6, oprnd4))

        if self._translation_mode == FULL_TRANSLATION:
            # Flags : CF, OF, SF, ZF, AF, PF
            self._undefine_flag(tb, self._flags["cf"])
            self._undefine_flag(tb, self._flags["of"])
            self._undefine_flag(tb, self._flags["sf"])
            self._undefine_flag(tb, self._flags["zf"])
            self._undefine_flag(tb, self._flags["af"])
            self._undefine_flag(tb, self._flags["pf"])

        return tb.instanciate(instruction.address)

    def _translate_inc(self, tb, instruction, in_operands=None, out_operands=None):
        # Flags Affected
        # The CF flag is not affected. The OF, SF, ZF, AF, and PF flags
        # are set according to the result.

        oprnd1 = in_operands[0]

        oprnd2 = out_operands[0]

        assert oprnd1.size

        imm0 = tb.immediate(1, oprnd1.size)

        tmp0 = tb.temporal(oprnd1.size*2)

        tb.add(self._builder.gen_add(oprnd1, imm0, tmp0))

        if self._translation_mode == FULL_TRANSLATION:
            # Flags : OF, SF, ZF, AF, PF
            self._translate_of(tb, oprnd1, oprnd1, tmp0)
            self._translate_sf(tb, oprnd1, oprnd1, tmp0)
            self._translate_zf(tb, oprnd1, oprnd1, tmp0)
            self._translate_af(tb, oprnd1, oprnd1, tmp0)
            self._translate_pf(tb, oprnd1, oprnd1, tmp0)

        tb.add(self._builder.gen_str(tmp0, oprnd2))

        return tb.instanciate(instruction.address)

    def _translate_dec(self, tb, instruction, in_operands=None, out_operands=None):
        # Flags Affected
        # The CF flag is not affected. The OF, SF, ZF, AF, and PF flags
        # are set according to the result.

        oprnd1 = in_operands[0]

        oprnd2 = out_operands[0]

        assert oprnd1.size

        imm0 = tb.immediate(1, oprnd1.size)

        tmp0 = tb.temporal(oprnd1.size*2)

        tb.add(self._builder.gen_sub(oprnd1, imm0, tmp0))

        if self._translation_mode == FULL_TRANSLATION:
            # Flags : OF, SF, ZF, AF, PF
            self._translate_of(tb, oprnd1, oprnd1, tmp0)
            self._translate_sf(tb, oprnd1, oprnd1, tmp0)
            self._translate_zf(tb, oprnd1, oprnd1, tmp0)
            self._translate_af(tb, oprnd1, oprnd1, tmp0)
            self._translate_pf(tb, oprnd1, oprnd1, tmp0)

        tb.add(self._builder.gen_str(tmp0, oprnd2))

        return tb.instanciate(instruction.address)

    def _translate_neg(self, tb, instruction, in_operands=None, out_operands=None):
        # Flags Affected
        # The CF flag set to 0 if the source operand is 0; otherwise it
        # is set to 1. The OF, SF, ZF, AF, and PF flags are set
        # according to the result.

        oprnd1 = in_operands[0]

        oprnd2 = out_operands[0]

        assert oprnd1.size

        imm0 = tb.immediate((2**oprnd1.size)-1, oprnd1.size)
        imm1 = tb.immediate(1, oprnd1.size)
        imm2 = tb.immediate(1, 1)

        tmp0 = tb.temporal(oprnd1.size)
        tmp1 = tb.temporal(1)

        tb.add(self._builder.gen_xor(oprnd1, imm0, tmp0))
        tb.add(self._builder.gen_add(tmp0, imm1, oprnd2))

        # Flags : CF
        tb.add(self._builder.gen_bisz(oprnd1, tmp1))
        tb.add(self._builder.gen_xor(tmp1, imm2, self._flags["cf"]))

        if self._translation_mode == FULL_TRANSLATION:
            # Flags : OF, SF, ZF, AF, PF
            self._translate_of(tb, oprnd1, oprnd1, oprnd2)
            self._translate_sf(tb, oprnd1, oprnd1, oprnd2)
            self._translate_zf(tb, oprnd1, oprnd1, oprnd2)
            self._translate_af(tb, oprnd1, oprnd1, oprnd2)
            self._translate_pf(tb, oprnd1, oprnd1, oprnd2)

        return tb.instanciate(instruction.address)

    def _translate_cmp(self, tb, instruction, in_operands=None, out_operands=None):
        # Flags Affected
        # The CF, OF, SF, ZF, AF, and PF flags are set according to the
        # result.

        oprnd1 = in_operands[0]
        oprnd2 = in_operands[1]

        assert oprnd1.size and oprnd2.size
        assert oprnd1.size == oprnd2.size

        tmp0 = tb.temporal(oprnd1.size*2)

        tb.add(self._builder.gen_sub(oprnd1, oprnd2, tmp0))

        # Flags : CF, OF, SF, ZF, AF, PF
        self._translate_cf(tb, oprnd1, oprnd2, tmp0)
        self._translate_of(tb, oprnd1, oprnd2, tmp0)
        self._translate_sf(tb, oprnd1, oprnd2, tmp0)
        self._translate_zf(tb, oprnd1, oprnd2, tmp0)
        self._translate_af(tb, oprnd1, oprnd2, tmp0)
        self._translate_pf(tb, oprnd1, oprnd2, tmp0)

        return tb.instanciate(instruction.address)

# "Decimal Arithmetic Instructions"
# ============================================================================ #

# "Logical Instructions"
# ============================================================================ #
    def _translate_and(self, tb, instruction, in_operands=None, out_operands=None):
        # Flags Affected
        # The OF and CF flags are cleared; the SF, ZF, and PF flags are
        # set according to the result. The state of the AF flag is
        # undefined.

        oprnd1 = in_operands[0]
        oprnd2 = in_operands[1]

        oprnd3 = out_operands[0]

        assert oprnd1.size and oprnd2.size
        assert oprnd1.size == oprnd2.size

        tb.add(self._builder.gen_and(oprnd1, oprnd2, oprnd3))

        if self._translation_mode == FULL_TRANSLATION:
            # Flags : OF, CF
            self._clear_flag(tb, self._flags["of"])
            self._clear_flag(tb, self._flags["cf"])

            # Flags : SF, ZF, PF
            self._translate_sf(tb, oprnd1, oprnd2, oprnd3)
            self._translate_zf(tb, oprnd1, oprnd2, oprnd3)
            self._translate_pf(tb, oprnd1, oprnd2, oprnd3)

            # Flags : AF
            self._undefine_flag(tb, self._flags["af"])

        return tb.instanciate(instruction.address)

    def _translate_or(self, tb, instruction, in_operands=None, out_operands=None):
        # Flags Affected
        # The OF and CF flags are cleared; the SF, ZF, and PF flags are
        # set according to the result. The state of the AF flag is
        # undefined.

        oprnd1 = in_operands[0]
        oprnd2 = in_operands[1]

        oprnd3 = out_operands[0]

        assert oprnd1.size and oprnd2.size
        assert oprnd1.size == oprnd2.size

        tb.add(self._builder.gen_or(oprnd1, oprnd2, oprnd3))

        if self._translation_mode == FULL_TRANSLATION:
            # Flags : OF, CF
            self._clear_flag(tb, self._flags["of"])
            self._clear_flag(tb, self._flags["cf"])

            # Flags : SF, ZF, PF
            self._translate_sf(tb, oprnd1, oprnd2, oprnd3)
            self._translate_zf(tb, oprnd1, oprnd2, oprnd3)
            self._translate_pf(tb, oprnd1, oprnd2, oprnd3)

            # Flags : AF
            self._undefine_flag(tb, self._flags["af"])

        return tb.instanciate(instruction.address)

    def _translate_xor(self, tb, instruction, in_operands=None, out_operands=None):
        # Flags Affected
        # The OF and CF flags are cleared; the SF, ZF, and PF flags are set
        # according to the result. The state of the AF flag is
        # undefined.

        oprnd1 = in_operands[0]
        oprnd2 = in_operands[1]

        oprnd3 = out_operands[0]

        assert oprnd1.size and oprnd2.size
        assert oprnd1.size == oprnd2.size

        tb.add(self._builder.gen_xor(oprnd1, oprnd2, oprnd3))

        if self._translation_mode == FULL_TRANSLATION:
            # Flags : OF, CF
            self._clear_flag(tb, self._flags["of"])
            self._clear_flag(tb, self._flags["cf"])

            # Flags : SF, ZF, PF
            self._translate_sf(tb, oprnd1, oprnd2, oprnd3)
            self._translate_zf(tb, oprnd1, oprnd2, oprnd3)
            self._translate_pf(tb, oprnd1, oprnd2, oprnd3)

            # Flags : AF
            self._undefine_flag(tb, self._flags["af"])

        return tb.instanciate(instruction.address)

    def _translate_not(self, tb, instruction, in_operands=None, out_operands=None):
        # Flags Affected
        # None.

        oprnd1 = in_operands[0]

        oprnd2 = out_operands[0]

        assert oprnd1.size

        imm0 = tb.immediate((2**oprnd1.size)-1, oprnd1.size)

        tb.add(self._builder.gen_xor(oprnd1, imm0, oprnd2))

        return tb.instanciate(instruction.address)

# "Shift and Rotate Instructions"
# ============================================================================ #
    def _translate_shr(self, tb, instruction, in_operands=None, out_operands=None):
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

        oprnd1 = in_operands[0]
        oprnd2 = in_operands[1]

        oprnd3 = out_operands[0]

        assert oprnd1.size and oprnd2.size

        imm0 = tb.immediate(1, oprnd1.size)
        imm1 = tb.immediate((2**oprnd1.size)-1, oprnd1.size)
        imm2 = tb.immediate(-1, oprnd1.size)

        tmp0 = tb.temporal(oprnd1.size)
        tmp1 = tb.temporal(oprnd1.size)
        tmp2 = tb.temporal(oprnd1.size)
        tmp3 = tb.temporal(oprnd1.size)
        tmp4 = tb.temporal(oprnd1.size)
        tmp5 = tb.temporal(oprnd1.size)

        # Extend 2nd operand to 1st operand size
        tb.add(self._builder.gen_str(oprnd2, tmp0))

        # Decrement in 1 shift amount
        tb.add(self._builder.gen_sub(tmp0, imm0, tmp1))

        # Negate
        tb.add(self._builder.gen_xor(tmp1, imm1, tmp2))
        tb.add(self._builder.gen_add(tmp2, imm0, tmp3))

        # Shift right
        tb.add(self._builder.gen_bsh(oprnd1, tmp3, tmp4))

        # Save LSB in CF
        tb.add(self._builder.gen_and(tmp4, imm0, tmp5))
        tb.add(self._builder.gen_str(tmp5, self._flags["cf"]))

        # Shift one more time
        tb.add(self._builder.gen_bsh(tmp4, imm2, oprnd3))

        if self._translation_mode == FULL_TRANSLATION:
            # Flags : OF
            # TODO: Implement translation for OF flag.

            # Flags : SF, ZF, PF
            self._translate_sf(tb, oprnd1, oprnd1, oprnd3)
            self._translate_zf(tb, oprnd1, oprnd1, oprnd3)
            self._translate_pf(tb, oprnd1, oprnd1, oprnd3)

            # Flags : AF
            self._undefine_flag(tb, self._flags["af"])

        return tb.instanciate(instruction.address)

    def _translate_shl(self, tb, instruction, in_operands=None, out_operands=None):
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

        oprnd1 = in_operands[0]
        oprnd2 = in_operands[1]

        oprnd3 = out_operands[0]

        assert oprnd1.size and oprnd2.size
        # assert oprnd2.size == 8

        imm0 = tb.immediate(1, oprnd1.size)

        tmp0 = tb.temporal(oprnd1.size)
        tmp1 = tb.temporal(oprnd1.size)
        tmp2 = tb.temporal(oprnd1.size)
        tmp3 = tb.temporal(oprnd1.size)

        # Extend 2nd operand to 1st operand size
        tb.add(self._builder.gen_str(oprnd2, tmp0))

        # Decrement in 1 shift amount
        tb.add(self._builder.gen_sub(tmp0, imm0, tmp1))

        # Shift left
        tb.add(self._builder.gen_bsh(oprnd1, tmp1, tmp2))

        # Save LSB in CF
        tb.add(self._builder.gen_and(tmp2, imm0, tmp3))
        tb.add(self._builder.gen_str(tmp3, self._flags["cf"]))

        # Shift one more time
        tb.add(self._builder.gen_bsh(tmp2, imm0, oprnd3))

        if self._translation_mode == FULL_TRANSLATION:
            # Flags : OF
            # TODO: Implement translation for OF flag.

            # Flags : SF, ZF, PF
            self._translate_sf(tb, oprnd1, oprnd1, oprnd3)
            self._translate_zf(tb, oprnd1, oprnd1, oprnd3)
            self._translate_pf(tb, oprnd1, oprnd1, oprnd3)

            # Flags : AF
            self._undefine_flag(tb, self._flags["af"])

        return tb.instanciate(instruction.address)

    def _translate_sal(self, tb, instruction, in_operands=None, out_operands=None):
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

        return self._translate_shl(tb, instruction, in_operands, out_operands)

    def _translate_sar(self, tb, instruction, in_operands=None, out_operands=None):
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

        oprnd1 = in_operands[0]
        oprnd2 = in_operands[1]

        oprnd3 = out_operands[0]

        assert oprnd1.size and oprnd2.size

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

        # Create labels.
        loop_lbl = tb.label('loop')

        # Initialize counter
        tb.add(self._builder.gen_str(oprnd2, tmp0))

        # Copy operand to temporal register
        tb.add(self._builder.gen_str(oprnd1, tmp1))

        # Filter sign bit
        tb.add(self._builder.gen_and(oprnd1, imm0, tmp2))

        tb.add(loop_lbl)

        # Filter lsb bit
        tb.add(self._builder.gen_and(oprnd1, imm1, tmp6))
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
        tb.add(self._builder.gen_str(tmp1, oprnd3))

        if self._translation_mode == FULL_TRANSLATION:
            # Flags : OF
            # TODO: Implement translation for OF flag.

            # Flags : SF, ZF, PF
            self._translate_sf(tb, oprnd1, oprnd1, oprnd3)
            self._translate_zf(tb, oprnd1, oprnd1, oprnd3)
            self._translate_pf(tb, oprnd1, oprnd1, oprnd3)

            # Flags : AF
            self._undefine_flag(tb, self._flags["af"])

        return tb.instanciate(instruction.address)

# "Bit and Byte Instructions"
# ============================================================================ #
    def _translate_test(self, tb, instruction, in_operands=None, out_operands=None):
        # Flags Affected
        # The OF and CF flags are set to 0. The SF, ZF, and PF flags are
        # set according to the result (see the “Operation” section
        # above). The state of the AF flag is undefined.

        oprnd1 = in_operands[0]
        oprnd2 = in_operands[0]

        assert oprnd1.size and oprnd2.size
        assert oprnd1.size == oprnd2.size

        tmp0 = tb.temporal(oprnd1.size)

        tb.add(self._builder.gen_and(oprnd1, oprnd2, tmp0))

        # Flags : OF, CF
        self._clear_flag(tb, self._flags["of"])
        self._clear_flag(tb, self._flags["cf"])

        # Flags : SF, ZF, PF
        self._translate_sf(tb, oprnd1, oprnd2, tmp0)
        self._translate_zf(tb, oprnd1, oprnd2, tmp0)
        self._translate_pf(tb, oprnd1, oprnd2, tmp0)

        # Flags : AF
        self._undefine_flag(tb, self._flags["af"])

        return tb.instanciate(instruction.address)

# "Control Transfer Instructions"
# ============================================================================ #
    def _translate_jmp(self, tb, instruction, in_operands=None, out_operands=None):
        # Flags Affected
        # All flags are affected if a task switch occurs; no flags are
        # affected if a task switch does not occur.

        oprnd1 = in_operands[0]

        assert oprnd1.size
        assert oprnd1.size in [32, 64]

        if isinstance(in_operands[0], ReilImmediateOperand):
            in_operands[0] = ReilImmediateOperand(in_operands[0].immediate << 8, in_operands[0].size + 8)

        oprnd1 = in_operands[0]

        imm0 = tb.immediate(1, 1)

        tb.add(self._builder.gen_jcc(imm0, oprnd1))

        return tb.instanciate(instruction.address)

    def _translate_ja(self, tb, instruction, in_operands=None, out_operands=None):
        # Jump near if above (CF=0 and ZF=0).

        oprnd1 = in_operands[0]

        assert oprnd1.size
        assert oprnd1.size in [32, 64]

        if isinstance(in_operands[0], ReilImmediateOperand):
            in_operands[0] = ReilImmediateOperand(in_operands[0].immediate << 8, in_operands[0].size + 8)

        oprnd1 = in_operands[0]

        imm0 = tb.immediate(1, 1)

        tmp0 = tb.temporal(1)
        tmp1 = tb.temporal(1)
        tmp2 = tb.temporal(1)

        tb.add(self._builder.gen_xor(self._flags["cf"], imm0, tmp0))
        tb.add(self._builder.gen_xor(self._flags["zf"], imm0, tmp1))
        tb.add(self._builder.gen_and(tmp0, tmp1, tmp2))
        tb.add(self._builder.gen_jcc(tmp2, oprnd1))

        return tb.instanciate(instruction.address)

    def _translate_jo(self, tb, instruction, in_operands=None, out_operands=None):
        # Jump near if overflow (OF=1).

        oprnd1 = in_operands[0]

        assert oprnd1.size
        assert oprnd1.size in [32, 64]

        if isinstance(in_operands[0], ReilImmediateOperand):
            in_operands[0] = ReilImmediateOperand(in_operands[0].immediate << 8, in_operands[0].size + 8)

        oprnd1 = in_operands[0]

        tb.add(self._builder.gen_jcc(self._flags["of"], oprnd1))

        return tb.instanciate(instruction.address)

    def _translate_jbe(self, tb, instruction, in_operands=None, out_operands=None):
        # Jump near if below or equal (CF=1 or ZF=1).

        oprnd1 = in_operands[0]

        assert oprnd1.size
        assert oprnd1.size in [32, 64]

        if isinstance(in_operands[0], ReilImmediateOperand):
            in_operands[0] = ReilImmediateOperand(in_operands[0].immediate << 8, in_operands[0].size + 8)

        oprnd1 = in_operands[0]

        tmp0 = tb.temporal(1)

        tb.add(self._builder.gen_or(self._flags["cf"], self._flags["zf"], tmp0))
        tb.add(self._builder.gen_jcc(tmp0, oprnd1))

        return tb.instanciate(instruction.address)

    def _translate_jl(self, tb, instruction, in_operands=None, out_operands=None):
        # Jump near if less (SF!=OF).

        oprnd1 = in_operands[0]

        assert oprnd1.size
        assert oprnd1.size in [32, 64]

        if isinstance(in_operands[0], ReilImmediateOperand):
            in_operands[0] = ReilImmediateOperand(in_operands[0].immediate << 8, in_operands[0].size + 8)

        oprnd1 = in_operands[0]

        imm0 = tb.immediate(1, 1)

        tmp0 = tb.temporal(8)
        tmp1 = tb.temporal(1)
        tmp2 = tb.temporal(1)

        tb.add(self._builder.gen_sub(self._flags["sf"], self._flags["of"], tmp0))
        tb.add(self._builder.gen_bisz(tmp0, tmp1))
        tb.add(self._builder.gen_xor(tmp1, imm0, tmp2))
        tb.add(self._builder.gen_jcc(tmp2, oprnd1))

        return tb.instanciate(instruction.address)

    def _translate_je(self, tb, instruction, in_operands=None, out_operands=None):
        # Jump near if equal (ZF=1).

        oprnd1 = in_operands[0]

        assert oprnd1.size
        assert oprnd1.size in [32, 64]

        if isinstance(in_operands[0], ReilImmediateOperand):
            in_operands[0] = ReilImmediateOperand(in_operands[0].immediate << 8, in_operands[0].size + 8)

        oprnd1 = in_operands[0]

        tb.add(self._builder.gen_jcc(self._flags["zf"], oprnd1))

        return tb.instanciate(instruction.address)

    def _translate_js(self, tb, instruction, in_operands=None, out_operands=None):
        # Jump near if sign (SF=1).

        oprnd1 = in_operands[0]

        assert oprnd1.size
        assert oprnd1.size in [32, 64]

        if isinstance(in_operands[0], ReilImmediateOperand):
            in_operands[0] = ReilImmediateOperand(in_operands[0].immediate << 8, in_operands[0].size + 8)

        oprnd1 = in_operands[0]

        tb.add(self._builder.gen_jcc(self._flags["sf"], oprnd1))

        return tb.instanciate(instruction.address)

    def _translate_jg(self, tb, instruction, in_operands=None, out_operands=None):
        # Jump near if greater (ZF=0 and SF=OF).

        oprnd1 = in_operands[0]

        assert oprnd1.size
        assert oprnd1.size in [32, 64]

        if isinstance(in_operands[0], ReilImmediateOperand):
            in_operands[0] = ReilImmediateOperand(in_operands[0].immediate << 8, in_operands[0].size + 8)

        oprnd1 = in_operands[0]

        imm0 = tb.immediate(1, 1)

        tmp0 = tb.temporal(8)
        tmp1 = tb.temporal(1)
        tmp2 = tb.temporal(1)
        tmp3 = tb.temporal(1)

        tb.add(self._builder.gen_sub(self._flags["sf"], self._flags["of"], tmp0))
        tb.add(self._builder.gen_bisz(tmp0, tmp1))
        tb.add(self._builder.gen_xor(self._flags["zf"], imm0, tmp2))
        tb.add(self._builder.gen_and(tmp1, tmp2, tmp3))
        tb.add(self._builder.gen_jcc(tmp3, oprnd1))

        return tb.instanciate(instruction.address)

    def _translate_jge(self, tb, instruction, in_operands=None, out_operands=None):
        # Jump near if greater or equal (SF=OF).

        oprnd1 = in_operands[0]

        assert oprnd1.size
        assert oprnd1.size in [32, 64]

        if isinstance(in_operands[0], ReilImmediateOperand):
            in_operands[0] = ReilImmediateOperand(in_operands[0].immediate << 8, in_operands[0].size + 8)

        oprnd1 = in_operands[0]

        tmp0 = tb.temporal(8)
        tmp1 = tb.temporal(1)

        tb.add(self._builder.gen_sub(self._flags["sf"], self._flags["of"], tmp0))
        tb.add(self._builder.gen_bisz(tmp0, tmp1))
        tb.add(self._builder.gen_jcc(tmp1, oprnd1))

        return tb.instanciate(instruction.address)

    def _translate_jae(self, tb, instruction, in_operands=None, out_operands=None):
        # Jump near if above or equal (CF=0).

        oprnd1 = in_operands[0]

        assert oprnd1.size
        assert oprnd1.size in [32, 64]

        if isinstance(in_operands[0], ReilImmediateOperand):
            in_operands[0] = ReilImmediateOperand(in_operands[0].immediate << 8, in_operands[0].size + 8)

        oprnd1 = in_operands[0]

        tmp0 = tb.temporal(1)

        tb.add(self._builder.gen_bisz(self._flags["cf"], tmp0))
        tb.add(self._builder.gen_jcc(tmp0, oprnd1))

        return tb.instanciate(instruction.address)

    def _translate_jno(self, tb, instruction, in_operands=None, out_operands=None):
        # Jump near if not overflow (OF=0).

        oprnd1 = in_operands[0]

        assert oprnd1.size
        assert oprnd1.size in [32, 64]

        if isinstance(in_operands[0], ReilImmediateOperand):
            in_operands[0] = ReilImmediateOperand(in_operands[0].immediate << 8, in_operands[0].size + 8)

        oprnd1 = in_operands[0]

        tmp0 = tb.temporal(1)

        tb.add(self._builder.gen_bisz(self._flags["of"], tmp0))
        tb.add(self._builder.gen_jcc(tmp0, oprnd1))

        return tb.instanciate(instruction.address)

    def _translate_jns(self, tb, instruction, in_operands=None, out_operands=None):
        # Jump near if not sign (SF=0).

        oprnd1 = in_operands[0]

        assert oprnd1.size
        assert oprnd1.size in [32, 64]

        if isinstance(in_operands[0], ReilImmediateOperand):
            in_operands[0] = ReilImmediateOperand(in_operands[0].immediate << 8, in_operands[0].size + 8)

        oprnd1 = in_operands[0]

        tmp0 = tb.temporal(1)

        tb.add(self._builder.gen_bisz(self._flags["sf"], tmp0))
        tb.add(self._builder.gen_jcc(tmp0, oprnd1))

        return tb.instanciate(instruction.address)

    def _translate_jb(self, tb, instruction, in_operands=None, out_operands=None):
        # Jump near if below (CF=1).

        oprnd1 = in_operands[0]

        assert oprnd1.size
        assert oprnd1.size in [32, 64]

        if isinstance(in_operands[0], ReilImmediateOperand):
            in_operands[0] = ReilImmediateOperand(in_operands[0].immediate << 8, in_operands[0].size + 8)

        oprnd1 = in_operands[0]

        tb.add(self._builder.gen_jcc(self._flags["cf"], oprnd1))

        return tb.instanciate(instruction.address)

    def _translate_jle(self, tb, instruction, in_operands=None, out_operands=None):
        # Jump near if less or equal (ZF=1 or SF!=OF).

        oprnd1 = in_operands[0]

        assert oprnd1.size
        assert oprnd1.size in [32, 64]

        if isinstance(in_operands[0], ReilImmediateOperand):
            in_operands[0] = ReilImmediateOperand(in_operands[0].immediate << 8, in_operands[0].size + 8)

        oprnd1 = in_operands[0]

        imm0 = tb.immediate(1, 1)

        tmp0 = tb.temporal(8)
        tmp1 = tb.temporal(1)
        tmp2 = tb.temporal(1)
        tmp3 = tb.temporal(1)

        tb.add(self._builder.gen_sub(self._flags["sf"], self._flags["of"], tmp0))
        tb.add(self._builder.gen_bisz(tmp0, tmp1))
        tb.add(self._builder.gen_xor(tmp1, imm0, tmp2))
        tb.add(self._builder.gen_or(tmp2, self._flags["zf"], tmp3))
        tb.add(self._builder.gen_jcc(tmp3, oprnd1))

        return tb.instanciate(instruction.address)

    def _translate_jz(self, tb, instruction, in_operands=None, out_operands=None):
        # Jump near if 0 (ZF=1).

        oprnd1 = in_operands[0]

        assert oprnd1.size
        assert oprnd1.size in [32, 64]

        if isinstance(in_operands[0], ReilImmediateOperand):
            in_operands[0] = ReilImmediateOperand(in_operands[0].immediate << 8, in_operands[0].size + 8)

        oprnd1 = in_operands[0]

        tb.add(self._builder.gen_jcc(self._flags["zf"], oprnd1))

        return tb.instanciate(instruction.address)

    def _translate_jne(self, tb, instruction, in_operands=None, out_operands=None):
        # Jump near if not equal (ZF=0).

        oprnd1 = in_operands[0]

        assert oprnd1.size
        assert oprnd1.size in [32, 64]

        if isinstance(in_operands[0], ReilImmediateOperand):
            in_operands[0] = ReilImmediateOperand(in_operands[0].immediate << 8, in_operands[0].size + 8)

        oprnd1 = in_operands[0]

        imm0 = tb.immediate(1, 1)

        tmp0 = tb.temporal(1)

        tb.add(self._builder.gen_xor(self._flags["zf"], imm0, tmp0))
        tb.add(self._builder.gen_jcc(tmp0, oprnd1))

        return tb.instanciate(instruction.address)

    def _translate_jnz(self, tb, instruction, in_operands=None, out_operands=None):
        # Jump near if not zero (ZF=0).

        oprnd1 = in_operands[0]

        assert oprnd1.size
        assert oprnd1.size in [32, 64]

        if isinstance(in_operands[0], ReilImmediateOperand):
            in_operands[0] = ReilImmediateOperand(in_operands[0].immediate << 8, in_operands[0].size + 8)

        oprnd1 = in_operands[0]

        imm0 = tb.immediate(1, 1)

        tmp0 = tb.temporal(1)

        tb.add(self._builder.gen_xor(self._flags["zf"], imm0, tmp0))
        tb.add(self._builder.gen_jcc(tmp0, oprnd1))

        return tb.instanciate(instruction.address)

    def _translate_jnbe(self, tb, instruction, in_operands=None, out_operands=None):
        # Jump near if not below or equal (CF=0 and ZF=0).

        oprnd1 = in_operands[0]

        assert oprnd1.size
        assert oprnd1.size in [32, 64]

        if isinstance(in_operands[0], ReilImmediateOperand):
            in_operands[0] = ReilImmediateOperand(in_operands[0].immediate << 8, in_operands[0].size + 8)

        oprnd1 = in_operands[0]

        imm0 = tb.immediate(1, 1)

        tmp0 = tb.temporal(1)
        tmp1 = tb.temporal(1)
        tmp2 = tb.temporal(1)

        tb.add(self._builder.gen_xor(self._flags["cf"], imm0, tmp0))
        tb.add(self._builder.gen_xor(self._flags["zf"], imm0, tmp1))
        tb.add(self._builder.gen_and(tmp0, tmp1, tmp2))
        tb.add(self._builder.gen_jcc(tmp2, oprnd1))

        return tb.instanciate(instruction.address)

    def _translate_jc(self, tb, instruction, in_operands=None, out_operands=None):
        # Jump near if carry (CF=1).

        oprnd1 = in_operands[0]

        assert oprnd1.size
        assert oprnd1.size in [32, 64]

        if isinstance(in_operands[0], ReilImmediateOperand):
            in_operands[0] = ReilImmediateOperand(in_operands[0].immediate << 8, in_operands[0].size + 8)

        oprnd1 = in_operands[0]

        tb.add(self._builder.gen_jcc(self._flags["cf"], oprnd1))

        return tb.instanciate(instruction.address)

    def _translate_jnc(self, tb, instruction, in_operands=None, out_operands=None):
        # Jump near if not carry (CF=0).

        oprnd1 = in_operands[0]

        assert oprnd1.size
        assert oprnd1.size in [32, 64]

        if isinstance(in_operands[0], ReilImmediateOperand):
            in_operands[0] = ReilImmediateOperand(in_operands[0].immediate << 8, in_operands[0].size + 8)

        oprnd1 = in_operands[0]

        imm0 = tb.immediate(1, 1)

        tmp0 = tb.temporal(1)

        tb.add(self._builder.gen_xor(self._flags["cf"], imm0, tmp0))
        tb.add(self._builder.gen_jcc(tmp0, oprnd1))

        return tb.instanciate(instruction.address)

    def _translate_jecxz(self, tb, instruction, in_operands=None, out_operands=None):
        # Jump short if ECX register is 0.

        oprnd1 = in_operands[0]

        assert oprnd1.size
        assert oprnd1.size in [32, 64]

        if isinstance(in_operands[0], ReilImmediateOperand):
            in_operands[0] = ReilImmediateOperand(in_operands[0].immediate << 8, in_operands[0].size + 8)

        oprnd1 = in_operands[0]

        tmp0 = tb.temporal(1)

        ecx = ReilRegisterOperand("ecx", 32)

        tb.add(self._builder.gen_bisz(ecx, tmp0))
        tb.add(self._builder.gen_jcc(tmp0, oprnd1))

        return tb.instanciate(instruction.address)

    def _translate_call(self, tb, instruction, in_operands=None, out_operands=None):
        # Flags Affected
        # All flags are affected if a task switch occurs; no flags are
        # affected if a task switch does not occur.

        oprnd1 = in_operands[0]

        assert oprnd1.size
        assert oprnd1.size in [32, 64]

        if isinstance(in_operands[0], ReilImmediateOperand):
            in_operands[0] = ReilImmediateOperand(in_operands[0].immediate << 8, in_operands[0].size + 8)

        oprnd1 = in_operands[0]

        imm1 = tb.immediate(1, 1)
        size = tb.immediate(instruction.size, self._sp.size)

        tmp0 = tb.temporal(self._sp.size)
        tmp1 = tb.temporal(self._sp.size)

        tb.add(self._builder.gen_sub(self._sp, self._ws, tmp0))
        tb.add(self._builder.gen_str(tmp0, self._sp))
        tb.add(self._builder.gen_add(self._ip, size, tmp1))
        tb.add(self._builder.gen_stm(tmp1, self._sp))
        tb.add(self._builder.gen_jcc(imm1, oprnd1))

        return tb.instanciate(instruction.address)

    def _translate_ret(self, tb, instruction, in_operands=None, out_operands=None):
        # Flags Affected
        # None.

        tmp0 = tb.temporal(self._sp.size)
        tmp1 = tb.temporal(self._sp.size)

        tb.add(self._builder.gen_ldm(self._sp, tmp1))
        tb.add(self._builder.gen_add(self._sp, self._ws, tmp0))
        tb.add(self._builder.gen_str(tmp0, self._sp))

        # Free stack.
        if len(in_operands) > 0:
            oprnd1 = in_operands[0]

            assert oprnd1.size
            assert oprnd1.size == 16
            assert isinstance(oprnd1, ReilImmediateOperand)

            imm0 = tb.immediate(oprnd1.immediate & (2**self._sp.size -1), self._sp.size)

            tmp2 = tb.temporal(self._sp.size)

            tb.add(self._builder.gen_add(self._sp, imm0, tmp2))
            tb.add(self._builder.gen_str(tmp2, self._sp))

		# TODO: Replace RET instruction with JCC [BYTE 0x1, EMPTY, {D,Q}WORD %0]
        tb.add(self._builder.gen_ret())

        return tb.instanciate(instruction.address)

# "String Instructions"
# ============================================================================ #
    # def _translate_movsb(self, tb, instruction, in_operands=None, out_operands=None):

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
    def _translate_leave(self, tb, instruction, in_operands=None, out_operands=None):
        # Flags Affected
        # None.

        tmp0 = tb.temporal(self._sp.size)

        tb.add(self._builder.gen_str(self._bp, self._sp))
        tb.add(self._builder.gen_ldm(self._sp, self._bp))
        tb.add(self._builder.gen_add(self._sp, self._ws, tmp0))
        tb.add(self._builder.gen_str(tmp0, self._sp))

        return tb.instanciate(instruction.address)

# "Flag Control (EFLAG) Instructions"
# ============================================================================ #
    def _translate_cld(self, tb, instruction, in_operands=None, out_operands=None):
        # Flags Affected
        # The DF flag is set to 0. The CF, OF, ZF, SF, AF, and PF flags
        # are unaffected.

        self._clear_flag(tb, self._flags["df"])

        return tb.instanciate(instruction.address)

    def _translate_clc(self, tb, instruction, in_operands=None, out_operands=None):
        # Flags Affected
        # The CF flag is set to 0. The OF, ZF, SF, AF, and PF flags are
        # unaffected.

        self._clear_flag(tb, self._flags["cf"])

        return tb.instanciate(instruction.address)

    def _translate_stc(self, tb, instruction, in_operands=None, out_operands=None):
        # Flags Affected
        # The CF flag is set. The OF, ZF, SF, AF, and PF flags are
        # unaffected.

        self._set_flag(tb, self._flags["cf"])

        return tb.instanciate(instruction.address)

# "Segment Register Instructions"
# ============================================================================ #

# "Miscellaneous Instructions"
# ============================================================================ #
    def _translate_lea(self, tb, instruction, in_operands=None, out_operands=None):
        # Flags Affected
        # None.

        oprnd1 = in_operands[0]
        oprnd2 = out_operands[0]

        assert oprnd1.size and oprnd2.size
        assert oprnd1.size == oprnd2.size

        tb.add(self._builder.gen_str(oprnd1, oprnd2))

        return tb.instanciate(instruction.address)

    def _translate_nop(self, tb, instruction, in_operands=None, out_operands=None):
        # Flags Affected
        # None.

        tb.add(self._builder.gen_nop())

        return tb.instanciate(instruction.address)

# "Random Number Generator Instruction"
# ============================================================================ #

# "Misc"
# ============================================================================ #
    def _translate_hlt(self, tb, instruction, in_operands=None, out_operands=None):
        # Flags Affected
        # None.

        tb.add(self._builder.gen_unkn())

        return tb.instanciate(instruction.address)
