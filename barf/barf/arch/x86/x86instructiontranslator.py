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
}

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
        # # If the instruction translation is not in cache, translate it
        # # and add it to the cache.
        # if not instruction.mnemonic in self.translation_cache:
        #     # Retrieve translation function.
        #     translator_name = "_translate_" + instruction.mnemonic
        #     translator_fn = getattr(self, translator_name, self._not_implemented)

        #     # Add instruction translation to the cache.
        #     self.translation_cache[instruction.mnemonic] = translator_fn(instruction)

        # # Retrieve instruction translation from the cache.
        # instrs = self.translation_cache[instruction.mnemonic]

        # ==================================================================== #

        # Retrieve translation function.
        translator_name = "_translate_" + instruction.mnemonic
        translator_fn = getattr(self, translator_name, self._not_implemented)

        instrs = translator_fn(instruction, in_operands, out_operands)

        # print map(str, instrs)

        # ==================================================================== #

        # Instanciate the translation with the data (sources and
        # destinations) of the instruction being translated.
        translation = self._instanciate_translation(instrs, in_operands, out_operands)

        return translation

    @property
    def translation_mode(self):
        return self._translation_mode

    @translation_mode.setter
    def translation_mode(self, value):
        self._translation_mode = value

# ============================================================================ #

    def _not_implemented(self, instruction, in_operands, out_operands):
        raise NotImplementedError("Instruction Not Implemented")

    @add_register_size
    def _instanciate_translation(self, instrs, in_operands, out_operands):
        """Instanciate an instruction translation.

        Each translation is a template translation. This means that there are
        some operands in the REIL instructions that need to be set according
        to the instruction being translate. For example, the x86 ADD instruction
        would be translated to the "ADD $0, $1, #0" REIL instruction. In this
        case, $0 and $1 mean first and second source operands and #0 its the
        destination operand. So, if we translate "ADD eax, ebx" the translation
        would be "ADD $0, $1, #0" and the instanciation of that translation
        would be "ADD eax, ebx, eax".

        Replacement types
        -----------------

            * $ : in operand
            * # : out operand
            * % : global temporary register
            * ? : local temporary register

        Parameters
        ----------

        :param instrs: REIL instructions
        :type instrs: a list of ReilInstruction

        :param in_operands: source operands
        :type in_operands: a list of ReilOperand

        :param out_operands: destination operands
        :type out_operands: a list of ReilOperand
        """

        # TODO: Is '?' placeholder really necessary?

        auto_reg_mapper = {}
        local_reg_mapper = {}

        # Create a copy of the instructions to "instantiate".
        new_instrs = copy.deepcopy(instrs)

        # Iterate instructions and "instantiate" operands where
        # necessary.
        for instr in new_instrs:
            for index, operand in enumerate(instr.operands):
                # If the operand has been tagged, it means it is a placeholder
                # operand and needs to be "instantiated".
                if operand.tag:
                    replacement_type = operand.tag[0]

                    if replacement_type == "?":
                        # Local Temporary Register.

                        # Extract temporary register name and index.
                        locality, index = (operand.tag[1:]).split('.')
                        index = int(index, 10)

                        if not locality in local_reg_mapper.keys():
                            local_reg_mapper[locality] = {}

                        if not index in local_reg_mapper[locality]:
                            local_reg_mapper[locality][index] = self.ir_name_generator.get_next()

                        # Set name accordingly.
                        operand.name = local_reg_mapper[locality][index]
                    elif replacement_type == "%":
                        # Gobal Temporary Register

                        # Extract temporary register index.
                        oprnd_index = int(operand.tag[1:], 10)

                        if not oprnd_index in auto_reg_mapper.keys():
                            auto_reg_mapper[oprnd_index] = self.ir_name_generator.get_next()

                        # Set name accordingly.
                        operand.name = auto_reg_mapper[oprnd_index]
                    elif replacement_type in ["$", "#"]:
                        # Source/Destination Registers
                        oprnd_index = int(operand.tag[1:], 10)

                        operands = in_operands if replacement_type == "$" else out_operands

                        # Set operands accordingly.
                        # print map(str, operands)
                        # print oprnd_index

                        if type(operands[oprnd_index]) == ReilRegisterOperand:
                            operand.name = operands[oprnd_index].name
                        elif type(operands[oprnd_index]) == ReilImmediateOperand:
                            if not isinstance(operand, ReilImmediateOperand):
                                operand = ReilImmediateOperand(operands[oprnd_index].immediate)

                                instr.operands[index] = operand
                            else:
                                operand.immediate = operands[oprnd_index].immediate
                        else:
                            raise Exception("Invalid source type : %s" % type(operands[oprnd_index]))

                        # print map(str, operands)
                        # print "size", operands[oprnd_index].size, operand.size

                        if operands[oprnd_index].size:
                            operand.size = operands[oprnd_index].size
                    else:
                        raise Exception()

        return new_instrs

# Translators
# ============================================================================ #
# ============================================================================ #

# "Flags"
# ============================================================================ #
    def _translate_af(self, oprnd1, oprnd2, oprnd_size, result, result_size):
        # TODO: Implement
        return []

    def _translate_pf(self, oprnd1, oprnd2, oprnd_size, result, result_size):
        # TODO: Implement
        return []

    def _translate_sf(self, oprnd1, oprnd2, oprnd_size, result, result_size):
        result_size_str = size_str[result_size]

        trans  = ["and [{0}   {2}, {0} {1}, {0} ?sf.0]".format(result_size_str, 2**(oprnd_size-1), result)]       # filter sign bit
        trans += ["bsh [{0} ?sf.0, {0} {1}, BYTE   sf]".format(result_size_str, -(oprnd_size-1))]                 # extract sign bit

        return trans

    def _translate_of(self, oprnd1, oprnd2, oprnd_size, result, result_size):
        oprnd_size_str  = size_str[oprnd_size]
        result_size_str = size_str[result_size]

        trans  = ["and [{0}   {2}, {0}   {1}, {0} ?of.0]".format(oprnd_size_str, 2**(oprnd_size-1), oprnd1)]                      # filter sign bit oprnd 1
        trans += ["and [{0}   {2}, {0}   {1}, {0} ?of.1]".format(oprnd_size_str, 2**(oprnd_size-1), oprnd2)]                      # filter sign bit oprnd 2
        trans += ["and [{0}   {2}, {0}   {1}, {3} ?of.2]".format(result_size_str, 2**(oprnd_size-1), result, oprnd_size_str)]     # filter sign bit result
        trans += ["xor [{0} ?of.0, {0} ?of.1, {0} ?of.3]".format(oprnd_size_str)]                                                 # sign bit oprnd1 ^ sign bit oprnd2
        trans += ["xor [{0} ?of.3, {0}     1, {0} ?of.4]".format(oprnd_size_str)]                                                 # sign bit oprnd1 ^ sign bit oprnd2 ^ 1
        trans += ["xor [{0} ?of.0, {0} ?of.2, {0} ?of.5]".format(oprnd_size_str)]                                                 # sign bit oprnd1 ^ sign bit result
        trans += ["and [{0} ?of.4, {0} ?of.5, {0} ?of.6]".format(oprnd_size_str)]                                                 # (sign bit oprnd1 ^ sign bit oprnd2 ^ 1) & (sign bit oprnd1 ^ sign bit result)
        trans += ["bsh [{0} ?of.6, {0}   {1}, BYTE   of]".format(oprnd_size_str, -(oprnd_size-1))]

        return trans

    def _translate_cf(self, oprnd1, oprnd2, oprnd_size, result, result_size):
        result_size_str = size_str[result_size]

        trans  = ["and [{0}   {2}, {0} {1}, {0} ?cf.0]".format(result_size_str, 2**oprnd_size, result)]           # filter carry bit
        trans += ["bsh [{0} ?cf.0, {0} {1}, BYTE   cf]".format(result_size_str, -oprnd_size)]

        return trans

    def _translate_zf(self, oprnd1, oprnd2, oprnd_size, result, result_size):
        result_size_str = size_str[result_size]

        trans  = ["and  [{0}   {2}, {0} {1}, {0} ?zf.0]".format(result_size_str, (2**oprnd_size)-1, result)]      # filter low part of result
        trans += ["bisz [{0} ?zf.0,   EMPTY, BYTE   zf]".format(result_size_str)]

        return trans

    def _undefine_flag(self, flag):
        trans = ["undef [EMPTY, EMPTY, BYTE {0}]".format(flag)]

        return trans

    def _clear_flag(self, flag):
        trans = ["str [BYTE 0, EMPTY, BYTE {0}]".format(flag)]

        return trans

# "Data Transfer Instructions"
# ============================================================================ #
    def _translate_mov(self, instruction, in_operands=None, out_operands=None):
        # Flags Affected
        # None.

        oprnd1 = in_operands[0]
        oprnd2 = in_operands[0]

        assert oprnd1.size and oprnd2.size
        assert oprnd1.size == oprnd2.size

        trans = ["str [$0, EMPTY, #0]"]

        return self._ir_parser.parse(trans, False)

    def _translate_movzx(self, instruction, in_operands=None, out_operands=None):
        # Flags Affected
        # None.

        oprnd1 = in_operands[0]
        oprnd2 = out_operands[0]

        assert oprnd1.size and oprnd2.size
        assert oprnd2.size > oprnd1.size

        trans = ["str [$0, EMPTY, #0]"]

        return self._ir_parser.parse(trans, False)

    def _translate_xchg(self, instruction, in_operands=None, out_operands=None):
        # Flags Affected
        # None.

        oprnd1 = in_operands[0]
        oprnd2 = in_operands[1]
        oprnd3 = out_operands[0]
        oprnd4 = out_operands[1]

        assert oprnd1.size and oprnd2.size
        assert oprnd1.size == oprnd2.size and oprnd3.size == oprnd4.size

        trans  = ["str [$0, EMPTY, %0]"]
        trans += ["str [$1, EMPTY, %1]"]
        trans += ["str [%0, EMPTY, #1]"]
        trans += ["str [%1, EMPTY, #0]"]

        return self._ir_parser.parse(trans, False)

    def _translate_push(self, instruction, in_operands=None, out_operands=None):
        # Flags Affected
        # None.

        oprnd1 = in_operands[0]

        assert oprnd1.size
        assert oprnd1.size in [32, 64]

        if self.architecture_mode == ARCH_X86_MODE_32:
            # push r32 == sub esp, 4 ; mov [esp], r32
            trans  = ["sub [DWORD esp, DWORD 4, DWORD  %0]"]
            trans += ["str [DWORD  %0,   EMPTY, DWORD esp]"]
            trans += ["stm [DWORD  $0,   EMPTY, DWORD esp]"]
        elif self.architecture_mode == ARCH_X86_MODE_64:
            # push r64 == sub rsp, 8 ; mov [rsp], r46
            trans  = ["sub [QWORD rsp, QWORD 8, QWORD  %0]"]
            trans += ["str [QWORD  %0,   EMPTY, QWORD rsp]"]
            trans += ["stm [QWORD  $0,   EMPTY, QWORD rsp]"]

        return self._ir_parser.parse(trans, False)

    def _translate_pop(self, instruction, in_operands=None, out_operands=None):
        # Flags Affected
        # None.

        oprnd1 = out_operands[0]

        assert oprnd1.size
        assert oprnd1.size in [32, 64]

        if self.architecture_mode == ARCH_X86_MODE_32:
            trans  = ["ldm [DWORD esp,   EMPTY, DWORD  #0]"]
            trans += ["add [DWORD esp, DWORD 4, DWORD  %0]"]
            trans += ["str [DWORD  %0,   EMPTY, DWORD esp]"]
        elif self.architecture_mode == ARCH_X86_MODE_64:
            trans  = ["ldm [QWORD rsp,   EMPTY, QWORD  #0]"]
            trans += ["add [QWORD rsp, QWORD 8, QWORD  %0]"]
            trans += ["str [QWORD  %0,   EMPTY, QWORD rsp]"]

        return self._ir_parser.parse(trans, False)

# "Binary Arithmetic Instructions"
# ============================================================================ #
    def _translate_add(self, instruction, in_operands=None, out_operands=None):
        # Flags Affected
        # The OF, SF, ZF, AF, CF, and PF flags are set according to the
        # result.

        oprnd1 = in_operands[0]
        oprnd2 = in_operands[1]

        assert oprnd1.size and oprnd2.size
        assert oprnd1.size == oprnd2.size

        oprnd_size = oprnd1.size
        result_size = 2*oprnd_size

        oprnd_size_str  = size_str[oprnd_size]
        result_size_str = size_str[result_size]

        trans  = ["add [{0} $0, {0} $1, {1} %0]".format(oprnd_size_str, result_size_str)]

        if self._translation_mode == FULL_TRANSLATION:
            # Flags : OF, SF, ZF, AF, CF, PF
            trans += self._translate_of("$0", "$1", oprnd_size, "%0", result_size)
            trans += self._translate_sf("$0", "$1", oprnd_size, "%0", result_size)
            trans += self._translate_zf("$0", "$1", oprnd_size, "%0", result_size)
            trans += self._translate_af("$0", "$1", oprnd_size, "%0", result_size)
            trans += self._translate_cf("$0", "$1", oprnd_size, "%0", result_size)
            trans += self._translate_pf("$0", "$1", oprnd_size, "%0", result_size)

        trans += ["str [%0, EMPTY, #0]"]

        return self._ir_parser.parse(trans, False)

    def _translate_adc(self, instruction, in_operands=None, out_operands=None):
        # Flags Affected
        # The OF, SF, ZF, AF, CF, and PF flags are set according to the result.

        oprnd1 = in_operands[0]
        oprnd2 = in_operands[1]

        assert oprnd1.size and oprnd2.size
        assert oprnd1.size == oprnd2.size

        oprnd_size = oprnd1.size
        result_size = 2*oprnd_size

        oprnd_size_str  = size_str[oprnd_size]
        result_size_str = size_str[result_size]

        trans  = ["add [{0}  $0, {0} $1, {1} %0]".format(oprnd_size_str, result_size_str)]
        trans += ["str [BYTE cf,  EMPTY, {0} %1]".format(result_size_str)]
        trans += ["add [{0}  %0, {0} %1, {0} %2]".format(result_size_str)]

        if self._translation_mode == FULL_TRANSLATION:
            # Flags : OF, SF, ZF, AF, CF, PF
            trans += self._translate_of("$0", "$1", oprnd_size, "%2", result_size)
            trans += self._translate_sf("$0", "$1", oprnd_size, "%2", result_size)
            trans += self._translate_zf("$0", "$1", oprnd_size, "%2", result_size)
            trans += self._translate_af("$0", "$1", oprnd_size, "%2", result_size)
            trans += self._translate_cf("$0", "$1", oprnd_size, "%2", result_size)
            trans += self._translate_pf("$0", "$1", oprnd_size, "%2", result_size)

        trans += ["str [%2, EMPTY, #0]"]

        return self._ir_parser.parse(trans, False)

    def _translate_sub(self, instruction, in_operands=None, out_operands=None):
        # Flags Affected
        # The OF, SF, ZF, AF, PF, and CF flags are set according to the
        # result.

        oprnd1 = in_operands[0]
        oprnd2 = in_operands[1]

        assert oprnd1.size and oprnd2.size
        assert oprnd1.size == oprnd2.size

        oprnd_size = oprnd1.size
        result_size = 2*oprnd_size

        oprnd_size_str  = size_str[oprnd_size]
        result_size_str = size_str[result_size]

        trans  = ["sub [{0} $0, {0} $1, {1} %0]".format(oprnd_size_str, result_size_str)]

        if self._translation_mode == FULL_TRANSLATION:
            # Flags : OF, SF, ZF, AF, PF, CF
            trans += self._translate_of("$0", "$1", oprnd_size, "%0", result_size)
            trans += self._translate_sf("$0", "$1", oprnd_size, "%0", result_size)
            trans += self._translate_zf("$0", "$1", oprnd_size, "%0", result_size)
            trans += self._translate_af("$0", "$1", oprnd_size, "%0", result_size)
            trans += self._translate_pf("$0", "$1", oprnd_size, "%0", result_size)
            trans += self._translate_cf("$0", "$1", oprnd_size, "%0", result_size)

        trans += ["str [%0, EMPTY, #0]"]

        return self._ir_parser.parse(trans, False)

    def _translate_sbb(self, instruction, in_operands=None, out_operands=None):
        # Flags Affected
        # The OF, SF, ZF, AF, PF, and CF flags are set according to the
        # result.

        oprnd1 = in_operands[0]
        oprnd2 = in_operands[1]

        assert oprnd1.size and oprnd2.size
        assert oprnd1.size == oprnd2.size

        oprnd_size = oprnd1.size
        result_size = 2*oprnd_size

        oprnd_size_str  = size_str[oprnd_size]
        result_size_str = size_str[result_size]

        trans  = ["sub [{0}  $0, {0} $1, {1} %0]".format(oprnd_size_str, result_size_str)]
        trans += ["str [BYTE cf,  EMPTY, {0} %1]".format(result_size_str)]
        trans += ["sub [{0}  %0, {0} %1, {0} %2]".format(result_size_str)]

        if self._translation_mode == FULL_TRANSLATION:
            # Flags : OF, SF, ZF, AF, PF, CF
            trans += self._translate_of("$0", "$1", oprnd_size, "%2", result_size)
            trans += self._translate_sf("$0", "$1", oprnd_size, "%2", result_size)
            trans += self._translate_zf("$0", "$1", oprnd_size, "%2", result_size)
            trans += self._translate_af("$0", "$1", oprnd_size, "%2", result_size)
            trans += self._translate_pf("$0", "$1", oprnd_size, "%2", result_size)
            trans += self._translate_cf("$0", "$1", oprnd_size, "%2", result_size)

        trans += ["str [%2, EMPTY, #0]"]

        return self._ir_parser.parse(trans, False)

    def _translate_mul(self, instruction, in_operands=None, out_operands=None):
        # Flags Affected
        # The OF and CF flags are set to 0 if the upper half of the
        # result is 0; otherwise, they are set to 1. The SF, ZF, AF, and
        # PF flags are undefined.

        oprnd1 = in_operands[0]
        oprnd2 = in_operands[1]

        assert oprnd1.size and oprnd2.size
        assert oprnd1.size == oprnd2.size

        oprnd_size = oprnd1.size
        result_size = 2*oprnd_size

        oprnd_size_str  = size_str[oprnd_size]
        result_size_str = size_str[result_size]

        trans  = ["mul [{0} $0, {0}  $1, {1} %0]".format(oprnd_size_str, result_size_str)]
        trans += ["bsh [{0} %0, {0} {1}, {2} #0]".format(result_size_str, -oprnd_size, oprnd_size_str)]   # save high part
        trans += ["str [{0} %0,   EMPTY, {1} #1]".format(result_size_str, oprnd_size_str)]                # save low part

        if self._translation_mode == FULL_TRANSLATION:
            # Flags : OF, CF
            trans += ["bsh  [{0}     %0, {0} {1}, {2}  ?of.0]".format(result_size_str, -oprnd_size, oprnd_size_str)]
            trans += ["bisz [{0}  ?of.0,   EMPTY, BYTE ?of.1]".format(result_size_str)]
            trans += ["xor  [BYTE ?of.1,  BYTE 1, BYTE    of]"]
            trans += ["xor  [BYTE ?of.1,  BYTE 1, BYTE    cf]"]

            # Flags : SF, ZF, AF, PF
            trans += self._undefine_flag("sf")
            trans += self._undefine_flag("zf")
            trans += self._undefine_flag("af")
            trans += self._undefine_flag("pf")

        return self._ir_parser.parse(trans, False)

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

        oprnd1 = in_operands[0]
        oprnd2 = in_operands[1]

        result = out_operands[0]

        assert oprnd1.size and oprnd2.size and result.size
        assert oprnd1.size == oprnd2.size
        assert oprnd1.size == result.size

        oprnd_size = oprnd1.size
        oprnd2_size = oprnd2.size
        result_size = 2*oprnd_size

        oprnd_size_str  = size_str[oprnd_size]
        oprnd2_size_str = size_str[oprnd2_size]
        result_size_str = size_str[result_size]

        # Extend second source operand to match the size of the first one.
        trans  = ["str [{0} $1,   EMPTY, {1} %0]".format(oprnd2_size_str, oprnd_size_str)]

        # Do multiplication.
        trans += ["mul [{0} $0, {0}  $1, {1} %1]".format(oprnd_size_str, result_size_str)]

        # Save result.
        if len(out_operands) == 1:
            trans += ["str [{0} %1,   EMPTY, {1} #0]".format(result_size_str, oprnd_size_str)]
        elif len(out_operands) == 2:
            trans += ["bsh [{0} %1, {0} {1}, {2} #0]".format(result_size_str, -oprnd_size, oprnd_size_str)]   # save high part
            trans += ["str [{0} %1,   EMPTY, {1} #1]".format(result_size_str, oprnd_size_str)]                # save low part
        else:
            raise Exeption()

        if self._translation_mode == FULL_TRANSLATION:
            # Flags : OF, CF
            # TODO: Implement.

            # Flags : SF, ZF, AF, PF
            trans += self._undefine_flag("sf")
            trans += self._undefine_flag("zf")
            trans += self._undefine_flag("af")
            trans += self._undefine_flag("pf")

        return self._ir_parser.parse(trans, False)

    def _translate_div(self, instruction, in_operands=None, out_operands=None):
        # Flags Affected
        # The CF, OF, SF, ZF, AF, and PF flags are undefined.

        oprnd1 = in_operands[0]
        oprnd2 = in_operands[1]
        oprnd3 = in_operands[2]

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

        # Extend operands to match their size.
        trans  = ["str [{0} $0, EMPTY, {1} %0]".format(oprnd1_size_str, oprnd_size_str)]
        trans += ["str [{0} $1, EMPTY, {1} %1]".format(oprnd2_size_str, oprnd_size_str)]
        trans += ["str [{0} $2, EMPTY, {1} %2]".format(oprnd3_size_str, oprnd_size_str)]

        # Put dividend together.
        trans += ["bsh [{0} %0, {0} {1}, {0} %3]".format(oprnd_size_str, oprnd1_size)]
        trans += ["or  [{0} %3, {0}  %1, {0} %4]".format(oprnd_size_str)]

        # Do division
        trans += ["div [{0} %4, {0}  %2, {0} %5]".format(oprnd_size_str)]
        trans += ["mod [{0} %4, {0}  %2, {0} %6]".format(oprnd_size_str)]
        trans += ["str [{0} %5,   EMPTY, {1} #1]".format(oprnd_size_str, result_size_str)]
        trans += ["str [{0} %6,   EMPTY, {1} #0]".format(oprnd_size_str, result_size_str)]

        if self._translation_mode == FULL_TRANSLATION:
            # Flags : CF, OF, SF, ZF, AF, PF
            trans += self._undefine_flag("cf")
            trans += self._undefine_flag("of")
            trans += self._undefine_flag("sf")
            trans += self._undefine_flag("zf")
            trans += self._undefine_flag("af")
            trans += self._undefine_flag("pf")

        return self._ir_parser.parse(trans, False)

    def _translate_inc(self, instruction, in_operands=None, out_operands=None):
        # Flags Affected
        # The CF flag is not affected. The OF, SF, ZF, AF, and PF flags
        # are set according to the result.

        oprnd1 = in_operands[0]

        assert oprnd1.size

        oprnd_size = oprnd1.size
        result_size = 2*oprnd_size

        oprnd_size_str  = size_str[oprnd_size]
        result_size_str = size_str[result_size]

        trans  = ["add [{0} $0, {0} 1, {1} %0]".format(oprnd_size_str, result_size_str)]

        if self._translation_mode == FULL_TRANSLATION:
            # Flags : OF, SF, ZF, AF, PF
            trans += self._translate_of("$0", "$0", oprnd_size, "%0", result_size)
            trans += self._translate_sf("$0", "$0", oprnd_size, "%0", result_size)
            trans += self._translate_zf("$0", "$0", oprnd_size, "%0", result_size)
            trans += self._translate_af("$0", "$0", oprnd_size, "%0", result_size)
            trans += self._translate_pf("$0", "$0", oprnd_size, "%0", result_size)

        trans += ["str [%0, EMPTY, #0]"]

        return self._ir_parser.parse(trans, False)

    def _translate_dec(self, instruction, in_operands=None, out_operands=None):
        # Flags Affected
        # The CF flag is not affected. The OF, SF, ZF, AF, and PF flags
        # are set according to the result.

        oprnd1 = in_operands[0]

        assert oprnd1.size

        oprnd_size = oprnd1.size
        result_size = 2*oprnd_size

        oprnd_size_str  = size_str[oprnd_size]
        result_size_str = size_str[result_size]

        trans  = ["sub [{0} $0, {0} 1, {1} %0]".format(oprnd_size_str, result_size_str)]

        if self._translation_mode == FULL_TRANSLATION:
            # Flags : OF, SF, ZF, AF, PF
            trans += self._translate_of("$0", "$0", oprnd_size, "%0", result_size)
            trans += self._translate_sf("$0", "$0", oprnd_size, "%0", result_size)
            trans += self._translate_zf("$0", "$0", oprnd_size, "%0", result_size)
            trans += self._translate_af("$0", "$0", oprnd_size, "%0", result_size)
            trans += self._translate_pf("$0", "$0", oprnd_size, "%0", result_size)

        trans += ["str [%0, EMPTY, #0]"]

        return self._ir_parser.parse(trans, False)

    def _translate_neg(self, instruction, in_operands=None, out_operands=None):
        # Flags Affected
        # The CF flag set to 0 if the source operand is 0; otherwise it
        # is set to 1. The OF, SF, ZF, AF, and PF flags are set
        # according to the result.

        oprnd1 = in_operands[0]

        assert oprnd1.size

        oprnd_size = oprnd1.size
        result_size = oprnd_size

        oprnd_size_str  = size_str[oprnd_size]
        result_size_str = size_str[result_size]

        trans  = ["xor [{0} $0, {0} {1}, {0} %0]".format(oprnd_size_str, (2**oprnd_size)-1)]
        trans += ["add [{0} %0, {0}   1, {0} #0]".format(oprnd_size_str)]

        # Flags : CF
        trans += ["bisz [{0}  $0,  EMPTY, BYTE %1]".format(oprnd_size_str)]
        trans += ["xor  [BYTE %1, BYTE 1, BYTE cf]"]

        if self._translation_mode == FULL_TRANSLATION:
            # Flags : OF, SF, ZF, AF, PF
            trans += self._translate_of("$0", "$0", oprnd_size, "#0", result_size)
            trans += self._translate_sf("$0", "$0", oprnd_size, "#0", result_size)
            trans += self._translate_zf("$0", "$0", oprnd_size, "#0", result_size)
            trans += self._translate_af("$0", "$0", oprnd_size, "#0", result_size)
            trans += self._translate_pf("$0", "$0", oprnd_size, "#0", result_size)

        return self._ir_parser.parse(trans, False)

    def _translate_cmp(self, instruction, in_operands=None, out_operands=None):
        # Flags Affected
        # The CF, OF, SF, ZF, AF, and PF flags are set according to the
        # result.

        oprnd1 = in_operands[0]
        oprnd2 = in_operands[1]

        assert oprnd1.size and oprnd2.size
        assert oprnd1.size == oprnd2.size

        oprnd_size = oprnd1.size
        result_size = 2*oprnd_size

        oprnd_size_str  = size_str[oprnd_size]
        result_size_str = size_str[result_size]

        trans  = ["sub [{0} $0, {0} $1, {1} %0]".format(oprnd_size_str, result_size_str)]

        # Flags : CF, OF, SF, ZF, AF, PF
        trans += self._translate_cf("$0", "$1", oprnd_size, "%0", result_size)
        trans += self._translate_of("$0", "$1", oprnd_size, "%0", result_size)
        trans += self._translate_sf("$0", "$1", oprnd_size, "%0", result_size)
        trans += self._translate_zf("$0", "$1", oprnd_size, "%0", result_size)
        trans += self._translate_af("$0", "$1", oprnd_size, "%0", result_size)
        trans += self._translate_pf("$0", "$1", oprnd_size, "%0", result_size)

        return self._ir_parser.parse(trans, False)

# "Decimal Arithmetic Instructions"
# ============================================================================ #

# "Logical Instructions"
# ============================================================================ #
    def _translate_and(self, instruction, in_operands=None, out_operands=None):
        # Flags Affected
        # The OF and CF flags are cleared; the SF, ZF, and PF flags are
        # set according to the result. The state of the AF flag is
        # undefined.

        oprnd1 = in_operands[0]
        oprnd2 = in_operands[1]

        assert oprnd1.size and oprnd2.size
        assert oprnd1.size == oprnd2.size

        oprnd_size = oprnd1.size
        result_size = oprnd_size

        oprnd_size_str  = size_str[oprnd_size]
        result_size_str = size_str[result_size]

        trans  = ["and [{0} $0, {0} $1, {1} #0]".format(oprnd_size_str, result_size_str)]

        if self._translation_mode == FULL_TRANSLATION:
            # Flags : OF, CF
            trans += self._clear_flag("of")
            trans += self._clear_flag("cf")

            # Flags : SF, ZF, PF
            trans += self._translate_sf("$0", "$1", oprnd_size, "#0", result_size)
            trans += self._translate_zf("$0", "$1", oprnd_size, "#0", result_size)
            trans += self._translate_pf("$0", "$1", oprnd_size, "#0", result_size)

            # Flags : AF
            trans += self._undefine_flag("af")

        return self._ir_parser.parse(trans, False)

    def _translate_or(self, instruction, in_operands=None, out_operands=None):
        # Flags Affected
        # The OF and CF flags are cleared; the SF, ZF, and PF flags are
        # set according to the result. The state of the AF flag is
        # undefined.

        oprnd1 = in_operands[0]
        oprnd2 = in_operands[1]

        assert oprnd1.size and oprnd2.size
        assert oprnd1.size == oprnd2.size

        oprnd_size = oprnd1.size
        result_size = oprnd_size

        oprnd_size_str  = size_str[oprnd_size]
        result_size_str = size_str[result_size]

        trans  = ["or [{0} $0, {0} $1, {1} #0]".format(oprnd_size_str, result_size_str)]

        if self._translation_mode == FULL_TRANSLATION:
            # Flags : OF, CF
            trans += self._clear_flag("of")
            trans += self._clear_flag("cf")

            # Flags : SF, ZF, PF
            trans += self._translate_sf("$0", "$1", oprnd_size, "#0", result_size)
            trans += self._translate_zf("$0", "$1", oprnd_size, "#0", result_size)
            trans += self._translate_pf("$0", "$1", oprnd_size, "#0", result_size)

            # Flags : AF
            trans += self._undefine_flag("af")

        return self._ir_parser.parse(trans, False)

    def _translate_xor(self, instruction, in_operands=None, out_operands=None):
        # Flags Affected
        # The OF and CF flags are cleared; the SF, ZF, and PF flags are set
        # according to the result. The state of the AF flag is
        # undefined.

        oprnd1 = in_operands[0]
        oprnd2 = in_operands[1]

        assert oprnd1.size and oprnd2.size
        assert oprnd1.size == oprnd2.size

        oprnd_size = oprnd1.size
        result_size = oprnd_size

        oprnd_size_str  = size_str[oprnd_size]
        result_size_str = size_str[result_size]

        trans  = ["xor [{0} $0, {0} $1, {1} #0]".format(oprnd_size_str, result_size_str)]

        if self._translation_mode == FULL_TRANSLATION:
            # Flags : OF, CF
            trans += self._clear_flag("of")
            trans += self._clear_flag("cf")

            # Flags : SF, ZF, PF
            trans += self._translate_sf("$0", "$1", oprnd_size, "#0", result_size)
            trans += self._translate_zf("$0", "$1", oprnd_size, "#0", result_size)
            trans += self._translate_pf("$0", "$1", oprnd_size, "#0", result_size)

            # Flags : AF
            trans += self._undefine_flag("af")

        return self._ir_parser.parse(trans, False)

    def _translate_not(self, instruction, in_operands=None, out_operands=None):
        # Flags Affected
        # None.

        oprnd1 = in_operands[0]

        assert oprnd1.size

        oprnd_size = oprnd1.size
        result_size = oprnd_size

        oprnd_size_str  = size_str[oprnd_size]
        result_size_str = size_str[result_size]

        trans  = ["xor [{0} $0, {0} {1}, {2} #0]".format(oprnd_size_str, (2**oprnd_size)-1, result_size_str)]

        return self._ir_parser.parse(trans, False)

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

        oprnd1 = in_operands[0]
        oprnd2 = in_operands[1]

        assert oprnd1.size and oprnd2.size

        oprnd1_size = oprnd1.size
        oprnd2_size = oprnd2.size

        oprnd_size  = oprnd1.size
        result_size = oprnd_size

        oprnd1_size_str = size_str[oprnd1_size]
        oprnd2_size_str = size_str[oprnd2_size]
        oprnd_size_str  = size_str[oprnd_size]
        result_size_str = size_str[result_size]

        # Extend 2nd operand to 1st operand size
        trans  = ["str [{0} $1,   EMPTY,  {1} %0]".format(oprnd2_size_str, oprnd_size_str)]

        # Decrement in 1 shift amount
        trans += ["sub [{0} %0,   {0} 1,  {0} %1]".format(oprnd_size_str)]

        # Negate
        trans += ["xor [{0} %1, {0} {1},  {0} %2]".format(oprnd_size_str, (2**oprnd_size)-1)]
        trans += ["add [{0} %2, {0}   1,  {0} %3]".format(oprnd_size_str)]

        # Shift right
        trans += ["bsh [{0} $0,  {0} %3,  {0} %4]".format(oprnd_size_str)]

        # Save LSB in CF
        trans += ["and [{0} %4,   {0} 1,  {0} %5]".format(oprnd_size_str)]
        trans += ["str [{0} %5,   EMPTY, BYTE cf]".format(oprnd_size_str)]

        # Shift one more time
        trans += ["bsh [{0} %4,  {0} -1,  {0} #0]".format(oprnd_size_str)]

        if self._translation_mode == FULL_TRANSLATION:
            # Flags : OF
            # TODO: Implement translation for OF flag.

            # Flags : SF, ZF, PF
            trans += self._translate_sf("$0", "$0", oprnd_size, "#0", result_size)
            trans += self._translate_zf("$0", "$0", oprnd_size, "#0", result_size)
            trans += self._translate_pf("$0", "$0", oprnd_size, "#0", result_size)

            # Flags : AF
            trans += self._undefine_flag("af")

        return self._ir_parser.parse(trans, False)

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

        oprnd1 = in_operands[0]
        oprnd2 = in_operands[1]

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

        # Extend 2nd operand to 1st operand size
        trans  = ["str [{0} $1,   EMPTY,  {1} %0]".format(oprnd2_size_str, oprnd_size_str)]

        # Decrement in 1 shift amount
        trans += ["sub [{0} %0,   {0} 1,  {0} %1]".format(oprnd_size_str)]

        # Shift left
        trans += ["bsh [{0} $0,  {0} %1,  {0} %2]".format(oprnd_size_str)]

        # Save LSB in CF
        trans += ["and [{0} %2,   {0} 1,  {0} %3]".format(oprnd_size_str)]
        trans += ["str [{0} %3,   EMPTY, BYTE cf]".format(oprnd_size_str)]

        # Shift one more time
        trans += ["bsh [{0} %2,   {0} 1,  {0} #0]".format(oprnd_size_str)]

        if self._translation_mode == FULL_TRANSLATION:
            # Flags : OF
            # TODO: Implement translation for OF flag.

            # Flags : SF, ZF, PF
            trans += self._translate_sf("$0", "$0", oprnd_size, "#0", result_size)
            trans += self._translate_zf("$0", "$0", oprnd_size, "#0", result_size)
            trans += self._translate_pf("$0", "$0", oprnd_size, "#0", result_size)

            # Flags : AF
            trans += self._undefine_flag("af")

        return self._ir_parser.parse(trans, False)

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

        oprnd1 = in_operands[0]
        oprnd2 = in_operands[1]

        assert oprnd1.size and oprnd2.size

        oprnd1_size = oprnd1.size
        oprnd2_size = oprnd2.size

        oprnd_size  = oprnd1.size
        result_size = oprnd_size

        oprnd1_size_str = size_str[oprnd1_size]
        oprnd2_size_str = size_str[oprnd2_size]
        oprnd_size_str  = size_str[oprnd_size]
        result_size_str = size_str[result_size]

        # Initialize counter
        trans  = ["str  [{0} $1,   EMPTY,      {0} %0]".format(oprnd_size_str)]

        # Copy operand to temporal register
        trans += ["str  [{0} $0,   EMPTY,      {0} %1]".format(oprnd_size_str)]

        # Filter sign bit
        trans += ["and  [{0} $0, {0} {1},      {0} %2]".format(oprnd_size_str, 2**(oprnd_size-1))]

        # Filter lsb bit
        trans += ["and  [{0} $0,   {0} 1,      {0} %6]".format(oprnd_size_str)]
        trans += ["str  [{0} %6,   EMPTY,     BYTE cf]".format(oprnd_size_str)]

        # Shift right
        trans += ["bsh  [{0} %1,  {0} -1,      {0} %3]".format(oprnd_size_str)]

        # Propagate sign bit
        trans += ["or   [{0} %3,  {0} %2,      {0} %1]".format(oprnd_size_str)]

        # Decrement counter
        trans += ["sub  [{0} %0,   {0} 1,      {0} %0]".format(oprnd_size_str)]

        # Compare counter to zero
        trans += ["bisz [{0} %0,   EMPTY,      {0} %4]".format(oprnd_size_str)]

        # Invert stop flag
        trans += ["xor  [{0} %4,   {0} 1,      {0} %5]".format(oprnd_size_str)]

        # Iterate
        trans += ["jcc  [{0} %5,   EMPTY, POINTER {1}]".format(oprnd_size_str, instruction.address << 8 | 0x3)]

        # Save result
        trans += ["str  [{0} %1,   EMPTY,      {0} #0]".format(oprnd_size_str)]

        if self._translation_mode == FULL_TRANSLATION:
            # Flags : OF
            # TODO: Implement translation for OF flag.

            # Flags : SF, ZF, PF
            trans += self._translate_sf("$0", "$0", oprnd_size, "#0", result_size)
            trans += self._translate_zf("$0", "$0", oprnd_size, "#0", result_size)
            trans += self._translate_pf("$0", "$0", oprnd_size, "#0", result_size)

            # Flags : AF
            trans += self._undefine_flag("af")

        return self._ir_parser.parse(trans, False)

# "Bit and Byte Instructions"
# ============================================================================ #
    def _translate_test(self, instruction, in_operands=None, out_operands=None):
        # Flags Affected
        # The OF and CF flags are set to 0. The SF, ZF, and PF flags are
        # set according to the result (see the “Operation” section
        # above). The state of the AF flag is undefined.

        oprnd1 = in_operands[0]
        oprnd2 = in_operands[0]

        assert oprnd1.size and oprnd2.size
        assert oprnd1.size == oprnd2.size

        oprnd_size = oprnd1.size
        result_size = oprnd_size

        oprnd_size_str  = size_str[oprnd_size]
        result_size_str = size_str[result_size]

        trans  = ["and [{0} $0, {0} $1, {1} %0]".format(oprnd_size_str, result_size_str)]

        # Flags : OF, CF
        trans += self._clear_flag("of")
        trans += self._clear_flag("cf")

        # Flags : SF, ZF, PF
        trans += self._translate_sf("$0", "$1", oprnd_size, "%0", result_size)
        trans += self._translate_zf("$0", "$1", oprnd_size, "%0", result_size)
        trans += self._translate_pf("$0", "$1", oprnd_size, "%0", result_size)

        # Flags : AF
        trans += self._undefine_flag("af")

        return self._ir_parser.parse(trans, False)

# "Control Transfer Instructions"
# ============================================================================ #
    def _translate_jmp(self, instruction, in_operands=None, out_operands=None):
        # Flags Affected
        # All flags are affected if a task switch occurs; no flags are
        # affected if a task switch does not occur.

        oprnd1 = in_operands[0]

        assert oprnd1.size
        assert oprnd1.size in [32, 64]

        if isinstance(in_operands[0], ReilImmediateOperand):
            in_operands[0] = ReilImmediateOperand(in_operands[0].immediate << 8, in_operands[0].size + 8)

        trans = ["jcc [BYTE 1, EMPTY, $0]"]

        return self._ir_parser.parse(trans, False)

    def _translate_ja(self, instruction, in_operands=None, out_operands=None):
        # Jump near if above (CF=0 and ZF=0).

        oprnd1 = in_operands[0]

        assert oprnd1.size
        assert oprnd1.size in [32, 64]

        if isinstance(in_operands[0], ReilImmediateOperand):
            in_operands[0] = ReilImmediateOperand(in_operands[0].immediate << 8, in_operands[0].size + 8)

        trans  = ["xor [BYTE cf,  BYTE 1, BYTE %0]"]
        trans += ["xor [BYTE zf,  BYTE 1, BYTE %1]"]
        trans += ["and [BYTE %0, BYTE %1, BYTE %2]"]
        trans += ["jcc [BYTE %2,   EMPTY,      $0]"]

        return self._ir_parser.parse(trans, False)

    def _translate_jo(self, instruction, in_operands=None, out_operands=None):
        # Jump near if overflow (OF=1).

        oprnd1 = in_operands[0]

        assert oprnd1.size
        assert oprnd1.size in [32, 64]

        if isinstance(in_operands[0], ReilImmediateOperand):
            in_operands[0] = ReilImmediateOperand(in_operands[0].immediate << 8, in_operands[0].size + 8)

        trans  = ["jcc [BYTE of, EMPTY, $0]"]

        return self._ir_parser.parse(trans, False)

    def _translate_jbe(self, instruction, in_operands=None, out_operands=None):
        # Jump near if below or equal (CF=1 or ZF=1).

        oprnd1 = in_operands[0]

        assert oprnd1.size
        assert oprnd1.size in [32, 64]

        if isinstance(in_operands[0], ReilImmediateOperand):
            in_operands[0] = ReilImmediateOperand(in_operands[0].immediate << 8, in_operands[0].size + 8)

        trans  = ["or  [BYTE cf, BYTE zf, BYTE %0]"]
        trans += ["jcc [BYTE %0,   EMPTY,      $0]"]

        return self._ir_parser.parse(trans, False)

    def _translate_jl(self, instruction, in_operands=None, out_operands=None):
        # Jump near if less (SF!=OF).

        oprnd1 = in_operands[0]

        assert oprnd1.size
        assert oprnd1.size in [32, 64]

        if isinstance(in_operands[0], ReilImmediateOperand):
            in_operands[0] = ReilImmediateOperand(in_operands[0].immediate << 8, in_operands[0].size + 8)

        trans  = ["sub  [BYTE sf, BYTE OF, BYTE %0]"]
        trans += ["bisz [BYTE %0,   EMPTY, BYTE %1]"]
        trans += ["xor  [BYTE %1,  BYTE 1, BYTE %2]"]
        trans += ["jcc  [BYTE %2,   EMPTY,      $0]"]

        return self._ir_parser.parse(trans, False)

    def _translate_je(self, instruction, in_operands=None, out_operands=None):
        # Jump near if equal (ZF=1).

        oprnd1 = in_operands[0]

        assert oprnd1.size
        assert oprnd1.size in [32, 64]

        if isinstance(in_operands[0], ReilImmediateOperand):
            in_operands[0] = ReilImmediateOperand(in_operands[0].immediate << 8, in_operands[0].size + 8)

        trans = ["jcc [BYTE zf, EMPTY, $0]"]

        return self._ir_parser.parse(trans, False)

    def _translate_js(self, instruction, in_operands=None, out_operands=None):
        # Jump near if sign (SF=1).

        oprnd1 = in_operands[0]

        assert oprnd1.size
        assert oprnd1.size in [32, 64]

        if isinstance(in_operands[0], ReilImmediateOperand):
            in_operands[0] = ReilImmediateOperand(in_operands[0].immediate << 8, in_operands[0].size + 8)

        trans = ["jcc [BYTE sf, EMPTY, $0]"]

        return self._ir_parser.parse(trans, False)

    def _translate_jg(self, instruction, in_operands=None, out_operands=None):
        # Jump near if greater (ZF=0 and SF=OF).

        oprnd1 = in_operands[0]

        assert oprnd1.size
        assert oprnd1.size in [32, 64]

        if isinstance(in_operands[0], ReilImmediateOperand):
            in_operands[0] = ReilImmediateOperand(in_operands[0].immediate << 8, in_operands[0].size + 8)

        trans  = ["sub  [BYTE sf, BYTE of, BYTE %0]"]
        trans += ["bisz [BYTE %0,   EMPTY, BYTE %1]"]
        trans += ["xor  [BYTE zf,  BYTE 1, BYTE %2]"]
        trans += ["and  [BYTE %1, BYTE %2, BYTE %3]"]
        trans += ["jcc  [BYTE %3,   EMPTY,      $0]"]

        return self._ir_parser.parse(trans, False)

    def _translate_jge(self, instruction, in_operands=None, out_operands=None):
        # Jump near if greater or equal (SF=OF).

        oprnd1 = in_operands[0]

        assert oprnd1.size
        assert oprnd1.size in [32, 64]

        if isinstance(in_operands[0], ReilImmediateOperand):
            in_operands[0] = ReilImmediateOperand(in_operands[0].immediate << 8, in_operands[0].size + 8)

        trans  = ["sub  [BYTE sf, BYTE of, BYTE %0]"]
        trans += ["bisz [BYTE %0,   EMPTY, BYTE %1]"]
        trans += ["jcc  [BYTE %1,   EMPTY,      $0]"]

        return self._ir_parser.parse(trans, False)

    def _translate_jae(self, instruction, in_operands=None, out_operands=None):
        # Jump near if above or equal (CF=0).

        oprnd1 = in_operands[0]

        assert oprnd1.size
        assert oprnd1.size in [32, 64]

        if isinstance(in_operands[0], ReilImmediateOperand):
            in_operands[0] = ReilImmediateOperand(in_operands[0].immediate << 8, in_operands[0].size + 8)

        trans  = ["bisz [BYTE cf, EMPTY, BYTE %0]"]
        trans += ["jcc  [BYTE %0, EMPTY,      $0]"]

        return self._ir_parser.parse(trans, False)

    def _translate_jno(self, instruction, in_operands=None, out_operands=None):
        # Jump near if not overflow (OF=0).

        oprnd1 = in_operands[0]

        assert oprnd1.size
        assert oprnd1.size in [32, 64]

        if isinstance(in_operands[0], ReilImmediateOperand):
            in_operands[0] = ReilImmediateOperand(in_operands[0].immediate << 8, in_operands[0].size + 8)

        trans  = ["bisz [BYTE of, EMPTY, BYTE %0]"]
        trans += ["jcc  [BYTE %0, EMPTY,      $0]"]

        return self._ir_parser.parse(trans, False)

    def _translate_jns(self, instruction, in_operands=None, out_operands=None):
        # Jump near if not sign (SF=0).

        oprnd1 = in_operands[0]

        assert oprnd1.size
        assert oprnd1.size in [32, 64]

        if isinstance(in_operands[0], ReilImmediateOperand):
            in_operands[0] = ReilImmediateOperand(in_operands[0].immediate << 8, in_operands[0].size + 8)

        trans  = ["bisz [BYTE sf, EMPTY, BYTE %0]"]
        trans += ["jcc  [BYTE %0, EMPTY,      $0]"]

        return self._ir_parser.parse(trans, False)

    def _translate_jb(self, instruction, in_operands=None, out_operands=None):
        # Jump near if below (CF=1).

        oprnd1 = in_operands[0]

        assert oprnd1.size
        assert oprnd1.size in [32, 64]

        if isinstance(in_operands[0], ReilImmediateOperand):
            in_operands[0] = ReilImmediateOperand(in_operands[0].immediate << 8, in_operands[0].size + 8)

        trans  = ["jcc [BYTE cf, EMPTY, $0]"]

        return self._ir_parser.parse(trans, False)

    def _translate_jle(self, instruction, in_operands=None, out_operands=None):
        # Jump near if less or equal (ZF=1 or SF!=OF).

        oprnd1 = in_operands[0]

        assert oprnd1.size
        assert oprnd1.size in [32, 64]

        if isinstance(in_operands[0], ReilImmediateOperand):
            in_operands[0] = ReilImmediateOperand(in_operands[0].immediate << 8, in_operands[0].size + 8)

        trans  = ["sub  [BYTE sf, BYTE of, BYTE %0]"]
        trans += ["bisz [BYTE %0,   EMPTY, BYTE %1]"]
        trans += ["xor  [BYTE %1,  BYTE 1, BYTE %2]"]
        trans += ["or   [BYTE %2, BYTE zf, BYTE %3]"]
        trans += ["jcc  [BYTE %3,   EMPTY,      $0]"]

        return self._ir_parser.parse(trans, False)

    def _translate_jz(self, instruction, in_operands=None, out_operands=None):
        # Jump near if 0 (ZF=1).

        oprnd1 = in_operands[0]

        assert oprnd1.size
        assert oprnd1.size in [32, 64]

        if isinstance(in_operands[0], ReilImmediateOperand):
            in_operands[0] = ReilImmediateOperand(in_operands[0].immediate << 8, in_operands[0].size + 8)

        trans = ["jcc [BYTE zf, EMPTY, $0]"]

        return self._ir_parser.parse(trans, False)

    def _translate_jne(self, instruction, in_operands=None, out_operands=None):
        # Jump near if not equal (ZF=0).

        oprnd1 = in_operands[0]

        assert oprnd1.size
        assert oprnd1.size in [32, 64]

        if isinstance(in_operands[0], ReilImmediateOperand):
            in_operands[0] = ReilImmediateOperand(in_operands[0].immediate << 8, in_operands[0].size + 8)

        trans  = ["xor [BYTE zf, BYTE 0x1, BYTE %0]"]
        trans += ["jcc [BYTE %0,    EMPTY,      $0]"]

        return self._ir_parser.parse(trans, False)

    def _translate_jnz(self, instruction, in_operands=None, out_operands=None):
        # Jump near if not zero (ZF=0).

        oprnd1 = in_operands[0]

        assert oprnd1.size
        assert oprnd1.size in [32, 64]

        if isinstance(in_operands[0], ReilImmediateOperand):
            in_operands[0] = ReilImmediateOperand(in_operands[0].immediate << 8, in_operands[0].size + 8)

        trans  = ["xor [BYTE zf, BYTE 1, %0]"]
        trans += ["jcc [BYTE %0,  EMPTY, $0]"]

        return self._ir_parser.parse(trans, False)

    def _translate_jnbe(self, instruction, in_operands=None, out_operands=None):
        # Jump near if not below or equal (CF=0 and ZF=0).

        oprnd1 = in_operands[0]

        assert oprnd1.size
        assert oprnd1.size in [32, 64]

        if isinstance(in_operands[0], ReilImmediateOperand):
            in_operands[0] = ReilImmediateOperand(in_operands[0].immediate << 8, in_operands[0].size + 8)

        trans  = ["xor [BYTE cf,  BYTE 1, BYTE %0]"]
        trans += ["xor [BYTE zf,  BYTE 1, BYTE %1]"]
        trans += ["and [BYTE %0, BYTE %1, BYTE %2]"]
        trans += ["jcc [BYTE %2,   EMPTY,      $0]"]

        return self._ir_parser.parse(trans, False)

    def _translate_jc(self, instruction, in_operands=None, out_operands=None):
        # Jump near if carry (CF=1).

        oprnd1 = in_operands[0]

        assert oprnd1.size
        assert oprnd1.size in [32, 64]

        if isinstance(in_operands[0], ReilImmediateOperand):
            in_operands[0] = ReilImmediateOperand(in_operands[0].immediate << 8, in_operands[0].size + 8)

        trans = ["jcc [BYTE cf, EMPTY, $0]"]

        return self._ir_parser.parse(trans, False)

    def _translate_jnc(self, instruction, in_operands=None, out_operands=None):
        # Jump near if not carry (CF=0).

        oprnd1 = in_operands[0]

        assert oprnd1.size
        assert oprnd1.size in [32, 64]

        if isinstance(in_operands[0], ReilImmediateOperand):
            in_operands[0] = ReilImmediateOperand(in_operands[0].immediate << 8, in_operands[0].size + 8)

        trans  = ["xor [BYTE cf, BYTE 1, BYTE %0]"]
        trans += ["jcc [BYTE %0,  EMPTY,      $0]"]

        return self._ir_parser.parse(trans, False)

    def _translate_jecxz(self, instruction, in_operands=None, out_operands=None):
        # Jump short if ECX register is 0.

        oprnd1 = in_operands[0]

        assert oprnd1.size
        assert oprnd1.size in [32, 64]

        if isinstance(in_operands[0], ReilImmediateOperand):
            in_operands[0] = ReilImmediateOperand(in_operands[0].immediate << 8, in_operands[0].size + 8)

        trans  = ["bisz [DWORD ecx, EMPTY, BYTE %0]"]
        trans += ["jcc  [BYTE   %0, EMPTY,      $0]"]

        return self._ir_parser.parse(trans, False)

    def _translate_call(self, instruction, in_operands=None, out_operands=None):
        # Flags Affected
        # All flags are affected if a task switch occurs; no flags are
        # affected if a task switch does not occur.

        oprnd1 = in_operands[0]

        assert oprnd1.size
        assert oprnd1.size in [32, 64]

        if isinstance(in_operands[0], ReilImmediateOperand):
            in_operands[0] = ReilImmediateOperand(in_operands[0].immediate << 8, in_operands[0].size + 8)

        if self.architecture_mode == ARCH_X86_MODE_32:
            trans  = ["sub [DWORD esp, DWORD   4, DWORD  %0]"]
            trans += ["str [DWORD  %0,     EMPTY, DWORD esp]"]
            trans += ["add [DWORD eip, DWORD {0}, DWORD  %1]".format(instruction.size)]
            trans += ["stm [DWORD  %1,     EMPTY, DWORD esp]"]
            trans += ["jcc [BYTE    1,     EMPTY, DWORD  $0]"]
        elif self.architecture_mode == ARCH_X86_MODE_64:
            trans  = ["sub [QWORD rsp, QWORD   8, QWORD  %0]"]
            trans += ["str [QWORD  %0,     EMPTY, QWORD rsp]"]
            trans += ["add [QWORD rip, QWORD {0}, QWORD  %1]".format(instruction.size)]
            trans += ["stm [QWORD  %1,     EMPTY, QWORD rsp]"]
            trans += ["jcc [BYTE    1,     EMPTY, QWORD  $0]"]

        return self._ir_parser.parse(trans, False)

    def _translate_ret(self, instruction, in_operands=None, out_operands=None):
        # Flags Affected
        # None.

        trans = ["ret [EMPTY, EMPTY, EMPTY]"]

        return self._ir_parser.parse(trans, False)

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

        if self.architecture_mode == ARCH_X86_MODE_32:
            # leave == mov esp, ebp ; pop ebp ->
            # leave == mov esp, ebp ; mov ebp, [esp] ; add esp, 4
            trans  = ["str [DWORD ebp,   EMPTY, DWORD esp]"]
            trans += ["ldm [DWORD esp,   EMPTY, DWORD ebp]"]
            trans += ["add [DWORD esp, DWORD 4, DWORD  %0]"]
            trans += ["str [DWORD  %0,   EMPTY, DWORD esp]"]
        elif self.architecture_mode == ARCH_X86_MODE_64:
            # leave == mov rsp, rbp ; pop rbp ->
            # leave == mov rsp, rbp ; mov rbp, [rsp] ; add rsp, 8

            trans  = ["str [QWORD rbp,   EMPTY, QWORD rsp]"]
            trans += ["ldm [QWORD rsp,   EMPTY, QWORD rbp]"]
            trans += ["add [QWORD rsp, QWORD 8, QWORD  %0]"]
            trans += ["str [QWORD  %0,   EMPTY, QWORD rsp]"]

        return self._ir_parser.parse(trans, False)

# "Flag Control (EFLAG) Instructions"
# ============================================================================ #
    def _translate_cld(self, instruction, in_operands=None, out_operands=None):
        # Flags Affected
        # The DF flag is set to 0. The CF, OF, ZF, SF, AF, and PF flags
        # are unaffected.

        trans = ["str [BYTE 0, EMPTY, BYTE df]"]

        return self._ir_parser.parse(trans, False)

    def _translate_clc(self, instruction, in_operands=None, out_operands=None):
        # Flags Affected
        # The CF flag is set to 0. The OF, ZF, SF, AF, and PF flags are
        # unaffected.

        trans = ["str [BYTE 0, EMPTY, BYTE cf]"]

        return self._ir_parser.parse(trans, False)

# "Segment Register Instructions"
# ============================================================================ #

# "Miscellaneous Instructions"
# ============================================================================ #
    def _translate_lea(self, instruction, in_operands=None, out_operands=None):
        # Flags Affected
        # None.

        oprnd1 = in_operands[0]
        oprnd2 = out_operands[0]

        assert oprnd1.size and oprnd2.size
        assert oprnd1.size == oprnd2.size

        trans = ["str [$0, EMPTY, #0]"]

        return self._ir_parser.parse(trans, False)

    def _translate_nop(self, instruction, in_operands=None, out_operands=None):
        # Flags Affected
        # None.

        trans = ["nop [EMPTY, EMPTY, EMPTY]"]

        return self._ir_parser.parse(trans, False)

# "Random Number Generator Instruction"
# ============================================================================ #

# "Misc"
# ============================================================================ #
    def _translate_hlt(self, instruction, in_operands=None, out_operands=None):
        # Flags Affected
        # None.

        trans = ["unkn [EMPTY, EMPTY, EMPTY]"]

        return self._ir_parser.parse(trans, False)
