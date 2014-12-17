import logging

import barf

from barf.arch import ARCH_X86_MODE_32
from barf.arch import ARCH_X86_MODE_64
from barf.arch.x86.x86base import X86ArchitectureInformation
from barf.arch.x86.x86base import X86ImmediateOperand
from barf.arch.x86.x86base import X86MemoryOperand
from barf.arch.x86.x86base import X86RegisterOperand
from barf.core.reil import ReilEmptyOperand
from barf.core.reil import ReilImmediateOperand
from barf.core.reil import ReilInstructionBuilder
from barf.core.reil import ReilMnemonic
from barf.core.reil import ReilRegisterOperand
from barf.utils.utils import VariableNamer

FULL_TRANSLATION = 0
LITE_TRANSLATION = 1

logger = logging.getLogger(__name__)

class Label(object):

    def __init__(self, name):
        self.name = name

class TranslationBuilder(object):

    def __init__(self, ir_name_generator, architecture_mode):
        self._ir_name_generator = ir_name_generator

        self._arch_info = X86ArchitectureInformation(architecture_mode)

        self._instructions = []

        self._builder = ReilInstructionBuilder()

    def add(self, instr):
        self._instructions.append(instr)

    def temporal(self, size):
        return ReilRegisterOperand(self._ir_name_generator.get_next(), size)

    def immediate(self, value, size):
        return ReilImmediateOperand(value, size)

    def label(self, name):
        return Label(name)

    def instanciate(self, address):
        # Set instructions address.
        instrs = self._instructions

        for instr in instrs:
            instr.address = address << 8

        self._resolve_loops(instrs)

        return instrs

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

            self.add(self._builder.gen_str(value, reil_operand))

        elif isinstance(x86_operand, barf.arch.x86.x86base.X86MemoryOperand):

            addr = self._compute_memory_address(x86_operand)

            self.add(self._builder.gen_stm(value, addr))

        else:
            raise Exception()

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

        if mem_operand.displacement and mem_operand.displacement != 0x0:
            disp = ReilImmediateOperand(mem_operand.displacement, size)

            if addr:
                tmp = self.temporal(size)

                self.add(self._builder.gen_add(addr, disp, tmp))

                addr = tmp
            else:
                addr = disp

        return addr

class X86Translator(object):

    """x86 to IR Translator."""

    def __init__(self, architecture_mode=ARCH_X86_MODE_32, translation_mode=FULL_TRANSLATION):

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
            "af" : ReilRegisterOperand("af", 1),
            "cf" : ReilRegisterOperand("cf", 1),
            "df" : ReilRegisterOperand("df", 1),
            "of" : ReilRegisterOperand("of", 1),
            "pf" : ReilRegisterOperand("pf", 1),
            "sf" : ReilRegisterOperand("sf", 1),
            "zf" : ReilRegisterOperand("zf", 1),
        }

        if self._arch_mode == ARCH_X86_MODE_32:
            self._sp = ReilRegisterOperand("esp", 32)
            self._bp = ReilRegisterOperand("ebp", 32)
            self._ip = ReilRegisterOperand("eip", 32)

            self._ws = ReilImmediateOperand(4, 32) # word size
        elif self._arch_mode == ARCH_X86_MODE_64:
            self._sp = ReilRegisterOperand("rsp", 64)
            self._bp = ReilRegisterOperand("rbp", 64)
            self._ip = ReilRegisterOperand("rip", 64)

            self._ws = ReilImmediateOperand(8, 64) # word size

    def translate(self, instruction):
        """Return IR representation of an instruction.
        """
        try:
            trans_instrs = self._translate(instruction)
        except NotImplementedError:
            trans_instrs = [self._builder.gen_unkn()]

            self._log_not_supported_instruction(instruction)
        except:
            self._log_translation_exception(instruction)

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
        tb = TranslationBuilder(self._ir_name_generator, self._arch_mode)

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
        if instruction.bytes:
            bytes_str = " ".join("%02x" % ord(b) for b in instruction.bytes)
        else:
            bytes_str = ""

        logger.info(
            "Instruction not supported: %s (%s  %s)",
            instruction.mnemonic,
            bytes_str,
            instruction
        )

    def _log_translation_exception(self, instruction):
        if instruction.bytes:
            bytes_str = " ".join("%02x" % ord(b) for b in instruction.bytes)
        else:
            bytes_str = ""

        logger.error(
            "Failed to translate x86 to REIL: %s (%s)",
            instruction,
            bytes_str,
            exc_info=True
        )

# ============================================================================ #

    def _not_implemented(self, tb, instruction):
        raise NotImplementedError("Instruction Not Implemented")

# Translators
# ============================================================================ #
# ============================================================================ #

# "Flags"
# ============================================================================ #
    def _update_af(self, tb, oprnd0, oprnd1, result):
        # TODO: Implement
        pass

    def _update_pf(self, tb, oprnd0, oprnd1, result):
        # TODO: Implement
        pass

    def _update_sf(self, tb, oprnd0, oprnd1, result):
        # Create temporal variables.
        tmp0 = tb.temporal(result.size)

        mask0 = tb.immediate(2**result.size-1, result.size)
        shift0 = tb.immediate(-(result.size-1), result.size)

        sf = self._flags["sf"]

        tb.add(self._builder.gen_and(result, mask0, tmp0))  # filter sign bit
        tb.add(self._builder.gen_bsh(tmp0, shift0, sf))     # extract sign bit

    def _update_of(self, tb, oprnd0, oprnd1, result):
        of = self._flags["of"]

        imm0 = tb.immediate(2**(oprnd0.size-1), oprnd0.size)
        imm1 = tb.immediate(1, oprnd0.size)
        imm3 = tb.immediate(-(oprnd0.size-1), oprnd0.size)
        imm4 = tb.immediate(2**(oprnd0.size-1), result.size)

        tmp0 = tb.temporal(oprnd0.size)
        tmp1 = tb.temporal(oprnd1.size)
        tmp2 = tb.temporal(oprnd0.size)
        tmp3 = tb.temporal(oprnd0.size)
        tmp4 = tb.temporal(oprnd0.size)
        tmp5 = tb.temporal(oprnd0.size)
        tmp6 = tb.temporal(oprnd0.size)

        tb.add(self._builder.gen_and(oprnd0, imm0, tmp0))   # filter sign bit oprnd 1
        tb.add(self._builder.gen_and(oprnd1, imm0, tmp1))   # filter sign bit oprnd 2
        tb.add(self._builder.gen_and(result, imm4, tmp2))   # filter sign bit result
        tb.add(self._builder.gen_xor(tmp0, tmp1, tmp3))     # sign bit oprnd0 ^ sign bit oprnd1
        tb.add(self._builder.gen_xor(tmp3, imm1, tmp4))     # sign bit oprnd0 ^ sign bit oprnd1 ^ 1
        tb.add(self._builder.gen_xor(tmp0, tmp2, tmp5))     # sign bit oprnd0 ^ sign bit result
        tb.add(self._builder.gen_and(tmp4, tmp5, tmp6))     # (sign bit oprnd0 ^ sign bit oprnd1 ^ 1) & (sign bit oprnd0 ^ sign bit result)
        tb.add(self._builder.gen_bsh(tmp6, imm3, of))

    def _update_cf(self, tb, oprnd0, oprnd1, result):
        cf = self._flags["cf"]

        imm0 = tb.immediate(2**oprnd0.size, result.size)
        imm1 = tb.immediate(-oprnd0.size, result.size)
        imm2 = tb.immediate(-oprnd0.size, oprnd0.size)

        tmp0 = tb.temporal(oprnd0.size)

        tb.add(self._builder.gen_and(result, imm0, tmp0))   # filter carry bit
        tb.add(self._builder.gen_bsh(tmp0, imm2, cf))

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

# "Data Transfer Instructions"
# ============================================================================ #
    def _translate_mov(self, tb, instruction):
        # Flags Affected
        # None.

        oprnd1 = tb.read(instruction.operands[1])

        tb.write(instruction.operands[0], oprnd1)

    def _translate_movzx(self, tb, instruction):
        # Flags Affected
        # None.

        oprnd1 = tb.read(instruction.operands[1])

        tb.write(instruction.operands[0], oprnd1)

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
            self._update_of(tb, oprnd0, oprnd1, tmp0)
            self._update_sf(tb, oprnd0, oprnd1, tmp0)
            self._update_zf(tb, oprnd0, oprnd1, tmp0)
            self._update_af(tb, oprnd0, oprnd1, tmp0)
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

        tb.add(self._builder.gen_sub(oprnd0, oprnd1, tmp0))
        tb.add(self._builder.gen_str(self._flags["cf"], tmp1))
        tb.add(self._builder.gen_sub(oprnd0, oprnd1, tmp2))

        if self._translation_mode == FULL_TRANSLATION:
            # Flags : OF, SF, ZF, AF, PF, CF
            self._update_of(tb, oprnd0, oprnd1, tmp2)
            self._update_sf(tb, oprnd0, oprnd1, tmp2)
            self._update_zf(tb, oprnd0, oprnd1, tmp2)
            self._update_af(tb, oprnd0, oprnd1, tmp2)
            self._update_pf(tb, oprnd0, oprnd1, tmp2)
            self._update_cf(tb, oprnd0, oprnd1, tmp2)

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
            tmp0 = tb.temporal(64)
            result_low = ReilRegisterOperand("rax", 64)
            result_high = ReilRegisterOperand("rdx", 64)

        imm0 = tb.immediate(-oprnd0.size, oprnd0.size*2)

        tb.add(self._builder.gen_mul(oprnd0, oprnd1, tmp0))
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

                tmp0 = tb.temporal(16)
                result_low = ReilRegisterOperand("al", 8)
                result_high = ReilRegisterOperand("ah", 8)
            elif oprnd0.size == 16:
                oprnd1 = ReilRegisterOperand("ax", 16)

                tmp0 = tb.temporal(32)
                result_low = ReilRegisterOperand("dx", 16)
                result_high = ReilRegisterOperand("ax", 16)
            elif oprnd0.size == 32:
                oprnd1 = ReilRegisterOperand("eax", 32)

                tmp0 = tb.temporal(64)
                result_low = ReilRegisterOperand("edx", 32)
                result_high = ReilRegisterOperand("eax", 32)
            elif oprnd0.size == 64:
                oprnd1 = ReilRegisterOperand("rax", 64)

                tmp0 = tb.temporal(64)
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

        # Do division
        tb.add(self._builder.gen_div(tmp4, tmp0, tmp5))
        tb.add(self._builder.gen_mod(tmp4, tmp0, tmp6))
        tb.add(self._builder.gen_str(tmp5, result_low))
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
            self._update_of(tb, oprnd0, oprnd0, tmp0)
            self._update_sf(tb, oprnd0, oprnd0, tmp0)
            self._update_zf(tb, oprnd0, oprnd0, tmp0)
            self._update_af(tb, oprnd0, oprnd0, tmp0)
            self._update_pf(tb, oprnd0, oprnd0, tmp0)

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
            self._update_of(tb, oprnd0, oprnd0, tmp0)
            self._update_sf(tb, oprnd0, oprnd0, tmp0)
            self._update_zf(tb, oprnd0, oprnd0, tmp0)
            self._update_af(tb, oprnd0, oprnd0, tmp0)
            self._update_pf(tb, oprnd0, oprnd0, tmp0)

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
            self._update_of(tb, oprnd0, oprnd0, tmp1)
            self._update_sf(tb, oprnd0, oprnd0, tmp1)
            self._update_zf(tb, oprnd0, oprnd0, tmp1)
            self._update_af(tb, oprnd0, oprnd0, tmp1)
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
        self._update_of(tb, oprnd0, oprnd1, tmp0)
        self._update_sf(tb, oprnd0, oprnd1, tmp0)
        self._update_zf(tb, oprnd0, oprnd1, tmp0)
        self._update_af(tb, oprnd0, oprnd1, tmp0)
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

        tmp0 = tb.temporal(oprnd0.size)
        tmp1 = tb.temporal(oprnd0.size)
        tmp2 = tb.temporal(oprnd0.size)
        tmp3 = tb.temporal(oprnd0.size)
        tmp4 = tb.temporal(oprnd0.size)
        tmp5 = tb.temporal(oprnd0.size)
        tmp6 = tb.temporal(oprnd0.size)

        # Extend 2nd operand to 1st operand size
        tb.add(self._builder.gen_str(oprnd1, tmp0))

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

        tmp0 = tb.temporal(oprnd0.size)
        tmp1 = tb.temporal(oprnd0.size)
        tmp2 = tb.temporal(oprnd0.size)
        tmp3 = tb.temporal(oprnd0.size)

        tmp4 = tb.temporal(oprnd0.size)

        # Extend 2nd operand to 1st operand size
        tb.add(self._builder.gen_str(oprnd1, tmp0))

        # Decrement in 1 shift amount
        tb.add(self._builder.gen_sub(tmp0, imm0, tmp1))

        # Shift left
        tb.add(self._builder.gen_bsh(oprnd0, tmp1, tmp2))

        # Save LSB in CF
        tb.add(self._builder.gen_and(tmp2, imm0, tmp3))
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
        tmp6 = tb.temporal(oprnd0.size)
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

# "Bit and Byte Instructions"
# ============================================================================ #
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
    def _translate_jmp(self, tb, instruction):
        # Flags Affected
        # All flags are affected if a task switch occurs; no flags are
        # affected if a task switch does not occur.

        oprnd0 = tb.read(instruction.operands[0])

        if isinstance(oprnd0, ReilImmediateOperand):
            oprnd0 = ReilImmediateOperand(oprnd0.immediate << 8, oprnd0.size + 8)

        imm0 = tb.immediate(1, 1)

        tb.add(self._builder.gen_jcc(imm0, oprnd0))

    def _translate_ja(self, tb, instruction):
        # Jump near if above (CF=0 and ZF=0).

        oprnd0 = tb.read(instruction.operands[0])

        if isinstance(oprnd0, ReilImmediateOperand):
            oprnd0 = ReilImmediateOperand(oprnd0.immediate << 8, oprnd0.size + 8)

        imm0 = tb.immediate(1, 1)

        tmp0 = tb.temporal(1)
        tmp1 = tb.temporal(1)
        tmp2 = tb.temporal(1)

        tb.add(self._builder.gen_xor(self._flags["cf"], imm0, tmp0))
        tb.add(self._builder.gen_xor(self._flags["zf"], imm0, tmp1))
        tb.add(self._builder.gen_and(tmp0, tmp1, tmp2))
        tb.add(self._builder.gen_jcc(tmp2, oprnd0))

    def _translate_jo(self, tb, instruction):
        # Jump near if overflow (OF=1).

        oprnd0 = tb.read(instruction.operands[0])

        if isinstance(oprnd0, ReilImmediateOperand):
            oprnd0 = ReilImmediateOperand(oprnd0.immediate << 8, oprnd0.size + 8)

        tb.add(self._builder.gen_jcc(self._flags["of"], oprnd0))

    def _translate_jbe(self, tb, instruction):
        # Jump near if below or equal (CF=1 or ZF=1).

        oprnd0 = tb.read(instruction.operands[0])

        if isinstance(oprnd0, ReilImmediateOperand):
            oprnd0 = ReilImmediateOperand(oprnd0.immediate << 8, oprnd0.size + 8)

        tmp0 = tb.temporal(1)

        tb.add(self._builder.gen_or(self._flags["cf"], self._flags["zf"], tmp0))
        tb.add(self._builder.gen_jcc(tmp0, oprnd0))

    def _translate_jl(self, tb, instruction):
        # Jump near if less (SF!=OF).

        oprnd0 = tb.read(instruction.operands[0])

        if isinstance(oprnd0, ReilImmediateOperand):
            oprnd0 = ReilImmediateOperand(oprnd0.immediate << 8, oprnd0.size + 8)

        imm0 = tb.immediate(1, 1)

        tmp0 = tb.temporal(8)
        tmp1 = tb.temporal(1)
        tmp2 = tb.temporal(1)

        tb.add(self._builder.gen_sub(self._flags["sf"], self._flags["of"], tmp0))
        tb.add(self._builder.gen_bisz(tmp0, tmp1))
        tb.add(self._builder.gen_xor(tmp1, imm0, tmp2))
        tb.add(self._builder.gen_jcc(tmp2, oprnd0))

    def _translate_je(self, tb, instruction):
        # Jump near if equal (ZF=1).

        oprnd0 = tb.read(instruction.operands[0])

        if isinstance(oprnd0, ReilImmediateOperand):
            oprnd0 = ReilImmediateOperand(oprnd0.immediate << 8, oprnd0.size + 8)

        tb.add(self._builder.gen_jcc(self._flags["zf"], oprnd0))

    def _translate_js(self, tb, instruction):
        # Jump near if sign (SF=1).

        oprnd0 = tb.read(instruction.operands[0])

        if isinstance(oprnd0, ReilImmediateOperand):
            oprnd0 = ReilImmediateOperand(oprnd0.immediate << 8, oprnd0.size + 8)

        tb.add(self._builder.gen_jcc(self._flags["sf"], oprnd0))

    def _translate_jg(self, tb, instruction):
        # Jump near if greater (ZF=0 and SF=OF).

        oprnd0 = tb.read(instruction.operands[0])

        if isinstance(oprnd0, ReilImmediateOperand):
            oprnd0 = ReilImmediateOperand(oprnd0.immediate << 8, oprnd0.size + 8)

        imm0 = tb.immediate(1, 1)

        tmp0 = tb.temporal(8)
        tmp1 = tb.temporal(1)
        tmp2 = tb.temporal(1)
        tmp3 = tb.temporal(1)

        tb.add(self._builder.gen_sub(self._flags["sf"], self._flags["of"], tmp0))
        tb.add(self._builder.gen_bisz(tmp0, tmp1))
        tb.add(self._builder.gen_xor(self._flags["zf"], imm0, tmp2))
        tb.add(self._builder.gen_and(tmp1, tmp2, tmp3))
        tb.add(self._builder.gen_jcc(tmp3, oprnd0))

    def _translate_jge(self, tb, instruction):
        # Jump near if greater or equal (SF=OF).

        oprnd0 = tb.read(instruction.operands[0])

        if isinstance(oprnd0, ReilImmediateOperand):
            oprnd0 = ReilImmediateOperand(oprnd0.immediate << 8, oprnd0.size + 8)

        tmp0 = tb.temporal(8)
        tmp1 = tb.temporal(1)

        tb.add(self._builder.gen_sub(self._flags["sf"], self._flags["of"], tmp0))
        tb.add(self._builder.gen_bisz(tmp0, tmp1))
        tb.add(self._builder.gen_jcc(tmp1, oprnd0))

    def _translate_jae(self, tb, instruction):
        # Jump near if above or equal (CF=0).

        oprnd0 = tb.read(instruction.operands[0])

        if isinstance(oprnd0, ReilImmediateOperand):
            oprnd0 = ReilImmediateOperand(oprnd0.immediate << 8, oprnd0.size + 8)

        tmp0 = tb.temporal(1)

        tb.add(self._builder.gen_bisz(self._flags["cf"], tmp0))
        tb.add(self._builder.gen_jcc(tmp0, oprnd0))

    def _translate_jno(self, tb, instruction):
        # Jump near if not overflow (OF=0).

        oprnd0 = tb.read(instruction.operands[0])

        if isinstance(oprnd0, ReilImmediateOperand):
            oprnd0 = ReilImmediateOperand(oprnd0.immediate << 8, oprnd0.size + 8)

        tmp0 = tb.temporal(1)

        tb.add(self._builder.gen_bisz(self._flags["of"], tmp0))
        tb.add(self._builder.gen_jcc(tmp0, oprnd0))

    def _translate_jns(self, tb, instruction):
        # Jump near if not sign (SF=0).

        oprnd0 = tb.read(instruction.operands[0])

        if isinstance(oprnd0, ReilImmediateOperand):
            oprnd0 = ReilImmediateOperand(oprnd0.immediate << 8, oprnd0.size + 8)

        tmp0 = tb.temporal(1)

        tb.add(self._builder.gen_bisz(self._flags["sf"], tmp0))
        tb.add(self._builder.gen_jcc(tmp0, oprnd0))

    def _translate_jb(self, tb, instruction):
        # Jump near if below (CF=1).

        oprnd0 = tb.read(instruction.operands[0])

        if isinstance(oprnd0, ReilImmediateOperand):
            oprnd0 = ReilImmediateOperand(oprnd0.immediate << 8, oprnd0.size + 8)

        tb.add(self._builder.gen_jcc(self._flags["cf"], oprnd0))

    def _translate_jle(self, tb, instruction):
        # Jump near if less or equal (ZF=1 or SF!=OF).

        oprnd0 = tb.read(instruction.operands[0])

        if isinstance(oprnd0, ReilImmediateOperand):
            oprnd0 = ReilImmediateOperand(oprnd0.immediate << 8, oprnd0.size + 8)

        imm0 = tb.immediate(1, 1)

        tmp0 = tb.temporal(8)
        tmp1 = tb.temporal(1)
        tmp2 = tb.temporal(1)
        tmp3 = tb.temporal(1)

        tb.add(self._builder.gen_sub(self._flags["sf"], self._flags["of"], tmp0))
        tb.add(self._builder.gen_bisz(tmp0, tmp1))
        tb.add(self._builder.gen_xor(tmp1, imm0, tmp2))
        tb.add(self._builder.gen_or(tmp2, self._flags["zf"], tmp3))
        tb.add(self._builder.gen_jcc(tmp3, oprnd0))

    def _translate_jz(self, tb, instruction):
        # Jump near if 0 (ZF=1).

        oprnd0 = tb.read(instruction.operands[0])

        if isinstance(oprnd0, ReilImmediateOperand):
            oprnd0 = ReilImmediateOperand(oprnd0.immediate << 8, oprnd0.size + 8)

        tb.add(self._builder.gen_jcc(self._flags["zf"], oprnd0))

    def _translate_jne(self, tb, instruction):
        # Jump near if not equal (ZF=0).

        oprnd0 = tb.read(instruction.operands[0])

        if isinstance(oprnd0, ReilImmediateOperand):
            oprnd0 = ReilImmediateOperand(oprnd0.immediate << 8, oprnd0.size + 8)

        imm0 = tb.immediate(1, 1)

        tmp0 = tb.temporal(1)

        tb.add(self._builder.gen_xor(self._flags["zf"], imm0, tmp0))
        tb.add(self._builder.gen_jcc(tmp0, oprnd0))

    def _translate_jnz(self, tb, instruction):
        # Jump near if not zero (ZF=0).

        oprnd0 = tb.read(instruction.operands[0])

        if isinstance(oprnd0, ReilImmediateOperand):
            oprnd0 = ReilImmediateOperand(oprnd0.immediate << 8, oprnd0.size + 8)

        imm0 = tb.immediate(1, 1)

        tmp0 = tb.temporal(1)

        tb.add(self._builder.gen_xor(self._flags["zf"], imm0, tmp0))
        tb.add(self._builder.gen_jcc(tmp0, oprnd0))

    def _translate_jnbe(self, tb, instruction):
        # Jump near if not below or equal (CF=0 and ZF=0).

        oprnd0 = tb.read(instruction.operands[0])

        if isinstance(oprnd0, ReilImmediateOperand):
            oprnd0 = ReilImmediateOperand(oprnd0.immediate << 8, oprnd0.size + 8)

        imm0 = tb.immediate(1, 1)

        tmp0 = tb.temporal(1)
        tmp1 = tb.temporal(1)
        tmp2 = tb.temporal(1)

        tb.add(self._builder.gen_xor(self._flags["cf"], imm0, tmp0))
        tb.add(self._builder.gen_xor(self._flags["zf"], imm0, tmp1))
        tb.add(self._builder.gen_and(tmp0, tmp1, tmp2))
        tb.add(self._builder.gen_jcc(tmp2, oprnd0))

    def _translate_jc(self, tb, instruction):
        # Jump near if carry (CF=1).

        oprnd0 = tb.read(instruction.operands[0])

        if isinstance(oprnd0, ReilImmediateOperand):
            oprnd0 = ReilImmediateOperand(oprnd0.immediate << 8, oprnd0.size + 8)

        tb.add(self._builder.gen_jcc(self._flags["cf"], oprnd0))

    def _translate_jnc(self, tb, instruction):
        # Jump near if not carry (CF=0).

        oprnd0 = tb.read(instruction.operands[0])

        if isinstance(oprnd0, ReilImmediateOperand):
            oprnd0 = ReilImmediateOperand(oprnd0.immediate << 8, oprnd0.size + 8)

        imm0 = tb.immediate(1, 1)

        tmp0 = tb.temporal(1)

        tb.add(self._builder.gen_xor(self._flags["cf"], imm0, tmp0))
        tb.add(self._builder.gen_jcc(tmp0, oprnd0))

    def _translate_jecxz(self, tb, instruction):
        # Jump short if ECX register is 0.

        oprnd0 = tb.read(instruction.operands[0])

        if isinstance(oprnd0, ReilImmediateOperand):
            oprnd0 = ReilImmediateOperand(oprnd0.immediate << 8, oprnd0.size + 8)

        tmp0 = tb.temporal(1)

        ecx = ReilRegisterOperand("ecx", 32)

        tb.add(self._builder.gen_bisz(ecx, tmp0))
        tb.add(self._builder.gen_jcc(tmp0, oprnd0))

    def _translate_call(self, tb, instruction):
        # Flags Affected
        # All flags are affected if a task switch occurs; no flags are
        # affected if a task switch does not occur.

        oprnd0 = tb.read(instruction.operands[0])

        if isinstance(oprnd0, ReilImmediateOperand):
            oprnd0 = ReilImmediateOperand(oprnd0.immediate << 8, oprnd0.size + 8)

        imm1 = tb.immediate(1, 1)
        size = tb.immediate(instruction.size, self._sp.size)

        tmp0 = tb.temporal(self._sp.size)
        tmp1 = tb.temporal(self._sp.size)

        tb.add(self._builder.gen_sub(self._sp, self._ws, tmp0))
        tb.add(self._builder.gen_str(tmp0, self._sp))
        tb.add(self._builder.gen_add(self._ip, size, tmp1))
        tb.add(self._builder.gen_stm(tmp1, self._sp))
        tb.add(self._builder.gen_jcc(imm1, oprnd0))

    def _translate_ret(self, tb, instruction):
        # Flags Affected
        # None.

        tmp0 = tb.temporal(self._sp.size)
        tmp1 = tb.temporal(self._sp.size)

        tb.add(self._builder.gen_ldm(self._sp, tmp1))
        tb.add(self._builder.gen_add(self._sp, self._ws, tmp0))
        tb.add(self._builder.gen_str(tmp0, self._sp))

        # Free stack.
        if len(instruction.operands) > 0:
            oprnd0 = tb.read(instruction.operands[0])

            imm0 = tb.immediate(oprnd0.immediate & (2**self._sp.size -1), self._sp.size)

            tmp2 = tb.temporal(self._sp.size)

            tb.add(self._builder.gen_add(self._sp, imm0, tmp2))
            tb.add(self._builder.gen_str(tmp2, self._sp))

        # TODO: Replace RET instruction with JCC [BYTE 0x1, EMPTY, {D,Q}WORD %0]
        tb.add(self._builder.gen_ret())

# "String Instructions"
# ============================================================================ #

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
