import logging

import barf

from barf.arch import ARCH_ARM_MODE_32
from barf.arch import ARCH_ARM_MODE_64
from barf.arch.arm.armbase import ArmArchitectureInformation
from barf.arch.arm.armbase import ArmShifterOperand
from barf.arch.arm.armbase import ArmImmediateOperand
from barf.arch.arm.armbase import ArmMemoryOperand
from barf.arch.arm.armbase import ArmRegisterOperand
from barf.arch.arm.armbase import ArmRegisterListOperand
from barf.core.reil import ReilEmptyOperand
from barf.core.reil import ReilImmediateOperand
from barf.core.reil import ReilInstructionBuilder
from barf.core.reil import ReilInstruction
from barf.core.reil import ReilMnemonic
from barf.core.reil import ReilRegisterOperand
from barf.utils.utils import VariableNamer
from barf.arch.arm.armbase import ARM_MEMORY_INDEX_OFFSET
from barf.arch.arm.armbase import ARM_MEMORY_INDEX_POST
from barf.arch.arm.armbase import ARM_MEMORY_INDEX_PRE
from barf.arch.arm.armbase import ARM_COND_CODE_EQ
from barf.arch.arm.armbase import ARM_COND_CODE_NE
from barf.arch.arm.armbase import ARM_COND_CODE_CS
from barf.arch.arm.armbase import ARM_COND_CODE_CC
from barf.arch.arm.armbase import ARM_COND_CODE_MI
from barf.arch.arm.armbase import ARM_COND_CODE_PL
from barf.arch.arm.armbase import ARM_COND_CODE_VS
from barf.arch.arm.armbase import ARM_COND_CODE_VC
from barf.arch.arm.armbase import ARM_COND_CODE_HI
from barf.arch.arm.armbase import ARM_COND_CODE_LS
from barf.arch.arm.armbase import ARM_COND_CODE_GE
from barf.arch.arm.armbase import ARM_COND_CODE_LT
from barf.arch.arm.armbase import ARM_COND_CODE_GT
from barf.arch.arm.armbase import ARM_COND_CODE_LE
from barf.arch.arm.armbase import ARM_COND_CODE_AL

FULL_TRANSLATION = 0
LITE_TRANSLATION = 1

logger = logging.getLogger(__name__)

class Label(object):

    def __init__(self, name):
        self.name = name

    def __str__(self):
        string = self.name + ":"

        return string


class TranslationBuilder(object):

    def __init__(self, ir_name_generator, architecture_mode):
        self._ir_name_generator = ir_name_generator

        self._arch_info = ArmArchitectureInformation(architecture_mode)

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
            
        instrs = self._resolve_loops(instrs)

        return instrs

    def read(self, arm_operand):

        if isinstance(arm_operand, ArmImmediateOperand):

            reil_operand = ReilImmediateOperand(arm_operand.immediate, arm_operand.size)

        elif isinstance(arm_operand, ArmRegisterOperand):

            reil_operand = ReilRegisterOperand(arm_operand.name, arm_operand.size)

        elif isinstance(arm_operand, ArmShifterOperand):
            
            reil_operand = self._compute_shifter_operand(arm_operand)

        elif isinstance(arm_operand, ArmMemoryOperand):
 
            addr = self._compute_memory_address(arm_operand)
 
            reil_operand = self.temporal(arm_operand.size)
 
            self.add(self._builder.gen_ldm(addr, reil_operand))
            
        elif isinstance(arm_operand, ArmRegisterListOperand):
 
            reil_operand = self._compute_register_list(arm_operand)
 
        else:
            raise NotImplementedError("Instruction Not Implemented: Unknown operand for read operation.")

        return reil_operand

    def write(self, arm_operand, value):

        if isinstance(arm_operand, ArmRegisterOperand):

            reil_operand = ReilRegisterOperand(arm_operand.name, arm_operand.size)

            self.add(self._builder.gen_str(value, reil_operand))

        elif isinstance(arm_operand, ArmMemoryOperand):
 
            addr = self._compute_memory_address(arm_operand)
 
            self.add(self._builder.gen_stm(value, addr))

        else:
            raise NotImplementedError("Instruction Not Implemented: Unknown operand for write operation.")

    def _resolve_loops(self, instrs):
        idx_by_labels = {}

        # Collect labels.
        curr = 0
        for index, instr in enumerate(instrs):
            if isinstance(instr, Label):
                idx_by_labels[instr.name] = curr

                del instrs[index]
            else:
                curr += 1

        # Resolve instruction addresses and JCC targets.
        for index, instr in enumerate(instrs):
            assert isinstance(instr, ReilInstruction)

            instr.address |= index

            if instr.mnemonic == ReilMnemonic.JCC:
                target = instr.operands[2]

                if isinstance(target, Label):
                    idx = idx_by_labels[target.name]
                    address = (instr.address & ~0xff) | idx

                    instr.operands[2] = ReilImmediateOperand(address, 40)

        return instrs

    def _compute_shifter_operand(self, sh_op):
        
        base = ReilRegisterOperand(sh_op.base_reg.name, sh_op.size)
        
        if sh_op.shift_amount:
            ret = self.temporal(sh_op.size)
            
            if isinstance(sh_op.shift_amount, ArmImmediateOperand):
                sh_am = ReilImmediateOperand(sh_op.shift_amount.immediate, sh_op.size)
            elif isinstance(sh_op.shift_amount, ArmRegisterOperand):
                sh_am = ReilRegisterOperand(sh_op.shift_amount.name, sh_op.shift_amount.size)
            else:
                raise NotImplementedError("Instruction Not Implemented: Unknown shift amount type.")
            
            if (sh_op.shift_type == 'lsl'):
                self.add(self._builder.gen_bsh(base, sh_am, ret))
            else:
                # TODO: Implement other shift types
                raise NotImplementedError("Instruction Not Implemented: Shift type.")
        else:
            ret = base

        return ret

    def _compute_memory_address(self, mem_operand):
        """Return operand memory access translation.
        """
        base = ReilRegisterOperand(mem_operand.base_reg.name, mem_operand.size)
        
        if mem_operand.displacement:
            ret = self.temporal(mem_operand.size)
            
            if isinstance(mem_operand.displacement, ArmRegisterOperand):
                disp = ReilRegisterOperand(mem_operand.displacement.name, mem_operand.size)
            elif isinstance(mem_operand.displacement, ArmImmediateOperand):
                disp = ReilImmediateOperand(mem_operand.displacement.immediate, mem_operand.size)
            elif isinstance(mem_operand.displacement, ArmShifterOperand):
                disp = self._compute_shifter_operand(mem_operand.displacement)
            else:
                raise NotImplementedError("Instruction Not Implemented")
    
            if mem_operand.disp_minus:
                self.add(self._builder.gen_sub(base, disp, ret))
            else:
                self.add(self._builder.gen_add(base, disp, ret))

            if mem_operand.index_type == ARM_MEMORY_INDEX_PRE:
                self.add(self._builder.gen_add(base, disp, base))
        else:
            ret = base

        return ret

    def _compute_register_list(self, operand):
        """Return operand register list.
        """
        
        ret = []
        for reg_range in operand.reg_list:
            if len(reg_range) == 1:
                ret.append(ReilRegisterOperand(reg_range[0].name, reg_range[0].size))
            else:
                reg_num = int(reg_range[0][1:]) # Assuming the register is named with one letter + number
                reg_end = int(reg_range[1][1:])
                if reg_num > reg_end:
                    raise NotImplementedError("Instruction Not Implemented: Invalid register range.")
                while reg_num <= reg_end:
                    ret.append(ReilRegisterOperand(reg_range[0].name[0] + str(reg_num), reg_range[0].size))
                    reg_num = reg_num + 1
        
        return ret


class ArmTranslator(object):

    """ARM to IR Translator."""

    def __init__(self, architecture_mode=ARCH_ARM_MODE_32, translation_mode=FULL_TRANSLATION):

        # Set *Architecture Mode*. The translation of each instruction
        # into the REIL language is based on this.
        self._arch_mode = architecture_mode

        # An instance of *ArchitectureInformation*.
        self._arch_info = ArmArchitectureInformation(architecture_mode)

        # Set *Translation Mode*.
        self._translation_mode = translation_mode

        # An instance of a *VariableNamer*. This is used so all the
        # temporary REIL registers are unique.
        self._ir_name_generator = VariableNamer("t", separator="")

        self._builder = ReilInstructionBuilder()

        self._flags = {
            "nf" : ReilRegisterOperand("nf", 1),
            "zf" : ReilRegisterOperand("zf", 1),
            "cf" : ReilRegisterOperand("cf", 1),
            "vf" : ReilRegisterOperand("vf", 1),
        }

        if self._arch_mode == ARCH_ARM_MODE_32:
            self._sp = ReilRegisterOperand("sp", 32)
            self._bp = ReilRegisterOperand("bp", 32)
            self._ip = ReilRegisterOperand("ip", 32)

            self._ws = ReilImmediateOperand(4, 32) # word size
        elif self._arch_mode == ARCH_ARM_MODE_64:
            self._sp = ReilRegisterOperand("sp", 64)
            self._bp = ReilRegisterOperand("bp", 64)
            self._ip = ReilRegisterOperand("ip", 64)

            self._ws = ReilImmediateOperand(8, 64) # word size

    def translate(self, instruction):
        """Return IR representation of an instruction.
        """
        try:
            trans_instrs = self._translate(instruction)
        except NotImplementedError as e:
            trans_instrs = [self._builder.gen_unkn()]

            self._log_not_supported_instruction(instruction)
            print("NotImplementedError: " + str(e))
            print(instruction)
#         except Exception as e:
#             trans_instrs = [self._builder.gen_unkn()]
#             self._log_translation_exception(instruction)
#             print("Exception: " + str(e))
#             print(instruction)

        return trans_instrs

    def _translate(self, instruction):
        """Translate a arm instruction into REIL language.

        :param instruction: a arm instruction
        :type instruction: ArmInstruction
        """
        
        # Retrieve translation function.
        translator_name = "_translate_" + instruction.mnemonic
        translator_fn = getattr(self, translator_name, self._not_implemented)

        # Translate instruction.
        tb = TranslationBuilder(self._ir_name_generator, self._arch_mode)

        # Pre-processing: evaluate flags
        nop_cc_lbl = tb.label('condition_code_not_met')
        self._evaluate_condition_code(tb, instruction, nop_cc_lbl)
        
        
        translator_fn(tb, instruction)


        # Post-processing: update flags
        pass
    
        tb.add(nop_cc_lbl)
        
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
            "Failed to translate arm to REIL: %s (%s)",
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
    def _update_nf(self, tb, oprnd0, oprnd1, result):
        # Create temporal variables.
        tmp0 = tb.temporal(result.size)

        mask0 = tb.immediate(2**result.size-1, result.size)
        shift0 = tb.immediate(-(result.size-1), result.size)

        tb.add(self._builder.gen_and(result, mask0, tmp0))  # filter sign bit
        tb.add(self._builder.gen_bsh(tmp0, shift0, self._flags["nf"]))     # extract sign bit

    def _update_vf(self, tb, oprnd0, oprnd1, result):
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
        tb.add(self._builder.gen_bsh(tmp6, imm3, self._flags["vf"]))

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
        
    def _all_ones_imm(self, tb, reg):
        return tb.immediate((2**reg.size) - 1, reg.size)
                            
    def _negate_reg(self, tb, reg):
        neg = tb.temporal(reg.size)
        tb.add(self._builder.gen_xor(reg, self._all_ones_imm(tb, reg), neg))
        return neg
    
    def _and_regs(self, tb, reg1, reg2):
        ret = tb.temporal(reg1.size)
        tb.add(self._builder.gen_and(reg1, reg2, ret))
        return ret
        
    def _or_regs(self, tb, reg1, reg2):
        ret = tb.temporal(reg1.size)
        tb.add(self._builder.gen_or(reg1, reg2, ret))
        return ret
        
    def _xor_regs(self, tb, reg1, reg2):
        ret = tb.temporal(reg1.size)
        tb.add(self._builder.gen_xor(reg1, reg2, ret))
        return ret
        
    def _equal_regs(self, tb, reg1, reg2):
        return self._negate_reg(tb, self._xor_regs(tb, reg1, reg2))
        
    # EQ: Z set
    def _evaluate_eq(self, tb):
        return self._flags["zf"]

    # NE: Z clear
    def _evaluate_ne(self, tb):
        return self._negate_reg(tb, self._flags["zf"])
    
    # CS: C set
    def _evaluate_cs(self, tb):
        return self._flags["cf"]

    # CC: C clear
    def _evaluate_cc(self, tb):
        return self._negate_reg(tb, self._flags["cf"])
    
    # MI: N set
    def _evaluate_mi(self, tb):
        return self._flags["nf"]

    # PL: N clear
    def _evaluate_pl(self, tb):
        return self._negate_reg(tb, self._flags["nf"])
    
    # VS: V set
    def _evaluate_vs(self, tb):
        return self._flags["vf"]

    # VC: V clear
    def _evaluate_vc(self, tb):
        return self._negate_reg(tb, self._flags["vf"])
    
    # HI: C set and Z clear
    def _evaluate_hi(self, tb):
        return self._and_regs(tb, self._flags["cf"], self._negate_reg(tb, self._flags["zf"]))

    # LS: C clear or Z set
    def _evaluate_ls(self, tb):
        return self._or_regs(tb, self._negate_reg(tb, self._flags["cf"]), self._flags["zf"])
    
    # GE: N == V
    def _evaluate_ge(self, tb):
        return self._equal_regs(tb, self._flags["nf"], self._flags["vf"])

    # LT: N != V
    def _evaluate_lt(self, tb):
        return self._negate_reg(tb, self._evaluate_ge(tb))
    
    # GT: (Z == 0) and (N == V)
    def _evaluate_gt(self, tb):
        return self._and_regs(tb, self._negate_reg(tb, self._flags["zf"]), self._evaluate_ge(tb))

    # LE: (Z == 1) or (N != V)
    def _evaluate_le(self, tb):
        return self._or_regs(tb, self._flags["zf"], self._evaluate_lt(tb))
    
    def _evaluate_condition_code(self, tb, instruction, nop_label):
        if (instruction.condition_code == ARM_COND_CODE_AL):
            return
        
        eval_cc_fn = {
            ARM_COND_CODE_EQ : self._evaluate_eq,
            ARM_COND_CODE_NE : self._evaluate_ne,
            ARM_COND_CODE_CS : self._evaluate_cs,
            ARM_COND_CODE_CC : self._evaluate_cc,
            ARM_COND_CODE_MI : self._evaluate_mi,
            ARM_COND_CODE_PL : self._evaluate_pl,
            ARM_COND_CODE_VS : self._evaluate_vs,
            ARM_COND_CODE_VC : self._evaluate_vc,
            ARM_COND_CODE_HI : self._evaluate_hi,
            ARM_COND_CODE_LS : self._evaluate_ls,
            ARM_COND_CODE_GE : self._evaluate_ge,
            ARM_COND_CODE_LT : self._evaluate_lt,
            ARM_COND_CODE_GT : self._evaluate_gt,
            ARM_COND_CODE_LE : self._evaluate_le,
        }
        
        neg_cond = self._negate_reg(tb, eval_cc_fn[instruction.condition_code](tb))
        
        tb.add(self._builder.gen_jcc(neg_cond, nop_label))
        
        return 
    

# "Data Transfer Instructions"
# ============================================================================ #
    def _translate_mov(self, tb, instruction):
        # Flags Affected
        # None.
        
        oprnd1 = tb.read(instruction.operands[1])

        tb.write(instruction.operands[0], oprnd1)


    # TODO: Add post-indexing (pre is included in compute_memory).
    def _translate_ldr(self, tb, instruction):
        
        oprnd1 = tb.read(instruction.operands[1])

        tb.write(instruction.operands[0], oprnd1)
    
    def _translate_str(self, tb, instruction):
        
        oprnd0 = tb.read(instruction.operands[0])

        tb.write(instruction.operands[1], oprnd0)
        
    def _translate_add(self, tb, instruction):
        oprnd1 = tb.read(instruction.operands[1])
        oprnd2 = tb.read(instruction.operands[2])

        tmp = tb.temporal(oprnd1.size)

        tb.add(self._builder.gen_add(oprnd1, oprnd2, tmp))

        tb.write(instruction.operands[0], tmp)

    def _translate_sub(self, tb, instruction):
        oprnd1 = tb.read(instruction.operands[1])
        oprnd2 = tb.read(instruction.operands[2])

        tmp = tb.temporal(oprnd1.size)

        tb.add(self._builder.gen_sub(oprnd1, oprnd2, tmp))

        tb.write(instruction.operands[0], tmp)

    def _translate_push(self, tb, instruction):
        # Flags Affected
        # None.

        oprnd0 = tb.read(instruction.operands[0])

        tmp0 = tb.temporal(self._sp.size)

        # TODO RESPECT REGISTER ORDER
        oprnd0.reverse() # Assuming the register list was in order
        for reg in oprnd0:
            tb.add(self._builder.gen_sub(self._sp, self._ws, tmp0))
            tb.add(self._builder.gen_str(tmp0, self._sp))
            tb.add(self._builder.gen_stm(reg, self._sp))

    def _translate_pop(self, tb, instruction):
        # Flags Affected
        # None.

#         size = self._arch_info.architecture_size

        oprnd0 = tb.read(instruction.operands[0])

        tmp0 = tb.temporal(self._sp.size)

        # TODO RESPECT REGISTER ORDER
        for reg in oprnd0:
            tb.add(self._builder.gen_ldm(self._sp, reg))
            tb.add(self._builder.gen_add(self._sp, self._ws, tmp0))
            tb.add(self._builder.gen_str(tmp0, self._sp))
