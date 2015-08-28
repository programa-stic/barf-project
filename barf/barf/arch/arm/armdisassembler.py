# Copyright (c) 2014, Fundacion Dr. Manuel Sadosky
# All rights reserved.
from barf.arch.arch import ARCH_ARM_MODE_THUMB

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

"""
This modules contains a ARM disassembler based on the Capstone
disassembly framework.

"""
from capstone import *
from capstone.arm import *

from barf.arch import ARCH_ARM_MODE_32
from barf.arch import ARCH_ARM_MODE_ARM
from barf.arch import ARCH_ARM_MODE_THUMB
from barf.arch import ARCH_ARM_MODES_MAX
from barf.arch.arm.armparser import ArmParser
from barf.core.disassembler import Disassembler

from barf.arch.arm.armbase import ArmInstruction
from barf.arch.arm.armbase import *

cc_capstone_barf_mapper = {
    ARM_CC_EQ : ARM_COND_CODE_EQ,
    ARM_CC_NE : ARM_COND_CODE_NE,
    ARM_CC_MI : ARM_COND_CODE_MI,
    ARM_CC_PL : ARM_COND_CODE_PL,
    ARM_CC_VS : ARM_COND_CODE_VS,
    ARM_CC_VC : ARM_COND_CODE_VC,
    ARM_CC_HI : ARM_COND_CODE_HI,
    ARM_CC_LS : ARM_COND_CODE_LS,
    ARM_CC_GE : ARM_COND_CODE_GE,
    ARM_CC_LT : ARM_COND_CODE_LT,
    ARM_CC_GT : ARM_COND_CODE_GT,
    ARM_CC_LE : ARM_COND_CODE_LE,
    ARM_CC_AL : ARM_COND_CODE_AL,
    ARM_CC_HS : ARM_COND_CODE_HS,
    ARM_CC_LO : ARM_COND_CODE_LO,
}

arch_mode_barf_to_capstone_mapper = {
    ARCH_ARM_MODE_ARM : CS_MODE_ARM,
    ARCH_ARM_MODE_THUMB : CS_MODE_THUMB,
}

class ArmDisassembler(Disassembler):
    """ARM Disassembler.
    """

    def __init__(self, architecture_mode=ARCH_ARM_MODE_32):
        super(ArmDisassembler, self).__init__()
        
        self._architecture_mode = architecture_mode
        self._arch_info = ArmArchitectureInformation(architecture_mode)

        arch_mode_map = {
            # TODO: ARM vs CS_MODE_THUMB
            ARCH_ARM_MODE_32 : CS_MODE_THUMB,
        }

        self._parser = ArmParser(architecture_mode)
        
        self._avaliable_disassemblers = [None] * ARCH_ARM_MODES_MAX
        self._avaliable_disassemblers[ARCH_ARM_MODE_ARM] = Cs(CS_ARCH_ARM, arch_mode_barf_to_capstone_mapper[ARCH_ARM_MODE_ARM])
        self._avaliable_disassemblers[ARCH_ARM_MODE_THUMB] = Cs(CS_ARCH_ARM, arch_mode_barf_to_capstone_mapper[ARCH_ARM_MODE_THUMB])
        # TODO: DECOUPLE: detail true vs false
        self._avaliable_disassemblers[ARCH_ARM_MODE_ARM].detail = True
        self._avaliable_disassemblers[ARCH_ARM_MODE_THUMB].detail = True
        
        self._disassembler = self._avaliable_disassemblers[0]

    def _cs_translate_operand(self, cs_op, cs_insn):
        
        if cs_op.type == ARM_OP_REG:
            name = cs_insn.reg_name(cs_op.value.reg)
            if name in self._arch_info.registers_size:
                size = self._arch_info.registers_size[name]
            else:
                size = self._arch_info.architecture_size
            oprnd = ArmRegisterOperand(name, size)

        elif cs_op.type == ARM_OP_IMM:
            size = self._arch_info.operand_size
            oprnd = ArmImmediateOperand(cs_op.value.imm, size)

        elif cs_op.type == ARM_OP_MEM:
            oprnd = None
            pass
        else:
            oprnd = None
            pass
            # TODO other operands
#             raise Exception("Unknown Capstone operand type.")
        
        return oprnd

    def _cs_translate_insn(self, cs_insn):

        operands = [self._cs_translate_operand(op, cs_insn) for op in cs_insn.operands]
        
        # Special case: register list "{rX - rX}", stored as a series of registers has
        # to be converted to ArmRegisterListOperand.
        if "{" in cs_insn.op_str:
            print "REGLIST"
            reg_list = []
            op_translated = []
            if not("push" in cs_insn.mnemonic or "pop" in cs_insn.mnemonic):
                # First operand is the base (in push/pop, the base register, sp,  is omitted)
                op_translated.append(operands[0])
                operands = operands[1:]
                 
            for r in operands:
                reg_list.append([r])
    
            op_translated.append(ArmRegisterListOperand(reg_list, reg_list[0][0].size))
            
            operands = op_translated
            
        # TODO: Temporary hack to accommodate THUMB short notation:
        # "add r0, r1" -> "add r0, r0, r1"
        if len(operands) == 2 and (cs_insn.mnemonic == "add" or
                                   cs_insn.mnemonic == "eor" or
                                   cs_insn.mnemonic == "orr" or
                                   cs_insn.mnemonic == "sub"):
            operands = [operands[0],operands[0],operands[1]]

        # TODO: Remove suffixes of the mnemonic (cs_insn.mnemonic[:-2])
    
        instr = ArmInstruction(
            cs_insn.mnemonic + " " + cs_insn.op_str,
            cs_insn.mnemonic,
            operands,
            self._architecture_mode
        )
        
        #DEBUG
#         import binascii
#         print "ORIG INSN: " + instr.orig_instr + "   ADD: " + hex(cs_insn.address) + "   SIZE: " + str(cs_insn.size)
#         import pprint
#         pprint.pprint(cs_insn.bytes)
    
        if cs_insn.cc is not ARM_CC_INVALID:
            instr.condition_code = cc_capstone_barf_mapper[cs_insn.cc]
    
        if cs_insn.update_flags:
            instr.update_flags = True
    
        # TODO: LOAD/STORE MODE (it may be necessary to parse the mnemonic).    
#         if "ldm_stm_addr_mode" in mnemonic:
#             instr.ldm_stm_addr_mode = ldm_stm_am_mapper[mnemonic["ldm_stm_addr_mode"]]
    
        return instr

    def disassemble(self, data, address, used_disassembler = 0):
        """Disassemble the data into an instruction.
        """
        
        self._disassembler = self._avaliable_disassemblers[used_disassembler]
        
        # TODO: DECOUPLE: parser vs capstone translation
        disasm = self._cs_disassemble_one(data, address)
        
        instr =  self._cs_translate_insn(disasm)

        if instr:
            instr.address = address
            instr.size = disasm.size
            instr.bytes = data[0:disasm.size]
 
        return instr
        
        

#         asm, size = self._cs_disassemble_one(data, address)
# 
#         instr = self._parser.parse(asm) if asm else None
# 
#         if instr:
#             instr.address = address
#             instr.size = size
#             instr.bytes = data[0:size]
# 
#         return instr

    def disassemble_all(self, data, address):
        """Disassemble the data into multiple instructions.
        """
        raise NotImplementedError()

    def _cs_disassemble_one(self, data, address):
        """Disassemble the data into an instruction in string form.
        """
        # TODO: DECOUPLE: disasm_lite vs disasm
        disasm = list(self._disassembler.disasm(data, address))
    
        if len(disasm) > 0:
            return disasm[0]
        else:
            cs_arm = Cs(CS_ARCH_ARM, CS_MODE_ARM)
            disasm = list(cs_arm.disasm(data, address))
            if len(disasm) > 0:
                return disasm[0]
            else:
                raise Exception("CAPSTONE: Unknown instruction (Addr: {:s}).".format(hex(address)))
            

#         asm, size = "", 0
# 
#         disasm = list(self._disassembler.disasm(data, address))
# 
#         if len(disasm) > 0:
#             address, size, mnemonic, op_str = disasm[0]
# 
#             asm = str(mnemonic + " " + op_str).strip()
#         else:
#             # FIXME: Hack to bypass immediate constants embedded in the
#             # text section that do not conform to any valid instruction.
#             asm = "mov r0, r0" # Preferred ARM no-operation code
#             size = 4
# 
#         return asm, size
