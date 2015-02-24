import os
import pickle
import random
import unittest

import pyasmjit

from barf.analysis.codeanalyzer import CodeAnalyzer
from barf.analysis.gadget.gadget import GadgetType
from barf.analysis.gadget.gadgetclassifier import GadgetClassifier
from barf.analysis.gadget.gadgetfinder import GadgetFinder
from barf.analysis.gadget.gadgetverifier import GadgetVerifier
from barf.arch.arm.armbase import ArmArchitectureInformation
from barf.arch.arm.armtranslator import ArmTranslator
from barf.arch.arm.armdisassembler import ArmDisassembler
from barf.arch import ARCH_ARM_MODE_32
from barf.arch.arm.armtranslator import FULL_TRANSLATION
from barf.arch.arm.armtranslator import LITE_TRANSLATION
from barf.arch.arm.armparser import ArmParser
from barf.core.reil import ReilEmulator
from barf.core.smt.smtlibv2 import Z3Solver as SmtSolver
from barf.core.smt.smttranslator import SmtTranslator
from barf.core.reil import ReilEmptyOperand
from barf.core.reil import ReilEmulator
from barf.core.reil import ReilImmediateOperand
from barf.core.reil import ReilRegisterOperand

class ArmParser32BitsTests(unittest.TestCase):
  
    def setUp(self):
        self._parser = ArmParser(ARCH_ARM_MODE_32)
  
    def test_data_processing_instructions(self):
           
        inst_samples = [
            "add r0, r0, r1, lsl #4",
            "mov r0, #0",
            "add r3, r3, #1",
            "cmp r7, #1000",
            "bic r9, r8, #0xff00",
            "mov r2, r0",
            "add r4, r3, r2",
            "cmp r7, r8",
            "mov r2, r0, lsl #2",
            "add r9, r5, r5, lsl #3",
            "sub r10, r9, r8, lsr #4",
            "mov r12, r4, ror r3",
            "rsb r9, r5, r8, rrx",
            
            # Same with conditino codes
            "addeq r0, r0, r1, lsl #4",
            "movne r0, #0",
            "addcs r3, r3, #1",
            "cmpcc r7, #1000",
            "bicmi r9, r8, #0xff00",
            "movpl r2, r0",
            "addvs r4, r3, r2",
            "cmpvc r7, r8",
            "movhi r2, r0, lsl #2",
            "addls r9, r5, r5, lsl #3",
            "subge r10, r9, r8, lsr #4",
            "movlt r12, r4, ror r3",
            "rsbgt r9, r5, r8, rrx",
            "rsble r9, r5, r8, rrx",
            "rsbal r9, r5, r8, rrx",
        ]
           
        for i in inst_samples:
            asm = self._parser.parse(i)
            self.assertEqual(str(asm), i)
  
    def test_load_store_instructions(self):
          
        inst_samples = [
            "ldr r2, [r3, #4]",
            "ldr r2, [r3, #-0x224]",
            "str r2, [r3, -r3]",
            "ldr r2, [r3, fp, ror #0x2]",
            "str r2, [r3, -#-0x3]",
  
            "ldr r2, [r3, #4]!",
            "str r1, [sp, #-0x2454]!",
            "ldr r2, [r0, -sp]!",
            "str r2, [r9, r12, lsr #0x33]!",
            "ldr r2, [r9, r12, rrx]!",
  
            "ldr r2, [r3], #4",
            "ldr r2, [sp], r0",
            "ldr r2, [r3], #-134314",
            "ldr r2, [r3], r3, lsl #0x12",
              
            #A3.11.4 (examples)
            "ldr r1, [r0]",
            "ldr r8, [r3, #4]",
            "ldr r12, [r13, #-4]",
            "str r2, [r1, #0x100]",
            "strb r4, [r10, #0x200]",
            "strb r10, [r7, -r4]",
            "ldr r11, [r3, r5, lsl #2]",
            "ldr r1, [r0, #4]!",
            "strb r7, [r6, #-1]!",
            "str r2, [r5], #8",
            "ldrh r12, [r13, #-6]",
            "ldrsb r4, [r10, #0xc1]",
            "strh r10, [r7, -r4]",
            "ldrsh r1, [r0, #2]!",
            "ldrsb r7, [r6, #-1]!",
            "strd r8, [r2, #0x2c]",
            "strh r2, [r5], #8",
              
            #A3.12.1 (examples of load/store multiple)
            "stmfd r13, {r0 - r12, lr}",
            "ldmfd r13, {r0 - r12, pc}",
            "ldmia r0, {r5 - r8}",
            "stmda r1, {r2, r5, r7, r11}",
            "stmda r1, {r1, r6 - r9, r11}",
        ]
          
        for i in inst_samples:
            asm = self._parser.parse(i)
            self.assertEqual(str(asm), i)
  
class ArmTranslationTests(unittest.TestCase):
  
    def setUp(self):
        self.trans_mode = FULL_TRANSLATION
  
        self.arch_mode = ARCH_ARM_MODE_32
  
        self.arch_info = ArmArchitectureInformation(self.arch_mode)
  
        self.arm_parser = ArmParser(self.arch_mode)
        self.arm_translator = ArmTranslator(self.arch_mode, self.trans_mode)
        self.smt_solver = SmtSolver()
        self.smt_translator = SmtTranslator(self.smt_solver, self.arch_info.address_size)
        self.reil_emulator = ReilEmulator(self.arch_info.address_size)
  
        self.reil_emulator.set_arch_registers(self.arch_info.registers_gp_all)
        self.reil_emulator.set_arch_registers_size(self.arch_info.registers_size)
        self.reil_emulator.set_reg_access_mapper(self.arch_info.registers_access_mapper())
  
        self.smt_translator.set_reg_access_mapper(self.arch_info.registers_access_mapper())
        self.smt_translator.set_arch_registers_size(self.arch_info.registers_size)
  
        self.context_filename = "failing_context.data"
  
    def __init_context(self):
        """Initialize register with random values.
        """
        #if os.path.isfile(self.context_filename):
        #    context = self.__load_failing_context()
        #else:
        #    context = self.__create_random_context()
        context = self.__create_random_context()
  
        return context
  
    def __create_random_context(self):
        context = {}
  
        for reg in self.arch_info.registers_gp_all:
            if reg not in ['r13', 'r14', 'r15', 'sp', 'lr', 'pc']:
                min_value, max_value = 0, 2**self.arch_info.operand_size - 1
                context[reg] = random.randint(min_value, max_value)
  
        # Only highest 4 bits (N, C, Z, V) are randomized, the rest are left in the default (user mode) value
        context['apsr'] = 0x00000010
        context['apsr'] |= random.randint(0x0, 0xF) << 28
  
        return context
  
    def __load_failing_context(self):
        f = open(self.context_filename, "rb")
        context = pickle.load(f)
        f.close()
  
        return context
  
    def __save_failing_context(self, context):
        f = open(self.context_filename, "wb")
        pickle.dump(context, f)
        f.close()        
  
    def __compare_contexts(self, context_init, arm_context, reil_context):
        match = True
        mask = 2**32-1
  
        for reg in sorted(context_init.keys()):
            if (arm_context[reg] & mask) != (reil_context[reg] & mask):
                match = False
                break
  
        return match
  
    def __print_contexts(self, context_init, arm_context, reil_context):
        out = "Contexts don't match!\n\n"
  
        header_fmt = " {0:^8s} : {1:^16s} | {2:>16s} ?= {3:<16s}\n"
        header = header_fmt.format("Register", "Initial", "ARM", "REIL")
        ruler = "-" * len(header) + "\n"
  
        out += header
        out += ruler
  
        fmt = " {0:>8s} : {1:08x} | {2:08x} {eq} {3:08x} {marker}\n"
  
        mask = 2**64-1
  
        for reg in sorted(context_init.keys()):
            if (arm_context[reg] & mask) != (reil_context[reg] & mask):
                eq, marker = "!=", "<"
            else:
                eq, marker = "==", ""
  
            out += fmt.format(
                reg,
                context_init[reg] & mask,
                arm_context[reg] & mask,
                reil_context[reg] & mask,
                eq=eq,
                marker=marker
            )
  
        # Pretty print flags.
        reg = "apsr"
        fmt = "{0:s} ({1:>4s}) : {2:08x} ({3:s})"
  
        arm_value = arm_context[reg] & mask
        reil_value = reil_context[reg] & mask
  
        if arm_value != reil_value:
            arm_flags_str = self.__print_flags(arm_context[reg])
            reil_flags_str = self.__print_flags(reil_context[reg])
  
            out += "\n"
            out += fmt.format(reg, "ARM", arm_value, arm_flags_str) + "\n"
            out += fmt.format(reg, "reil", reil_value, reil_flags_str)
  
        return out
  
    def __print_flags(self, flags_reg):
        # flags
        flags = {
             31 : "nf",  # bit 31
             30 : "zf",  # bit 30
             29 : "cf",  # bit 29
             28 : "vf",  # bit 28
        }
  
        out = ""
  
        for bit, flag in flags.items():
            flag_str = flag.upper() if flags_reg & 2**bit else flag.lower()
            out +=  flag_str + " "
  
        return out[:-1]
  
    def __fix_reil_flag(self, reil_context, arm_context, flag):
        reil_context_out = dict(reil_context)
  
        flags_reg = 'eflags' if 'eflags' in reil_context_out else 'rflags'
  
        arch_size = self.arch_info.architecture_size
  
        _, bit = self.arch_info.registers_access_mapper()[flag]
  
        # Clean flag.
        reil_context_out[flags_reg] &= ~(2**bit) & (2**32-1)
  
        # Copy flag.
        reil_context_out[flags_reg] |= (arm_context[flags_reg] & 2**bit)
  
        return reil_context_out
  
    def __fix_reil_flags(self, reil_context, arm_context):
        # Remove this when AF and PF are implemented.
        reil_context_out = self.__fix_reil_flag(reil_context, arm_context, "af")
        reil_context_out = self.__fix_reil_flag(reil_context, arm_context, "pf")
  
        return reil_context_out
  
    def __set_address(self, address, arm_instrs):
        addr = address
  
        for arm_instr in arm_instrs:
            arm_instr.address = addr
            addr += 1
  
    def _test_asm_instruction(self, asm):
        print(asm)
  
        arm_instrs = map(self.arm_parser.parse, asm)
  
        self.__set_address(0xdeadbeef, arm_instrs)
  
        reil_instrs = map(self.arm_translator.translate, arm_instrs)
  
        ctx_init = self.__init_context()
  
        arm_rv, arm_ctx_out = pyasmjit.arm_execute("\n".join(asm), ctx_init)
        reil_ctx_out, reil_mem_out = self.reil_emulator.execute(
            reil_instrs,
            0xdeadbeef << 8,
            context=ctx_init
        )
  
        cmp_result = self.__compare_contexts(ctx_init, arm_ctx_out, reil_ctx_out)
  
        if not cmp_result:
            self.__save_failing_context(ctx_init)
  
        self.assertTrue(cmp_result, self.__print_contexts(ctx_init, arm_ctx_out, reil_ctx_out))
  
    # TODO: R13 (SP), R14 (LR), R15 (PC) are outside testing scope for now
      
    def test_data_proc_inst(self):
        inst_samples = [
            # No flags
            ["mov r0, r1"],
            ["mov r3, r8"],
            ["mov r5, r8"],
            ["and r0, r1, r2"],
            ["and r0, r6, #0x33"],
            ["orr r3, r5, r8"],
            ["orr r3, r5, #0x79"],
            ["orr r3, r5, r8, lsl #0x19"],
            ["eor r3, r5, r8"],
            ["eor r8, r4, r5, lsl r6"],
            ["eor r8, r4, r5, lsl #0x11"],
            ["add r8, r9, r11"],
            ["sub r0, r3, r12"],
            ["cmp r3, r12"],
            ["cmn r3, r12"],
            ['mov r8, r5, lsl r6'],
            ['eor r8, r4, r5, lsl r6'],
            ['mul r3, r4, r8'],
            ["mov r8, #0", 'mul r3, r4, r8'],
            ['mul r3, r4, r4'],
              
            # Flags update
            ["movs r0, #0"],
            ["movs r0, #-10"],
            ["mov r0, #0x7FFFFFFF", "mov r1, r0", "adds r3, r0, r1"],
            ["mov r0, #0x7FFFFFFF", "mov r1, r0", "subs r3, r0, r1"],
            ["mov r0, #0x00FFFFFF", "add r1, r0, #10", "subs r3, r0, r1"],
            ["mov r0, #0xFFFFFFFF", "adds r3, r0, #10"],
            ["mov r0, #0x7FFFFFFF", "mov r1,  #5", "adds r3, r0, r1"],
            ["mov r0, #0x80000000", "mov r1,  #5", "subs r3, r0, r1"],
              
              
            # Flags evaluation
            ["moveq r0, r1"],
            ["movne r3, r8"],
            ["movcs r5, r8"],
            ["andcc r0, r1, r2"],
            ["andmi r0, r6, #0x33"],
            ["orrpl r3, r5, r8"],
            ["orrvs r3, r5, #0x79"],
            ["orrvc r3, r5, r8, lsl #0x19"],
            ["eorhi r3, r5, r8"],
            ["eorls r8, r4, r5, lsl r6"],
            ["eorge r8, r4, r5, lsl #0x11"],
            ["addlt r8, r9, r11"],
            ["subgt r0, r3, r12"],
            ["cmple r3, r12"],
            ["cmnal r3, r12"],
            ["addhs r8, r9, r11"],
            ["sublo r0, r3, r12"],
        ]
          
          
        for i in inst_samples:
            self._test_asm_instruction(i)


class ArmGadgetClassifierTests(unittest.TestCase):

    def setUp(self):
        
        self._arch_info = ArmArchitectureInformation(ARCH_ARM_MODE_32)
        self._smt_solver = SmtSolver()
        self._smt_translator = SmtTranslator(self._smt_solver, self._arch_info.address_size)
        self._ir_emulator = ReilEmulator(self._arch_info.address_size)

        self._ir_emulator.set_arch_registers(self._arch_info.registers_gp_all)
        self._ir_emulator.set_arch_registers_size(self._arch_info.registers_size)
        self._ir_emulator.set_reg_access_mapper(self._arch_info.registers_access_mapper())

        self._smt_translator.set_reg_access_mapper(self._arch_info.registers_access_mapper())
        self._smt_translator.set_arch_registers_size(self._arch_info.registers_size)

        self._code_analyzer = CodeAnalyzer(self._smt_solver, self._smt_translator)

        self._g_classifier = GadgetClassifier(self._ir_emulator, self._arch_info)
        self._g_verifier = GadgetVerifier(self._code_analyzer, self._arch_info)

    def _find_and_classify_gadgets(self, binary):
        g_finder = GadgetFinder(ArmDisassembler(), binary, ArmTranslator(translation_mode=LITE_TRANSLATION))

        g_candidates = g_finder.find_arm(0x00000000, len(binary), instrs_depth=4)
        g_classified = self._g_classifier.classify(g_candidates[0])
        
#         self._print_candidates(g_candidates)
#         self._print_classified(g_classified)
        
        return g_candidates, g_classified
        
    def test_move_register_1(self):
        # testing : dst_reg <- src_reg
        binary  = "\x04\x00\xa0\xe1"                     # 0x00 : (4)  mov    r0, r4
        binary += "\x31\xff\x2f\xe1"                     # 0x04 : (4)  blx    r1
        
        g_candidates, g_classified = self._find_and_classify_gadgets(binary)

        self.assertEquals(len(g_candidates), 1)
        self.assertEquals(len(g_classified), 1)

        self.assertEquals(g_classified[0].type, GadgetType.MoveRegister)
        self.assertEquals(g_classified[0].sources, [ReilRegisterOperand("r4", 32)])
        self.assertEquals(g_classified[0].destination, [ReilRegisterOperand("r0", 32)])

        self.assertEquals(len(g_classified[0].modified_registers), 0)
        
        self.assertTrue(self._g_verifier.verify(g_classified[0]))

    def test_move_register_2(self):
        # testing : dst_reg <- src_reg
        binary  = "\x00\x00\x84\xe2"                     # 0x00 : (4)  add    r0, r4, #0
        binary += "\x1e\xff\x2f\xe1"                     # 0x04 : (4)  bx     lr
#         binary += "\x00\x80\xbd\xe8"                     # 0x04 : (4)  pop     {pc} # TODO: Not supported yet because it's not an excplicit jump

        
        g_candidates, g_classified = self._find_and_classify_gadgets(binary)

        self.assertEquals(len(g_candidates), 1)
        self.assertEquals(len(g_classified), 1)

        self.assertEquals(g_classified[0].type, GadgetType.MoveRegister)
        self.assertEquals(g_classified[0].sources, [ReilRegisterOperand("r4", 32)])
        self.assertEquals(g_classified[0].destination, [ReilRegisterOperand("r0", 32)])

        self.assertEquals(len(g_classified[0].modified_registers), 0)
        
        self.assertTrue(self._g_verifier.verify(g_classified[0]))

    # TODO: test_move_register_n: mul r0, r4, #1
    
    def test_load_constant_1(self):
        # testing : dst_reg <- constant
        binary  = "\x0a\x20\xa0\xe3"                     # 0x00 : (4)  mov    r2, #10
        binary += "\x1e\xff\x2f\xe1"                     # 0x04 : (4)  bx     lr
        
        g_candidates, g_classified = self._find_and_classify_gadgets(binary)

        self.assertEquals(len(g_candidates), 1)
        self.assertEquals(len(g_classified), 1)

        self.assertEquals(g_classified[0].type, GadgetType.LoadConstant)
        self.assertEquals(g_classified[0].sources, [ReilImmediateOperand(10, 32)])
        self.assertEquals(g_classified[0].destination, [ReilRegisterOperand("r2", 32)])

        self.assertEquals(len(g_classified[0].modified_registers), 0)
        self.assertFalse(ReilRegisterOperand("r2", 32) in g_classified[0].modified_registers)
        
        self.assertTrue(self._g_verifier.verify(g_classified[0]))

    def test_load_constant_2(self):
        # testing : dst_reg <- constant
        binary  = "\x02\x20\x42\xe0"                     # 0x00 : (4)  sub    r2, r2, r2
        binary += "\x1e\xff\x2f\xe1"                     # 0x04 : (4)  bx     lr
        
        g_candidates, g_classified = self._find_and_classify_gadgets(binary)

        self.assertEquals(len(g_candidates), 1)
        self.assertEquals(len(g_classified), 1)

        self.assertEquals(g_classified[0].type, GadgetType.LoadConstant)
        self.assertEquals(g_classified[0].sources, [ReilImmediateOperand(0, 32)])
        self.assertEquals(g_classified[0].destination, [ReilRegisterOperand("r2", 32)])

        self.assertEquals(len(g_classified[0].modified_registers), 0)
        self.assertFalse(ReilRegisterOperand("r2", 32) in g_classified[0].modified_registers)
        
        self.assertTrue(self._g_verifier.verify(g_classified[0]))

    def test_load_constant_3(self):
        # testing : dst_reg <- constant
        binary  = "\x02\x20\x22\xe0"                     # 0x00 : (4)  eor    r2, r2, r2
        binary += "\x1e\xff\x2f\xe1"                     # 0x04 : (4)  bx     lr
        
        g_candidates, g_classified = self._find_and_classify_gadgets(binary)

        self.assertEquals(len(g_candidates), 1)
        self.assertEquals(len(g_classified), 1)

        self.assertEquals(g_classified[0].type, GadgetType.LoadConstant)
        self.assertEquals(g_classified[0].sources, [ReilImmediateOperand(0, 32)])
        self.assertEquals(g_classified[0].destination, [ReilRegisterOperand("r2", 32)])

        self.assertEquals(len(g_classified[0].modified_registers), 0)
        self.assertFalse(ReilRegisterOperand("r2", 32) in g_classified[0].modified_registers)
        
        self.assertTrue(self._g_verifier.verify(g_classified[0]))

    def test_load_constant_4(self):
        # testing : dst_reg <- constant
        binary  = "\x00\x20\x02\xe2"                     # 0x00 : (4)  and    r2, r2, #0
        binary += "\x1e\xff\x2f\xe1"                     # 0x04 : (4)  bx     lr
        
        g_candidates, g_classified = self._find_and_classify_gadgets(binary)

        self.assertEquals(len(g_candidates), 1)
        self.assertEquals(len(g_classified), 1)

        self.assertEquals(g_classified[0].type, GadgetType.LoadConstant)
        self.assertEquals(g_classified[0].sources, [ReilImmediateOperand(0, 32)])
        self.assertEquals(g_classified[0].destination, [ReilRegisterOperand("r2", 32)])

        self.assertEquals(len(g_classified[0].modified_registers), 0)
        self.assertFalse(ReilRegisterOperand("r2", 32) in g_classified[0].modified_registers)
        
        self.assertTrue(self._g_verifier.verify(g_classified[0]))

    def test_load_constant_5(self):
        # testing : dst_reg <- constant
        binary  = "\x00\x20\x02\xe2"                     # and    r2, r2, #0
        binary += "\x21\x20\x82\xe3"                     # orr    r2, r2, #33
        binary += "\x1e\xff\x2f\xe1"                     # bx     lr
        
        g_candidates, g_classified = self._find_and_classify_gadgets(binary)

        self.assertEquals(len(g_candidates), 1)
        self.assertEquals(len(g_classified), 1)

        self.assertEquals(g_classified[0].type, GadgetType.LoadConstant)
        self.assertEquals(g_classified[0].sources, [ReilImmediateOperand(33, 32)])
        self.assertEquals(g_classified[0].destination, [ReilRegisterOperand("r2", 32)])

        self.assertEquals(len(g_classified[0].modified_registers), 0)
        self.assertFalse(ReilRegisterOperand("r2", 32) in g_classified[0].modified_registers)
        
        self.assertTrue(self._g_verifier.verify(g_classified[0]))

    def test_arithmetic_add_1(self):
        # testing : dst_reg <- src1_reg + src2_reg
        binary  = "\x08\x00\x84\xe0"                     # 0x00 : (4)  add    r0, r4, r8
        binary += "\x1e\xff\x2f\xe1"                     # 0x04 : (4)  bx     lr
        
        g_candidates, g_classified = self._find_and_classify_gadgets(binary)

        self.assertEquals(len(g_candidates), 1)
        self.assertEquals(len(g_classified), 1)
 
        self.assertEquals(g_classified[0].type, GadgetType.Arithmetic)
        self.assertEquals(g_classified[0].sources, [ReilRegisterOperand("r4", 32), ReilRegisterOperand("r8", 32)])
        self.assertEquals(g_classified[0].destination, [ReilRegisterOperand("r0", 32)])
        self.assertEquals(g_classified[0].operation, "+")
 
        self.assertEquals(len(g_classified[0].modified_registers), 0)
        
        self.assertTrue(self._g_verifier.verify(g_classified[0]))
        
    def test_arithmetic_sub_1(self):
        # testing : dst_reg <- src1_reg + src2_reg
        binary  = "\x08\x00\x44\xe0"                     # 0x00 : (4)  sub    r0, r4, r8
        binary += "\x1e\xff\x2f\xe1"                     # 0x04 : (4)  bx     lr
        
        g_candidates, g_classified = self._find_and_classify_gadgets(binary)

        self.assertEquals(len(g_candidates), 1)
        self.assertEquals(len(g_classified), 1)
 
        self.assertEquals(g_classified[0].type, GadgetType.Arithmetic)
        self.assertEquals(g_classified[0].sources, [ReilRegisterOperand("r4", 32), ReilRegisterOperand("r8", 32)])
        self.assertEquals(g_classified[0].destination, [ReilRegisterOperand("r0", 32)])
        self.assertEquals(g_classified[0].operation, "-")
 
        self.assertEquals(len(g_classified[0].modified_registers), 0)
        
        self.assertTrue(self._g_verifier.verify(g_classified[0]))
        
    def test_load_memory_1(self):
        # testing : dst_reg <- m[src_reg]
        binary  = "\x00\x30\x94\xe5"                     # 0x00 : (4)  ldr    r3, [r4]
        binary += "\x1e\xff\x2f\xe1"                     # 0x04 : (4)  bx     lr
        
        g_candidates, g_classified = self._find_and_classify_gadgets(binary)

        self.assertEquals(len(g_candidates), 1)
        self.assertEquals(len(g_classified), 1)
 
        self.assertEquals(g_classified[0].type, GadgetType.LoadMemory)
        self.assertEquals(g_classified[0].sources, [ReilRegisterOperand("r4", 32), ReilImmediateOperand(0x0, 32)])
        self.assertEquals(g_classified[0].destination, [ReilRegisterOperand("r3", 32)])
 
        self.assertEquals(len(g_classified[0].modified_registers), 0)
        
        self.assertTrue(self._g_verifier.verify(g_classified[0]))

    def test_load_memory_2(self):
        # testing : dst_reg <- m[src_reg + offset]
        binary  = "\x33\x30\x94\xe5"                     # 0x00 : (4)  ldr    r3, [r4 + 0x33]
        binary += "\x1e\xff\x2f\xe1"                     # 0x04 : (4)  bx     lr
        
        g_candidates, g_classified = self._find_and_classify_gadgets(binary)

        self.assertEquals(len(g_candidates), 1)
        self.assertEquals(len(g_classified), 1)
 
        self.assertEquals(g_classified[0].type, GadgetType.LoadMemory)
        self.assertEquals(g_classified[0].sources, [ReilRegisterOperand("r4", 32), ReilImmediateOperand(0x33, 32)])
        self.assertEquals(g_classified[0].destination, [ReilRegisterOperand("r3", 32)])
 
        self.assertEquals(len(g_classified[0].modified_registers), 0)
        
        self.assertTrue(self._g_verifier.verify(g_classified[0]))
        
    # TODO: ARM's ldr rd, [rn, r2] is not a valid classification right now
    
    def test_store_memory_1(self):
        # testing : dst_reg <- m[src_reg]
        binary  = "\x00\x30\x84\xe5"                     # 0x00 : (4)  str    r3, [r4]
        binary += "\x1e\xff\x2f\xe1"                     # 0x04 : (4)  bx     lr
        
        g_candidates, g_classified = self._find_and_classify_gadgets(binary)

        self.assertEquals(len(g_candidates), 1)
        self.assertEquals(len(g_classified), 1)
 
        self.assertEquals(g_classified[0].type, GadgetType.StoreMemory)
        self.assertEquals(g_classified[0].sources, [ReilRegisterOperand("r3", 32)])
        self.assertEquals(g_classified[0].destination, [ReilRegisterOperand("r4", 32), ReilImmediateOperand(0x0, 32)])
 
        self.assertEquals(len(g_classified[0].modified_registers), 0)
        
        self.assertTrue(self._g_verifier.verify(g_classified[0]))

    def test_store_memory_2(self):
        # testing : dst_reg <- m[src_reg + offset]
        binary  = "\x33\x30\x84\xe5"                     # 0x00 : (4)  str    r3, [r4 + 0x33]
        binary += "\x1e\xff\x2f\xe1"                     # 0x04 : (4)  bx     lr
        
        g_candidates, g_classified = self._find_and_classify_gadgets(binary)

        self.assertEquals(len(g_candidates), 1)
        self.assertEquals(len(g_classified), 1)
 
        self.assertEquals(g_classified[0].type, GadgetType.StoreMemory)
        self.assertEquals(g_classified[0].sources, [ReilRegisterOperand("r3", 32)])
        self.assertEquals(g_classified[0].destination, [ReilRegisterOperand("r4", 32), ReilImmediateOperand(0x33, 32)])
 
        self.assertEquals(len(g_classified[0].modified_registers), 0)
        
        self.assertTrue(self._g_verifier.verify(g_classified[0]))

    def test_arithmetic_load_add_1(self):
        # testing : dst_reg <- dst_reg + mem[src_reg]
        binary  = "\x00\x30\x94\xe5"                     # 0x00 : (4)  ldr    r3, [r4]
        binary += "\x03\x00\x80\xe0"                     # 0x00 : (4)  add    r0, r0, r3
        binary += "\x1e\xff\x2f\xe1"                     # 0x04 : (4)  bx     lr
        
        g_candidates, g_classified = self._find_and_classify_gadgets(binary)

        self.assertEquals(len(g_candidates), 1)
        self.assertEquals(len(g_classified), 2)
 
        self.assertEquals(g_classified[1].type, GadgetType.ArithmeticLoad)
        self.assertEquals(g_classified[1].sources, [ReilRegisterOperand("r0", 32), ReilRegisterOperand("r4", 32), ReilImmediateOperand(0x0, 32)])
        self.assertEquals(g_classified[1].destination, [ReilRegisterOperand("r0", 32)])
        self.assertEquals(g_classified[1].operation, "+")
 
        self.assertEquals(len(g_classified[1].modified_registers), 1)
        
        self.assertFalse(ReilRegisterOperand("r0", 32) in g_classified[1].modified_registers)
        self.assertTrue(ReilRegisterOperand("r3", 32) in g_classified[1].modified_registers)
        
        self.assertTrue(self._g_verifier.verify(g_classified[1]))

    def test_arithmetic_load_add_2(self):
        # testing : dst_reg <- dst_reg + mem[src_reg + offset]
        binary  = "\x22\x30\x94\xe5"                     # 0x00 : (4)  ldr    r3, [r4, 0x22]
        binary += "\x03\x00\x80\xe0"                     # 0x00 : (4)  add    r0, r0, r3
        binary += "\x1e\xff\x2f\xe1"                     # 0x04 : (4)  bx     lr
        
        g_candidates, g_classified = self._find_and_classify_gadgets(binary)

        self.assertEquals(len(g_candidates), 1)
        self.assertEquals(len(g_classified), 2)
 
        self.assertEquals(g_classified[1].type, GadgetType.ArithmeticLoad)
        self.assertEquals(g_classified[1].sources, [ReilRegisterOperand("r0", 32), ReilRegisterOperand("r4", 32), ReilImmediateOperand(0x22, 32)])
        self.assertEquals(g_classified[1].destination, [ReilRegisterOperand("r0", 32)])
        self.assertEquals(g_classified[1].operation, "+")
 
        self.assertEquals(len(g_classified[1].modified_registers), 1)
        
        self.assertFalse(ReilRegisterOperand("r0", 32) in g_classified[1].modified_registers)
        self.assertTrue(ReilRegisterOperand("r3", 32) in g_classified[1].modified_registers)
        
        self.assertTrue(self._g_verifier.verify(g_classified[1]))

    def test_arithmetic_store_add_1(self):
        # testing : m[dst_reg] <- m[dst_reg] + src_reg
        binary  = "\x00\x30\x94\xe5"                     # 0x00 : (4)  ldr    r3, [r4]
        binary += "\x03\x30\x80\xe0"                     # 0x00 : (4)  add    r3, r0, r3
        binary += "\x00\x30\x84\xe5"                     # 0x00 : (4)  str    r3, [r4]
        binary += "\x1e\xff\x2f\xe1"                     # 0x04 : (4)  bx     lr
        
        g_candidates, g_classified = self._find_and_classify_gadgets(binary)

        self.assertEquals(len(g_candidates), 1)
        self.assertEquals(len(g_classified), 2)
  
        self.assertEquals(g_classified[1].type, GadgetType.ArithmeticStore)
        self.assertEquals(g_classified[1].sources, [ReilRegisterOperand("r4", 32), ReilImmediateOperand(0x0, 32), ReilRegisterOperand("r0", 32)])
        self.assertEquals(g_classified[1].destination, [ReilRegisterOperand("r4", 32), ReilImmediateOperand(0x0, 32)])
        self.assertEquals(g_classified[1].operation, "+")
  
        self.assertEquals(len(g_classified[1].modified_registers), 1)
         
        self.assertFalse(ReilRegisterOperand("r4", 32) in g_classified[1].modified_registers)
        self.assertTrue(ReilRegisterOperand("r3", 32) in g_classified[1].modified_registers)
        
        self.assertTrue(self._g_verifier.verify(g_classified[1]))

    def test_arithmetic_store_add_2(self):
        # testing : dst_reg <- dst_reg + mem[src_reg + offset]
        binary  = "\x22\x30\x94\xe5"                     # 0x00 : (4)  ldr    r3, [r4, 0x22]
        binary += "\x03\x30\x80\xe0"                     # 0x00 : (4)  add    r3, r0, r3
        binary += "\x22\x30\x84\xe5"                     # 0x00 : (4)  str    r3, [r4, 0x22]
        binary += "\x1e\xff\x2f\xe1"                     # 0x04 : (4)  bx     lr
        
        g_candidates, g_classified = self._find_and_classify_gadgets(binary)

        self.assertEquals(len(g_candidates), 1)
        self.assertEquals(len(g_classified), 2)
  
        self.assertEquals(g_classified[1].type, GadgetType.ArithmeticStore)
        self.assertEquals(g_classified[1].sources, [ReilRegisterOperand("r4", 32), ReilImmediateOperand(0x22, 32), ReilRegisterOperand("r0", 32)])
        self.assertEquals(g_classified[1].destination, [ReilRegisterOperand("r4", 32), ReilImmediateOperand(0x22, 32)])
        self.assertEquals(g_classified[1].operation, "+")
  
        self.assertEquals(len(g_classified[1].modified_registers), 1)
         
        self.assertFalse(ReilRegisterOperand("r4", 32) in g_classified[1].modified_registers)
        self.assertTrue(ReilRegisterOperand("r3", 32) in g_classified[1].modified_registers)
        
        self.assertTrue(self._g_verifier.verify(g_classified[1]))

    def _print_candidates(self, candidates):
        print "Candidates :"

        for g in candidates:
            print g
            print "-" * 10

    def _print_classified(self, classified):
        print "Classified :"

        for g in classified:
            print g
            print g.type
            print "-" * 10


def main():
    unittest.main()


if __name__ == '__main__':
    main()
