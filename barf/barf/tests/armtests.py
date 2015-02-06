import os
import pickle
import random
import unittest

import pyasmjit

from barf.arch.arm.armbase import ArmArchitectureInformation
from barf.arch.arm.armtranslator import ArmTranslator
from barf.arch import ARCH_ARM_MODE_32
from barf.arch.arm.armtranslator import FULL_TRANSLATION
from barf.arch.arm.armtranslator import LITE_TRANSLATION
from barf.arch.arm.armparser import ArmParser
from barf.core.reil import ReilEmulator
from barf.core.smt.smtlibv2 import Z3Solver as SmtSolver
from barf.core.smt.smttranslator import SmtTranslator

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
            "rsb r9, r5, r8, rrx"
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
            # TODO: Fix how ldm/stm are printed (regarding addressing mode aliases)
#             "stmfd r13, {r0 - r12, lr}",
#             "ldmfd r13, {r0 - r12, pc}",
#             "ldmia r0, {r5 - r8}",
#             "stmda r1, {r2, r5, r7, r11}",
#             "stmda r1, {r1, r6 - r9, r11}",
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
        if os.path.isfile(self.context_filename):
            context = self.__load_failing_context()
        else:
            context = self.__create_random_context()

        return context

    def __create_random_context(self):
        context = {}

        for reg in self.arch_info.registers_gp_all:
            if reg not in ['r13', 'r14', 'r15', 'sp', 'lr', 'pc']:
                min_value, max_value = 0, 2**self.arch_info.operand_size - 1
                context[reg] = random.randint(min_value, max_value)

        context['apsr'] = 0x10

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

        fmt = " {0:>8s} : {1:016x} | {2:016x} {eq} {3:016x} {marker}\n"

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
        fmt = "{0:s} ({1:>4s}) : {2:016x} ({3:s})"

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

    def test_and(self):
        asm = ["and r1, r2, r3"]

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

#         reil_ctx_out = self.__fix_reil_flags(reil_ctx_out, arm_ctx_out)

        cmp_result = self.__compare_contexts(ctx_init, arm_ctx_out, reil_ctx_out)

        if not cmp_result:
            self.__save_failing_context(ctx_init)

        self.assertTrue(cmp_result, self.__print_contexts(ctx_init, arm_ctx_out, reil_ctx_out))


def main():
    unittest.main()


if __name__ == '__main__':
    main()
