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

import pickle
import random
import unittest
import struct

import pyasmjit

from barf.arch import ARCH_ARM_MODE_32
from barf.arch.arm.armbase import ArmArchitectureInformation
from barf.arch.arm.armparser import ArmParser
from barf.arch.arm.armtranslator import ArmTranslator
from barf.arch.arm.armtranslator import FULL_TRANSLATION
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
        self.reil_emulator = ReilEmulator(self.arch_info.address_size)

        self.reil_emulator.set_arch_registers(self.arch_info.registers_gp_all)
        self.reil_emulator.set_arch_registers_size(self.arch_info.registers_size)
        self.reil_emulator.set_reg_access_mapper(self.arch_info.alias_mapper)

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

        for reg in self.arch_info.registers_gp_base:
            if reg not in ['r13', 'r14', 'r15']:
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

        _, bit = self.arch_info.alias_mapper[flag]

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
            arm_instr.size = 4
            addr += 4

    def _test_asm_instruction(self, asm):
        print(asm)

        arm_instrs = map(self.arm_parser.parse, asm)

        self.__set_address(0xdeadbeef, arm_instrs)

        reil_instrs = map(self.arm_translator.translate, arm_instrs)

        ctx_init = self.__init_context()

        arm_rv, arm_ctx_out, _ = pyasmjit.arm_execute("\n".join(asm), ctx_init)
        reil_ctx_out, reil_mem_out = self.reil_emulator.execute(
            reil_instrs,
            0xdeadbeef << 8,
            context=ctx_init
        )

        cmp_result = self.__compare_contexts(ctx_init, arm_ctx_out, reil_ctx_out)

        if not cmp_result:
            self.__save_failing_context(ctx_init)

        self.assertTrue(cmp_result, self.__print_contexts(ctx_init, arm_ctx_out, reil_ctx_out))

    def _execute_asm(self, asm, ini_addr = 0x8000):
        print(asm)

        arm_instrs = map(self.arm_parser.parse, asm)

        self.__set_address(ini_addr, arm_instrs)

        reil_instrs = map(self.arm_translator.translate, arm_instrs)

#         for rr in reil_instrs:
#             for reil_instr in rr:
#                 print("{0:14} : {1}".format(hex(reil_instr.address), reil_instr))

        ctx_init = self.__init_context()

        reil_ctx_out, reil_mem_out = self.reil_emulator.execute(
            reil_instrs,
            0xdeadbeef << 8,
            context=ctx_init
        )

        return reil_ctx_out

    # R11 is used as a dirty register to check if the branch was taken or not
    def test_asm_branch_instruction(self):
        untouched_value = 0x45454545
        touched_value = 0x31313131

        inst_samples_touched = [
            ["mov r11, #0x{:x}".format(untouched_value),
               "b #0x800c",
               "mov r11, #0x{:x}".format(touched_value),
               "mov r0, r0",
            ],

            ["mov r11, #0x{:x}".format(untouched_value),
               "bx #0x800c",
               "mov r11, #0x{:x}".format(touched_value),
               "mov r0, r0",
            ],

            ["mov r11, #0x{:x}".format(untouched_value),
               "bl #0x800c",
               "mov r11, #0x{:x}".format(touched_value),
               "mov r0, r0",
            ],

            ["mov r11, #0x{:x}".format(untouched_value),
               "blx #0x800c",
               "mov r11, #0x{:x}".format(touched_value),
               "mov r0, r0",
            ],

            ["movs r11, #0x{:x}".format(untouched_value),
               "bne #0x800c",
               "mov r11, #0x{:x}".format(touched_value),
               "mov r0, r0",
            ],

            ["mov r11, #0x{:x}".format(untouched_value),
               "mov r1, #0x8010",
               "bx r1",
               "mov r11, #0x{:x}".format(touched_value),
               "mov r0, r0",
            ],

            ["mov r11, #0x{:x}".format(untouched_value),
               "mov r1, #0x8010",
               "blx r1",
               "mov r11, #0x{:x}".format(touched_value),
               "mov r0, r0",
            ],

        ]


        for asm in inst_samples_touched:
            reil_ctx_out = self._execute_asm(asm, 0x8000)
            self.assertTrue(reil_ctx_out['r11'] == untouched_value)
#             print reil_ctx_out

    # TODO: Merge with previous test function
    def _test_asm_instruction_with_mem(self, asm, reg_mem):
        print(asm)

        mem_dir = pyasmjit.arm_alloc(4096)

        # print("DIR (in Python): " + hex(mem_dir))

        arm_instrs = map(self.arm_parser.parse, asm)

        self.__set_address(0xdeadbeef, arm_instrs)

        reil_instrs = map(self.arm_translator.translate, arm_instrs)

        ctx_init = self.__init_context()

        ctx_init[reg_mem] = mem_dir

        arm_rv, arm_ctx_out, arm_mem_out = pyasmjit.arm_execute("\n".join(asm), ctx_init)

        self.reil_emulator._mem._memory = {} # TODO: Check how to clean emulator memory.

        #for reil_instr in reil_instrs:
        #    for r in reil_instr:
        #        print("{0:14}{1}".format("", r))


        reil_ctx_out, reil_mem_out = self.reil_emulator.execute(
            reil_instrs,
            0xdeadbeef << 8,
            context=ctx_init
        )

        base_dir = mem_dir

        #print("reil_mem_out._memory: " + str(reil_mem_out._memory))
       # for k, v in reil_mem_out._memory.iteritems():
        #     print(hex(k) + ": " + hex(v))
        for idx, b in enumerate(struct.unpack("B" * len(arm_mem_out), arm_mem_out)):
            if (base_dir + idx) in reil_mem_out._memory: # TODO: Don't access variable directly.
                #print("idx: " + hex(idx))
               # print("B: " + hex(b))
               # print("reil_mem_out._memory[base_dir + idx]: " + hex(reil_mem_out._memory[base_dir + idx]))
                self.assertTrue(b == reil_mem_out._memory[base_dir + idx])
            else:
                #print("B: " + hex(b))
                self.assertTrue(b == 0x0) # Memory in pyasmjit is initialized to 0


        cmp_result = self.__compare_contexts(ctx_init, arm_ctx_out, reil_ctx_out)

        if not cmp_result:
            self.__save_failing_context(ctx_init)

        self.assertTrue(cmp_result, self.__print_contexts(ctx_init, arm_ctx_out, reil_ctx_out))

        pyasmjit.arm_free() # There is only one memory pool, so there is no need (for now) to specify the address


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

    # R12 is loaded with the memory address
    def test_mem_inst(self):
        inst_samples = [
            ["str r0, [r12]", "ldr  r1, [r12]"],
            ["stm r12!, {r0 - r4}",   "ldmdb r12, {r5 - r9}"],
            ["stmia r12, {r8 - r9}",  "ldmia r12, {r1 - r2}"],
            ["stmib r12!, {r11}",    "ldmda r12!, {r3}"],
            ["add r12, r12, #0x100", "stmda r12, {r9 - r11}",   "ldmda r12, {r1 - r3}"],
            ["add r12, r12, #0x100", "stmdb r12!, {r3}",   "ldmia r12!, {r9}"],
            ["add r12, r12, #0x100", "stmfd r12, {r2 - r4}"],
            ["stmfa r12!, {r1 - r4}"],
            ["add r12, r12, #0x100", "stmed r12, {r6 - r9}"],
            ["stmea r12!, {r5 - r7}"],
            ["mov r0, r13", "mov r13, r12", "push {r1 - r10}", "pop {r2 - r11}", "mov r13, r0", "mov r0, #0"], # The last inst. is needed because the emulator has no access to the real value of native r13 (SP) which is not passed in the context
            ["mov r0, r13", "mov r13, r12", "push {r2 - r11}", "pop {r1 - r10}", "mov r13, r0", "mov r0, #0"],
        ]

        for i in inst_samples:
            self._test_asm_instruction_with_mem(i, 'r12')


def main():
    unittest.main()


if __name__ == '__main__':
    main()
