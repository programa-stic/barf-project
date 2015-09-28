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
import platform
import random
import unittest
import struct
import tempfile
import os
import subprocess

import pyasmjit

from barf.arch import ARCH_ARM_MODE_THUMB
from barf.arch.arm.armbase import ArmArchitectureInformation
from barf.arch.arm.armparser import ArmParser
from barf.arch.arm.armtranslator import ArmTranslator
from barf.arch.arm.armtranslator import FULL_TRANSLATION
from barf.core.reil import ReilContainer
from barf.core.reil import ReilEmulator
from barf.core.reil import ReilSequence
from barf.arch.arm.armdisassembler import ArmDisassembler


@unittest.skipUnless(platform.machine().lower() == 'armv6l',
                     'Not running on an ARMv6 system')
class ArmTranslationTests(unittest.TestCase):

    def setUp(self):
        self.trans_mode = FULL_TRANSLATION
        self.arch_mode = ARCH_ARM_MODE_THUMB
        self.arch_info = ArmArchitectureInformation(self.arch_mode)
        self.arm_parser = ArmParser(self.arch_mode)
        self.arm_translator = ArmTranslator(self.arch_mode, self.trans_mode)
        self.reil_emulator = ReilEmulator(self.arch_info)

        self.context_filename = "failing_context.data"

    def __init_context(self):
        """Initialize register with random values.
        """
        context = self.__create_random_context()

        return context

    def __create_random_context(self):
        context = {}

        for reg in self.arch_info.registers_gp_base:
            if reg not in ['r13', 'r14', 'r15']:
                min_value, max_value = 0, 2**self.arch_info.operand_size - 1
                context[reg] = random.randint(min_value, max_value)

        # Only highest 4 bits (N, C, Z, V) are randomized, the rest are
        # left in the default (user mode) value.
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
            out += flag_str + " "

        return out[:-1]

    def __set_address(self, address, arm_instrs):
        addr = address

        for arm_instr in arm_instrs:
            arm_instr.address = addr
            arm_instr.size = 4
            addr += 4

    def __translate(self, asm_instrs):
        instr_container = ReilContainer()

        asm_instr_last = None
        instr_seq_prev = None

        for asm_instr in asm_instrs:
            instr_seq = ReilSequence()

            for reil_instr in self.arm_translator.translate(asm_instr):
                instr_seq.append(reil_instr)

            if instr_seq_prev:
                instr_seq_prev.next_sequence_address = instr_seq.address

            instr_container.add(instr_seq)

            instr_seq_prev = instr_seq

        if instr_seq_prev:
            if asm_instr_last:
                instr_seq_prev.next_sequence_address = (asm_instr_last.address + asm_instr_last.size) << 8

        return instr_container

    def __asm_to_reil_use_parser(self, asm_list, address):
        # Using the parser:

        arm_instrs = [self.arm_parser.parse(asm) for asm in asm_list]

        self.__set_address(address, arm_instrs)

        reil_instrs = self.__translate(arm_instrs)

        return reil_instrs

    def __asm_to_reil(self, asm_list, address):
        # Using gcc:

        asm = "\n".join(asm_list)

        bytes = self._arm_compile(asm)

        curr_addr = 0
        end_addr = len(bytes)

        dis = ArmDisassembler();

        arm_instr_list = []

        while curr_addr < end_addr:
            # disassemble instruction
            start, end = curr_addr, min(curr_addr + 16, end_addr)

            USE_ARM = 0
            arm_instr = dis.disassemble(bytes[start:end], 0x8000, USE_ARM)

            if not arm_instr:
                raise Exception("Error in capstone disassembly")

            arm_instr_list.append(arm_instr)

            # update instruction pointer
            curr_addr += arm_instr.size


        # TODO: Separate parser tests vs CS->BARF translator
#         arm_instrs = [self.arm_parser.parse(asm) for asm in asm_list]

        self.__set_address(address, arm_instr_list)

        reil_instrs = self.__translate(arm_instr_list)

#         # DEBUG:
#         for reil_instr in reil_instrs:
#             print("  {}".format(reil_instr))

        return reil_instrs

    def _arm_compile(self, assembly):
        # TODO: This is a copy of the pyasmjit

        # Initialize return values
        rc = 0
        ctx = {}

        # Create temporary files for compilation.
        f_asm = tempfile.NamedTemporaryFile(delete=False)
        f_obj = tempfile.NamedTemporaryFile(delete=False)
        f_bin = tempfile.NamedTemporaryFile(delete=False)

        # Write assembly to a file.
        f_asm.write(assembly + '\n')  # TODO: -mthumb is not working (so the "code" directive is added)
        f_asm.close()

        # Run nasm.
        cmd_fmt = "gcc -c -x assembler {asm} -o {obj} -mthumb -march=armv7-a; objcopy -O binary {obj} {bin};"
        cmd = cmd_fmt.format(asm=f_asm.name, obj=f_obj.name, bin=f_bin.name)
        return_code = subprocess.call(cmd, shell=True)

        # Check for assembler errors.
        if return_code == 0:
            # Read binary code.
            binary = ""
            byte = f_bin.read(1)
            while byte:
                binary += byte
                byte = f_bin.read(1)
            f_bin.close()

        else:
            raise Exception("gcc error")

        # Remove temporary files.
        os.remove(f_asm.name)
        os.remove(f_obj.name)
        os.remove(f_bin.name)

        return binary


    def __run_code(self, asm_list, address, ctx_init):
        reil_instrs = self.__asm_to_reil(asm_list, address)

        _, arm_ctx_out, _ = pyasmjit.arm_execute("\n".join(asm_list), ctx_init)
        reil_ctx_out, _ = self.reil_emulator.execute(reil_instrs, start=address << 8, registers=ctx_init)

        return arm_ctx_out, reil_ctx_out

    def __test_asm_instruction(self, asm_list):
        ctx_init = self.__init_context()

        arm_ctx_out, reil_ctx_out = self.__run_code(asm_list, 0xdeadbeef, ctx_init)

        cmp_result = self.__compare_contexts(ctx_init, arm_ctx_out, reil_ctx_out)

        if not cmp_result:
            self.__save_failing_context(ctx_init)

        self.assertTrue(cmp_result, self.__print_contexts(ctx_init, arm_ctx_out, reil_ctx_out))

    def __test_asm_instruction_with_mem(self, asm_list, address_register):
        # TODO: Merge with previous test function.

        mem_addr = pyasmjit.arm_alloc(4096)

        self.reil_emulator.reset()

        reil_instrs = self.__asm_to_reil(asm_list, 0xdeadbeef)

        ctx_init = self.__init_context()
        ctx_init[address_register] = mem_addr

        _, arm_ctx_out, arm_mem_out = pyasmjit.arm_execute("\n".join(asm_list), ctx_init)
        reil_ctx_out, reil_mem_out = self.reil_emulator.execute(reil_instrs, 0xdeadbeef << 8, registers=ctx_init)

        base_addr = mem_addr

        for idx, b in enumerate(struct.unpack("B" * len(arm_mem_out), arm_mem_out)):
            addr = base_addr + idx

            # TODO: Don't access variable directly.
            if addr in reil_mem_out._memory:
                self.assertTrue(b == reil_mem_out.read(addr, 1))
            else:
                # Memory in pyasmjit is initialized to 0.
                self.assertTrue(b == 0x0)

        cmp_result = self.__compare_contexts(ctx_init, arm_ctx_out, reil_ctx_out)

        if not cmp_result:
            self.__save_failing_context(ctx_init)

        self.assertTrue(cmp_result, self.__print_contexts(ctx_init, arm_ctx_out, reil_ctx_out))

        # NOTE: There is only one memory pool, so there is no need
        # (for now) to specify the address.
        pyasmjit.arm_free()

    def __execute_asm(self, asm_list, address=0x8000):
        reil_instrs = self.__asm_to_reil_use_parser(asm_list, address)

        ctx_init = self.__init_context()

        reil_ctx_out, _ = self.reil_emulator.execute(reil_instrs, address << 8, registers=ctx_init)

        return reil_ctx_out

    def test_data_instructions(self):
        # TODO: R13 (SP), R14 (LR), R15 (PC) are outside testing scope
        # for now.

        instr_samples = [
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
            ["rsb r0, r3, r12"],
            ["cmp r3, r12"],
            ["cmn r3, r12"],
            ["mov r8, r5, lsl r6"],
            ["eor r8, r4, r5, lsl r6"],
            ["mul r3, r4, r8"],
            ["mov r8, #0",
             "mul r3, r4, r8"],
            ["mul r3, r4, r4"],
            # ["movw r5, #0x1235"], # Not supported by the Raspberry Pi (ARMv6)
            ["mvn r3, r8"],
            # ["lsl r7, r2"], # TODO: Not implemented yet.
            ["lsl r2, r4, #0x0"],
            ["lsl r2, r4, #0x1"],
            ["lsl r2, r4, #10"],
            ["lsl r2, r4, #31"],


            # Flags update
            ["movs r0, #0"],
            ["movs r0, #-10"],
            ["mov r0, #0x7FFFFFFF",
             "mov r1, r0",
             "adds r3, r0, r1"],
            ["mov r0, #0x7FFFFFFF",
             "mov r1, r0",
             "subs r3, r0, r1"],
            ["mov r0, #0x00FFFFFF",
             "add r1, r0, #10",
             "subs r3, r0, r1"],
            ["mov r0, #0x00FFFFFF",
             "add r1, r0, #10",
             "rsbs r3, r0, r1"],
            ["mov r0, #0xFFFFFFFF",
             "adds r3, r0, #10"],
            ["mov r0, #0x7FFFFFFF",
             "mov r1,  #5",
             "adds r3, r0, r1"],
            ["mov r0, #0x80000000",
             "mov r1,  #5",
             "subs r3, r0, r1"],
            ["mov r0, #0x80000000",
             "mov r1,  #5",
             "rsbs r3, r0, r1"],
            ["lsls r2, r4, #0x0"],
            ["lsls r2, r4, #0x1"],
            ["lsls r2, r4, #10"],
            ["lsls r2, r4, #31"],

            # TODO: CHECK ReilCpuInvalidAddressError !!!!

            # Flags evaluation
#             ["moveq r0, r1"],
#             ["movne r3, r8"],
#             ["movcs r5, r8"],
#             ["andcc r0, r1, r2"],
#             ["andmi r0, r6, #0x33"],
#             ["orrpl r3, r5, r8"],
#             ["orrvs r3, r5, #0x79"],
#             ["orrvc r3, r5, r8, lsl #0x19"],
#             ["eorhi r3, r5, r8"],
#             ["eorls r8, r4, r5, lsl r6"],
#             ["eorge r8, r4, r5, lsl #0x11"],
#             ["addlt r8, r9, r11"],
#             ["subgt r0, r3, r12"],
#             # ["rsbgt r0, r3, r12"], #TODO: Check this after the AddressError Fix
#             ["cmple r3, r12"],
#             ["cmnal r3, r12"],
#             ["addhs r8, r9, r11"],
#             ["sublo r0, r3, r12"],
#             # ["rsblo r0, r3, r12"], #TODO: Check this after the AddressError Fix
        ]

        for instr in instr_samples:
            self.__test_asm_instruction(instr)

    def test_memory_instructions(self):
        # R12 is loaded with the memory address

        instr_samples = [
            ["str r0, [r12]",
             "ldr  r1, [r12]"],
            ["strb r0, [r12]",
             "ldrb  r1, [r12]"],
            ["strh r0, [r12]",
             "ldrh  r1, [r12]"],
            ["strd r6, [r12]",
             "ldrd  r2, [r12]"],
            ["strd r6, r7, [r12]",
             "ldrd  r8, r9, [r12]"],
            ["stm r12!, {r0 - r4}",
             "ldmdb r12, {r5 - r9}"],
            ["stmia r12, {r8 - r9}",
             "ldmia r12, {r1 - r2}"],
            ["stmib r12!, {r11}",
             "ldmda r12!, {r3}"],
            ["add r12, r12, #0x100",
             "stmda r12, {r9 - r11}",
             "ldmda r12, {r1 - r3}"],
            ["add r12, r12, #0x100",
             "stmdb r12!, {r3}",
             "ldmia r12!, {r9}"],
            ["add r12, r12, #0x100",
             "stmfd r12, {r2 - r4}"],
            ["stmfa r12!, {r1 - r4}"],
            ["add r12, r12, #0x100",
             "stmed r12, {r6 - r9}"],
            ["stmea r12!, {r5 - r7}"],
            # NOTE: The last instr. is needed because the emulator has
            # no access to the real value of native r13 (SP) which is
            # not passed in the context.
            ["mov r0, r13",
             "mov r13, r12",
             "push {r1 - r10}",
             "pop {r2 - r11}",
             "mov r13, r0",
             "mov r0, #0"],

            # TODO: Investigate sporadic seg fault in RPi
#             ["mov r0, r13",
#              "add r13, r12",
#              "push {r2 - r11}",
#              "pop {r1 - r10}",
#              "mov r13, r0",
#              "mov r0, #0"],
        ]

        for instr in instr_samples:
            self.__test_asm_instruction_with_mem(instr, 'r12')

    def test_branch_instructions(self):
        untouched_value = 0x45454545
        touched_value = 0x31313131

        # R11 is used as a dirty register to check if the branch was
        # taken or not.
        instr_samples = [
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

        for instr in instr_samples:
            reil_ctx_out = self.__execute_asm(instr, 0x8000)

            self.assertTrue(reil_ctx_out['r11'] == untouched_value)


def main():
    unittest.main()


if __name__ == '__main__':
    main()
