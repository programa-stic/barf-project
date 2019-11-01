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

from __future__ import absolute_import

import os
import pickle
import random
import struct
import unittest

import pyasmjit

from barf.arch import ARCH_ARM_MODE_THUMB
from barf.arch.arm import ArmArchitectureInformation
from barf.arch.arm.helpers import compare_contexts
from barf.arch.arm.helpers import print_contexts
from barf.arch.arm.parser import ArmParser
from barf.arch.arm.translator import ArmTranslator
from barf.core.reil.container import ReilContainer
from barf.core.reil.container import ReilSequence
from barf.core.reil.emulator.emulator import ReilEmulator


class ArmTranslationTestCase(unittest.TestCase):

    def setUp(self):
        self.arch_mode = ARCH_ARM_MODE_THUMB

        self.arch_info = ArmArchitectureInformation(self.arch_mode)

        self.arm_parser = ArmParser(self.arch_mode)
        self.arm_translator = ArmTranslator(architecture_mode=self.arch_mode)
        self.reil_emulator = ReilEmulator(self.arch_info)

        self.context_filename = "failing_context.data"

    # Auxiliary methods
    # ======================================================================== #
    def _init_context(self):
        """Initialize register with random values.
        """
        if os.path.isfile(self.context_filename):
            context = self._load_failing_context()
        else:
            context = self._create_random_context()

        return context

    def _create_random_context(self):
        context = {}

        for reg in self.arch_info.registers_gp_base:
            if reg not in ['r13', 'r14', 'r15']:
                min_value, max_value = 0, 2**self.arch_info.operand_size - 1
                context[reg] = random.randint(min_value, max_value)

        context['apsr'] = self._create_random_flags()

        return context

    def _create_random_flags(self):
        # Only highest 4 bits (N, C, Z, V) are randomized, the rest are
        # left in the default (user mode) value.
        flags = 0x00000010
        flags |= random.randint(0x0, 0xF) << 28

        return flags

    def _load_failing_context(self):
        f = open(self.context_filename, "rb")
        context = pickle.load(f)
        f.close()

        return context

    def _save_failing_context(self, context):
        f = open(self.context_filename, "wb")
        pickle.dump(context, f)
        f.close()

    def _compare_contexts(self, context_init, arm_context, reil_context):
        return compare_contexts(context_init, arm_context, reil_context)

    def _print_contexts(self, context_init, arm_context, reil_context):
        out = "Contexts don't match!\n\n"
        out += print_contexts(context_init, arm_context, reil_context)

        return out

    def _set_address(self, address, arm_instrs):
        addr = address

        for arm_instr in arm_instrs:
            arm_instr.address = addr
            arm_instr.size = 4
            addr += 4

    def _translate(self, asm_instrs):
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

    def _asm_to_reil(self, asm_list, address):
        x86_instrs = [self.arm_parser.parse(asm) for asm in asm_list]

        self._set_address(address, x86_instrs)

        reil_instrs = self._translate(x86_instrs)

        return reil_instrs

    def _run_code(self, asm_list, address, ctx_init):
        reil_instrs = self._asm_to_reil(asm_list, address)

        _, arm_ctx_out, _ = pyasmjit.arm_execute("\n".join(asm_list), ctx_init)
        reil_ctx_out, _ = self.reil_emulator.execute(reil_instrs, start=address << 8, registers=ctx_init)

        return arm_ctx_out, reil_ctx_out

    def _test_asm_instruction(self, asm_list):
        self.reil_emulator.reset()

        ctx_init = self._init_context()

        arm_ctx_out, reil_ctx_out = self._run_code(asm_list, 0xdeadbeef, ctx_init)

        cmp_result = self._compare_contexts(ctx_init, arm_ctx_out, reil_ctx_out)

        if not cmp_result:
            self._save_failing_context(ctx_init)

        self.assertTrue(cmp_result, self._print_contexts(ctx_init, arm_ctx_out, reil_ctx_out))

    def _test_asm_instruction_with_mem(self, asm_list, address_register):
        # TODO: Merge with previous test function.

        mem_addr = pyasmjit.arm_alloc(4096)

        self.reil_emulator.reset()

        reil_instrs = self._asm_to_reil(asm_list, 0xdeadbeef)

        ctx_init = self._init_context()
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

        cmp_result = self._compare_contexts(ctx_init, arm_ctx_out, reil_ctx_out)

        if not cmp_result:
            self._save_failing_context(ctx_init)

        self.assertTrue(cmp_result, self._print_contexts(ctx_init, arm_ctx_out, reil_ctx_out))

        # NOTE: There is only one memory pool, so there is no need
        # (for now) to specify the address.
        pyasmjit.arm_free()

    def _execute_asm(self, asm_list, address=0x8000):
        reil_instrs = self._asm_to_reil(asm_list, address)

        ctx_init = self._init_context()

        reil_ctx_out, _ = self.reil_emulator.execute(reil_instrs, address << 8, registers=ctx_init)

        return reil_ctx_out
