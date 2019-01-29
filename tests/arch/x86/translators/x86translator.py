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
import unittest

import pyasmjit

from barf.arch import ARCH_X86_MODE_64
from barf.arch.x86 import X86ArchitectureInformation
from barf.arch.x86.helpers import compare_contexts
from barf.arch.x86.helpers import print_contexts
from barf.arch.x86.parser import X86Parser
from barf.arch.x86.translator import X86Translator
from barf.core.reil.container import ReilContainer
from barf.core.reil.container import ReilSequence
from barf.core.reil.emulator.emulator import ReilEmulator


class X86TranslationTestCase(unittest.TestCase):

    def setUp(self):
        self.arch_mode = ARCH_X86_MODE_64

        self.arch_info = X86ArchitectureInformation(self.arch_mode)

        self.x86_parser = X86Parser(self.arch_mode)
        self.x86_translator = X86Translator(self.arch_mode)
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
            if reg not in ['rsp', 'rip', 'rbp']:
                min_value, max_value = 0, 2**self.arch_info.operand_size - 1
                context[reg] = random.randint(min_value, max_value)

        context['rflags'] = self._create_random_flags()

        return context

    def _create_random_flags(self):
        flags_mapper = {
            "cf": 0,
            "pf": 2,
            "af": 4,
            "zf": 6,
            "sf": 7,
            "df": 10,
            "of": 11,
        }

        # Set 'mandatory' flags.
        flags = 0x202

        for _, bit in flags_mapper.items():
            flags = flags | (2**bit * random.randint(0, 1))

        # TODO: Check why PyAsmJIT throws an exception when DF flag is set.
        # Set DF flag to zero.
        flags = flags & ~(2**flags_mapper["df"])

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

    def _compare_contexts(self, context_init, x86_context, reil_context):
        return compare_contexts(context_init, x86_context, reil_context)

    def _print_contexts(self, context_init, x86_context, reil_context):
        out = "Contexts don't match!\n\n"
        out += print_contexts(context_init, x86_context, reil_context)

        return out

    def _fix_reil_flag(self, reil_context, x86_context, flag):
        reil_context_out = dict(reil_context)

        flags_reg = 'eflags' if 'eflags' in reil_context_out else 'rflags'

        _, bit = self.arch_info.alias_mapper[flag]

        # Clean flag.
        reil_context_out[flags_reg] &= ~(2**bit) & (2**32-1)

        # Copy flag.
        reil_context_out[flags_reg] |= (x86_context[flags_reg] & 2**bit)

        return reil_context_out

    def _set_address(self, address, x86_instrs):
        addr = address

        for x86_instr in x86_instrs:
            x86_instr.address = addr
            x86_instr.size = 1
            addr += 1

    def _translate(self, asm_instrs):
        instr_container = ReilContainer()

        asm_instr_last = None
        instr_seq_prev = None

        for asm_instr in asm_instrs:
            instr_seq = ReilSequence()

            for reil_instr in self.x86_translator.translate(asm_instr):
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
        x86_instrs = [self.x86_parser.parse(asm) for asm in asm_list]

        self._set_address(address, x86_instrs)

        reil_instrs = self._translate(x86_instrs)

        return reil_instrs

    def _run_code(self, asm_list, address, ctx_init):
        reil_instrs = self._asm_to_reil(asm_list, address)

        _, x86_ctx_out = pyasmjit.x86_64_execute("\n".join(asm_list), ctx_init)
        reil_ctx_out, _ = self.reil_emulator.execute(reil_instrs, start=address << 8, registers=ctx_init)

        return x86_ctx_out, reil_ctx_out
