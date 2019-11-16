# Copyright (c) 2019, Fundacion Dr. Manuel Sadosky
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

import platform
import unittest

from .armtranslator import ArmTranslationTestCase


@unittest.skipUnless(platform.machine().lower() in ['armv6l', 'armv7l'],
                     'Not running on an ARMv6 system')
class ArmTranslationLoadStoreTests(ArmTranslationTestCase):

    def test_memory_instructions(self):
        # R12 is loaded with the memory address.

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
            # ["mov r0, r13",
            #  "add r13, r12",
            #  "push {r2 - r11}",
            #  "pop {r1 - r10}",
            #  "mov r13, r0",
            #  "mov r0, #0"],
        ]

        for instr in instr_samples:
            self._test_asm_instruction_with_mem(instr, 'r12')
