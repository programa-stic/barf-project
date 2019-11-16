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
class ArmTranslationDataTests(ArmTranslationTestCase):

    def test_data_instructions(self):
        # NOTE: R13 (SP), R14 (LR), R15 (PC) are outside testing scope.

        instr_samples = [
            # No flags.
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
            # ["movw r5, #0x1235"], # Not supported in ARM mode.
            ["mvn r3, r8"],
            # ["lsl r7, r2"],
            ["lsl r2, r4, #0x0"],
            ["lsl r2, r4, #0x1"],
            ["lsl r2, r4, #10"],
            ["lsl r2, r4, #31"],

            # Flags update.
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
            # ["lsls r2, r4, #0x0"],
            # ["lsls r2, r4, #0x1"],
            # ["lsls r2, r4, #10"],
            # ["lsls r2, r4, #31"],

            # Flags evaluation.
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
            ["rsbgt r0, r3, r12"],
            ["cmple r3, r12"],
            ["cmnal r3, r12"],
            ["addhs r8, r9, r11"],
            ["sublo r0, r3, r12"],
            ["rsblo r0, r3, r12"],
        ]

        for instr in instr_samples:
            self._test_asm_instruction(instr)
