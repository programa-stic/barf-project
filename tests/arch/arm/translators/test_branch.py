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
class ArmTranslationBranchTests(ArmTranslationTestCase):

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
            reil_ctx_out = self._execute_asm(instr, 0x8000)

            self.assertTrue(reil_ctx_out['r11'] == untouched_value)
