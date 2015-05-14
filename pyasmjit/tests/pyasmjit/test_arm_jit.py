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

import platform
import unittest

import pyasmjit


@unittest.skipUnless('arm' in platform.processor().lower(),
                     'Not running on an ARM system')
class Test_arm_jit(unittest.TestCase):
    def test_adds(self):
        code = """
            movs r8, r2, lsl #31
            mov r7, #0x7FFFFFFF
            mov r8, #0x7FFFFFFF
            adds r7, r7, r8
        """
        ctx_in = {
            'r0': 0x0,
            'r1': 0x1,
            'r2': 0x2,
            'r3': 0x3,
            'r4': 0x4,
            'r5': 0x5,
            'r6': 0x6,
            'r7': 0x7,
            'r8': 0x8,
            'r9': 0x9,
            'r10': 0xa,
            'r11': 0xb,
            'r12': 0xc,
            'apsr': 0x0,
        }

        rv, ctx_out = pyasmjit.arm_execute(code, ctx_in)
        self.assertEqual(0xFFFFFFFE, ctx_out['r7'])
