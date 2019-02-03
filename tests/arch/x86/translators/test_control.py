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

import platform
import pyasmjit
import unittest

from .x86translator import X86TranslationTestCase


@unittest.skipUnless(platform.machine().lower() == 'x86_64',
                     'Not running on an x86_64 system')
class X86TranslationControlTests(X86TranslationTestCase):

    def test_call(self):
        # TODO: Implement.
        pass

    def test_jcc(self):
        conds = [
            'a', 'ae', 'b', 'be', 'c', 'e', 'g', 'ge', 'l', 'le', 'na', 'nae',
            'nb', 'nbe', 'nc', 'ne', 'ng', 'nge', 'nl', 'nle', 'no', 'np', 'ns',
            'nz', 'o', 'p', 'pe', 'po', 's', 'z'
        ]

        for c in conds:
            self.__test_jcc(c)

    def test_jecxz(self):
        # TODO: Implement.
        pass

    def test_loop(self):
        # TODO: Implement.
        pass

    def test_loope(self):
        # TODO: Implement.
        pass

    def test_loopne(self):
        # TODO: Implement.
        pass

    def test_loopnz(self):
        # TODO: Implement.
        pass

    def test_loopz(self):
        # TODO: Implement.
        pass

    def test_ret(self):
        # TODO: Implement.
        pass

    # Auxiliary functions
    # ============================================================================ #
    def __test_jcc(self, jmp_cond):
        untouched_value = 0x45454545
        touched_value = 0x31313131

        asm = [
            "mov rax, 0x{:x}".format(untouched_value),
            "j" + jmp_cond + " {:s}",
            "mov rax, 0x{:x}".format(touched_value),
            "xchg rax, rax",
        ]

        asm_reil = list(asm)
        asm_reil[1] = asm_reil[1].format(str(0xdeadbeef + 0x3))

        asm_pyasmjit = list(asm)
        asm_pyasmjit[1] = asm_pyasmjit[1].format("$+0x07")

        reil_instrs = self._asm_to_reil(asm_reil, 0xdeadbeef)

        ctx_init = self._init_context()

        _, x86_ctx_out = pyasmjit.x86_64_execute("\n".join(asm_pyasmjit), ctx_init)
        reil_ctx_out, _ = self.reil_emulator.execute(
            reil_instrs,
            start=0xdeadbeef << 8,
            registers=ctx_init
        )

        cmp_result = self._compare_contexts(ctx_init, x86_ctx_out, reil_ctx_out)

        if not cmp_result:
            self._save_failing_context(ctx_init)

        self.assertTrue(cmp_result, self._print_contexts(ctx_init, x86_ctx_out, reil_ctx_out))
