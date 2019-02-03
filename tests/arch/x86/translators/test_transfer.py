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
class X86TranslationTransferTests(X86TranslationTestCase):

    def test_bswap_1(self):
        asm = ["bswap eax"]

        ctx_init = self._init_context()

        x86_ctx_out, reil_ctx_out = self._run_code(asm, 0xdeadbeef, ctx_init)

        cmp_result = self._compare_contexts(ctx_init, x86_ctx_out, reil_ctx_out)

        if not cmp_result:
            self._save_failing_context(ctx_init)

        self.assertTrue(cmp_result, self._print_contexts(ctx_init, x86_ctx_out, reil_ctx_out))

    def test_bswap_2(self):
        asm = ["bswap rax"]

        ctx_init = self._init_context()

        x86_ctx_out, reil_ctx_out = self._run_code(asm, 0xdeadbeef, ctx_init)

        cmp_result = self._compare_contexts(ctx_init, x86_ctx_out, reil_ctx_out)

        if not cmp_result:
            self._save_failing_context(ctx_init)

        self.assertTrue(cmp_result, self._print_contexts(ctx_init, x86_ctx_out, reil_ctx_out))

    def test_cdq(self):
        asm = ["cdq"]

        ctx_init = self._init_context()

        x86_ctx_out, reil_ctx_out = self._run_code(asm, 0xdeadbeef, ctx_init)

        cmp_result = self._compare_contexts(ctx_init, x86_ctx_out, reil_ctx_out)

        if not cmp_result:
            self._save_failing_context(ctx_init)

        self.assertTrue(cmp_result, self._print_contexts(ctx_init, x86_ctx_out, reil_ctx_out))

    def test_cdqe(self):
        asm = ["cdqe"]

        ctx_init = self._init_context()

        x86_ctx_out, reil_ctx_out = self._run_code(asm, 0xdeadbeef, ctx_init)

        cmp_result = self._compare_contexts(ctx_init, x86_ctx_out, reil_ctx_out)

        if not cmp_result:
            self._save_failing_context(ctx_init)

        self.assertTrue(cmp_result, self._print_contexts(ctx_init, x86_ctx_out, reil_ctx_out))

    def test_cmova(self):
        asm = ["cmova eax, ebx"]

        ctx_init = self._init_context()

        x86_ctx_out, reil_ctx_out = self._run_code(asm, 0xdeadbeef, ctx_init)

        cmp_result = self._compare_contexts(ctx_init, x86_ctx_out, reil_ctx_out)

        if not cmp_result:
            self._save_failing_context(ctx_init)

        self.assertTrue(cmp_result, self._print_contexts(ctx_init, x86_ctx_out, reil_ctx_out))

    def test_cmovae(self):
        asm = ["cmovae eax, ebx"]

        ctx_init = self._init_context()

        x86_ctx_out, reil_ctx_out = self._run_code(asm, 0xdeadbeef, ctx_init)

        cmp_result = self._compare_contexts(ctx_init, x86_ctx_out, reil_ctx_out)

        if not cmp_result:
            self._save_failing_context(ctx_init)

        self.assertTrue(cmp_result, self._print_contexts(ctx_init, x86_ctx_out, reil_ctx_out))

    def test_cmovb(self):
        asm = ["cmovb eax, ebx"]

        ctx_init = self._init_context()

        x86_ctx_out, reil_ctx_out = self._run_code(asm, 0xdeadbeef, ctx_init)

        cmp_result = self._compare_contexts(ctx_init, x86_ctx_out, reil_ctx_out)

        if not cmp_result:
            self._save_failing_context(ctx_init)

        self.assertTrue(cmp_result, self._print_contexts(ctx_init, x86_ctx_out, reil_ctx_out))

    def test_cmovbe(self):
        asm = ["cmovbe eax, ebx"]

        ctx_init = self._init_context()

        x86_ctx_out, reil_ctx_out = self._run_code(asm, 0xdeadbeef, ctx_init)

        cmp_result = self._compare_contexts(ctx_init, x86_ctx_out, reil_ctx_out)

        if not cmp_result:
            self._save_failing_context(ctx_init)

        self.assertTrue(cmp_result, self._print_contexts(ctx_init, x86_ctx_out, reil_ctx_out))

    def test_cmovc(self):
        asm = ["cmovc eax, ebx"]

        ctx_init = self._init_context()

        x86_ctx_out, reil_ctx_out = self._run_code(asm, 0xdeadbeef, ctx_init)

        cmp_result = self._compare_contexts(ctx_init, x86_ctx_out, reil_ctx_out)

        if not cmp_result:
            self._save_failing_context(ctx_init)

        self.assertTrue(cmp_result, self._print_contexts(ctx_init, x86_ctx_out, reil_ctx_out))

    def test_cmove(self):
        asm = ["cmove eax, ebx"]

        ctx_init = self._init_context()

        x86_ctx_out, reil_ctx_out = self._run_code(asm, 0xdeadbeef, ctx_init)

        cmp_result = self._compare_contexts(ctx_init, x86_ctx_out, reil_ctx_out)

        if not cmp_result:
            self._save_failing_context(ctx_init)

        self.assertTrue(cmp_result, self._print_contexts(ctx_init, x86_ctx_out, reil_ctx_out))

    def test_cmovg(self):
        asm = ["cmovg eax, ebx"]

        ctx_init = self._init_context()

        x86_ctx_out, reil_ctx_out = self._run_code(asm, 0xdeadbeef, ctx_init)

        cmp_result = self._compare_contexts(ctx_init, x86_ctx_out, reil_ctx_out)

        if not cmp_result:
            self._save_failing_context(ctx_init)

        self.assertTrue(cmp_result, self._print_contexts(ctx_init, x86_ctx_out, reil_ctx_out))

    def test_cmovge(self):
        asm = ["cmovge eax, ebx"]

        ctx_init = self._init_context()

        x86_ctx_out, reil_ctx_out = self._run_code(asm, 0xdeadbeef, ctx_init)

        cmp_result = self._compare_contexts(ctx_init, x86_ctx_out, reil_ctx_out)

        if not cmp_result:
            self._save_failing_context(ctx_init)

        self.assertTrue(cmp_result, self._print_contexts(ctx_init, x86_ctx_out, reil_ctx_out))

    def test_cmovl(self):
        asm = ["cmovl eax, ebx"]

        ctx_init = self._init_context()

        x86_ctx_out, reil_ctx_out = self._run_code(asm, 0xdeadbeef, ctx_init)

        cmp_result = self._compare_contexts(ctx_init, x86_ctx_out, reil_ctx_out)

        if not cmp_result:
            self._save_failing_context(ctx_init)

        self.assertTrue(cmp_result, self._print_contexts(ctx_init, x86_ctx_out, reil_ctx_out))

    def test_cmovle(self):
        asm = ["cmovle eax, ebx"]

        ctx_init = self._init_context()

        x86_ctx_out, reil_ctx_out = self._run_code(asm, 0xdeadbeef, ctx_init)

        cmp_result = self._compare_contexts(ctx_init, x86_ctx_out, reil_ctx_out)

        if not cmp_result:
            self._save_failing_context(ctx_init)

        self.assertTrue(cmp_result, self._print_contexts(ctx_init, x86_ctx_out, reil_ctx_out))

    def test_cmovna(self):
        asm = ["cmovna eax, ebx"]

        ctx_init = self._init_context()

        x86_ctx_out, reil_ctx_out = self._run_code(asm, 0xdeadbeef, ctx_init)

        cmp_result = self._compare_contexts(ctx_init, x86_ctx_out, reil_ctx_out)

        if not cmp_result:
            self._save_failing_context(ctx_init)

        self.assertTrue(cmp_result, self._print_contexts(ctx_init, x86_ctx_out, reil_ctx_out))

    def test_cmovnae(self):
        asm = ["cmovnae eax, ebx"]

        ctx_init = self._init_context()

        x86_ctx_out, reil_ctx_out = self._run_code(asm, 0xdeadbeef, ctx_init)

        cmp_result = self._compare_contexts(ctx_init, x86_ctx_out, reil_ctx_out)

        if not cmp_result:
            self._save_failing_context(ctx_init)

        self.assertTrue(cmp_result, self._print_contexts(ctx_init, x86_ctx_out, reil_ctx_out))

    def test_cmovnb(self):
        asm = ["cmovnb eax, ebx"]

        ctx_init = self._init_context()

        x86_ctx_out, reil_ctx_out = self._run_code(asm, 0xdeadbeef, ctx_init)

        cmp_result = self._compare_contexts(ctx_init, x86_ctx_out, reil_ctx_out)

        if not cmp_result:
            self._save_failing_context(ctx_init)

        self.assertTrue(cmp_result, self._print_contexts(ctx_init, x86_ctx_out, reil_ctx_out))

    def test_cmovnbe(self):
        asm = ["cmovnbe eax, ebx"]

        ctx_init = self._init_context()

        x86_ctx_out, reil_ctx_out = self._run_code(asm, 0xdeadbeef, ctx_init)

        cmp_result = self._compare_contexts(ctx_init, x86_ctx_out, reil_ctx_out)

        if not cmp_result:
            self._save_failing_context(ctx_init)

        self.assertTrue(cmp_result, self._print_contexts(ctx_init, x86_ctx_out, reil_ctx_out))

    def test_cmovnc(self):
        asm = ["cmovnc eax, ebx"]

        ctx_init = self._init_context()

        x86_ctx_out, reil_ctx_out = self._run_code(asm, 0xdeadbeef, ctx_init)

        cmp_result = self._compare_contexts(ctx_init, x86_ctx_out, reil_ctx_out)

        if not cmp_result:
            self._save_failing_context(ctx_init)

        self.assertTrue(cmp_result, self._print_contexts(ctx_init, x86_ctx_out, reil_ctx_out))

    def test_cmovne(self):
        asm = ["cmovne eax, ebx"]

        ctx_init = self._init_context()

        x86_ctx_out, reil_ctx_out = self._run_code(asm, 0xdeadbeef, ctx_init)

        cmp_result = self._compare_contexts(ctx_init, x86_ctx_out, reil_ctx_out)

        if not cmp_result:
            self._save_failing_context(ctx_init)

        self.assertTrue(cmp_result, self._print_contexts(ctx_init, x86_ctx_out, reil_ctx_out))

    def test_cmovng(self):
        asm = ["cmovng eax, ebx"]

        ctx_init = self._init_context()

        x86_ctx_out, reil_ctx_out = self._run_code(asm, 0xdeadbeef, ctx_init)

        cmp_result = self._compare_contexts(ctx_init, x86_ctx_out, reil_ctx_out)

        if not cmp_result:
            self._save_failing_context(ctx_init)

        self.assertTrue(cmp_result, self._print_contexts(ctx_init, x86_ctx_out, reil_ctx_out))

    def test_cmovnge(self):
        asm = ["cmovnge eax, ebx"]

        ctx_init = self._init_context()

        x86_ctx_out, reil_ctx_out = self._run_code(asm, 0xdeadbeef, ctx_init)

        cmp_result = self._compare_contexts(ctx_init, x86_ctx_out, reil_ctx_out)

        if not cmp_result:
            self._save_failing_context(ctx_init)

        self.assertTrue(cmp_result, self._print_contexts(ctx_init, x86_ctx_out, reil_ctx_out))

    def test_cmovnl(self):
        asm = ["cmovnl eax, ebx"]

        ctx_init = self._init_context()

        x86_ctx_out, reil_ctx_out = self._run_code(asm, 0xdeadbeef, ctx_init)

        cmp_result = self._compare_contexts(ctx_init, x86_ctx_out, reil_ctx_out)

        if not cmp_result:
            self._save_failing_context(ctx_init)

        self.assertTrue(cmp_result, self._print_contexts(ctx_init, x86_ctx_out, reil_ctx_out))

    def test_cmovnle(self):
        asm = ["cmovnle eax, ebx"]

        ctx_init = self._init_context()

        x86_ctx_out, reil_ctx_out = self._run_code(asm, 0xdeadbeef, ctx_init)

        cmp_result = self._compare_contexts(ctx_init, x86_ctx_out, reil_ctx_out)

        if not cmp_result:
            self._save_failing_context(ctx_init)

        self.assertTrue(cmp_result, self._print_contexts(ctx_init, x86_ctx_out, reil_ctx_out))

    def test_cmovno(self):
        asm = ["cmovno eax, ebx"]

        ctx_init = self._init_context()

        x86_ctx_out, reil_ctx_out = self._run_code(asm, 0xdeadbeef, ctx_init)

        cmp_result = self._compare_contexts(ctx_init, x86_ctx_out, reil_ctx_out)

        if not cmp_result:
            self._save_failing_context(ctx_init)

        self.assertTrue(cmp_result, self._print_contexts(ctx_init, x86_ctx_out, reil_ctx_out))

    def test_cmovnp(self):
        asm = ["cmovnp eax, ebx"]

        ctx_init = self._init_context()

        x86_ctx_out, reil_ctx_out = self._run_code(asm, 0xdeadbeef, ctx_init)

        cmp_result = self._compare_contexts(ctx_init, x86_ctx_out, reil_ctx_out)

        if not cmp_result:
            self._save_failing_context(ctx_init)

        self.assertTrue(cmp_result, self._print_contexts(ctx_init, x86_ctx_out, reil_ctx_out))

    def test_cmovns(self):
        asm = ["cmovns eax, ebx"]

        ctx_init = self._init_context()

        x86_ctx_out, reil_ctx_out = self._run_code(asm, 0xdeadbeef, ctx_init)

        cmp_result = self._compare_contexts(ctx_init, x86_ctx_out, reil_ctx_out)

        if not cmp_result:
            self._save_failing_context(ctx_init)

        self.assertTrue(cmp_result, self._print_contexts(ctx_init, x86_ctx_out, reil_ctx_out))

    def test_cmovnz(self):
        asm = ["cmovnz eax, ebx"]

        ctx_init = self._init_context()

        x86_ctx_out, reil_ctx_out = self._run_code(asm, 0xdeadbeef, ctx_init)

        cmp_result = self._compare_contexts(ctx_init, x86_ctx_out, reil_ctx_out)

        if not cmp_result:
            self._save_failing_context(ctx_init)

        self.assertTrue(cmp_result, self._print_contexts(ctx_init, x86_ctx_out, reil_ctx_out))

    def test_cmovo(self):
        asm = ["cmovo eax, ebx"]

        ctx_init = self._init_context()

        x86_ctx_out, reil_ctx_out = self._run_code(asm, 0xdeadbeef, ctx_init)

        cmp_result = self._compare_contexts(ctx_init, x86_ctx_out, reil_ctx_out)

        if not cmp_result:
            self._save_failing_context(ctx_init)

        self.assertTrue(cmp_result, self._print_contexts(ctx_init, x86_ctx_out, reil_ctx_out))

    def test_cmovp(self):
        asm = ["cmovp eax, ebx"]

        ctx_init = self._init_context()

        x86_ctx_out, reil_ctx_out = self._run_code(asm, 0xdeadbeef, ctx_init)

        cmp_result = self._compare_contexts(ctx_init, x86_ctx_out, reil_ctx_out)

        if not cmp_result:
            self._save_failing_context(ctx_init)

        self.assertTrue(cmp_result, self._print_contexts(ctx_init, x86_ctx_out, reil_ctx_out))

    def test_cmovpe(self):
        asm = ["cmovpe eax, ebx"]

        ctx_init = self._init_context()

        x86_ctx_out, reil_ctx_out = self._run_code(asm, 0xdeadbeef, ctx_init)

        cmp_result = self._compare_contexts(ctx_init, x86_ctx_out, reil_ctx_out)

        if not cmp_result:
            self._save_failing_context(ctx_init)

        self.assertTrue(cmp_result, self._print_contexts(ctx_init, x86_ctx_out, reil_ctx_out))

    def test_cmovpo(self):
        asm = ["cmovpo eax, ebx"]

        ctx_init = self._init_context()

        x86_ctx_out, reil_ctx_out = self._run_code(asm, 0xdeadbeef, ctx_init)

        cmp_result = self._compare_contexts(ctx_init, x86_ctx_out, reil_ctx_out)

        if not cmp_result:
            self._save_failing_context(ctx_init)

        self.assertTrue(cmp_result, self._print_contexts(ctx_init, x86_ctx_out, reil_ctx_out))

    def test_cmovs(self):
        asm = ["cmovs eax, ebx"]

        ctx_init = self._init_context()

        x86_ctx_out, reil_ctx_out = self._run_code(asm, 0xdeadbeef, ctx_init)

        cmp_result = self._compare_contexts(ctx_init, x86_ctx_out, reil_ctx_out)

        if not cmp_result:
            self._save_failing_context(ctx_init)

        self.assertTrue(cmp_result, self._print_contexts(ctx_init, x86_ctx_out, reil_ctx_out))

    def test_cmovz(self):
        asm = ["cmovz eax, ebx"]

        ctx_init = self._init_context()

        x86_ctx_out, reil_ctx_out = self._run_code(asm, 0xdeadbeef, ctx_init)

        cmp_result = self._compare_contexts(ctx_init, x86_ctx_out, reil_ctx_out)

        if not cmp_result:
            self._save_failing_context(ctx_init)

        self.assertTrue(cmp_result, self._print_contexts(ctx_init, x86_ctx_out, reil_ctx_out))

    def test_cmpxchg(self):
        asm = ["cmpxchg ebx, ecx"]

        ctx_init = self._init_context()

        _, x86_ctx_out = pyasmjit.x86_64_execute("\n".join(asm), ctx_init)
        reil_ctx_out, _ = self.reil_emulator.execute(
            self._asm_to_reil(asm, 0xdeadbeef),
            start=0xdeadbeef << 8,
            end=(0xdeadbeef + 0x1) << 8,
            registers=ctx_init
        )

        cmp_result = self._compare_contexts(ctx_init, x86_ctx_out, reil_ctx_out)

        if not cmp_result:
            self._save_failing_context(ctx_init)

        self.assertTrue(cmp_result, self._print_contexts(ctx_init, x86_ctx_out, reil_ctx_out))

    def test_mov_1(self):
        asm = ["mov eax, ebx"]

        ctx_init = self._init_context()

        x86_ctx_out, reil_ctx_out = self._run_code(asm, 0xdeadbeef, ctx_init)

        cmp_result = self._compare_contexts(ctx_init, x86_ctx_out, reil_ctx_out)

        if not cmp_result:
            self._save_failing_context(ctx_init)

        self.assertTrue(cmp_result, self._print_contexts(ctx_init, x86_ctx_out, reil_ctx_out))

    def test_mov_2(self):
        asm = ["mov eax, eax"]

        ctx_init = self._init_context()

        x86_ctx_out, reil_ctx_out = self._run_code(asm, 0xdeadbeef, ctx_init)

        cmp_result = self._compare_contexts(ctx_init, x86_ctx_out, reil_ctx_out)

        if not cmp_result:
            self._save_failing_context(ctx_init)

        self.assertTrue(cmp_result, self._print_contexts(ctx_init, x86_ctx_out, reil_ctx_out))

    def test_movabs(self):
        # TODO: Implement.
        pass

    def test_movsx(self):
        asm = ["movsx eax, bx"]

        ctx_init = self._init_context()

        x86_ctx_out, reil_ctx_out = self._run_code(asm, 0xdeadbeef, ctx_init)

        cmp_result = self._compare_contexts(ctx_init, x86_ctx_out, reil_ctx_out)

        if not cmp_result:
            self._save_failing_context(ctx_init)

        self.assertTrue(cmp_result, self._print_contexts(ctx_init, x86_ctx_out, reil_ctx_out))

    def test_movsxd(self):
        # TODO: Implement.
        pass

    def test_movzx_1(self):
        asm = ["movzx eax, bx"]

        ctx_init = self._init_context()

        x86_ctx_out, reil_ctx_out = self._run_code(asm, 0xdeadbeef, ctx_init)

        cmp_result = self._compare_contexts(ctx_init, x86_ctx_out, reil_ctx_out)

        if not cmp_result:
            self._save_failing_context(ctx_init)

        self.assertTrue(cmp_result, self._print_contexts(ctx_init, x86_ctx_out, reil_ctx_out))

    def test_movzx_2(self):
        asm = ["movzx eax, al"]

        ctx_init = self._init_context()

        ctx_init["rax"] = 0x1

        x86_ctx_out, reil_ctx_out = self._run_code(asm, 0xdeadbeef, ctx_init)

        cmp_result = self._compare_contexts(ctx_init, x86_ctx_out, reil_ctx_out)

        if not cmp_result:
            self._save_failing_context(ctx_init)

        self.assertTrue(cmp_result, self._print_contexts(ctx_init, x86_ctx_out, reil_ctx_out))

    def test_pop(self):
        # TODO: Implement.
        pass

    def test_push(self):
        # TODO: Implement.
        pass

    def test_seta(self):
        asm = ["seta al"]

        ctx_init = self._init_context()

        x86_ctx_out, reil_ctx_out = self._run_code(asm, 0xdeadbeef, ctx_init)

        cmp_result = self._compare_contexts(ctx_init, x86_ctx_out, reil_ctx_out)

        if not cmp_result:
            self._save_failing_context(ctx_init)

        self.assertTrue(cmp_result, self._print_contexts(ctx_init, x86_ctx_out, reil_ctx_out))

    def test_setae(self):
        asm = ["setae al"]

        ctx_init = self._init_context()

        x86_ctx_out, reil_ctx_out = self._run_code(asm, 0xdeadbeef, ctx_init)

        cmp_result = self._compare_contexts(ctx_init, x86_ctx_out, reil_ctx_out)

        if not cmp_result:
            self._save_failing_context(ctx_init)

        self.assertTrue(cmp_result, self._print_contexts(ctx_init, x86_ctx_out, reil_ctx_out))

    def test_setb(self):
        asm = ["setb al"]

        ctx_init = self._init_context()

        x86_ctx_out, reil_ctx_out = self._run_code(asm, 0xdeadbeef, ctx_init)

        cmp_result = self._compare_contexts(ctx_init, x86_ctx_out, reil_ctx_out)

        if not cmp_result:
            self._save_failing_context(ctx_init)

        self.assertTrue(cmp_result, self._print_contexts(ctx_init, x86_ctx_out, reil_ctx_out))

    def test_setbe(self):
        asm = ["setbe al"]

        ctx_init = self._init_context()

        x86_ctx_out, reil_ctx_out = self._run_code(asm, 0xdeadbeef, ctx_init)

        cmp_result = self._compare_contexts(ctx_init, x86_ctx_out, reil_ctx_out)

        if not cmp_result:
            self._save_failing_context(ctx_init)

        self.assertTrue(cmp_result, self._print_contexts(ctx_init, x86_ctx_out, reil_ctx_out))

    def test_setc(self):
        asm = ["setc al"]

        ctx_init = self._init_context()

        x86_ctx_out, reil_ctx_out = self._run_code(asm, 0xdeadbeef, ctx_init)

        cmp_result = self._compare_contexts(ctx_init, x86_ctx_out, reil_ctx_out)

        if not cmp_result:
            self._save_failing_context(ctx_init)

        self.assertTrue(cmp_result, self._print_contexts(ctx_init, x86_ctx_out, reil_ctx_out))

    def test_sete(self):
        asm = ["sete al"]

        ctx_init = self._init_context()

        x86_ctx_out, reil_ctx_out = self._run_code(asm, 0xdeadbeef, ctx_init)

        cmp_result = self._compare_contexts(ctx_init, x86_ctx_out, reil_ctx_out)

        if not cmp_result:
            self._save_failing_context(ctx_init)

        self.assertTrue(cmp_result, self._print_contexts(ctx_init, x86_ctx_out, reil_ctx_out))

    def test_setg(self):
        asm = ["setg al"]

        ctx_init = self._init_context()

        x86_ctx_out, reil_ctx_out = self._run_code(asm, 0xdeadbeef, ctx_init)

        cmp_result = self._compare_contexts(ctx_init, x86_ctx_out, reil_ctx_out)

        if not cmp_result:
            self._save_failing_context(ctx_init)

        self.assertTrue(cmp_result, self._print_contexts(ctx_init, x86_ctx_out, reil_ctx_out))

    def test_setge(self):
        asm = ["setge al"]

        ctx_init = self._init_context()

        x86_ctx_out, reil_ctx_out = self._run_code(asm, 0xdeadbeef, ctx_init)

        cmp_result = self._compare_contexts(ctx_init, x86_ctx_out, reil_ctx_out)

        if not cmp_result:
            self._save_failing_context(ctx_init)

        self.assertTrue(cmp_result, self._print_contexts(ctx_init, x86_ctx_out, reil_ctx_out))

    def test_setl(self):
        asm = ["setl al"]

        ctx_init = self._init_context()

        x86_ctx_out, reil_ctx_out = self._run_code(asm, 0xdeadbeef, ctx_init)

        cmp_result = self._compare_contexts(ctx_init, x86_ctx_out, reil_ctx_out)

        if not cmp_result:
            self._save_failing_context(ctx_init)

        self.assertTrue(cmp_result, self._print_contexts(ctx_init, x86_ctx_out, reil_ctx_out))

    def test_setle(self):
        asm = ["setle al"]

        ctx_init = self._init_context()

        x86_ctx_out, reil_ctx_out = self._run_code(asm, 0xdeadbeef, ctx_init)

        cmp_result = self._compare_contexts(ctx_init, x86_ctx_out, reil_ctx_out)

        if not cmp_result:
            self._save_failing_context(ctx_init)

        self.assertTrue(cmp_result, self._print_contexts(ctx_init, x86_ctx_out, reil_ctx_out))

    def test_setna(self):
        asm = ["setna al"]

        ctx_init = self._init_context()

        x86_ctx_out, reil_ctx_out = self._run_code(asm, 0xdeadbeef, ctx_init)

        cmp_result = self._compare_contexts(ctx_init, x86_ctx_out, reil_ctx_out)

        if not cmp_result:
            self._save_failing_context(ctx_init)

        self.assertTrue(cmp_result, self._print_contexts(ctx_init, x86_ctx_out, reil_ctx_out))

    def test_setnae(self):
        asm = ["setnae al"]

        ctx_init = self._init_context()

        x86_ctx_out, reil_ctx_out = self._run_code(asm, 0xdeadbeef, ctx_init)

        cmp_result = self._compare_contexts(ctx_init, x86_ctx_out, reil_ctx_out)

        if not cmp_result:
            self._save_failing_context(ctx_init)

        self.assertTrue(cmp_result, self._print_contexts(ctx_init, x86_ctx_out, reil_ctx_out))

    def test_setnb(self):
        asm = ["setnb al"]

        ctx_init = self._init_context()

        x86_ctx_out, reil_ctx_out = self._run_code(asm, 0xdeadbeef, ctx_init)

        cmp_result = self._compare_contexts(ctx_init, x86_ctx_out, reil_ctx_out)

        if not cmp_result:
            self._save_failing_context(ctx_init)

        self.assertTrue(cmp_result, self._print_contexts(ctx_init, x86_ctx_out, reil_ctx_out))

    def test_setnbe(self):
        asm = ["setnbe al"]

        ctx_init = self._init_context()

        x86_ctx_out, reil_ctx_out = self._run_code(asm, 0xdeadbeef, ctx_init)

        cmp_result = self._compare_contexts(ctx_init, x86_ctx_out, reil_ctx_out)

        if not cmp_result:
            self._save_failing_context(ctx_init)

        self.assertTrue(cmp_result, self._print_contexts(ctx_init, x86_ctx_out, reil_ctx_out))

    def test_setnc(self):
        asm = ["setnc al"]

        ctx_init = self._init_context()

        x86_ctx_out, reil_ctx_out = self._run_code(asm, 0xdeadbeef, ctx_init)

        cmp_result = self._compare_contexts(ctx_init, x86_ctx_out, reil_ctx_out)

        if not cmp_result:
            self._save_failing_context(ctx_init)

        self.assertTrue(cmp_result, self._print_contexts(ctx_init, x86_ctx_out, reil_ctx_out))

    def test_setne(self):
        asm = ["setne al"]

        ctx_init = self._init_context()

        x86_ctx_out, reil_ctx_out = self._run_code(asm, 0xdeadbeef, ctx_init)

        cmp_result = self._compare_contexts(ctx_init, x86_ctx_out, reil_ctx_out)

        if not cmp_result:
            self._save_failing_context(ctx_init)

        self.assertTrue(cmp_result, self._print_contexts(ctx_init, x86_ctx_out, reil_ctx_out))

    def test_setng(self):
        asm = ["setng al"]

        ctx_init = self._init_context()

        x86_ctx_out, reil_ctx_out = self._run_code(asm, 0xdeadbeef, ctx_init)

        cmp_result = self._compare_contexts(ctx_init, x86_ctx_out, reil_ctx_out)

        if not cmp_result:
            self._save_failing_context(ctx_init)

        self.assertTrue(cmp_result, self._print_contexts(ctx_init, x86_ctx_out, reil_ctx_out))

    def test_setnge(self):
        asm = ["setnge al"]

        ctx_init = self._init_context()

        x86_ctx_out, reil_ctx_out = self._run_code(asm, 0xdeadbeef, ctx_init)

        cmp_result = self._compare_contexts(ctx_init, x86_ctx_out, reil_ctx_out)

        if not cmp_result:
            self._save_failing_context(ctx_init)

        self.assertTrue(cmp_result, self._print_contexts(ctx_init, x86_ctx_out, reil_ctx_out))

    def test_setnl(self):
        asm = ["setnl al"]

        ctx_init = self._init_context()

        x86_ctx_out, reil_ctx_out = self._run_code(asm, 0xdeadbeef, ctx_init)

        cmp_result = self._compare_contexts(ctx_init, x86_ctx_out, reil_ctx_out)

        if not cmp_result:
            self._save_failing_context(ctx_init)

        self.assertTrue(cmp_result, self._print_contexts(ctx_init, x86_ctx_out, reil_ctx_out))

    def test_setnle(self):
        asm = ["setnle al"]

        ctx_init = self._init_context()

        x86_ctx_out, reil_ctx_out = self._run_code(asm, 0xdeadbeef, ctx_init)

        cmp_result = self._compare_contexts(ctx_init, x86_ctx_out, reil_ctx_out)

        if not cmp_result:
            self._save_failing_context(ctx_init)

        self.assertTrue(cmp_result, self._print_contexts(ctx_init, x86_ctx_out, reil_ctx_out))

    def test_setno(self):
        asm = ["setno al"]

        ctx_init = self._init_context()

        x86_ctx_out, reil_ctx_out = self._run_code(asm, 0xdeadbeef, ctx_init)

        cmp_result = self._compare_contexts(ctx_init, x86_ctx_out, reil_ctx_out)

        if not cmp_result:
            self._save_failing_context(ctx_init)

        self.assertTrue(cmp_result, self._print_contexts(ctx_init, x86_ctx_out, reil_ctx_out))

    def test_setnp(self):
        asm = ["setnp al"]

        ctx_init = self._init_context()

        x86_ctx_out, reil_ctx_out = self._run_code(asm, 0xdeadbeef, ctx_init)

        cmp_result = self._compare_contexts(ctx_init, x86_ctx_out, reil_ctx_out)

        if not cmp_result:
            self._save_failing_context(ctx_init)

        self.assertTrue(cmp_result, self._print_contexts(ctx_init, x86_ctx_out, reil_ctx_out))

    def test_setns(self):
        asm = ["setns al"]

        ctx_init = self._init_context()

        x86_ctx_out, reil_ctx_out = self._run_code(asm, 0xdeadbeef, ctx_init)

        cmp_result = self._compare_contexts(ctx_init, x86_ctx_out, reil_ctx_out)

        if not cmp_result:
            self._save_failing_context(ctx_init)

        self.assertTrue(cmp_result, self._print_contexts(ctx_init, x86_ctx_out, reil_ctx_out))

    def test_setnz(self):
        asm = ["setnz al"]

        ctx_init = self._init_context()

        x86_ctx_out, reil_ctx_out = self._run_code(asm, 0xdeadbeef, ctx_init)

        cmp_result = self._compare_contexts(ctx_init, x86_ctx_out, reil_ctx_out)

        if not cmp_result:
            self._save_failing_context(ctx_init)

        self.assertTrue(cmp_result, self._print_contexts(ctx_init, x86_ctx_out, reil_ctx_out))

    def test_seto(self):
        asm = ["seto al"]

        ctx_init = self._init_context()

        x86_ctx_out, reil_ctx_out = self._run_code(asm, 0xdeadbeef, ctx_init)

        cmp_result = self._compare_contexts(ctx_init, x86_ctx_out, reil_ctx_out)

        if not cmp_result:
            self._save_failing_context(ctx_init)

        self.assertTrue(cmp_result, self._print_contexts(ctx_init, x86_ctx_out, reil_ctx_out))

    def test_setp(self):
        asm = ["setp al"]

        ctx_init = self._init_context()

        x86_ctx_out, reil_ctx_out = self._run_code(asm, 0xdeadbeef, ctx_init)

        cmp_result = self._compare_contexts(ctx_init, x86_ctx_out, reil_ctx_out)

        if not cmp_result:
            self._save_failing_context(ctx_init)

        self.assertTrue(cmp_result, self._print_contexts(ctx_init, x86_ctx_out, reil_ctx_out))

    def test_setpe(self):
        asm = ["setpe al"]

        ctx_init = self._init_context()

        x86_ctx_out, reil_ctx_out = self._run_code(asm, 0xdeadbeef, ctx_init)

        cmp_result = self._compare_contexts(ctx_init, x86_ctx_out, reil_ctx_out)

        if not cmp_result:
            self._save_failing_context(ctx_init)

        self.assertTrue(cmp_result, self._print_contexts(ctx_init, x86_ctx_out, reil_ctx_out))

    def test_setpo(self):
        asm = ["setpo al"]

        ctx_init = self._init_context()

        x86_ctx_out, reil_ctx_out = self._run_code(asm, 0xdeadbeef, ctx_init)

        cmp_result = self._compare_contexts(ctx_init, x86_ctx_out, reil_ctx_out)

        if not cmp_result:
            self._save_failing_context(ctx_init)

        self.assertTrue(cmp_result, self._print_contexts(ctx_init, x86_ctx_out, reil_ctx_out))

    def test_sets(self):
        asm = ["sets al"]

        ctx_init = self._init_context()

        x86_ctx_out, reil_ctx_out = self._run_code(asm, 0xdeadbeef, ctx_init)

        cmp_result = self._compare_contexts(ctx_init, x86_ctx_out, reil_ctx_out)

        if not cmp_result:
            self._save_failing_context(ctx_init)

        self.assertTrue(cmp_result, self._print_contexts(ctx_init, x86_ctx_out, reil_ctx_out))

    def test_setz(self):
        asm = ["setz al"]

        ctx_init = self._init_context()

        x86_ctx_out, reil_ctx_out = self._run_code(asm, 0xdeadbeef, ctx_init)

        cmp_result = self._compare_contexts(ctx_init, x86_ctx_out, reil_ctx_out)

        if not cmp_result:
            self._save_failing_context(ctx_init)

        self.assertTrue(cmp_result, self._print_contexts(ctx_init, x86_ctx_out, reil_ctx_out))

    def test_xadd_1(self):
        asm = ["add eax, ebx"]

        ctx_init = self._init_context()

        x86_ctx_out, reil_ctx_out = self._run_code(asm, 0xdeadbeef, ctx_init)

        cmp_result = self._compare_contexts(ctx_init, x86_ctx_out, reil_ctx_out)

        if not cmp_result:
            self._save_failing_context(ctx_init)

        self.assertTrue(cmp_result, self._print_contexts(ctx_init, x86_ctx_out, reil_ctx_out))

    def test_xadd_2(self):
        asm = ["add rax, rbx"]

        ctx_init = self._init_context()

        x86_ctx_out, reil_ctx_out = self._run_code(asm, 0xdeadbeef, ctx_init)

        cmp_result = self._compare_contexts(ctx_init, x86_ctx_out, reil_ctx_out)

        if not cmp_result:
            self._save_failing_context(ctx_init)

        self.assertTrue(cmp_result, self._print_contexts(ctx_init, x86_ctx_out, reil_ctx_out))

    def test_xchg(self):
        asm = ["xchg eax, ebx"]

        ctx_init = self._init_context()

        x86_ctx_out, reil_ctx_out = self._run_code(asm, 0xdeadbeef, ctx_init)

        cmp_result = self._compare_contexts(ctx_init, x86_ctx_out, reil_ctx_out)

        if not cmp_result:
            self._save_failing_context(ctx_init)

        self.assertTrue(cmp_result, self._print_contexts(ctx_init, x86_ctx_out, reil_ctx_out))
