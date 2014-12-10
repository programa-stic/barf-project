import unittest

import pyasmjit

from barf.arch import ARCH_X86_MODE_32
from barf.arch import ARCH_X86_MODE_64
from barf.arch.x86.x86base import X86ArchitectureInformation
from barf.arch.x86.x86instructiontranslator import FULL_TRANSLATION
from barf.arch.x86.x86instructiontranslator import LITE_TRANSLATION
from barf.arch.x86.x86parser import X86Parser
from barf.arch.x86.x86translator import X86Translator
from barf.core.reil import ReilEmulator
from barf.core.smt.smtlibv2 import Z3Solver as SmtSolver
from barf.core.smt.smttranslator import SmtTranslator


class X86Parser32BitsTests(unittest.TestCase):

    def setUp(self):
        self._parser = X86Parser(ARCH_X86_MODE_32)

    def test_two_oprnd_reg_reg(self):
        asm = self._parser.parse("add eax, ebx")

        self.assertEqual(str(asm), "add eax, ebx")

    def test_two_oprnd_reg_imm(self):
        asm = self._parser.parse("add eax, 0x12345678")

        self.assertEqual(str(asm), "add eax, 0x12345678")

    def test_two_oprnd_reg_mem(self):
        asm = self._parser.parse("add eax, [ebx + edx * 4 + 0x10]")

        self.assertEqual(str(asm), "add eax, [ebx+edx*4+0x10]")

    def test_two_oprnd_mem_reg(self):
        asm = self._parser.parse("add [ebx + edx * 4 + 0x10], eax")

        self.assertEqual(str(asm), "add [ebx+edx*4+0x10], eax")

    def test_one_oprnd_reg(self):
        asm = self._parser.parse("inc eax")

        self.assertEqual(str(asm), "inc eax")

    def test_one_oprnd_imm(self):
        asm = self._parser.parse("jmp 0x12345678")

        self.assertEqual(str(asm), "jmp 0x12345678")

    def test_one_oprnd_mem(self):
        asm = self._parser.parse("inc dword ptr [ebx+edx*4+0x10]")

        self.assertEqual(str(asm), "inc dword ptr [ebx+edx*4+0x10]")

    def test_zero_oprnd(self):
        asm = self._parser.parse("nop")

        self.assertEqual(str(asm), "nop")

    # Misc
    # ======================================================================== #
    def test_misc_1(self):
        asm = self._parser.parse("mov dword ptr [-0x21524111], ecx")

        self.assertEqual(str(asm), "mov dword ptr [0xdeadbeef], ecx")

    def test_misc_2(self):
        asm = self._parser.parse("fucompi st(1)")

        self.assertEqual(str(asm), "fucompi st(1)")


class X86Parser64BitsTests(unittest.TestCase):

    def setUp(self):
        self._parser = X86Parser(ARCH_X86_MODE_64)

    def test_64_two_oprnd_reg_reg(self):
        asm = self._parser.parse("add rax, rbx")

        self.assertEqual(str(asm), "add rax, rbx")

    def test_64_two_oprnd_reg_reg_2(self):
        asm = self._parser.parse("add rax, r8")

        self.assertEqual(str(asm), "add rax, r8")

    def test_64_two_oprnd_reg_mem(self):
        asm = self._parser.parse("add rax, [rbx + r15 * 4 + 0x10]")

        self.assertEqual(str(asm), "add rax, [rbx+r15*4+0x10]")

    # Misc
    # ======================================================================== #
    def test_misc_offset_1(self):
        asm = self._parser.parse("add byte ptr [rax+0xffffff89], cl")

        self.assertEqual(str(asm), "add byte ptr [rax+0xffffff89], cl")

class X86TranslationTests(unittest.TestCase):

    def setUp(self):
        self.trans_mode = FULL_TRANSLATION

        self.arch_mode = ARCH_X86_MODE_64

        self.arch_info = X86ArchitectureInformation(self.arch_mode)

        self.x86_parser = X86Parser(self.arch_mode)
        self.x86_translator = X86Translator(self.arch_mode, self.trans_mode)
        self.smt_solver = SmtSolver()
        self.smt_translator = SmtTranslator(self.smt_solver, self.arch_info.address_size)
        self.reil_emulator = ReilEmulator(self.arch_info.address_size)

        self.reil_emulator.set_arch_registers(self.arch_info.registers_gp)
        self.reil_emulator.set_arch_registers_size(self.arch_info.register_size)
        self.reil_emulator.set_reg_access_mapper(self.arch_info.register_access_mapper())

        self.smt_translator.set_reg_access_mapper(self.arch_info.register_access_mapper())
        self.smt_translator.set_arch_registers_size(self.arch_info.register_size)

    def test_lea(self):
        asm = ["lea eax, [ebx + 0x100]"]

        x86_instrs = map(self.x86_parser.parse, asm)

        self.__set_address(0xdeadbeef, x86_instrs)

        reil_instrs = map(self.x86_translator.translate, x86_instrs)

        ctx_init = self.__init_context()

        x86_rv, x86_ctx_out = pyasmjit.execute("\n".join(asm), ctx_init)
        reil_ctx_out, reil_mem_out = self.reil_emulator.execute(
            reil_instrs,
            0xdeadbeef << 8,
            context=ctx_init
        )

        reil_ctx_out = self.__fix_reil_flags(reil_ctx_out, x86_ctx_out)

        self.assertTrue(self.__compare_contexts(
            ctx_init,
            x86_ctx_out,
            reil_ctx_out
        ))

    def test_cld(self):
        asm = ["cld"]

        x86_instrs = map(self.x86_parser.parse, asm)

        self.__set_address(0xdeadbeef, x86_instrs)

        reil_instrs = map(self.x86_translator.translate, x86_instrs)

        ctx_init = self.__init_context()

        x86_rv, x86_ctx_out = pyasmjit.execute("\n".join(asm), ctx_init)
        reil_ctx_out, reil_mem_out = self.reil_emulator.execute(
            reil_instrs,
            0xdeadbeef << 8,
            context=ctx_init
        )

        reil_ctx_out = self.__fix_reil_flags(reil_ctx_out, x86_ctx_out)

        self.assertTrue(self.__compare_contexts(
            ctx_init,
            x86_ctx_out,
            reil_ctx_out
        ))

    def test_clc(self):
        asm = ["clc"]

        x86_instrs = map(self.x86_parser.parse, asm)

        self.__set_address(0xdeadbeef, x86_instrs)

        reil_instrs = map(self.x86_translator.translate, x86_instrs)

        ctx_init = self.__init_context()

        x86_rv, x86_ctx_out = pyasmjit.execute("\n".join(asm), ctx_init)
        reil_ctx_out, reil_mem_out = self.reil_emulator.execute(
            reil_instrs,
            0xdeadbeef << 8,
            context=ctx_init
        )

        reil_ctx_out = self.__fix_reil_flags(reil_ctx_out, x86_ctx_out)

        self.assertTrue(self.__compare_contexts(
            ctx_init,
            x86_ctx_out,
            reil_ctx_out
        ))

    def test_nop(self):
        asm = ["nop"]

        x86_instrs = map(self.x86_parser.parse, asm)

        self.__set_address(0xdeadbeef, x86_instrs)

        reil_instrs = map(self.x86_translator.translate, x86_instrs)

        ctx_init = self.__init_context()

        x86_rv, x86_ctx_out = pyasmjit.execute("\n".join(asm), ctx_init)
        reil_ctx_out, reil_mem_out = self.reil_emulator.execute(
            reil_instrs,
            0xdeadbeef << 8,
            context=ctx_init
        )

        reil_ctx_out = self.__fix_reil_flags(reil_ctx_out, x86_ctx_out)

        self.assertTrue(self.__compare_contexts(
            ctx_init,
            x86_ctx_out,
            reil_ctx_out
        ))

    def test_test(self):
        asm = ["test eax, ebx"]

        x86_instrs = map(self.x86_parser.parse, asm)

        self.__set_address(0xdeadbeef, x86_instrs)

        reil_instrs = map(self.x86_translator.translate, x86_instrs)

        ctx_init = self.__init_context()

        x86_rv, x86_ctx_out = pyasmjit.execute("\n".join(asm), ctx_init)
        reil_ctx_out, reil_mem_out = self.reil_emulator.execute(
            reil_instrs,
            0xdeadbeef << 8,
            context=ctx_init
        )

        reil_ctx_out = self.__fix_reil_flags(reil_ctx_out, x86_ctx_out)

        self.assertTrue(self.__compare_contexts(
            ctx_init,
            x86_ctx_out,
            reil_ctx_out
        ))

    def test_not(self):
        asm = ["not eax"]

        x86_instrs = map(self.x86_parser.parse, asm)

        self.__set_address(0xdeadbeef, x86_instrs)

        reil_instrs = map(self.x86_translator.translate, x86_instrs)

        ctx_init = self.__init_context()

        x86_rv, x86_ctx_out = pyasmjit.execute("\n".join(asm), ctx_init)
        reil_ctx_out, reil_mem_out = self.reil_emulator.execute(
            reil_instrs,
            0xdeadbeef << 8,
            context=ctx_init
        )

        reil_ctx_out = self.__fix_reil_flags(reil_ctx_out, x86_ctx_out)

        self.assertTrue(self.__compare_contexts(
            ctx_init,
            x86_ctx_out,
            reil_ctx_out
        ))

    def test_xor(self):
        asm = ["xor eax, ebx"]

        x86_instrs = map(self.x86_parser.parse, asm)

        self.__set_address(0xdeadbeef, x86_instrs)

        reil_instrs = map(self.x86_translator.translate, x86_instrs)

        ctx_init = self.__init_context()

        x86_rv, x86_ctx_out = pyasmjit.execute("\n".join(asm), ctx_init)
        reil_ctx_out, reil_mem_out = self.reil_emulator.execute(
            reil_instrs,
            0xdeadbeef << 8,
            context=ctx_init
        )

        reil_ctx_out = self.__fix_reil_flags(reil_ctx_out, x86_ctx_out)

        self.assertTrue(self.__compare_contexts(
            ctx_init,
            x86_ctx_out,
            reil_ctx_out
        ))

    def test_or(self):
        asm = ["or eax, ebx"]

        x86_instrs = map(self.x86_parser.parse, asm)

        self.__set_address(0xdeadbeef, x86_instrs)

        reil_instrs = map(self.x86_translator.translate, x86_instrs)

        ctx_init = self.__init_context()

        x86_rv, x86_ctx_out = pyasmjit.execute("\n".join(asm), ctx_init)
        reil_ctx_out, reil_mem_out = self.reil_emulator.execute(
            reil_instrs,
            0xdeadbeef << 8,
            context=ctx_init
        )

        reil_ctx_out = self.__fix_reil_flags(reil_ctx_out, x86_ctx_out)

        self.assertTrue(self.__compare_contexts(
            ctx_init,
            x86_ctx_out,
            reil_ctx_out
        ))

    def test_and(self):
        asm = ["and eax, ebx"]

        x86_instrs = map(self.x86_parser.parse, asm)

        self.__set_address(0xdeadbeef, x86_instrs)

        reil_instrs = map(self.x86_translator.translate, x86_instrs)

        ctx_init = self.__init_context()

        x86_rv, x86_ctx_out = pyasmjit.execute("\n".join(asm), ctx_init)
        reil_ctx_out, reil_mem_out = self.reil_emulator.execute(
            reil_instrs,
            0xdeadbeef << 8,
            context=ctx_init
        )

        reil_ctx_out = self.__fix_reil_flags(reil_ctx_out, x86_ctx_out)

        self.assertTrue(self.__compare_contexts(
            ctx_init,
            x86_ctx_out,
            reil_ctx_out
        ))

    def test_cmp(self):
        asm = ["cmp eax, ebx"]

        x86_instrs = map(self.x86_parser.parse, asm)

        self.__set_address(0xdeadbeef, x86_instrs)

        reil_instrs = map(self.x86_translator.translate, x86_instrs)

        ctx_init = self.__init_context()

        x86_rv, x86_ctx_out = pyasmjit.execute("\n".join(asm), ctx_init)
        reil_ctx_out, reil_mem_out = self.reil_emulator.execute(
            reil_instrs,
            0xdeadbeef << 8,
            context=ctx_init
        )

        reil_ctx_out = self.__fix_reil_flags(reil_ctx_out, x86_ctx_out)

        self.assertTrue(self.__compare_contexts(
            ctx_init,
            x86_ctx_out,
            reil_ctx_out
        ))

    def test_neg(self):
        asm = ["neg eax"]

        x86_instrs = map(self.x86_parser.parse, asm)

        self.__set_address(0xdeadbeef, x86_instrs)

        reil_instrs = map(self.x86_translator.translate, x86_instrs)

        ctx_init = self.__init_context()

        x86_rv, x86_ctx_out = pyasmjit.execute("\n".join(asm), ctx_init)
        reil_ctx_out, reil_mem_out = self.reil_emulator.execute(
            reil_instrs,
            0xdeadbeef << 8,
            context=ctx_init
        )

        reil_ctx_out = self.__fix_reil_flags(reil_ctx_out, x86_ctx_out)

        self.assertTrue(self.__compare_contexts(
            ctx_init,
            x86_ctx_out,
            reil_ctx_out
        ))

    def test_dec(self):
        asm = ["dec eax"]

        x86_instrs = map(self.x86_parser.parse, asm)

        self.__set_address(0xdeadbeef, x86_instrs)

        reil_instrs = map(self.x86_translator.translate, x86_instrs)

        ctx_init = self.__init_context()

        x86_rv, x86_ctx_out = pyasmjit.execute("\n".join(asm), ctx_init)
        reil_ctx_out, reil_mem_out = self.reil_emulator.execute(
            reil_instrs,
            0xdeadbeef << 8,
            context=ctx_init
        )

        reil_ctx_out = self.__fix_reil_flags(reil_ctx_out, x86_ctx_out)

        self.assertTrue(self.__compare_contexts(
            ctx_init,
            x86_ctx_out,
            reil_ctx_out
        ))

    def test_inc(self):
        asm = ["inc eax"]

        x86_instrs = map(self.x86_parser.parse, asm)

        self.__set_address(0xdeadbeef, x86_instrs)

        reil_instrs = map(self.x86_translator.translate, x86_instrs)

        ctx_init = self.__init_context()

        x86_rv, x86_ctx_out = pyasmjit.execute("\n".join(asm), ctx_init)
        reil_ctx_out, reil_mem_out = self.reil_emulator.execute(
            reil_instrs,
            0xdeadbeef << 8,
            context=ctx_init
        )

        reil_ctx_out = self.__fix_reil_flags(reil_ctx_out, x86_ctx_out)

        self.assertTrue(self.__compare_contexts(
            ctx_init,
            x86_ctx_out,
            reil_ctx_out
        ))

    def test_div(self):
        asm = ["div ebx"]

        x86_instrs = map(self.x86_parser.parse, asm)

        self.__set_address(0xdeadbeef, x86_instrs)

        reil_instrs = map(self.x86_translator.translate, x86_instrs)

        ctx_init = {
            'rax'    : 0x10,
            'rbx'    : 0x2,
            'rdx'    : 0x0,
            'rflags' : 0x202,
        }

        x86_rv, x86_ctx_out = pyasmjit.execute("\n".join(asm), ctx_init)
        reil_ctx_out, reil_mem_out = self.reil_emulator.execute(
            reil_instrs,
            0xdeadbeef << 8,
            context=ctx_init
        )

        reil_ctx_out = self.__fix_reil_flags(reil_ctx_out, x86_ctx_out)

        self.assertTrue(self.__compare_contexts(
            ctx_init,
            x86_ctx_out,
            reil_ctx_out
        ))

    def test_imul(self):
        asm = ["imul eax, ebx"]

        x86_instrs = map(self.x86_parser.parse, asm)

        self.__set_address(0xdeadbeef, x86_instrs)

        reil_instrs = map(self.x86_translator.translate, x86_instrs)

        ctx_init = self.__init_context()

        x86_rv, x86_ctx_out = pyasmjit.execute("\n".join(asm), ctx_init)
        reil_ctx_out, reil_mem_out = self.reil_emulator.execute(
            reil_instrs,
            0xdeadbeef << 8,
            context=ctx_init
        )

        reil_ctx_out = self.__fix_reil_flags(reil_ctx_out, x86_ctx_out)

        self.assertTrue(self.__compare_contexts(
            ctx_init,
            x86_ctx_out,
            reil_ctx_out
        ))

    def test_mul(self):
        asm = ["mul ebx"]

        x86_instrs = map(self.x86_parser.parse, asm)

        self.__set_address(0xdeadbeef, x86_instrs)

        reil_instrs = map(self.x86_translator.translate, x86_instrs)

        ctx_init = self.__init_context()

        x86_rv, x86_ctx_out = pyasmjit.execute("\n".join(asm), ctx_init)
        reil_ctx_out, reil_mem_out = self.reil_emulator.execute(
            reil_instrs,
            0xdeadbeef << 8,
            context=ctx_init
        )

        reil_ctx_out = self.__fix_reil_flags(reil_ctx_out, x86_ctx_out)

        self.assertTrue(self.__compare_contexts(
            ctx_init,
            x86_ctx_out,
            reil_ctx_out
        ))

    def test_sbb(self):
        asm = ["sbb eax, ebx"]

        x86_instrs = map(self.x86_parser.parse, asm)

        self.__set_address(0xdeadbeef, x86_instrs)

        reil_instrs = map(self.x86_translator.translate, x86_instrs)

        ctx_init = self.__init_context()

        x86_rv, x86_ctx_out = pyasmjit.execute("\n".join(asm), ctx_init)
        reil_ctx_out, reil_mem_out = self.reil_emulator.execute(
            reil_instrs,
            0xdeadbeef << 8,
            context=ctx_init
        )

        reil_ctx_out = self.__fix_reil_flags(reil_ctx_out, x86_ctx_out)

        self.assertTrue(self.__compare_contexts(
            ctx_init,
            x86_ctx_out,
            reil_ctx_out
        ))

    def test_sub(self):
        asm = ["sub eax, ebx"]

        x86_instrs = map(self.x86_parser.parse, asm)

        self.__set_address(0xdeadbeef, x86_instrs)

        reil_instrs = map(self.x86_translator.translate, x86_instrs)

        ctx_init = self.__init_context()

        x86_rv, x86_ctx_out = pyasmjit.execute("\n".join(asm), ctx_init)
        reil_ctx_out, reil_mem_out = self.reil_emulator.execute(
            reil_instrs,
            0xdeadbeef << 8,
            context=ctx_init
        )

        reil_ctx_out = self.__fix_reil_flags(reil_ctx_out, x86_ctx_out)

        self.assertTrue(self.__compare_contexts(
            ctx_init,
            x86_ctx_out,
            reil_ctx_out
        ))

    def test_adc(self):
        asm = ["adc eax, ebx"]

        x86_instrs = map(self.x86_parser.parse, asm)

        self.__set_address(0xdeadbeef, x86_instrs)

        reil_instrs = map(self.x86_translator.translate, x86_instrs)

        ctx_init = self.__init_context()

        x86_rv, x86_ctx_out = pyasmjit.execute("\n".join(asm), ctx_init)
        reil_ctx_out, reil_mem_out = self.reil_emulator.execute(
            reil_instrs,
            0xdeadbeef << 8,
            context=ctx_init
        )

        reil_ctx_out = self.__fix_reil_flags(reil_ctx_out, x86_ctx_out)

        self.assertTrue(self.__compare_contexts(
            ctx_init,
            x86_ctx_out,
            reil_ctx_out
        ))

    def test_add(self):
        asm = ["add eax, ebx"]

        x86_instrs = map(self.x86_parser.parse, asm)

        self.__set_address(0xdeadbeef, x86_instrs)

        reil_instrs = map(self.x86_translator.translate, x86_instrs)

        ctx_init = self.__init_context()

        x86_rv, x86_ctx_out = pyasmjit.execute("\n".join(asm), ctx_init)
        reil_ctx_out, reil_mem_out = self.reil_emulator.execute(
            reil_instrs,
            0xdeadbeef << 8,
            context=ctx_init
        )

        reil_ctx_out = self.__fix_reil_flags(reil_ctx_out, x86_ctx_out)

        self.assertTrue(self.__compare_contexts(
            ctx_init,
            x86_ctx_out,
            reil_ctx_out
        ))

    def test_xchg(self):
        asm = ["xchg eax, ebx"]

        x86_instrs = map(self.x86_parser.parse, asm)

        self.__set_address(0xdeadbeef, x86_instrs)

        reil_instrs = map(self.x86_translator.translate, x86_instrs)

        ctx_init = self.__init_context()

        x86_rv, x86_ctx_out = pyasmjit.execute("\n".join(asm), ctx_init)
        reil_ctx_out, reil_mem_out = self.reil_emulator.execute(
            reil_instrs,
            0xdeadbeef << 8,
            context=ctx_init
        )

        reil_ctx_out = self.__fix_reil_flags(reil_ctx_out, x86_ctx_out)

        self.assertTrue(self.__compare_contexts(
            ctx_init,
            x86_ctx_out,
            reil_ctx_out
        ))

    def test_movzx(self):
        asm = ["movzx eax, bx"]

        x86_instrs = map(self.x86_parser.parse, asm)

        self.__set_address(0xdeadbeef, x86_instrs)

        reil_instrs = map(self.x86_translator.translate, x86_instrs)

        ctx_init = self.__init_context()

        x86_rv, x86_ctx_out = pyasmjit.execute("\n".join(asm), ctx_init)
        reil_ctx_out, reil_mem_out = self.reil_emulator.execute(
            reil_instrs,
            0xdeadbeef << 8,
            context=ctx_init
        )

        reil_ctx_out = self.__fix_reil_flags(reil_ctx_out, x86_ctx_out)

        self.assertTrue(self.__compare_contexts(
            ctx_init,
            x86_ctx_out,
            reil_ctx_out
        ))

    def test_mov(self):
        asm = ["mov eax, ebx"]

        x86_instrs = map(self.x86_parser.parse, asm)

        self.__set_address(0xdeadbeef, x86_instrs)

        reil_instrs = map(self.x86_translator.translate, x86_instrs)

        ctx_init = self.__init_context()

        x86_rv, x86_ctx_out = pyasmjit.execute("\n".join(asm), ctx_init)
        reil_ctx_out, reil_mem_out = self.reil_emulator.execute(
            reil_instrs,
            0xdeadbeef << 8,
            context=ctx_init
        )

        reil_ctx_out = self.__fix_reil_flags(reil_ctx_out, x86_ctx_out)

        self.assertTrue(self.__compare_contexts(
            ctx_init,
            x86_ctx_out,
            reil_ctx_out
        ))

    def test_shr(self):
        asm = ["shr eax, 3"]

        x86_instrs = map(self.x86_parser.parse, asm)

        self.__set_address(0xdeadbeef, x86_instrs)

        reil_instrs = map(self.x86_translator.translate, x86_instrs)

        ctx_init = self.__init_context()

        x86_rv, x86_ctx_out = pyasmjit.execute("\n".join(asm), ctx_init)
        reil_ctx_out, reil_mem_out = self.reil_emulator.execute(
            reil_instrs,
            0xdeadbeef << 8,
            context=ctx_init
        )

        reil_ctx_out = self.__fix_reil_flags(reil_ctx_out, x86_ctx_out)

        self.assertTrue(self.__compare_contexts(
            ctx_init,
            x86_ctx_out,
            reil_ctx_out
        ))

    def test_shl(self):
        asm = ["shl eax, 3"]

        x86_instrs = map(self.x86_parser.parse, asm)

        self.__set_address(0xdeadbeef, x86_instrs)

        reil_instrs = map(self.x86_translator.translate, x86_instrs)

        ctx_init = self.__init_context()

        x86_rv, x86_ctx_out = pyasmjit.execute("\n".join(asm), ctx_init)
        reil_ctx_out, reil_mem_out = self.reil_emulator.execute(
            reil_instrs,
            0xdeadbeef << 8,
            context=ctx_init
        )

        reil_ctx_out = self.__fix_reil_flags(reil_ctx_out, x86_ctx_out)

        self.assertTrue(self.__compare_contexts(
            ctx_init,
            x86_ctx_out,
            reil_ctx_out
        ))

    def test_sal(self):
        asm = ["sal eax, 3"]

        x86_instrs = map(self.x86_parser.parse, asm)

        self.__set_address(0xdeadbeef, x86_instrs)

        reil_instrs = map(self.x86_translator.translate, x86_instrs)

        ctx_init = self.__init_context()

        x86_rv, x86_ctx_out = pyasmjit.execute("\n".join(asm), ctx_init)
        reil_ctx_out, reil_mem_out = self.reil_emulator.execute(
            reil_instrs,
            0xdeadbeef << 8,
            context=ctx_init
        )

        reil_ctx_out = self.__fix_reil_flags(reil_ctx_out, x86_ctx_out)

        self.assertTrue(self.__compare_contexts(
            ctx_init,
            x86_ctx_out,
            reil_ctx_out
        ))

    def test_sar(self):
        asm = ["sar eax, 3"]

        x86_instrs = map(self.x86_parser.parse, asm)

        self.__set_address(0xdeadbeef, x86_instrs)

        reil_instrs = map(self.x86_translator.translate, x86_instrs)

        ctx_init = self.__init_context()

        x86_rv, x86_ctx_out = pyasmjit.execute("\n".join(asm), ctx_init)
        reil_ctx_out, reil_mem_out = self.reil_emulator.execute(
            reil_instrs,
            0xdeadbeef << 8,
            context=ctx_init
        )

        reil_ctx_out = self.__fix_reil_flags(reil_ctx_out, x86_ctx_out)

        self.assertTrue(self.__compare_contexts(
            ctx_init,
            x86_ctx_out,
            reil_ctx_out
        ))

    def test_stc(self):
        asm = ["stc"]

        x86_instrs = map(self.x86_parser.parse, asm)

        self.__set_address(0xdeadbeef, x86_instrs)

        reil_instrs = map(self.x86_translator.translate, x86_instrs)

        ctx_init = self.__init_context()

        x86_rv, x86_ctx_out = pyasmjit.execute("\n".join(asm), ctx_init)

        reil_ctx_out, reil_mem_out = self.reil_emulator.execute(
            reil_instrs,
            0xdeadbeef << 8,
            context=ctx_init
        )

        reil_ctx_out = self.__fix_reil_flags(reil_ctx_out, x86_ctx_out)

        self.assertTrue(self.__compare_contexts(
            ctx_init,
            x86_ctx_out,
            reil_ctx_out
        ))

    def __init_context(self):
        return {
            'rax'    : 0xa,
            'rbx'    : 0x2,
            'rcx'    : 0xb,
            'rdx'    : 0xc,
            'rdi'    : 0xd,
            'rsi'    : 0xe,
            'rflags' : 0x202,
        }

    def __compare_contexts(self, context_init, x86_context, reil_context):
        match = True

        fmt = "%s (x86)  : %s (%s)"

        mask = 2**64-1

        for reg in sorted(context_init.keys()):
            if ((2**64-1) & x86_context[reg]) != ((2**64-1) & reil_context[reg]):
                x86_value = x86_context[reg] & mask
                reil_value = reil_context[reg] & mask

                if reg in ['rflags', 'eflags']:
                    x86_flags_str = self.__print_flags(x86_context[reg])
                    reil_flags_str = self.__print_flags(reil_context[reg])

                    print ("%s (x86)  : %s (%s)" % (reg, hex(x86_value), x86_flags_str))
                    print ("%s (reil) : %s (%s)" % (reg, hex(reil_value), reil_flags_str))
                else:
                    print ("%s (x86)  : %s " % (reg, hex(x86_value)))
                    print ("%s (reil) : %s " % (reg, hex(reil_value)))

                match = False
                break

        if not match:
            self.__print_contexts(context_init, x86_context, reil_context)

        return match

    def __print_contexts(self, context_init, x86_context, reil_context):
        header_fmt = "{0:^8s} : {1:>16s} ?= {2:<16s}"
        header = header_fmt.format("Register", "x86", "REIL")
        ruler  = "-" * len(header)

        print(header)
        print(ruler)

        fmt = "{0:>8s} : {1:016x} {eq} {2:016x} ({1:>5d} {eq} {2:<5d}) {marker}"
        mask = 2**64-1

        for reg in sorted(context_init.keys()):
            if (x86_context[reg] & mask) != (reil_context[reg] & mask):
                eq = "!="
                marker = "<"
            else:
                eq = "=="
                marker = ""

            print fmt.format(
                reg,
                (2**64-1) & x86_context[reg],
                (2**64-1) & reil_context[reg],
                eq=eq,
                marker=marker
            )

    def __print_flags(self, flags_reg):
        # flags
        flags = {
             0 : "cf",  # bit 0
             2 : "pf",  # bit 2
             4 : "af",  # bit 4
             6 : "zf",  # bit 6
             7 : "sf",  # bit 7
            11 : "of",  # bit 11
            10 : "df",  # bit 10
        }

        out = ""

        for bit, flag in flags.items():
            if flags_reg & 2**bit:
                out += flag.upper() + " "
            else:
                out += flag.lower() + " "

        return out[:-1]

    def __fix_reil_flags(self, reil_context, x86_context):
        reil_context_out = dict(reil_context)

        flags_reg = 'eflags' if 'eflags' in reil_context_out else 'rflags'

        # Remove this when AF and PF are implemented.
        reil_context_out[flags_reg] |= (x86_context[flags_reg] & 2**4) # AF
        reil_context_out[flags_reg] |= (x86_context[flags_reg] & 2**2) # PF

        return reil_context_out

    def __set_address(self, address, x86_instrs):
        addr = address

        for x86_instr in x86_instrs:
            x86_instr.address = addr
            addr += 1

def main():
    unittest.main()


if __name__ == '__main__':
    main()
