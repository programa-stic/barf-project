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

        reil_instrs = map(self.x86_translator.translate, x86_instrs)

        context_init = self.__init_context()

        x86_rv, x86_context_out  = pyasmjit.execute("\n".join(asm), context_init)
        reil_context_out, reil_memory_out = self.reil_emulator.execute(reil_instrs, 0xdeadbeef << 8, context=self.__update_flags_from_rflags(context_init))

        self.assertTrue(self.__compare_contexts(context_init, x86_context_out, reil_context_out))

    def test_cld(self):
        asm = ["cld"]

        x86_instrs = map(self.x86_parser.parse, asm)

        reil_instrs = map(self.x86_translator.translate, x86_instrs)

        context_init = self.__init_context()

        x86_rv, x86_context_out  = pyasmjit.execute("\n".join(asm), context_init)
        reil_context_out, reil_memory_out = self.reil_emulator.execute(reil_instrs, 0xdeadbeef << 8, context=self.__update_flags_from_rflags(context_init))

        self.assertTrue(self.__compare_contexts(context_init, x86_context_out, reil_context_out))

    def test_clc(self):
        asm = ["clc"]

        x86_instrs = map(self.x86_parser.parse, asm)

        reil_instrs = map(self.x86_translator.translate, x86_instrs)

        context_init = self.__init_context()

        x86_rv, x86_context_out  = pyasmjit.execute("\n".join(asm), context_init)
        reil_context_out, reil_memory_out = self.reil_emulator.execute(reil_instrs, 0xdeadbeef << 8, context=self.__update_flags_from_rflags(context_init))

        self.assertTrue(self.__compare_contexts(context_init, x86_context_out, reil_context_out))

    def test_nop(self):
        asm = ["nop"]

        x86_instrs = map(self.x86_parser.parse, asm)

        reil_instrs = map(self.x86_translator.translate, x86_instrs)

        context_init = self.__init_context()

        x86_rv, x86_context_out  = pyasmjit.execute("\n".join(asm), context_init)
        reil_context_out, reil_memory_out = self.reil_emulator.execute(reil_instrs, 0xdeadbeef << 8, context=self.__update_flags_from_rflags(context_init))

        self.assertTrue(self.__compare_contexts(context_init, x86_context_out, reil_context_out))

    def test_test(self):
        asm = ["test eax, ebx"]

        x86_instrs = map(self.x86_parser.parse, asm)

        reil_instrs = map(self.x86_translator.translate, x86_instrs)

        context_init = self.__init_context()

        x86_rv, x86_context_out  = pyasmjit.execute("\n".join(asm), context_init)
        reil_context_out, reil_memory_out = self.reil_emulator.execute(reil_instrs, 0xdeadbeef << 8, context=self.__update_flags_from_rflags(context_init))

        self.assertTrue(self.__compare_contexts(context_init, x86_context_out, reil_context_out))

    def test_not(self):
        asm = ["not eax"]

        x86_instrs = map(self.x86_parser.parse, asm)

        reil_instrs = map(self.x86_translator.translate, x86_instrs)

        context_init = self.__init_context()

        x86_rv, x86_context_out  = pyasmjit.execute("\n".join(asm), context_init)
        reil_context_out, reil_memory_out = self.reil_emulator.execute(reil_instrs, 0xdeadbeef << 8, context=self.__update_flags_from_rflags(context_init))

        self.assertTrue(self.__compare_contexts(context_init, x86_context_out, reil_context_out))

    def test_xor(self):
        asm = ["xor eax, ebx"]

        x86_instrs = map(self.x86_parser.parse, asm)

        reil_instrs = map(self.x86_translator.translate, x86_instrs)

        context_init = self.__init_context()

        x86_rv, x86_context_out  = pyasmjit.execute("\n".join(asm), context_init)
        reil_context_out, reil_memory_out = self.reil_emulator.execute(reil_instrs, 0xdeadbeef << 8, context=self.__update_flags_from_rflags(context_init))

        self.assertTrue(self.__compare_contexts(context_init, x86_context_out, reil_context_out))

    def test_or(self):
        asm = ["or eax, ebx"]

        x86_instrs = map(self.x86_parser.parse, asm)

        reil_instrs = map(self.x86_translator.translate, x86_instrs)

        context_init = self.__init_context()

        x86_rv, x86_context_out  = pyasmjit.execute("\n".join(asm), context_init)
        reil_context_out, reil_memory_out = self.reil_emulator.execute(reil_instrs, 0xdeadbeef << 8, context=self.__update_flags_from_rflags(context_init))

        self.assertTrue(self.__compare_contexts(context_init, x86_context_out, reil_context_out))

    def test_and(self):
        asm = ["and eax, ebx"]

        x86_instrs = map(self.x86_parser.parse, asm)

        reil_instrs = map(self.x86_translator.translate, x86_instrs)

        context_init = self.__init_context()

        x86_rv, x86_context_out  = pyasmjit.execute("\n".join(asm), context_init)
        reil_context_out, reil_memory_out = self.reil_emulator.execute(reil_instrs, 0xdeadbeef << 8, context=self.__update_flags_from_rflags(context_init))

        self.assertTrue(self.__compare_contexts(context_init, x86_context_out, reil_context_out))

    def test_cmp(self):
        asm = ["cmp eax, ebx"]

        x86_instrs = map(self.x86_parser.parse, asm)

        reil_instrs = map(self.x86_translator.translate, x86_instrs)

        context_init = self.__init_context()

        x86_rv, x86_context_out  = pyasmjit.execute("\n".join(asm), context_init)
        reil_context_out, reil_memory_out = self.reil_emulator.execute(reil_instrs, 0xdeadbeef << 8, context=self.__update_flags_from_rflags(context_init))

        self.assertTrue(self.__compare_contexts(context_init, x86_context_out, reil_context_out))

    def test_neg(self):
        asm = ["neg eax"]

        x86_instrs = map(self.x86_parser.parse, asm)

        reil_instrs = map(self.x86_translator.translate, x86_instrs)

        context_init = self.__init_context()

        x86_rv, x86_context_out  = pyasmjit.execute("\n".join(asm), context_init)
        reil_context_out, reil_memory_out = self.reil_emulator.execute(reil_instrs, 0xdeadbeef << 8, context=self.__update_flags_from_rflags(context_init))

        self.assertTrue(self.__compare_contexts(context_init, x86_context_out, reil_context_out))

    def test_dec(self):
        asm = ["dec eax"]

        x86_instrs = map(self.x86_parser.parse, asm)

        reil_instrs = map(self.x86_translator.translate, x86_instrs)

        context_init = self.__init_context()

        x86_rv, x86_context_out  = pyasmjit.execute("\n".join(asm), context_init)
        reil_context_out, reil_memory_out = self.reil_emulator.execute(reil_instrs, 0xdeadbeef << 8, context=self.__update_flags_from_rflags(context_init))

        self.assertTrue(self.__compare_contexts(context_init, x86_context_out, reil_context_out))

    def test_inc(self):
        asm = ["inc eax"]

        x86_instrs = map(self.x86_parser.parse, asm)

        reil_instrs = map(self.x86_translator.translate, x86_instrs)

        context_init = self.__init_context()

        x86_rv, x86_context_out  = pyasmjit.execute("\n".join(asm), context_init)
        reil_context_out, reil_memory_out = self.reil_emulator.execute(reil_instrs, 0xdeadbeef << 8, context=self.__update_flags_from_rflags(context_init))

        self.assertTrue(self.__compare_contexts(context_init, x86_context_out, reil_context_out))

    def test_div(self):
        asm = ["div ebx"]

        x86_instrs = map(self.x86_parser.parse, asm)

        reil_instrs = map(self.x86_translator.translate, x86_instrs)

        context_init = {
            'rax'    : 0x10,
            'rbx'    : 0x2,
            'rdx'    : 0x0,
            'rflags' : 0x202,
        }

        x86_rv, x86_context_out  = pyasmjit.execute("\n".join(asm), context_init)
        reil_context_out, reil_memory_out = self.reil_emulator.execute(reil_instrs, 0xdeadbeef << 8, context=self.__update_flags_from_rflags(context_init))

        self.assertTrue(self.__compare_contexts(context_init, x86_context_out, reil_context_out))

    def test_imul(self):
        asm = ["imul eax, ebx"]

        x86_instrs = map(self.x86_parser.parse, asm)

        reil_instrs = map(self.x86_translator.translate, x86_instrs)

        context_init = self.__init_context()

        x86_rv, x86_context_out  = pyasmjit.execute("\n".join(asm), context_init)
        reil_context_out, reil_memory_out = self.reil_emulator.execute(reil_instrs, 0xdeadbeef << 8, context=self.__update_flags_from_rflags(context_init))

        self.assertTrue(self.__compare_contexts(context_init, x86_context_out, reil_context_out))

    def test_mul(self):
        asm = ["mul ebx"]

        x86_instrs = map(self.x86_parser.parse, asm)

        reil_instrs = map(self.x86_translator.translate, x86_instrs)

        context_init = self.__init_context()

        x86_rv, x86_context_out  = pyasmjit.execute("\n".join(asm), context_init)
        reil_context_out, reil_memory_out = self.reil_emulator.execute(reil_instrs, 0xdeadbeef << 8, context=self.__update_flags_from_rflags(context_init))

        self.assertTrue(self.__compare_contexts(context_init, x86_context_out, reil_context_out))

    def test_sbb(self):
        asm = ["sbb eax, ebx"]

        x86_instrs = map(self.x86_parser.parse, asm)

        reil_instrs = map(self.x86_translator.translate, x86_instrs)

        context_init = self.__init_context()

        x86_rv, x86_context_out  = pyasmjit.execute("\n".join(asm), context_init)
        reil_context_out, reil_memory_out = self.reil_emulator.execute(reil_instrs, 0xdeadbeef << 8, context=self.__update_flags_from_rflags(context_init))

        self.assertTrue(self.__compare_contexts(context_init, x86_context_out, reil_context_out))

    def test_sub(self):
        asm = ["sub eax, ebx"]

        x86_instrs = map(self.x86_parser.parse, asm)

        reil_instrs = map(self.x86_translator.translate, x86_instrs)

        context_init = self.__init_context()

        x86_rv, x86_context_out  = pyasmjit.execute("\n".join(asm), context_init)
        reil_context_out, reil_memory_out = self.reil_emulator.execute(reil_instrs, 0xdeadbeef << 8, context=self.__update_flags_from_rflags(context_init))

        self.assertTrue(self.__compare_contexts(context_init, x86_context_out, reil_context_out))

    def test_adc(self):
        asm = ["adc eax, ebx"]

        x86_instrs = map(self.x86_parser.parse, asm)

        reil_instrs = map(self.x86_translator.translate, x86_instrs)

        context_init = self.__init_context()

        x86_rv, x86_context_out  = pyasmjit.execute("\n".join(asm), context_init)
        reil_context_out, reil_memory_out = self.reil_emulator.execute(reil_instrs, 0xdeadbeef << 8, context=self.__update_flags_from_rflags(context_init))

        self.assertTrue(self.__compare_contexts(context_init, x86_context_out, reil_context_out))

    def test_add(self):
        asm = ["add eax, ebx"]

        x86_instrs = map(self.x86_parser.parse, asm)

        reil_instrs = map(self.x86_translator.translate, x86_instrs)

        context_init = self.__init_context()

        x86_rv, x86_context_out  = pyasmjit.execute("\n".join(asm), context_init)
        reil_context_out, reil_memory_out = self.reil_emulator.execute(reil_instrs, 0xdeadbeef << 8, context=self.__update_flags_from_rflags(context_init))

        self.assertTrue(self.__compare_contexts(context_init, x86_context_out, reil_context_out))

    def test_xchg(self):
        asm = ["xchg eax, ebx"]

        x86_instrs = map(self.x86_parser.parse, asm)

        reil_instrs = map(self.x86_translator.translate, x86_instrs)

        context_init = self.__init_context()

        x86_rv, x86_context_out  = pyasmjit.execute("\n".join(asm), context_init)
        reil_context_out, reil_memory_out = self.reil_emulator.execute(reil_instrs, 0xdeadbeef << 8, context=self.__update_flags_from_rflags(context_init))

        self.assertTrue(self.__compare_contexts(context_init, x86_context_out, reil_context_out))

    def test_movzx(self):
        asm = ["movzx eax, bx"]

        x86_instrs = map(self.x86_parser.parse, asm)

        reil_instrs = map(self.x86_translator.translate, x86_instrs)

        context_init = self.__init_context()

        x86_rv, x86_context_out  = pyasmjit.execute("\n".join(asm), context_init)
        reil_context_out, reil_memory_out = self.reil_emulator.execute(reil_instrs, 0xdeadbeef << 8, context=self.__update_flags_from_rflags(context_init))

        self.assertTrue(self.__compare_contexts(context_init, x86_context_out, reil_context_out))

    def test_mov(self):
        asm = ["mov eax, ebx"]

        x86_instrs = map(self.x86_parser.parse, asm)

        reil_instrs = map(self.x86_translator.translate, x86_instrs)

        context_init = self.__init_context()

        x86_rv, x86_context_out  = pyasmjit.execute("\n".join(asm), context_init)
        reil_context_out, reil_memory_out = self.reil_emulator.execute(reil_instrs, 0xdeadbeef << 8, context=self.__update_flags_from_rflags(context_init))

        self.assertTrue(self.__compare_contexts(context_init, x86_context_out, reil_context_out))

    def test_shr(self):
        asm = ["shr eax, 3"]

        x86_instrs = map(self.x86_parser.parse, asm)

        reil_instrs = map(self.x86_translator.translate, x86_instrs)

        context_init = self.__init_context()

        x86_rv, x86_context_out  = pyasmjit.execute("\n".join(asm), context_init)
        reil_context_out, reil_memory_out = self.reil_emulator.execute(reil_instrs, 0xdeadbeef << 8, context=self.__update_flags_from_rflags(context_init))

        self.assertTrue(self.__compare_contexts(context_init, x86_context_out, reil_context_out))

    def test_shl(self):
        asm = ["shl eax, 3"]

        x86_instrs = map(self.x86_parser.parse, asm)

        reil_instrs = map(self.x86_translator.translate, x86_instrs)

        context_init = self.__init_context()

        x86_rv, x86_context_out  = pyasmjit.execute("\n".join(asm), context_init)
        reil_context_out, reil_memory_out = self.reil_emulator.execute(reil_instrs, 0xdeadbeef << 8, context=self.__update_flags_from_rflags(context_init))

        self.assertTrue(self.__compare_contexts(context_init, x86_context_out, reil_context_out))

    def test_sal(self):
        asm = ["sal eax, 3"]

        x86_instrs = map(self.x86_parser.parse, asm)

        reil_instrs = map(self.x86_translator.translate, x86_instrs)

        context_init = self.__init_context()

        x86_rv, x86_context_out  = pyasmjit.execute("\n".join(asm), context_init)
        reil_context_out, reil_memory_out = self.reil_emulator.execute(reil_instrs, 0xdeadbeef << 8, context=self.__update_flags_from_rflags(context_init))

        self.assertTrue(self.__compare_contexts(context_init, x86_context_out, reil_context_out))

    def test_sar(self):
        asm = ["sar eax, 3"]

        x86_instrs = map(self.x86_parser.parse, asm)
        x86_instrs[0].address = 0xdeadbeef

        reil_instrs = map(self.x86_translator.translate, x86_instrs)

        context_init = self.__init_context()

        x86_rv, x86_context_out  = pyasmjit.execute("\n".join(asm), context_init)
        reil_context_out, reil_memory_out = self.reil_emulator.execute(reil_instrs, 0xdeadbeef << 8, context=self.__update_flags_from_rflags(context_init))

        self.assertTrue(self.__compare_contexts(context_init, x86_context_out, reil_context_out))

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

        for reg in sorted(context_init.keys()):
            if ((2**64-1) & x86_context[reg]) != ((2**64-1) & reil_context[reg]):
                print ("%s : %s " % (reg, hex((2**64-1) & x86_context[reg])))
                print ("%s : %s " % (reg, hex((2**64-1) & reil_context[reg])))
                match = False
                break

        return match

    def __print_contexts(self, context_init, x86_context, reil_context):
        header_fmt = "{0:^8s} : {1:>16s} ?= {2:<16s}"
        header = header_fmt.format("Register", "x86", "REIL")
        ruler  = "-" * len(header)

        print(header)
        print(ruler)

        for reg in sorted(context_init.keys()):
            if  ((2**64-1) & x86_context[reg]) != ((2**64-1) & reil_context[reg]):
                eq = "!="
                marker = "<"
            else:
                eq = "=="
                marker = ""

            fmt = "{0:>8s} : {1:016x} {eq} {2:016x} ({1:>5d} {eq} {2:<5d}) {marker}"

            print fmt.format(
                reg,
                (2**64-1) & x86_context[reg],
                (2**64-1) & reil_context[reg],
                eq=eq,
                marker=marker
            )

    def __update_rflags(self, reil_context_out, x86_context_out):

        reil_context = dict((reg, value) for reg, value in reil_context_out.items() if reg in x86_context_out.keys())

        reil_context['rflags'] = 0xffffffff & (
            0x0                      << 31 | # Reserved
            0x0                      << 30 | # Reserved
            0x0                      << 29 | # Reserved
            0x0                      << 28 | # Reserved
            0x0                      << 27 | # Reserved
            0x0                      << 26 | # Reserved
            0x0                      << 25 | # Reserved
            0x0                      << 24 | # Reserved
            0x0                      << 23 | # Reserved
            0x0                      << 22 | # Reserved
            0x0                      << 21 | # ID
            0x0                      << 20 | # VIP
            0x0                      << 19 | # VIF
            0x0                      << 18 | # AC
            0x0                      << 17 | # VM
            0x0                      << 16 | # RF
            0x0                      << 15 | # Reserved
            0x0                      << 14 | # NT
            0x0                      << 13 | # IOPL
            0x0                      << 12 | # IOPL
            reil_context_out['of']   << 11 | # OF
            reil_context_out['df']   << 10 | # DF
            0x1                      <<  9 | # IF
            0x0                      <<  8 | # TF
            reil_context_out['sf']   <<  7 | # SF
            reil_context_out['zf']   <<  6 | # ZF
            0x0                      <<  5 | # Reserved
            # reil_context_out['af'] <<  4 | # AF
            (x86_context_out['rflags'] & 0x10) | # AF
            0x0                      <<  3 | # Reserved
            # reil_context_out['pf'] <<  2 | # PF
            (x86_context_out['rflags'] & 0x4)  | # PF
            0x1                      <<  1 | # Reserved
            reil_context_out['cf']   <<  0   # CF
        )

        return reil_context

    def __update_flags_from_rflags(self, reil_context):
        reil_context_out = dict(reil_context)

        flags_reg = None

        if 'rflags' in reil_context_out:
            flags_reg = 'rflags'

        if 'eflags' in reil_context_out:
            flags_reg = 'eflags'

        if flags_reg:
            reil_context_out['of'] = reil_context_out[flags_reg] & 2**11 # OF
            reil_context_out['df'] = reil_context_out[flags_reg] & 2**10 # DF
            reil_context_out['sf'] = reil_context_out[flags_reg] & 2**7  # SF
            reil_context_out['zf'] = reil_context_out[flags_reg] & 2**6  # ZF
            reil_context_out['af'] = reil_context_out[flags_reg] & 2**4  # AF
            reil_context_out['pf'] = reil_context_out[flags_reg] & 2**2  # PF
            reil_context_out['cf'] = reil_context_out[flags_reg] & 2**0  # CF

        return reil_context_out


def main():
    unittest.main()


if __name__ == '__main__':
    main()
