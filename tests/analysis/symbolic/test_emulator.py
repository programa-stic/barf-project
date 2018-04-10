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

import unittest
import os

from barf.analysis.symbolic.emulator import ReilSymbolicEmulator
from barf.analysis.symbolic.emulator import State
from barf.analysis.symbolic.emulator import SymExecResult
from barf.arch.x86.x86base import X86ArchitectureInformation
from barf.core.bi import BinaryFile
from barf.utils.reil import ReilContainerBuilder


def get_full_path(filename):
    return os.path.dirname(os.path.abspath(__file__)) + filename


class ReilSymbolicEmulatorTests(unittest.TestCase):

    def setUp(self):
        self.__arch_mode = None
        self.__arch = None
        self.__disassembler = None
        self.__translator = None

    def test_se_1(self):
        binary = BinaryFile(get_full_path("/data/bin/check_serial_1"))

        arch_info = X86ArchitectureInformation(binary.architecture_mode)

        functions = [
            ("check_serial", 0x0804841d, 0x08048452)
        ]

        reil_container = ReilContainerBuilder(binary).build(functions)

        # Set up initial state
        initial_state = State(arch_info, mode="initial")

        # Set up stack
        esp = 0xffffceec

        initial_state.write_register("esp", esp)

        # Set up parameters
        user_password_addr = 0xdeadbeef
        user_password_len = 0x6

        initial_state.write_memory(esp + 0x4, 4, user_password_addr)    # password
        initial_state.write_memory(esp + 0x0, 4, 0x41414141)            # fake return address

        # Each byte of the password should be an ascii char.
        for i in xrange(0, user_password_len):
            value = initial_state.query_memory(user_password_addr + i, 1)

            initial_state.add_constraint(value.uge(0x21))
            initial_state.add_constraint(value.ule(0x7e))

        sym_exec = ReilSymbolicEmulator(arch_info)

        paths = sym_exec.find_address(
            reil_container, start=0x0804841d, end=0x08048452,
            find=0x08048451, avoid=[0x0804843b], initial_state=initial_state)

        # There's only one way to reach 'find' address.
        self.assertEqual(len(paths), 1)

        final_state = State(arch_info, mode="final")

        user_password_expected = bytearray("AAAAAA")
        user_password = bytearray()

        se_res = SymExecResult(arch_info, initial_state, paths[0], final_state)

        for i in xrange(0, user_password_len):
            value = se_res.query_memory(user_password_addr + i, 1)
            user_password.append(value)

        self.assertEqual(user_password, user_password_expected)

    def test_se_2(self):
        binary = BinaryFile(get_full_path("/data/bin/check_serial_2"))

        arch_info = X86ArchitectureInformation(binary.architecture_mode)

        functions = [
            ("check_serial", 0x0804841d, 0x08048467)
        ]

        reil_container = ReilContainerBuilder(binary).build(functions)

        # Set up initial state
        initial_state = State(arch_info, mode="initial")

        # Set up stack
        esp = 0xffffceec

        initial_state.write_register("esp", esp)

        # Set up parameters
        user_password_addr = 0xdeadbeef
        user_password_len = 0x6

        initial_state.write_memory(esp + 0x8, 4, user_password_len)     # password length
        initial_state.write_memory(esp + 0x4, 4, user_password_addr)    # password
        initial_state.write_memory(esp + 0x0, 4, 0x41414141)            # fake return address

        # Each byte of the password should be an ascii char.
        for i in xrange(0, user_password_len):
            value = initial_state.query_memory(user_password_addr + i, 1)

            initial_state.add_constraint(value.uge(0x21))
            initial_state.add_constraint(value.ule(0x7e))

        # Set up memory
        ref_key = bytearray("\x31\x27\x30\x2b\x23\x2e")

        initial_state.write_memory(0x0804a020, 4, 0xcafecafe)

        for i in xrange(0, len(ref_key)):
            initial_state.write_memory(0xcafecafe + i, 1, ref_key[i])

        sym_exec = ReilSymbolicEmulator(arch_info)

        paths = sym_exec.find_address(
            reil_container, start=0x0804841d, end=0x08048467,
            find=0x08048466, avoid=[0x0804844e], initial_state=initial_state)

        # There's only one way to reach 'find' address.
        self.assertEqual(len(paths), 1)

        final_state = State(arch_info, mode="final")

        user_password_expected = bytearray("serial")
        user_password = bytearray()

        se_res = SymExecResult(arch_info, initial_state, paths[0], final_state)

        for i in xrange(0, user_password_len):
            value = se_res.query_memory(user_password_addr + i, 1)
            user_password.append(value)

        self.assertEqual(user_password, user_password_expected)

    # # TODO Uncomment once support for indirect jump is implemented.
    # def test_se_3(self):
    #     binary = BinaryFile(get_full_path("/data/bin/check_serial_3"))

    #     arch_info = X86ArchitectureInformation(binary.architecture_mode)

    #     functions = [
    #         ("compare_byte", 0x0804841d, 0x0804843a),
    #         ("check_serial", 0x0804843b, 0x08048486)
    #     ]

    #     reil_container = ReilContainerBuilder(binary).build(functions)

    #     # Set up initial state
    #     initial_state = State(arch_info, mode="initial")

    #     # Set up stack
    #     esp = 0xffffceec

    #     initial_state.write_register("esp", esp)

    #     # Set up parameters
    #     user_password_addr = 0xdeadbeef
    #     user_password_len = 0x6

    #     initial_state.write_memory(esp + 0x8, 4, user_password_len)     # password length
    #     initial_state.write_memory(esp + 0x4, 4, user_password_addr)    # password
    #     initial_state.write_memory(esp + 0x0, 4, 0x41414141)            # fake return address

    #     # Each byte of the password should be an ascii char.
    #     for i in xrange(0, user_password_len):
    #         value = initial_state.query_memory(user_password_addr + i, 1)

    #         initial_state.add_constraint(value.uge(0x21))
    #         initial_state.add_constraint(value.ule(0x7e))

    #     # Set up memory
    #     ref_key = bytearray("\x31\x27\x30\x2b\x23\x2e")

    #     initial_state.write_memory(0x0804a020, 4, 0xcafecafe)

    #     for i in xrange(0, len(ref_key)):
    #         initial_state.write_memory(0xcafecafe + i, 1, ref_key[i])

    #     sym_exec = ReilSymbolicEmulator(arch_info)

    #     paths = sym_exec.find_address(
    #         reil_container, start=0x0804843b, end=0x08048486,
    #         find=0x08048486, avoid=[0x0804846d], initial_state=initial_state)

    #     # There's only one way to reach 'find' address.
    #     self.assertEqual(len(paths), 1)

    #     final_state = State(arch_info, mode="final")

    #     user_password_expected = bytearray("serial")
    #     user_password = bytearray()

    #     se_res = SymExecResult(arch_info, initial_state, paths[0], final_state)

    #     for i in xrange(0, user_password_len):
    #         value = se_res.query_memory(user_password_addr + i, 1)
    #         user_password.append(value)

    #     self.assertEqual(user_password, user_password_expected)

    # # TODO Uncomment once support for indirect jump is implemented.
    # def test_se_4(self):
    #     binary = BinaryFile(get_full_path("/data/bin/check_serial_4"))

    #     arch_info = X86ArchitectureInformation(binary.architecture_mode)

    #     functions = [
    #         ("compare_byte", 0x0804841d, 0x0804843a),
    #         ("check_serial", 0x0804843b, 0x08048486)
    #     ]

    #     reil_container = ReilContainerBuilder(binary).build(functions)

    #     # Set up initial state
    #     initial_state = State(arch_info, mode="initial")

    #     # Set up stack
    #     esp = 0xffffceec

    #     initial_state.write_register("esp", esp)

    #     # Set up parameters
    #     user_password_addr = 0xdeadbeef
    #     user_password_len = 0x6

    #     initial_state.write_memory(esp + 0xc, 4, 0x0804841d)            # compare_byte function address
    #     initial_state.write_memory(esp + 0x8, 4, user_password_len)     # password length
    #     initial_state.write_memory(esp + 0x4, 4, user_password_addr)    # password
    #     initial_state.write_memory(esp + 0x0, 4, 0x41414141)            # fake return address

    #     # Each byte of the password should be an ascii char.
    #     for i in xrange(0, user_password_len):
    #         value = initial_state.query_memory(user_password_addr + i, 1)

    #         initial_state.add_constraint(value.uge(0x21))
    #         initial_state.add_constraint(value.ule(0x7e))

    #     # Set up memory
    #     ref_key = bytearray("\x31\x27\x30\x2b\x23\x2e")

    #     initial_state.write_memory(0x0804a020, 4, 0xcafecafe)

    #     for i in xrange(0, len(ref_key)):
    #         initial_state.write_memory(0xcafecafe + i, 1, ref_key[i])

    #     sym_exec = ReilSymbolicEmulator(arch_info)

    #     paths = sym_exec.find_address(
    #         reil_container, start=0x0804843b, end=0x08048486,
    #         find=0x08048486, avoid=[0x0804846d], initial_state=initial_state)

    #     # There's only one way to reach 'find' address.
    #     self.assertEqual(len(paths), 1)

    #     final_state = State(arch_info, mode="final")

    #     user_password_expected = bytearray("serial")
    #     user_password = bytearray()

    #     se_res = SymExecResult(arch_info, initial_state, paths[0], final_state)

    #     for i in xrange(0, user_password_len):
    #         value = se_res.query_memory(user_password_addr + i, 1)
    #         user_password.append(value)

    #     self.assertEqual(user_password, user_password_expected)

    # # TODO Uncomment once support for indirect jump is implemented.
    # def test_se_5(self):
    #     binary = BinaryFile(get_full_path("/data/bin/check_serial_5"))

    #     arch_info = X86ArchitectureInformation(binary.architecture_mode)

    #     functions = [
    #         ("compare_byte_0", 0x0804841d, 0x0804843c),
    #         ("compare_byte_1", 0x0804843d, 0x08048462),
    #         ("compare_byte_2", 0x08048463, 0x08048488),
    #         ("compare_byte_3", 0x08048489, 0x080484ae),
    #         ("compare_byte_4", 0x080484af, 0x080484d4),
    #         ("compare_byte_5", 0x080484d5, 0x080484fa),
    #         ("check_serial", 0x080484fb, 0x08048560)
    #     ]

    #     reil_container = ReilContainerBuilder(binary).build(functions)

    #     # Set up initial state
    #     initial_state = State(arch_info, mode="initial")

    #     # Set up stack
    #     esp = 0xffffceec

    #     initial_state.write_register("esp", esp)

    #     # Set up parameters
    #     user_password_addr = 0xdeadbeef
    #     user_password_len = 0x6

    #     initial_state.write_memory(esp + 0x8, 4, user_password_len)     # password length
    #     initial_state.write_memory(esp + 0x4, 4, user_password_addr)    # password
    #     initial_state.write_memory(esp + 0x0, 4, 0x41414141)            # fake return address

    #     # Each byte of the password should be an ascii char.
    #     for i in xrange(0, user_password_len):
    #         value = initial_state.query_memory(user_password_addr + i, 1)

    #         initial_state.add_constraint(value.uge(0x21))
    #         initial_state.add_constraint(value.ule(0x7e))

    #     # Set up memory
    #     ref_key = bytearray("\x31\x27\x30\x2b\x23\x2e")

    #     initial_state.write_memory(0x0804a020, 4, 0xcafecafe)

    #     for i in xrange(0, len(ref_key)):
    #         initial_state.write_memory(0xcafecafe + i, 1, ref_key[i])

    #     sym_exec = ReilSymbolicEmulator(arch_info)

    #     paths = sym_exec.find_address(
    #         reil_container, start=0x080484fb, end=0x08048560,
    #         find=0x08048560, avoid=[0x08048547], initial_state=initial_state)

    #     # There's only one way to reach 'find' address.
    #     self.assertEqual(len(paths), 1)

    #     final_state = State(arch_info, mode="final")

    #     user_password_expected = bytearray("serial")
    #     user_password = bytearray()

    #     se_res = SymExecResult(arch_info, initial_state, paths[0], final_state)

    #     for i in xrange(0, user_password_len):
    #         value = se_res.query_memory(user_password_addr + i, 1)
    #         user_password.append(value)

    #     self.assertEqual(user_password, user_password_expected)

    def test_se_6(self):
        binary = BinaryFile(get_full_path("/data/bin/check_serial_6"))

        arch_info = X86ArchitectureInformation(binary.architecture_mode)

        functions = [
            ("expand", 0x0804849b, 0x080484dd)
        ]

        reil_container = ReilContainerBuilder(binary).build(functions)

        # Set up initial state
        initial_state = State(arch_info, mode="initial")

        # Set up stack
        esp = 0xffffceec

        initial_state.write_register("esp", esp)

        # Set up parameters
        out_array_addr = 0xdeadbeef
        in_array_addr = 0xdeadbeef + 0x5

        initial_state.write_memory(esp + 0x04, 4, out_array_addr)      # out
        initial_state.write_memory(esp + 0x08, 4, in_array_addr)       # in
        initial_state.write_memory(esp + 0x0c, 4, 0xAAAAAAAA)
        initial_state.write_memory(esp + 0x10, 4, 0xBBBBBBBB)

        # Set the in array
        for i, b in enumerate(bytearray("\x02\x03\x05\x07")):
            initial_state.write_memory(in_array_addr + i, 1, b)

        #
        # Set up final state
        #
        final_state = State(arch_info, mode="final")

        # Set the B array
        for i, b in enumerate(bytearray("\xFC\xFB\xF5\xF7")):
            final_state.write_memory(out_array_addr + i, 1, b)

        start_addr = 0x0804849b
        end_addr = 0x080484dd

        sym_exec = ReilSymbolicEmulator(arch_info)

        paths = sym_exec.find_state(reil_container, start=start_addr, end=end_addr,
            initial_state=initial_state, final_state=final_state)

        # There's only one way to reach 'find' address.
        self.assertEqual(len(paths), 1)

        se_res = SymExecResult(arch_info, initial_state, paths[0], final_state)

        self.assertEqual(se_res.query_memory(esp + 0x4, 4), 0xdeadbeef)
        self.assertEqual(se_res.query_memory(esp + 0x8, 4), 0xdeadbef4)


def main():
    unittest.main()


if __name__ == '__main__':
    main()
