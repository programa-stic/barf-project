#! /usr/bin/env python

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
from __future__ import print_function

from barf.analysis.symbolic.emulator import ReilSymbolicEmulator
from barf.analysis.symbolic.emulator import State
from barf.analysis.symbolic.emulator import SymExecResult
from barf.arch.x86 import X86ArchitectureInformation
from barf.core.binary import BinaryFile
from barf.utils.reil import ReilContainerBuilder


def solve():
    #
    # Load binary
    #
    binary = BinaryFile("bin/very_success")

    arch_info = X86ArchitectureInformation(binary.architecture_mode)

    # Create a REIL container for the function of interest
    functions = [
        ("sub_401084", 0x00401084, 0x004010de)
    ]

    reil_container = ReilContainerBuilder(binary).build(functions)

    #
    # Set up initial state
    #
    initial_state = State(arch_info, mode="initial")

    # Set up stack
    esp = 0xffffceec

    initial_state.write_register("esp", esp)

    # Set up parameters
    user_password_addr = 0x00402159
    user_password_len = 0x25
    ref_key_addr = 0x004010e4

    initial_state.write_memory(esp + 0xc, 4, user_password_len)
    initial_state.write_memory(esp + 0x8, 4, user_password_addr)
    initial_state.write_memory(esp + 0x4, 4, ref_key_addr)
    initial_state.write_memory(esp + 0x0, 4, 0x41414141)    # return address

    # Set memory
    for i in range(user_password_len):
        initial_state.write_memory(ref_key_addr + i, 1,
                                   binary.text_section[ref_key_addr + i])

    #
    # Run concolic execution
    #
    sym_exec = ReilSymbolicEmulator(arch_info)

    paths = sym_exec.find_address(
        reil_container, start=0x00401084, end=0x004010de,
        find=0x004010d5, avoid=[0x004010d7], initial_state=initial_state)

    # There's only one way to reach 'find' address.
    assert len(paths) == 1

    #
    # Query input buffer and print content
    #
    final_state = State(arch_info, mode="final")

    se_res = SymExecResult(arch_info, initial_state, paths[0], final_state)

    user_password = bytearray()

    for i in range(user_password_len):
        user_password.append(se_res.query_memory(user_password_addr + i, 1))

    print("User password: {}".format(user_password))

    assert user_password == bytearray("a_Little_b1t_harder_plez@flare-on.com")


if __name__ == "__main__":
    solve()
