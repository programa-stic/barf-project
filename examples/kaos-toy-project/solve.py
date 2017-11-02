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

import struct

from barf.analysis.symbolic.emulator import ReilSymbolicEmulator
from barf.analysis.symbolic.emulator import State
from barf.analysis.symbolic.emulator import SymExecResult
from barf.arch.x86.x86base import X86ArchitectureInformation
from barf.core.bi import BinaryFile
from barf.utils.reil import ReilContainerBuilder


def __get_in_array():
    # Taken from: https://github.com/Cr4sh/openreil/blob/master/tests/test_kao.py
    in_data = ""
    kao_installation_id = '97FF58287E87FB74-979950C854E3E8B3-55A3F121A5590339-6A8DF5ABA981F7CE'

    # convert installation ID into the binary form
    for s in kao_installation_id.split('-'):
        in_data += struct.pack('I', int(s[:8], 16))
        in_data += struct.pack('I', int(s[8:], 16))

    return in_data


def __get_out_array():
    return "0how4zdy81jpe5xfu92kar6cgiq3lst7"


def __save_path(trace, index):
    print("[+] Saving trace... " + "trace_{:02d}.log".format(index))

    with open("trace_{:02d}.log".format(index), "w") as trace_file:
        for reil_instr, _ in trace:
            line = "{:08x}.{:02x}    {}\n".format(reil_instr.address >> 0x8, reil_instr.address & 0xff, reil_instr)
            trace_file.write(line)


def solve():
    #
    # Load Binary
    #
    binary = BinaryFile("bin/toyproject.exe")

    arch_info = X86ArchitectureInformation(binary.architecture_mode)

    # Identify functions of interest
    functions = [
        ("sub_4010ec", 0x004010ec, 0x004010ec + 0x3a)
    ]

    # Create a REIL container
    reil_container_builder = ReilContainerBuilder(binary)

    reil_container = reil_container_builder.build(functions)

    #
    # Set up initial state
    #
    initial_state = State(arch_info, mode="initial")

    # Set up stack
    esp = 0x00001500

    initial_state.write_register("esp", esp)

    # Set up parameters
    out_array_addr = esp - 0x25
    in_array_addr = 0x4093a8

    initial_state.write_memory(esp + 0x0, 4, 0x41414141)  # fake return address

    # TODO: Find a way to mark 'x' and 'y' as symbolic variables.
    # initial_state.write_memory(esp + 0x4, 4, x) # Mark as Symbolic
    # initial_state.write_memory(esp + 0x8, 4, y) # Mark as Symbolic

    # Set the A array
    in_array_expected = bytearray(__get_in_array())

    for i in xrange(len(in_array_expected)):
        initial_state.write_memory(in_array_addr + i, 1, in_array_expected[i])

    #
    # Set up final state
    #
    final_state = State(arch_info, mode="final")

    # Set the B array
    out_array_expected = bytearray(__get_out_array())

    for i in xrange(32):
        # Avoid trivial solution
        initial_state.write_memory(out_array_addr + i, 1, 0)

        # Assert final (desired) state
        final_state.write_memory(out_array_addr + i, 1, out_array_expected[i])

    #
    # Run concolic execution
    #
    sym_exec = ReilSymbolicEmulator(arch_info)

    paths = sym_exec.find_state(reil_container, start=0x004010ec, end=0x0040111d,
                                initial_state=initial_state, final_state=final_state)

    # There's only one way to reach the final state.
    # assert len(paths) == 1

    print("[+] Number of paths: {}".format(len(paths)))

    # for index, path in enumerate(paths):
    #     __save_path(path, index)

    #
    # Query input buffer and print content
    #
    print("A (in)  : {:s}".format(" ".join(["{:02x}".format(b) for b in in_array_expected])))
    print("B (out) : {:s}".format(" ".join(["{:02x}".format(b) for b in out_array_expected])))

    if len(paths) > 0:
        se_res = SymExecResult(arch_info, initial_state, paths[0], final_state)

        print("x: {0:#010x} ({0:d})".format(se_res.query_memory(esp + 0x4, 4)))
        print("y: {0:#010x} ({0:d})".format(se_res.query_memory(esp + 0x8, 4)))
    else:
        print("[-] State Not Found!")


if __name__ == "__main__":
    solve()
