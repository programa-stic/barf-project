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

import sys
import time

from barf import BARF
from barf.arch import ARCH_ARM
from barf.arch import ARCH_ARM_MODE_ARM
from barf.arch import ARCH_ARM_MODE_THUMB
from barf.arch import ARCH_X86
from barf.arch import ARCH_X86_MODE_32
from barf.arch import ARCH_X86_MODE_64
from barf.arch.arm.armbase import ArmArchitectureInformation
from barf.arch.x86.x86base import X86ArchitectureInformation
from barf.core.symbols import load_symbols


def __print_stack(emulator, sp, addr_size):
    out = ""

    header_fmt = " {0:^15s} : {1:^16s}\n"
    header = header_fmt.format("Address", "Value")
    ruler = "-" * len(header) + "\n"

    out += header
    out += ruler

    for addr in xrange(sp - 6*addr_size, sp + 6*addr_size, addr_size):
        value = emulator.read_memory(addr, addr_size)

        if addr == sp:
            out += "{:016x} : {:016x} <\n".format(addr, value)
        else:
            out += "{:016x} : {:016x}\n".format(addr, value)

    print(out)


def split_command_line(argv):
    if '--' in argv:
        prg_options = argv[1:argv.index('--')]
        prg_arguments = argv[argv.index('--')+1:]
    else:
        prg_options = argv[1:]
        prg_arguments = []

    return prg_options, prg_arguments


def read_c_string(reil_emulator, address, max_length=1024):
    i = 0
    data = bytearray()
    while i < max_length:
        b = reil_emulator.read_memory(address + i, 1)
        if b == 0:
            break
        data.append(b)
        i += 1
    return data.decode()


def write_c_string(reil_emulator, address, string):
    for i, b in enumerate(string):
        reil_emulator.write_memory(address + i, 1, b)


def atoi_hook(emulator, state):
    print("[+] atoi hooked!")

    arch = state["arch"]
    binary = state["binary"]

    # Read parameters.
    if binary.architecture == ARCH_X86:
        if binary.architecture_mode == ARCH_X86_MODE_32:
            sp = emulator.registers[arch.stack_pointer_register()]
            ws = arch.address_size / 8

            nptr = emulator.read_memory(sp + 1 * ws, ws)

        if binary.architecture_mode == ARCH_X86_MODE_64:
            nptr = emulator.registers["rdi"]

    if binary.architecture == ARCH_ARM:
        nptr = emulator.registers["r0"]

    int_str = read_c_string(emulator, nptr, max_length=1024)

    # Emulate function behavior.
    if binary.architecture == ARCH_X86:
        if binary.architecture_mode == ARCH_X86_MODE_32:
            emulator.registers["eax"] = int(int_str)

        if binary.architecture_mode == ARCH_X86_MODE_64:
            emulator.registers["rax"] = int(int_str)

    if binary.architecture == ARCH_ARM:
        emulator.registers["r0"] = int(int_str)


def printf_hook(emulator, state):
    print("[+] printf hooked!")

    arch = state["arch"]
    binary = state["binary"]

    # Read parameters.
    if binary.architecture == ARCH_X86:
        if binary.architecture_mode == ARCH_X86_MODE_32:
            sp = emulator.registers[arch.stack_pointer_register()]
            ws = arch.address_size / 8

            fmt_ptr = emulator.read_memory(sp + 1 * ws, ws)

        if binary.architecture_mode == ARCH_X86_MODE_64:
            fmt_ptr = emulator.registers["rdi"]

    if binary.architecture == ARCH_ARM:
        fmt_ptr = emulator.registers["r0"]

    fmt = read_c_string(emulator, fmt_ptr, max_length=1024)

    # Emulate function behavior.
    print(fmt)


def get_symbols(binary_path):
    symbols_by_addr = load_symbols(binary_path)

    symbols_by_name = {}
    for addr in symbols_by_addr:
        name, size, returns = symbols_by_addr[addr]
        symbols_by_name[name] = (addr, size, returns)

    return symbols_by_addr, symbols_by_name


def get_arch(binary):
    if binary.architecture == ARCH_X86:
        return X86ArchitectureInformation(architecture_mode=binary.architecture_mode)
    elif binary.architecture == ARCH_ARM:
        return ArmArchitectureInformation(architecture_mode=binary.architecture_mode)
    else:
        raise Exception("Architecture not supported.")


def load_args(addr_size, args, argv_args_addr, argv_base_addr, reil_emulator):
    argv_entry_addr = {}

    # Load args into memory.
    base_addr = argv_args_addr
    for index, arg in enumerate(args):
        argv_entry_addr[index] = base_addr

        for b in bytearray(arg + "\x00"):
            reil_emulator.write_memory(base_addr, 1, b)
            base_addr += 1

    # Build args array.
    for index in xrange(len(args)):
        addr = argv_entry_addr[index]
        reil_emulator.write_memory(argv_base_addr + index * addr_size, addr_size, addr)
    # Add null terminator.
    reil_emulator.write_memory(argv_base_addr + len(args) * addr_size, addr_size, 0x0)


def setup_emulator(reil_emulator, binary, args):
    arch = get_arch(binary)

    sp = 0x00001500
    ws = arch.address_size / 8

    argv_base_addr = 0x2500
    argv_args_addr = 0x3500

    load_args(ws, args, argv_args_addr, argv_base_addr, reil_emulator)

    if binary.architecture == ARCH_X86:
        if binary.architecture_mode == ARCH_X86_MODE_32:
            reil_emulator.write_memory(sp + 1 * ws, ws, len(args))            # argc
            reil_emulator.write_memory(sp + 2 * ws, ws, argv_base_addr)       # argv
            reil_emulator.write_memory(sp + 3 * ws, ws, 0x00000000)           # envp

        if binary.architecture_mode == ARCH_X86_MODE_64:
            reil_emulator.registers["rdi"] = len(args)
            reil_emulator.registers["rsi"] = argv_base_addr
            reil_emulator.registers["rdx"] = 0x00000000

    if binary.architecture == ARCH_ARM:
        reil_emulator.registers["r0"] = len(args)
        reil_emulator.registers["r1"] = argv_base_addr
        reil_emulator.registers["r2"] = 0x00000000

    # Loading symbols.
    # ======================================================================== #
    print("[+] Loading symbols...")

    symbols_by_addr, symbols_by_name = get_symbols(binary.filename)

    start = symbols_by_name["main"][0]
    size = symbols_by_name["main"][1]

    # TODO Remove hardcoded addresses.
    if binary.architecture == ARCH_X86:
        end = start + size - 1

        if binary.architecture_mode == ARCH_X86_MODE_32:
            atoi_addr = 0x8048380
            printf_addr = 0x8048350

        if binary.architecture_mode == ARCH_X86_MODE_64:
            atoi_addr = 0x4004d0
            printf_addr = 0x4004a0

    if binary.architecture == ARCH_ARM:
        end = start + size - 8 - 8

        if start & 0x1 == 0x1:      # ARCH_ARM_MODE_THUMB
            atoi_addr = 0x10394
            printf_addr = 0x1035c

        if start & 0x1 == 0x0:      # ARCH_ARM_MODE_ARM
            atoi_addr = 0x10388
            printf_addr = 0x10358

    state = {
        'arch': arch,
        'binary': binary,
    }

    ctx_init = {
        'registers': {
            arch.flags_register(): arch.flags_default_value(),
            arch.stack_pointer_register(): sp,
        }
    }

    hooks = {
        atoi_addr: (atoi_hook, state, True, 0),
        printf_addr: (printf_hook, state, True, 0),
    }

    return ctx_init, start, end, hooks


def main():
    start_time = time.time()

    # Split program arguments.
    # ======================================================================== #
    prg_options, prg_arguments = split_command_line(sys.argv)

    binary_path = prg_arguments[0]

    # Loading binary.
    # ======================================================================== #
    print("[+] Loading binary...")

    barf = BARF(binary_path)

    if barf.binary.architecture not in [ARCH_X86, ARCH_ARM]:
        print("[-] Architecture not supported!")

        sys.exit(1)

    # Setup emulator.
    # ======================================================================== #
    ctx_init, start, end, hooks = setup_emulator(barf.ir_emulator, barf.binary, prg_arguments)

    # Emulate.
    # ======================================================================== #
    barf.emulate(context=ctx_init, start=start, end=end, hooks=hooks, print_asm=False)

    end_time = time.time()

    total_time = end_time - start_time

    print("[+] Total processing time: {0:8.3f}s".format(total_time))


if __name__ == '__main__':
    if len(sys.argv) != 4:
        print("Usage: {} -- loop-simple1.[x86|x86_64|arm|arm_thumb] <iters>".format(sys.argv[0]))
        sys.exit(1)

    main()
