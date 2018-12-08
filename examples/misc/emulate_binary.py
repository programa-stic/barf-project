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

import sys
import time

from barf import BARF
from barf.arch import ARCH_ARM
from barf.arch import ARCH_X86
from barf.arch import ARCH_X86_MODE_32
from barf.arch import ARCH_X86_MODE_64
from barf.core.symbols import load_symbols
from barf.utils.cconv import ArmSystemV
from barf.utils.cconv import X86SystemV
from barf.utils.cconv import X86_64SystemV
from barf.utils.utils import read_c_string
from barf.utils.utils import write_c_string


def split_command_line(argv):
    if '--' in argv:
        prg_options = argv[1:argv.index('--')]
        prg_arguments = argv[argv.index('--')+1:]
    else:
        prg_options = argv[1:]
        prg_arguments = []

    return prg_options, prg_arguments


def atoi_hook(emulator, state):
    print("[+] atoi hooked!")

    # int atoi(const char *nptr);

    cc = state['cc']

    # Read parameters.
    nptr = cc.parameters[0]

    # Emulate function behavior.
    value = int(read_c_string(emulator, nptr, max_length=1024))

    # Save result.
    cc.return_value = value


def printf_hook(emulator, state):
    print("[+] printf hooked!")

    # int printf(const char *format, ...);

    cc = state["cc"]

    # Read parameters.
    fmt_ptr = cc.parameters[0]

    # Emulate function behavior.
    fmt = read_c_string(emulator, fmt_ptr, max_length=1024)
    out = fmt

    print(out)

    # Save result.
    cc.return_value = len(out)


def get_symbols(binary_path):
    symbols_by_addr = load_symbols(binary_path)

    symbols_by_name = {}
    for addr in symbols_by_addr:
        name, size, returns = symbols_by_addr[addr]
        symbols_by_name[name] = (addr, size, returns)

    return symbols_by_addr, symbols_by_name


def setup_argv(emulator, argv, base_addr):
    addr_size = emulator.arch_info.address_size // 8

    argv_entry_addr = {}

    # Copy arguments into the stack but first leave space for the argv
    # array (null-terminated).
    addr = base_addr + (len(argv) + 1) * addr_size
    for index, arg in enumerate(argv):
        argv_entry_addr[index] = addr
        write_c_string(emulator, addr, arg)
        addr += len(arg) + 1    # each argument is null-terminated

    # Build argv array.
    for index in range(len(argv)):
        addr = argv_entry_addr[index]
        emulator.write_memory(base_addr + index * addr_size, addr_size, addr)
    # Add null terminator.
    emulator.write_memory(base_addr + len(argv) * addr_size, addr_size, 0x0)


def setup_emulator(emulator, binary, args):
    # Instantiate calling convention.
    if binary.architecture == ARCH_X86:
        if binary.architecture_mode == ARCH_X86_MODE_32:
            cc = X86SystemV(emulator)
        else:
            cc = X86_64SystemV(emulator)
    elif binary.architecture == ARCH_ARM:
        cc = ArmSystemV(emulator)

    arch = emulator.arch_info
    sp = 0x1500
    base_argv = 0x2500

    emulator.registers[arch.stack_pointer_register()] = sp

    setup_argv(emulator, args, base_argv)

    # Setup main's parameters: argc, argv and envp.
    cc.parameters[0] = len(args)    # argc
    cc.parameters[1] = base_argv    # argv
    cc.parameters[2] = 0x0          # envp

    # Load symbols.
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
        'cc': cc,
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
    ctx_init, start, end, hooks = setup_emulator(barf.emulator, barf.binary, prg_arguments)

    # Emulate.
    # ======================================================================== #
    barf.emulate(context=ctx_init, start=start, end=end, hooks=hooks, print_asm=False)

    end_time = time.time()

    total_time = end_time - start_time

    print("[+] Total processing time: {0:8.3f}s".format(total_time))


if __name__ == '__main__':
    if len(sys.argv) != 4:
        print("Usage: {} -- samples/bin/loop-simple1.[x86|x86_64|arm|arm_thumb] <iters>".format(sys.argv[0]))
        sys.exit(1)

    main()
