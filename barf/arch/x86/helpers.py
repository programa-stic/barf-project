# Copyright (c) 2017, Fundacion Dr. Manuel Sadosky
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


def fix_flags(src_flag, dst_flag, flags, arch_info):
    for flag in flags:
        _, bit = arch_info.alias_mapper[flag]

        # Clean flag.
        dst_flag &= ~(2**bit) & (2**32-1)

        # Copy flag.
        dst_flag |= (src_flag & 2**bit)

    return src_flag


def compare_contexts(context_init, x86_context, reil_context):
    match = True
    mask = 2**64-1

    for reg in sorted(context_init.keys()):
        if (x86_context[reg] & mask) != (reil_context[reg] & mask):
            match = False
            break

    return match


def print_contexts(context_init, x86_context, reil_context, skip=None):
    header_fmt = " {0:^12s}: {1:^16s} | {2:^16s} || {3:^16s}\n"
    header = header_fmt.format("Register", "Initial", "Expected", "Obtained")
    ruler = "-" * len(header) + "\n"

    out = header
    out += ruler

    fmt = " {0:>12s}: {1:016x} | {2:016x} {eq} {3:016x} {marker}\n"

    mask = 2**64-1

    for reg in sorted(context_init.keys()):
        if skip and reg in skip:
            continue

        if (x86_context[reg] & mask) != (reil_context[reg] & mask):
            eq, marker = "!=", "<"
        else:
            eq, marker = "==", ""

        out += fmt.format(
            reg,
            context_init[reg] & mask,
            x86_context[reg] & mask,
            reil_context[reg] & mask,
            eq=eq,
            marker=marker
        )

    # Pretty print flags.
    fmt = "{0:>6s} ({1:>8s}): {2:016x} ({3:s})"

    reg = "eflags" if "eflags" in context_init else "rflags"

    init_value = context_init[reg]
    x86_value = x86_context[reg]
    reil_value = reil_context[reg]

    init_flags_str = print_flags(context_init[reg])
    x86_flags_str = print_flags(x86_context[reg])
    reil_flags_str = print_flags(reil_context[reg])

    out += "\n"
    out += fmt.format(reg, "initial", init_value, init_flags_str) + "\n"
    out += fmt.format(reg, "expected", x86_value, x86_flags_str) + "\n"
    out += fmt.format(reg, "obtained", reil_value, reil_flags_str)

    return out


def print_registers(registers):
    out = ""

    header_fmt = " {0:^8s} : {1:^16s}\n"
    header = header_fmt.format("Register", "Value")
    ruler = "-" * len(header) + "\n"

    out += header
    out += ruler

    fmt = " {0:>8s} : {1:016x}\n"

    for reg in sorted(registers.keys()):
        out += fmt.format(reg, registers[reg])

    return out


def print_flags(flags):
    # flags
    flags_mapper = {
        0: "cf",   # bit 0
        2: "pf",   # bit 2
        4: "af",   # bit 4
        6: "zf",   # bit 6
        7: "sf",   # bit 7
        10: "df",  # bit 10
        11: "of",  # bit 11
    }

    out = ""

    for bit, flag in flags_mapper.items():
        flag_str = flag.upper() if flags & 2**bit else flag.lower()
        out += flag_str + " "

    return out[:-1]


def print_stack(emulator, sp, addr_size):
    out = ""

    header_fmt = " {0:^15s} : {1:^16s}\n"
    header = header_fmt.format("Address", "Value")
    ruler = "-" * len(header) + "\n"

    out += header
    out += ruler

    for addr in range(sp - 6*addr_size, sp + 6*addr_size, addr_size):
        value = emulator.read_memory(addr, addr_size)

        if addr == sp:
            out += "{:016x} : {:016x} <\n".format(addr, value)
        else:
            out += "{:016x} : {:016x}\n".format(addr, value)

    return out

