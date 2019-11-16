# Copyright (c) 2019, Fundacion Dr. Manuel Sadosky
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


def compare_contexts(context_init, arm_context, reil_context):
    match = True
    mask = 2**32-1

    for reg in sorted(context_init.keys()):
        if (arm_context[reg] & mask) != (reil_context[reg] & mask):
            match = False
            break

    return match


def print_contexts(context_init, arm_context, reil_context):
    header_fmt = " {0:^8s} : {1:^16s} | {2:>16s} ?= {3:<16s}\n"
    header = header_fmt.format("Register", "Initial", "ARM", "REIL")
    ruler = "-" * len(header) + "\n"

    out = header
    out += ruler

    fmt = " {0:>8s} : {1:08x} | {2:08x} {eq} {3:08x} {marker}\n"

    mask = 2**64-1

    for reg in sorted(context_init.keys()):
        if (arm_context[reg] & mask) != (reil_context[reg] & mask):
            eq, marker = "!=", "<"
        else:
            eq, marker = "==", ""

        out += fmt.format(
            reg,
            context_init[reg] & mask,
            arm_context[reg] & mask,
            reil_context[reg] & mask,
            eq=eq,
            marker=marker
        )

    # Pretty print flags.
    fmt = "{0:s} ({1:>4s}) : {2:08x} ({3:s})"

    reg = "apsr"

    arm_value = arm_context[reg] & mask
    reil_value = reil_context[reg] & mask

    if arm_value != reil_value:
        arm_flags_str = print_flags(arm_context[reg])
        reil_flags_str = print_flags(reil_context[reg])

        out += "\n"
        out += fmt.format(reg, "ARM", arm_value, arm_flags_str) + "\n"
        out += fmt.format(reg, "reil", reil_value, reil_flags_str)

    return out


def print_flags(flags_reg):
    # flags
    flags = {
         31: "nf",  # bit 31
         30: "zf",  # bit 30
         29: "cf",  # bit 29
         28: "vf",  # bit 28
    }

    out = ""

    for bit, flag in flags.items():
        flag_str = flag.upper() if flags_reg & 2**bit else flag.lower()
        out += flag_str + " "

    return out[:-1]
