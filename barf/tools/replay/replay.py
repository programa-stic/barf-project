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

from __future__ import absolute_import
from __future__ import print_function

import argparse
import sys

from pygments import highlight
from pygments.formatters import TerminalFormatter
from pygments.lexers.asm import NasmLexer

import barf.arch.emulator

from barf.arch import ARCH_X86
from barf.arch import ARCH_X86_MODE_32
from barf.arch import ARCH_X86_MODE_64
from barf.arch.emulator import Emulator
from barf.arch.x86 import X86ArchitectureInformation
from barf.arch.x86.disassembler import X86Disassembler
from barf.arch.x86.helpers import compare_contexts
from barf.arch.x86.helpers import fix_flags
from barf.arch.x86.helpers import print_contexts
from barf.arch.x86.parser import X86Parser
from barf.arch.x86.trace import AsmTraceAnalyzer
from barf.arch.x86.trace import parse_trace
from barf.arch.x86.translator import X86Translator
from barf.core.binary import BinaryFile
from barf.core.reil.emulator.emulator import ReilEmulator


class AsmReplayAnalyzer(AsmTraceAnalyzer):

    def __init__(self, arch, trace, start_address, options):
        AsmTraceAnalyzer.__init__(self, arch, trace)

        self._options = options

        disassembler = X86Disassembler(arch.architecture_mode)
        ir_translator = X86Translator(arch.architecture_mode)

        self._emulator = Emulator(arch, ReilEmulator(arch), ir_translator, disassembler)

        self._undefined_flags = {
            "bsf": ["cf", "of", "sf", "af", "pf"],
            "bt": ["pf"],       # TODO Check.
            "div": ["cf", "of", "sf", "zf", "af", "pf"],
            "imul": ["pf"],     # TODO Check.
            "shl": ["of"],      # TODO Check.
            "shr": ["of"],      # TODO Check.
        }

        self._set_regs = True
        self._next_addr = start_address

    def initialize(self):
        self._trace.set_next_address(self._next_addr)

    def before(self):
        asm_instr, _, reads, regs = self._trace.current()

        # Set registers if necessary (after syscall.)
        if self._set_regs:
            print("[+] Setting registers...")
            self._emulator.set_registers(regs)

        # Initialize memory.
        self._emulator.set_memory(reads)

    def analyze(self):
        # Fetch instruction from the trace.
        asm_instr, _, _, _ = self._trace.current()

        # Execute instruction.
        try:
            self._next_addr = self._emulator.execute(asm_instr)
            self._set_regs = False
        except barf.arch.emulator.Syscall:
            self._next_addr = None
            self._set_regs = True
        except barf.arch.emulator.InstructionNotImplemented as e:
            print("[-] Instruction not implemented: {:#x} {}".format(asm_instr.address, e.instruction))

            if self._options.abort:
                sys.exit(1)
            else:
                self._next_addr = asm_instr.address + asm_instr.size
                self._set_regs = True

    def after(self):
        state_curr = self._trace.current()

        # Advance to the next instruction.
        self._trace.set_next_address(self._next_addr)

        state_next = self._trace.current()

        # Compare contexts.
        asm_instr_curr, _, _, regs_curr = state_curr
        _, _, _, regs_next = state_next

        # Print instruction.
        if self._options.verbose:
            asm_str = format_asm_instruction(asm_instr_curr, self._options)
            print("{:#010x}:\t{}".format(asm_instr_curr.address, asm_str))

        if asm_instr_curr.mnemonic in ["sysenter"]:
            return

        # Fix undefine flags.
        if asm_instr_curr.mnemonic in self._undefined_flags:
            print("Fixing undefined flags...")

            flags_reg = self._arch.flags_register()

            flags_next = regs_next[flags_reg]
            flags_curr = self._emulator.ir_emulator.registers[flags_reg]
            flags_undef = self._undefined_flags[asm_instr_curr.mnemonic]

            self._emulator.ir_emulator.registers[flags_reg] = fix_flags(flags_next, flags_curr, flags_undef, self._arch)

        # Check registers values.
        cmp_result = compare_contexts(regs_curr, regs_next, self._emulator.ir_emulator.registers)

        if not cmp_result:
            print("Contexts don't match!\n\n")

            print(print_contexts(regs_curr, regs_next, self._emulator.ir_emulator.registers, skip=["eax_next", "rax_next"]))

            if self._options.abort:
                sys.exit(1)
            else:
                self._set_regs = True

    def finalize(self):
        self._trace.close()


def format_asm_instruction(asm_instr, options):
    nasm_lexer = NasmLexer()
    term_formatter = TerminalFormatter()

    if options.color:
        asm_str = highlight(str(asm_instr), nasm_lexer, term_formatter)[:-1]
    else:
        asm_str = str(asm_instr)

    return asm_str


class DotDict(dict):
    """
    a dictionary that supports dot notation
    as well as dictionary access notation
    usage: d = DotDict() or d = DotDict({'val1':'first'})
    set attributes: d.val2 = 'second' or d['val2'] = 'second'
    get attributes: d.val2 or d['val2']
    """
    __getattr__ = dict.__getitem__
    __setattr__ = dict.__setitem__
    __delattr__ = dict.__delitem__

    def __init__(self, dct, **kwargs):
        super(DotDict, self).__init__(**kwargs)

        for key, value in dct.items():
            if hasattr(value, 'keys'):
                value = DotDict(value)
            self[key] = value


def init_parser():

    description = "Tool for replaying a x86 binary trace."

    arg_parser = argparse.ArgumentParser(
        formatter_class=argparse.RawDescriptionHelpFormatter,
        description=description)

    arg_parser.add_argument(
        "-a", "--abort",
        default=False,
        action="store_true",
        help="abort on error")

    arg_parser.add_argument(
        "-c", "--color",
        action="store_true",
        help="format assembler with ANSI color sequences, for output in a 256-color terminal or console")

    arg_parser.add_argument(
        "-v", "--verbose",
        default=False,
        action="store_true",
        help="verbose")

    arg_parser.add_argument(
        "-s", "--start-address",
        type=str,
        help="start address")

    arg_parser.add_argument(
        "binary",
        type=str,
        help="binary file name")

    arg_parser.add_argument(
        "trace",
        type=str,
        help="trace file name")

    return arg_parser


def main():
    # Process program arguments.
    parser = init_parser()
    args = parser.parse_args()

    # Open binary.
    binary = BinaryFile(args.binary)

    # Check binary arch and mode.
    if binary.architecture != ARCH_X86 or \
            binary.architecture_mode not in [ARCH_X86_MODE_32, ARCH_X86_MODE_64]:
        print("[!] Architecture not supported.")
        sys.exit(1)

    # Load architecture information for the binary.
    arch_info = X86ArchitectureInformation(binary.architecture_mode)

    # Extract entrypoint (in case a starting address was not provided.)
    start_address = int(args.start_address, 16) if args.start_address else binary.entry_point

    # Prepare options.
    options = DotDict({})
    options.abort = args.abort
    options.color = args.color
    options.verbose = args.verbose

    print("[+] Loading trace...")
    asm_trace = parse_trace(args.trace, X86Parser(arch_info.architecture_mode),
                            start_address=start_address)

    print("[+] Replaying trace...")
    analyzer = AsmReplayAnalyzer(arch_info, asm_trace, start_address, options)

    analyzer.run()


if __name__ == "__main__":
    main()
