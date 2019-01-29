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

import codecs


def _parse_memory(accesses_string):
    accesses = {}

    for token in [t for t in accesses_string.split(",") if t]:
        addr, value = token.split('=')
        accesses[int(addr, 16)] = value

    return accesses


def _parse_registers(registers_string):
    reg_state = {}

    for token in [t for t in registers_string.split(",") if t]:
        reg, value = token.split("=")

        if reg.startswith("xmm"):
            reg_state[reg] = int(codecs.encode(codecs.decode(value, "hex")[::-1], "hex"), 16)
        else:
            reg_state[reg] = int(value, 16)

    return reg_state


def parse_trace(filename, asm_parser, start_address=None):
    start_found = start_address is None
    trace_index = 0
    trace_asm_rep = None
    fold_reps_active = False

    last_syscall = False

    delay_instr = None
    issue_asm = None

    with open(filename, "r") as f:
        for index, line in enumerate(f):
            try:
                tokens = [token.strip().lower() for token in line[:-1].split('|')]

                assert len(tokens) in [5]

                # Check for the requested start address of the trace.
                instr_addr_str, image = tokens[0].split(':')
                image = image.strip()
                instr_addr = int(instr_addr_str, 16)

                if not start_found:
                    if instr_addr == start_address:
                        start_found = True
                    else:
                        # Skip current instruction.
                        continue

                instr_disasm, instr_encoding, reads, registers = tokens[1:5]

                # Parse memory reads and writes.
                mem_reads = _parse_memory(reads)

                # Parse registers.
                reg_state = _parse_registers(registers)

                # Parse instruction.
                asm = asm_parser.parse(instr_disasm)

                # print("Index #{})".format(index))

                if asm:
                    asm.address = instr_addr
                    asm.bytes = codecs.decode(instr_encoding, "hex")
                    asm.size = len(asm.bytes)

                    if asm.prefix and asm.prefix.startswith("rep"):
                        if not fold_reps_active:
                            # print("[+] Start folding {} (#{})".format(asm, index))
                            fold_reps_active = True
                            trace_asm_rep = asm, image, mem_reads, reg_state
                        else:
                            # print("[+] Folding {} (#{})".format(asm, index))
                            asm1, image1, mem_reads1, reg_state1 = trace_asm_rep
                            mem_reads1.update(mem_reads)
                            trace_asm_rep = asm1, image1, mem_reads1, reg_state1

                        continue
                    else:
                        if fold_reps_active:
                            # print("[+] Folding finished {} (#{})".format(asm, index))
                            fold_reps_active = False

                            delay_instr = trace_asm_rep

                        issue_asm = asm, image, mem_reads, reg_state

                    if last_syscall:
                        asm_prev, image_prev, mem_reads_prev, reg_state_prev = delay_instr

                        if "eax" in reg_state:
                            reg_state_prev["eax_next"] = reg_state["eax"]
                        else:
                            reg_state_prev["rax_next"] = reg_state["rax"]

                        delay_instr = asm_prev, image_prev, mem_reads_prev, reg_state_prev

                        last_syscall = False

                    if asm.mnemonic in ["int", "syscall", "sysenter"]:
                        last_syscall = True
                        delay_instr = issue_asm

                        continue

                    if delay_instr:
                        yield delay_instr

                    delay_instr = None

                    yield issue_asm

                    issue_asm = None
                else:
                    raise Exception()
            except GeneratorExit:
                return
            except:
                import traceback
                print(traceback.format_exc())
                print("[-] Error loading instruction #{} (line: #{}): {}".format(trace_index, index, line))

    try:
        if delay_instr:
            yield delay_instr

        if issue_asm:
            yield issue_asm
    except GeneratorExit:
        return


class AsmTrace(object):

    def __init__(self, trace):
        self._curr = None
        self._id = 0
        self._trace = trace

    def current(self):
        if not self._curr:
            raise Exception("Invalid current instruction.")

        return self._curr

    def __next(self):
        self._id += 1
        self._curr = next(self._trace)

        return self._curr

    def set_next_address(self, address):
        self.__next()

        if address:
            try:
                while self._curr[0].address != address:
                    self.__next()
            except StopIteration:
                print("Invalid instruction address: {:#x}.".format(address))
                raise StopIteration()

    def close(self):
        self._trace.close()


class AsmTraceAnalyzer(object):

    def __init__(self, arch, trace):
        self._arch = arch
        self._trace = AsmTrace(trace)
        self._loop = True

    def run(self):
        self.initialize()
        while self._loop:
            try:
                self.before()
                self.analyze()
                self.after()
            except StopIteration:
                self._loop = False
        self.finalize()

    def initialize(self):
        raise NotImplementedError()

    def before(self):
        raise NotImplementedError()

    def after(self):
        raise NotImplementedError()

    def analyze(self):
        raise NotImplementedError()

    def finalize(self):
        raise NotImplementedError()
