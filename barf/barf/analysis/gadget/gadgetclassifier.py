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

"""
This is the gadget classifier. It classify gadgets in 10 different
types: No Operation, Jump, Move Register, Load Constant, Arithmetic,
Load Memory, Store Memory, Arithmetic Load, Arithmetic Store or
Undefined. This classification is based on the paper "Q: Exploit
Hardening Made Easy." So, given a gadget (RawGadget object) it generate
one o more TypedGadgets with its type.

This algorithm is architecture agnostic since it operates on the IR
representation of the underlying assembly code.

"""

import random

from barf.analysis.gadget import GadgetType
from barf.analysis.gadget import TypedGadget
from barf.core.reil import ReilEmptyOperand
from barf.core.reil import ReilImmediateOperand
from barf.core.reil import ReilRegisterOperand

class GadgetClassifier(object):

    """Gadget Classifier.
    """

    def __init__(self, ir_emulator, architecture_info):

        # An instance of a REIL emulator
        self._ir_emulator = ir_emulator

        # Classifiers ordered by gadget type.
        self._classifiers = {
            GadgetType.NoOperation     : self._classify_no_operation,
            GadgetType.Jump            : self._classify_jump,
            GadgetType.MoveRegister    : self._classify_move_register,
            GadgetType.LoadConstant    : self._classify_load_constant,
            GadgetType.Arithmetic      : self._classify_arithmetic,
            GadgetType.LoadMemory      : self._classify_load_memory,
            GadgetType.StoreMemory     : self._classify_store_memory,
            GadgetType.ArithmeticLoad  : self._classify_arithmetic_load,
            GadgetType.ArithmeticStore : self._classify_arithmetic_store,
        }

        # Supported arithmetic and logical operations for arithmetic
        # gadgets.
        self._binary_ops = {
            # Arithmetic
            "+"  : lambda x, y : x + y,
            "-"  : lambda x, y : x - y,

            # "*"  : lambda x, y : x * y,
            # "/"  : lambda x, y : x / y,
            # "%"  : lambda x, y : x % y,

            # Bitwise
            "&"  : lambda x, y : x & y,
            "^"  : lambda x, y : x ^ y,
            "|"  : lambda x, y : x | y,

            # "<<" : lambda x, y : x << y,
            # ">>" : lambda x, y : x >> y,
        }

        # Architecture information.
        self._arch_info = architecture_info

        self._arch_regs = self._arch_info.registers_gp_all
        self._arch_regs_parent = self._arch_info.registers_gp_base
        self._arch_regs_size = self._arch_info.registers_size
        self._address_size = self._arch_info.address_size

        # Number of simulation iterations.
        self._emu_iters = 10

    def classify(self, gadget):
        """Classify gadget.
        """
        typed_gadgets = []

        for g_type, g_classifier in self._classifiers.items():
            try:
                typed_gadgets += self._classify(gadget, g_classifier, g_type, self._emu_iters)
            except:
                import traceback

                print("[-] Error classifying gadgets :")
                print(gadget)
                print("")
                print(traceback.format_exc())

        return typed_gadgets

    # Classifiers
    # ======================================================================== #
    def _classify_no_operation(self, regs_init, regs_fini, mem_fini, written_regs, read_regs):
        """Classify no-operation gadgets.
        """
        # TODO: Flags should be taken into account

        matchings = []

        # Check that registers didn't change their value.
        regs_changed = any(regs_init[r] != regs_fini[r] for r in regs_init)

        # Check that flags didn't change their value.
        flags_changed = False

        # Check that memory didn't change.
        mem_changed = mem_fini.get_write_count() != 0

        if not regs_changed and not flags_changed and not mem_changed:
            matchings.append({
                "op" : "nop",
            })

        return matchings

    def _classify_jump(self, regs_init, regs_fini, mem_fini, written_regs, read_regs):
        """Classify jump gadgets.
        """
        # TODO: Implement.

        matchings = []

        return matchings

    def _classify_move_register(self, regs_init, regs_fini, mem_fini, written_regs, read_regs):
        """Classify move-register gadgets.
        """
        matchings = []

        regs_init_inv = self._invert_dictionary(regs_init)

        # Check for "dst_reg <- src_reg" pattern.
        for dst_reg, dst_val in regs_fini.items():
            # Make sure the *dst* register was written.
            if dst_reg not in written_regs:
                continue

            for src_reg in regs_init_inv.get(dst_val, []):
                # Make sure the *src* register was read.
                if src_reg not in read_regs:
                    continue

                # Check restrictions...
                if self._arch_regs_size[src_reg] != self._arch_regs_size[dst_reg]:
                    continue

                if src_reg == dst_reg:
                    continue

                if regs_init[dst_reg] == regs_init[src_reg]:
                    continue

                src_reg_ir = ReilRegisterOperand(src_reg, self._arch_regs_size[src_reg])
                dst_reg_ir = ReilRegisterOperand(dst_reg, self._arch_regs_size[dst_reg])

                matchings.append({
                    "src" : [src_reg_ir],
                    "dst" : [dst_reg_ir]
                })

        return matchings

    def _classify_load_constant(self, regs_init, regs_fini, mem_fini, written_regs, read_regs):
        """Classify load-constant gadgets.
        """
        matchings = []

        # Check for "dst_reg <- constant" pattern.
        for dst_reg, dst_val in regs_fini.items():
            # Make sure the *dst* register was written.
            if dst_reg not in written_regs:
                continue

            # Check restrictions...
            if dst_val == regs_init[dst_reg]:
                continue

            dst_val_ir = ReilImmediateOperand(dst_val, self._arch_regs_size[dst_reg])
            dst_reg_ir = ReilRegisterOperand(dst_reg, self._arch_regs_size[dst_reg])

            matchings.append({
                "src" : [dst_val_ir],
                "dst" : [dst_reg_ir]
            })

        return matchings

    def _classify_arithmetic(self, regs_init, regs_fini, mem_fini, written_regs, read_regs):
        """Classify binary-operation gadgets.
        """
        matchings = []

        # TODO: Review these restrictions.
        op_restrictions = {
            "+" : lambda x, y : False,
            "-" : lambda x, y : x == y,
            "|" : lambda x, y : x == y,
            "&" : lambda x, y : x == y,
            "^" : lambda x, y : x == y,
        }

        # Check for "dst_reg <- src1_reg OP src2_reg" pattern.
        for op_name, op_fn in self._binary_ops.items():
            for src_1_reg, src_1_val in regs_init.items():
                # Make sure the *src* register was read.
                if src_1_reg not in read_regs:
                    continue

                for src_2_reg, src_2_val in regs_init.items():
                    # Make sure the *src* register was read.
                    if src_2_reg not in read_regs:
                        continue

                    for dst_reg, dst_val in regs_fini.items():
                        # Make sure the *dst* register was written.
                        if dst_reg not in written_regs:
                            continue

                        # Check restrictions.
                        if self._arch_regs_size[src_1_reg] != self._arch_regs_size[src_2_reg] or \
                            self._arch_regs_size[src_1_reg] != self._arch_regs_size[dst_reg]:
                            continue

                        # Avoid trivial operations.
                        if op_restrictions[op_name](src_1_reg, src_2_reg):
                            continue

                        size = self._arch_regs_size[src_1_reg]

                        if dst_val == op_fn(src_1_val, src_2_val) & (2**size - 1):
                            src = sorted([src_1_reg, src_2_reg])

                            src_ir = [
                                ReilRegisterOperand(src[0], self._arch_regs_size[src[0]]),
                                ReilRegisterOperand(src[1], self._arch_regs_size[src[1]])
                            ]

                            dst_reg_ir = ReilRegisterOperand(dst_reg, self._arch_regs_size[dst_reg])

                            matchings.append({
                                "src" : src_ir,
                                "dst" : [dst_reg_ir],
                                "op"  : op_name
                            })

        return matchings

    def _classify_load_memory(self, regs_init, regs_fini, mem_fini, written_regs, read_regs):
        """Classify load-memory gadgets.
        """
        matchings = []

        regs_init_inv = self._invert_dictionary(regs_init)

        # Check for "dst_reg <- mem[src_reg + offset]" pattern.
        for dst_reg, dst_val in regs_fini.items():
            # Make sure the *dst* register was written.
            if dst_reg not in written_regs:
                continue

            dst_size = self._arch_regs_size[dst_reg]

            # Look for memory addresses that contain *dst_val*.
            for src_addr in mem_fini.read_inverse(dst_val, dst_size / 8):

                # Look for registers whose values are used as memory
                # addresses.
                for src_reg, src_val in regs_init.items():
                    # Make sure the *src* register was read.
                    if src_reg not in read_regs:
                        continue

                    # Check restrictions.
                    if self._arch_regs_size[src_reg] != self._address_size:
                        continue

                    offset = (src_addr - src_val) & (2**self._address_size - 1)

                    src_reg_ir = ReilRegisterOperand(src_reg, self._arch_regs_size[src_reg])
                    src_off_ir = ReilImmediateOperand(offset, self._arch_regs_size[src_reg])
                    dst_reg_ir = ReilRegisterOperand(dst_reg, self._arch_regs_size[dst_reg])

                    matchings.append({
                        "src" : [src_reg_ir, src_off_ir],
                        "dst" : [dst_reg_ir]
                    })

        # Check for "dst_reg <- mem[offset]" pattern.
        for dst_reg, dst_val in regs_fini.items():
            # Make sure the *dst* register was written.
            if dst_reg not in written_regs:
                continue

            dst_size = self._arch_regs_size[dst_reg]

            for src_addr in mem_fini.read_inverse(dst_val, dst_size / 8):
                src_reg_ir = ReilEmptyOperand()
                src_off_ir = ReilImmediateOperand(src_addr, self._address_size)
                dst_reg_ir = ReilRegisterOperand(dst_reg, self._arch_regs_size[dst_reg])

                matchings.append({
                    "src" : [src_reg_ir, src_off_ir],
                    "dst" : [dst_reg_ir]
                })

        return matchings

    def _classify_store_memory(self, regs_init, regs_fini, mem_fini, written_regs, read_regs):
        """Classify store-memory gadgets.
        """
        matchings = []

        regs_init_inv = self._invert_dictionary(regs_init)

        # Check for "mem[dst_reg + offset] <- src_reg" pattern.
        for src_reg, src_val in regs_init.items():
            # Make sure the *src* register was read.
            if not src_reg in read_regs:
                continue

            src_size = self._arch_regs_size[src_reg]

            for addr in mem_fini.read_inverse(src_val, src_size / 8):
                for dst_reg, dst_val in regs_init.items():
                    # Make sure the *dst* register was written.
                    if not dst_reg in read_regs:
                        continue

                    # Check restrictions.
                    if self._arch_regs_size[dst_reg] != self._address_size:
                        continue

                    offset = (addr - dst_val) & (2**self._address_size - 1)

                    src_reg_ir = ReilRegisterOperand(src_reg, self._arch_regs_size[src_reg])
                    dst_reg_ir = ReilRegisterOperand(dst_reg, self._arch_regs_size[dst_reg])
                    dst_off_ir = ReilImmediateOperand(offset, self._arch_regs_size[dst_reg])

                    matchings.append({
                        "src" : [src_reg_ir],
                        "dst" : [dst_reg_ir, dst_off_ir]
                    })

        # Check for "mem[offset] <- src_reg" pattern.
        for src_reg, src_val in regs_init.items():
            # Make sure the *src* register was read.
            if not src_reg in read_regs:
                continue

            src_size = self._arch_regs_size[src_reg]

            for addr in mem_fini.read_inverse(src_val, src_size / 8):
                offset = addr & (2**self._address_size - 1)

                src_reg_ir = ReilRegisterOperand(src_reg, self._arch_regs_size[src_reg])
                dst_reg_ir = ReilEmptyOperand()
                dst_off_ir = ReilImmediateOperand(offset, self._address_size)

                matchings.append({
                    "src" : [src_reg_ir],
                    "dst" : [dst_reg_ir, dst_off_ir]
                })

        return matchings

    def _classify_arithmetic_load(self, regs_init, regs_fini, mem_fini, written_regs, read_regs):
        """Classify arithmetic-load gadgets.
        """
        matchings = []

        # Check for "dst_reg <- dst_reg OP mem[src_reg + offset]" pattern.
        for op_name, op_fn in self._binary_ops.items():
            for dst_reg, dst_val in regs_fini.items():
                # Make sure the *dst* register was read and written.
                if dst_reg not in written_regs or dst_reg not in read_regs:
                    continue

                dst_size = self._arch_regs_size[dst_reg]

                for addr in mem_fini.get_addresses():
                    success, val = mem_fini.try_read(addr, dst_size / 8)

                    if success and dst_val == op_fn(regs_init[dst_reg], val) & (2**dst_size - 1):

                        for src_reg, src_val in regs_init.items():
                            # Make sure the *src* register was read.
                            if not src_reg in read_regs:
                                continue

                            # Check restrictions.
                            if self._arch_regs_size[src_reg] != self._address_size:
                                continue

                            offset = (addr - src_val) & (2**self._address_size - 1)

                            src_reg_ir = ReilRegisterOperand(src_reg, self._arch_regs_size[src_reg])
                            src_off_ir = ReilImmediateOperand(offset, self._address_size)
                            dst_reg_ir = ReilRegisterOperand(dst_reg, self._arch_regs_size[dst_reg])

                            matchings.append({
                                "src" : [dst_reg_ir, src_reg_ir, src_off_ir],
                                "dst" : [dst_reg_ir],
                                "op"  : op_name
                            })

        # Check for "dst_reg <- dst_reg OP mem[offset]" pattern.
        for op_name, op_fn in self._binary_ops.items():
            for dst_reg, dst_val in regs_fini.items():
                # Make sure the *dst* register was read and written.
                if dst_reg not in written_regs or dst_reg not in read_regs:
                    continue

                dst_size = self._arch_regs_size[dst_reg]

                for addr in mem_fini.get_addresses():
                    success, val = mem_fini.try_read(addr, dst_size / 8)

                    if success and dst_val == op_fn(regs_init[dst_reg], val) & (2**dst_size - 1):
                        src_reg_ir = ReilEmptyOperand()
                        src_off_ir = ReilImmediateOperand(addr, self._address_size)
                        dst_reg_ir = ReilRegisterOperand(dst_reg, self._arch_regs_size[dst_reg])

                        matchings.append({
                            "src" : [dst_reg_ir, src_reg_ir, src_off_ir],
                            "dst" : [dst_reg_ir],
                            "op"  : op_name
                        })

        return matchings

    def _classify_arithmetic_store(self, regs_init, regs_fini, mem_fini, written_regs, read_regs):
        """Classify arithmetic-store gadgets.
        """
        matchings = []

        # Check for "m[dst_reg + offset] <- m[dst_reg + offset] OP src_reg" pattern.
        for op_name, op_fn in self._binary_ops.items():
            for size in [8, 16, 32, 64]:
                for addr in mem_fini.get_addresses():
                    success_read_curr, val_curr = mem_fini.try_read(addr, size / 8)
                    success_read_prev, val_prev = mem_fini.try_read_prev(addr, size / 8)

                    if success_read_curr and success_read_prev:
                        for src_reg, src_val in regs_init.items():
                            # Make sure the *src* register was read.
                            if not src_reg in read_regs:
                                continue

                            # Check restrictions.
                            if self._arch_regs_size[src_reg] != size:
                                continue

                            if val_curr == op_fn(src_val, val_prev) & (2**size - 1):
                                # find dst + offset
                                for dst_reg, dst_val in regs_init.items():
                                    # Make sure the *dst* register was written.
                                    if not dst_reg in read_regs:
                                        continue

                                    # Check restrictions.
                                    if self._arch_regs_size[dst_reg] != self._address_size:
                                        continue

                                    offset = (addr - dst_val) & (2**self._address_size - 1)

                                    src_reg_ir = ReilRegisterOperand(src_reg, self._arch_regs_size[src_reg])
                                    dst_reg_ir = ReilRegisterOperand(dst_reg, self._arch_regs_size[dst_reg])
                                    dst_off_ir = ReilImmediateOperand(offset, self._address_size)

                                    matchings.append({
                                        "src" : [dst_reg_ir, dst_off_ir, \
                                            src_reg_ir],
                                        "dst" : [dst_reg_ir, dst_off_ir],
                                        "op"  : op_name
                                    })

        # Check for "m[offset] <- m[offset] OP src_reg" pattern.
        for op_name, op_fn in self._binary_ops.items():
            for size in [8, 16, 32, 64]:
                for addr in mem_fini.get_addresses():
                    success_read_curr, val_curr = mem_fini.try_read(addr, size / 8)
                    success_read_prev, val_prev = mem_fini.try_read_prev(addr, size / 8)

                    if success_read_curr and success_read_prev:
                        for src_reg, src_val in regs_init.items():
                            # Make sure the *src* register was read.
                            if not src_reg in read_regs:
                                continue

                            # Check restrictions.
                            if self._arch_regs_size[src_reg] != size:
                                continue

                            if val_curr == op_fn(src_val, val_prev) & (2**size - 1):
                                src_reg_ir = ReilRegisterOperand(src_reg, self._arch_regs_size[src_reg])
                                dst_reg_ir = ReilEmptyOperand()
                                dst_off_ir = ReilImmediateOperand(addr, self._address_size)

                                matchings.append({
                                    "src" : [dst_reg_ir, dst_off_ir, src_reg_ir],
                                    "dst" : [dst_reg_ir, dst_off_ir],
                                    "op"  : op_name
                                })

        return matchings

    # Auxiliary functions
    # ======================================================================== #
    def _classify(self, gadget, classifier, gadget_type, iters):
        """Classify gadgets.
        """
        # Collect REIL instructions of the gadget.
        instrs = [ir_instr for g_instrs in gadget.instrs
                           for ir_instr in g_instrs.ir_instrs]

        # Repeat classification.
        results = []

        for _ in xrange(iters):
            # Reset emulator.
            self._ir_emulator.reset()

            # Generate random values for registers.
            regs_initial = self._init_regs_random()

            # Emulate gadget.
            try:
                regs_final, mem_final = self._ir_emulator.execute_lite(
                    instrs,
                    regs_initial
                )
            except:
                # Catch emulator exceptions like ZeroDivisionError, etc.
                results += [([], [])]

                continue

            # Compute values for all registers. For example, in x86, it
            # computes 'al' from 'eax'.
            regs_initial_full = self._compute_full_context(regs_initial)
            regs_final_full   = self._compute_full_context(regs_final)

            # Get written and read registers.
            regs_written = self._ir_emulator.written_registers
            regs_read    = self._ir_emulator.read_registers

            # Compute modifiead registers.
            mod_regs = self._compute_mod_regs(
                regs_initial_full,
                regs_final_full
            )

            # Classified gadgets based on initial and final context.
            matchings = classifier(
                regs_initial_full,
                regs_final_full,
                mem_final,
                regs_written,
                regs_read
            )

            # Save results.
            results += [(matchings, mod_regs)]

        # Analyze results and compute candidate gadgets.
        candidates, mod_regs = self._analize_execution_results(results)

        # Create classified gadgets.
        classified = self._create_typed_gadgets(
            gadget,
            candidates,
            mod_regs,
            gadget_type
        )

        return classified

    def _analize_execution_results(self, results):
        matching_candidates, _ = results[0]

        classified_candidates = []

        for matching_candidate in matching_candidates:
            valid_matching = True

            for matchings, _ in results[1:]:
                if matching_candidate not in matchings:
                    valid_matching = False

            if valid_matching and \
                matching_candidate not in classified_candidates:
                classified_candidates.append(matching_candidate)

        modified_regs = set()

        for _, mod_regs in results:
            modified_regs = modified_regs.union(set(mod_regs))

        return classified_candidates, list(modified_regs)

    def _create_typed_gadgets(self, gadget, classified_gadgets, modified_regs, \
        gadget_type):
        typed_gadgets = []

        # Remove register aliases
        mod_regs = []

        for r in modified_regs:
            alias, _ =  self._arch_info.alias_mapper.get(r, (None, None))

            if not alias:
                mod_regs += [r]
            elif alias not in modified_regs:
                mod_regs += [r]

        modified_regs_ir = [ReilRegisterOperand(r, self._arch_regs_size[r]) for r in mod_regs]

        for candidate in classified_gadgets:
            typed_gadget = TypedGadget(gadget, gadget_type)

            if gadget_type in [GadgetType.Arithmetic, \
                GadgetType.ArithmeticLoad, GadgetType.ArithmeticStore]:
                typed_gadget.operation = candidate["op"]

            if candidate.get("op", "") != "nop":
                typed_gadget.sources = candidate["src"]
                typed_gadget.destination = candidate["dst"]

                if gadget_type == GadgetType.StoreMemory:
                    typed_gadget.modified_registers = [r for r in modified_regs_ir]
                else:
                    typed_gadget.modified_registers = [r for r in modified_regs_ir \
                        if r not in typed_gadget.destination]

            typed_gadgets += [typed_gadget]

        return typed_gadgets

    def _init_regs_random(self):
        """Initialize register with random values.
        """
        # Generate random values and make sure they are all different.
        values = set()

        while len(values) != len(self._arch_regs_parent):
            values.add(random.randint(0, 2**self._arch_info.operand_size - 1))

        values = list(values)

        # Assign random values to registers.
        regs = {}

        for idx, reg in enumerate(self._arch_regs_parent):
            regs[reg] = values[idx] & (2**self._arch_regs_size[reg] - 1)

        return regs

    def _compute_mod_regs(self, regs_init, regs_fini):
        """Compute modified registers.
        """
        assert regs_init.keys() == regs_fini.keys()

        modified_regs  = []

        for reg in regs_init:
            if regs_init[reg] != regs_fini[reg]:
                modified_regs.append(reg)

        return modified_regs

    def _invert_dictionary(self, d):
        """Invert a dictinary.
        """
        inv_dict = {}

        for k, v in d.items():
            inv_dict[v]  = inv_dict.get(v, [])
            inv_dict[v] += [k]

        return inv_dict

    def _print_memory(self, memory):
        """Print memory.
        """
        for addr, value in memory.items():
            print("    0x%08x : 0x%08x (%d)" % (addr, value, value))

    def _print_registers(self, registers):
        """Print registers.
        """
        for reg, value in registers.items():
            print("    %s : 0x%08x (%d)" % (reg, value, value))

    def _compute_full_context(self, registers):
        regs_full = {}

        reg_mapper = self._arch_info.alias_mapper

        for reg in self._arch_regs:
            base_reg_name, offset = reg_mapper.get(reg, (None, None))

            if base_reg_name:
                reg_value = registers[base_reg_name]
                reg_value = self._extract_value(reg_value, offset, self._arch_info.registers_size[reg])
            else:
                reg_value = registers[reg]

            regs_full[reg] = reg_value

        return regs_full

    def _extract_value(self, main_value, offset, size):
        return (main_value >> offset) & 2**size-1

    def _insert_value(self, main_value, value_to_insert, offset, size):
        main_value &= ~((2**size-1) << offset)
        main_value |= (value_to_insert & 2**size-1) << offset

        return main_value
