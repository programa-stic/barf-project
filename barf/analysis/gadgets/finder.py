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
This module implements a gadgets finder based on the paper "The Geometry of
Innocent Flesh on the Bone: Return-into-libc without Function Calls
(on the x86)."

Some more work is needed to make this algorithm truly architecture
agnostic.

"""
from __future__ import absolute_import

from past.builtins import xrange

import re

from barf.analysis.gadgets import RawGadget
from barf.arch import ARCH_ARM
from barf.arch import ARCH_X86
from barf.arch.disassembler import InvalidDisassemblerData
from barf.core.reil import ReilMnemonic
from barf.core.reil import ReilRegisterOperand


class GadgetFinder(object):

    """Gadget Finder.
    """

    def __init__(self, disasm, mem, ir_trans, architecture, architecture_mode):

        # A disassembler instance.
        self._disasm = disasm

        # Binary memory.
        self._mem = mem

        # A REIL translator
        self._ir_trans = ir_trans

        # Maximum disassembler lookahead bytes.
        self._max_bytes = 20

        # Maximum disassembled instructions.
        self._instrs_depth = 2

        # Binary architecture
        self._architecture = architecture
        self._architecture_mode = architecture_mode

    def find(self, start_address, end_address, byte_depth=20, instrs_depth=2):
        """Find gadgets.
        """
        self._max_bytes = byte_depth
        self._instrs_depth = instrs_depth

        if self._architecture == ARCH_X86:
            candidates = self._find_x86_candidates(start_address, end_address)
        elif self._architecture == ARCH_ARM:
            candidates = self._find_arm_candidates(start_address, end_address)
        else:
            raise Exception("Architecture not supported.")

        # Sort and return.
        return sorted(candidates, key=lambda g: g.address)

    # Auxiliary functions
    # ======================================================================== #
    def _find_x86_candidates(self, start_address, end_address):
        """Finds possible 'RET-ended' gadgets.
        """
        roots = []

        # find gadgets tail
        for addr in xrange(start_address, end_address + 1):
            # TODO: Make this 'speed improvement' architecture-agnostic
            op_codes = [
                0xc3,     # RET
                0xc2,     # RET imm16
                0xeb,     # JMP rel8
                0xe8,     # CALL rel{16,32}
                0xe9,     # JMP rel{16,32}
                0xff,     # JMP/CALL r/m{16,32,64}
            ]

            if self._mem[addr] not in op_codes:
                continue

            try:
                asm_instr = self._disasm.disassemble(
                    self._mem[addr:min(addr+16, end_address + 1)],
                    addr
                )
            except:
                asm_instr = None

            if not asm_instr:
                continue

            # restarts ir register numbering
            self._ir_trans.reset()

            try:
                ins_ir = self._ir_trans.translate(asm_instr)
            except:
                continue

            # build gadgets
            if ins_ir[-1] and (ins_ir[-1].mnemonic == ReilMnemonic.JCC and isinstance(ins_ir[-1].operands[2], ReilRegisterOperand)):

                # add for REX.W + FF /3 call instruction
                if ins_ir[-1].mnemonic == ReilMnemonic.JCC:
                    # try addr - 1
                    try:
                        asm_instr_1 = self._disasm.disassemble(
                            self._mem[addr-1:min(addr+15, end_address + 1)],
                            addr
                        )

                        self._ir_trans.reset()

                        ins_ir_1 = self._ir_trans.translate(asm_instr_1)

                        if ins_ir_1[-1].mnemonic == ReilMnemonic.JCC:
                            addr = addr - 1
                            asm_instr = asm_instr_1
                            ins_ir = ins_ir_1
                    except:
                            pass

                asm_instr.ir_instrs = ins_ir

                root = GadgetTreeNode(asm_instr)

                roots.append(root)

                self._build_from(addr, root, start_address, self._instrs_depth)

        # filter roots with no children
        roots = [r for r in roots if len(r.get_children()) > 0]

        # build gadgets
        root_gadgets = [self._build_gadgets(r) for r in roots]

        # flatten root gadgets list
        candidates = [item for l in root_gadgets for item in l]

        return candidates

    # Auxiliary functions
    # ======================================================================== #
    def _find_arm_candidates(self, start_address, end_address):
        """Finds possible 'RET-ended' gadgets.
        """
        roots = []
        gadget_tail_addr = []

        # From ROPgadget:
        free_jump_gadgets = [
            b"[\x10-\x19\x1e]{1}\xff\x2f\xe1",  # bx   reg
            b"[\x30-\x39\x3e]{1}\xff\x2f\xe1",  # blx  reg
            b"[\x00-\xff]{1}\x80\xbd\xe8",      # pop {,pc}
        ]

        # find gadgets tail
        for addr in xrange(start_address, end_address + 1):
            # TODO: Make this 'speed improvement' architecture-agnostic
            # TODO: Add thumb
            # TODO: Little-Endian

            # TODO: Evaluate performance
            gad_found = False
            for gad in free_jump_gadgets:
                if len(re.findall(gad, self._mem[addr:min(addr+4, end_address + 1)])) > 0:     # TODO: Add thumb (+2)
                    gad_found = True
                    break
            if not gad_found:
                continue

            gadget_tail_addr.append(addr)

        for addr in gadget_tail_addr:
            try:
                asm_instr = self._disasm.disassemble(
                    self._mem[addr:min(addr+4, end_address + 1)],   # TODO: Add thumb (+16)
                    addr,
                    architecture_mode=self._architecture_mode
                )
            except:
                asm_instr = None

            if not asm_instr:
                continue

            # restarts ir register numbering
            self._ir_trans.reset()

            try:
                ins_ir = self._ir_trans.translate(asm_instr)
            except:
                continue

            asm_instr.ir_instrs = ins_ir

            root = GadgetTreeNode(asm_instr)

            roots.append(root)

            self._build_from(addr, root, start_address, self._instrs_depth)

        # filter roots with no children
        roots = [r for r in roots if len(r.get_children()) > 0]

        # build gadgets
        root_gadgets = [self._build_gadgets(r) for r in roots]

        # flatten root gadgets list
        candidates = [item for l in root_gadgets for item in l]

        return candidates

    def _build_from(self, address, root, base_address, depth=2):
        """Build gadgets recursively.
        """
        if depth == 0:
            return

        end_addr = address

        for step in range(1, self._max_bytes + 1):
            start_addr = address - step

            if start_addr < 0 or start_addr < base_address:
                break

            raw_bytes = self._mem[start_addr:end_addr]

            # TODO: Improve this code.
            if self._architecture == ARCH_ARM:
                try:
                    asm_instr = self._disasm.disassemble(raw_bytes, start_addr, architecture_mode=self._architecture_mode)
                except InvalidDisassemblerData:
                    continue
            else:
                try:
                    asm_instr = self._disasm.disassemble(raw_bytes, start_addr)
                except:
                    asm_instr = None

            if not asm_instr or asm_instr.size != step:
                continue

            try:
                ir_instrs = self._ir_trans.translate(asm_instr)
            except:
                continue

            if self._is_valid_ins(ir_instrs):
                asm_instr.ir_instrs = ir_instrs

                child = GadgetTreeNode(asm_instr)

                root.add_child(child)

                self._build_from(address - step, child, base_address, depth - 1)

    def _build_gadgets(self, gadget_tree_root):
        """Return a gadgets list.
        """
        node_list = self._build_gadgets_rec(gadget_tree_root)

        return [RawGadget(n) for n in node_list]

        # TODO: Update x86 gadgets tests before uncommenting the following.
        # (this change breaks x86 gadgets tests.)
        # gadgets = []

        # for node in node_list:
        #     for i in xrange(len(node)):
        #         gadgets.append(RawGadget(node[i:]))

        # return gadgets

    def _build_gadgets_rec(self, gadget_tree_root):
        """Build a gadgets from a gadgets tree.
        """
        root = gadget_tree_root.get_root()
        children = gadget_tree_root.get_children()

        node_list = []

        root_gadget_ins = root

        if not children:
            node_list += [[root_gadget_ins]]
        else:
            for child in children:
                node_list_rec = self._build_gadgets_rec(child)

                node_list += [n + [root_gadget_ins] for n in node_list_rec]

        return node_list

    def _is_valid_ins(self, ins_ir):
        """Check for instruction validity as a gadgets.
        """
        invalid_instrs = [
            ReilMnemonic.JCC,
            ReilMnemonic.UNDEF,
            ReilMnemonic.UNKN,
        ]

        return not any([i.mnemonic in invalid_instrs for i in ins_ir])


class GadgetTreeNode(object):

    """Tree Data Structure.
    """

    def __init__(self, root):
        self._root = root
        self._children = []

    def get_root(self):
        """Get node root.
        """
        return self._root

    def add_child(self, child):
        """Add a child to the node.
        """
        self._children.append(child)

    def get_children(self):
        """Get node's children.
        """
        return self._children
