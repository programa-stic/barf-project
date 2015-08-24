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

import bisect
import networkx

from Queue import Queue

from pydot import Dot
from pydot import Edge
from pydot import Node

from barf.core.reil import DualInstruction
from barf.core.reil import ReilMnemonic
from barf.core.reil import ReilImmediateOperand

# CFG recovery mode
BARF_DISASM_LINEAR = 0       # Linear Sweep
BARF_DISASM_RECURSIVE = 1    # Recursive Descent

class BasicBlock(object):

    """Basic block representation.
    """

    def __init__(self):

        # List of instruction within the basic block. Each instruction
        # is a 'dual' instruction, e.i. it pairs an assembler
        # instruction with its REIL translation.
        self._instrs = []

        # Start address of the basic block.
        self._address = None

        # Taken branch address. If a basic block ends in a conditional
        # instruction, this field has the address of the taken branch
        # (condition equals True)
        self._taken_branch = None

        # Similar to taken branch but it holds the target address of
        # the jump when the condition is false.
        self._not_taken_branch = None

        # If a basic block ends in a direct jump or in an instruction
        # different from a conditional jump, this fields holds the
        # address of the jump or next instruction.
        self._direct_branch = None

    @property
    def instrs(self):
        """Get basic block instructions.
        """
        return self._instrs

    @property
    def address(self):
        """Get basic block start address.
        """
        if self._instrs == []:
            return None

        return self._instrs[0].address

    @property
    def start_address(self):
        """Get basic block start address.
        """
        if self._instrs is []:
            return None

        return self._instrs[0].address

    @property
    def end_address(self):
        """Get basic block end address.
        """
        if self._instrs is []:
            return None

        return self._instrs[-1].address + self._instrs[-1].asm_instr.size - 1

    @property
    def size(self):
        """Get basic block size.
        """
        if self._instrs is []:
            return None

        return sum([dinstr.asm_instr.size for dinstr in self._instrs])

    @property
    def taken_branch(self):
        """Get basic block taken branch.
        """
        return self._taken_branch

    @taken_branch.setter
    def taken_branch(self, value):
        """Set basic block taken branch.
        """
        self._taken_branch = value

    @property
    def not_taken_branch(self):
        """Get basic block not taken branch.
        """
        return self._not_taken_branch

    @not_taken_branch.setter
    def not_taken_branch(self, value):
        """Set basic block not taken branch.
        """
        self._not_taken_branch = value

    @property
    def direct_branch(self):
        """Get basic block direct branch.
        """
        return self._direct_branch

    @direct_branch.setter
    def direct_branch(self, value):
        """Set basic block direct branch.
        """
        self._direct_branch = value

    @property
    def branches(self):
        """Get basic block branches.
        """
        branches = []

        if self._taken_branch:
            branches += [(self._taken_branch, 'taken')]

        if self._not_taken_branch:
            branches += [(self._not_taken_branch, 'not-taken')]

        if self._direct_branch:
            branches += [(self._direct_branch, 'direct')]

        return branches

    def contains(self, address):
        """Check if an address is within the range of a basic block.
        """
        return self.address <= address and address <= self.end_address

    def empty(self):
        """Check if a basic block is empty.
        """
        return len(self._instrs) == 0

    def __str__(self):
        lines = ["Basic Block @ 0x%08x" % (self.address if self.address else 0)]

        for instr in self._instrs:
            lines += ["    %s ; %s" % (str(instr.ir_instrs[0]).ljust(25), str(instr.asm_instr))]

            for ir_instr in instr.ir_instrs[1:]:
                lines += ["    %s" % str(ir_instr)]

        return "\n".join(lines)

    def __eq__(self, other):
        # Assumes that you are comparing basic block from the same binary
        return self.address == other.address and self.end_address == other.end_address

    def __ne__(self, other):
        return not self.__eq__(other)

    def __iter__(self):
        for instr in self._instrs:
            yield instr

    def __len__(self):
        return len(self._instrs)


class BasicBlockGraph(object):

    """Basic block graph representation.
    """

    def __init__(self, basic_blocks):

        # List of basic blocks.
        self._basic_blocks = basic_blocks

        # Basic block accessed by address
        self._bb_by_addr = dict([(bb.address, bb) for bb in basic_blocks])

        # Basic block graph
        self._graph = self._build_graph()

    def all_simple_bb_paths(self, start_address, end_address):
        """Return a list of path between start and end address.
        """
        bb_start = self._find_basic_block(start_address)
        bb_end = self._find_basic_block(end_address)

        paths = networkx.all_simple_paths(self._graph, \
            source=bb_start.address, target=bb_end.address)

        return (map(lambda addr: self._bb_by_addr[addr], path) for path in paths)

    def save(self, filename, print_ir=False, format='dot'):
        """Save basic block graph into a file.
        """
        node_format = {
            'shape' : 'Mrecord',
            'rankdir' : 'LR',
            'fontname' : 'monospace',
            'fontsize' : '9.0'
        }

        edge_format = {
            'fontname' : 'monospace',
            'fontsize' : '8.0'
        }

        edge_colors = {
            'taken' : 'green',
            'not-taken' : 'red',
            'direct' : 'blue'
        }

        try:
            # for each conneted component
            for idx, gr in enumerate(networkx.connected_component_subgraphs(self._graph.to_undirected())):
                graph = Dot(graph_type="digraph", rankdir="TB")

                # add nodes
                nodes = {}
                for bb_addr in gr.node.keys():
                    # Skip jmp/jcc to sub routines.
                    if not bb_addr in self._bb_by_addr:
                        continue

                    dump = self._dump_bb(self._bb_by_addr[bb_addr], print_ir)

                    # html-encode colon character
                    dump = dump.replace("!", "&#33;")
                    dump = dump.replace("#", "&#35;")
                    dump = dump.replace(":", "&#58;")
                    dump = dump.replace("{", "&#123;")
                    dump = dump.replace("}", "&#125;")

                    label = "{<f0> 0x%08x | %s}" % (bb_addr, dump)

                    nodes[bb_addr] = Node(bb_addr, label=label, **node_format)

                    graph.add_node(nodes[bb_addr])

                # add edges
                for bb_src_addr in gr.node.keys():
                    # Skip jmp/jcc to sub routines.
                    if not bb_src_addr in self._bb_by_addr:
                        continue

                    for bb_dst_addr, branch_type in self._bb_by_addr[bb_src_addr].branches:
                        # Skip jmp/jcc to sub routines.
                        if not bb_dst_addr in self._bb_by_addr:
                            continue

                        graph.add_edge(Edge(nodes[bb_src_addr],
                            nodes[bb_dst_addr], label=branch_type, \
                            color=edge_colors[branch_type], **edge_format))

                graph.write("%s_%03d.%s" % (filename, idx, format), format=format)
        except Exception as err:
            import traceback
            import sys
            print("[E] Error loading BARF (%s:%d) : '%s'" %
                (__name__, sys.exc_traceback.tb_lineno, str(err)))
            print("")
            print(traceback.format_exc())

    # Auxiliary functions
    # ======================================================================== #
    def _build_graph(self):
        graph = networkx.DiGraph()

        # add nodes
        for bb_addr in self._bb_by_addr.keys():
            graph.add_node(bb_addr, address=bb_addr)

        # add edges
        for bb_src_addr in self._bb_by_addr.keys():
            for bb_dst_addr, branch_type in self._bb_by_addr[bb_src_addr].branches:
                graph.add_edge(bb_src_addr, bb_dst_addr, branch_type=branch_type)

        return graph

    def _find_basic_block(self, address):
        bb_rv = None

        for bb in self._basic_blocks:
            if address >= bb.address and address <= bb.end_address:
                bb_rv = bb
                break

        return bb_rv

    def _dump_bb(self, basic_block, print_ir=False):
        lines = []

        for instr in basic_block.instrs:
            lines += ["0x%08x [%02d] " % (instr.address, instr.asm_instr.size) + str(instr.asm_instr) + "\\l"]

            if print_ir:
                for ir_instr in instr.ir_instrs:
                    lines += ["              " + str(ir_instr) + "\\l"]

        return "".join(lines)

    @property
    def basic_blocks(self):
        return self._basic_blocks

    def get_basic_block(self, address):
        return self._bb_by_addr[address]


class BasicBlockBuilder(object):

    """Basic block builder.
    """

    def __init__(self, disassembler, memory, translator):

        # An instance of a disassembler.
        self._disasm = disassembler

        # And instance of a REIL translator.
        self._ir_trans = translator

        # Maximun number of bytes that gets from memory to disassemble.
        self._lookahead_max = 16

        # Memory of the program being analyze.
        self._mem = memory

    def build(self, start_address, end_address, symbols=None):
        """Return the list of basic blocks.

        Linear Sweep Disassembly.

        @param start_address: Address of the first byte to start disassembling
        basic blocks.
        @param end_address: Address of the last byte (inclusive) to finish
        disassembling basic blocks.

        """
        if not symbols:
            symbols = {}

        # 1.
        # bbs = self._find_candidate_bbs(start_address, end_address, symbols=symbols)
        # bbs = self._refine_bbs(bbs, symbols)

        # 2.
        bbs = self._find_candidate_bbs(start_address, end_address, symbols=symbols)
        bbs = self._refine_bbs(bbs, symbols)

        # Collect subroutine address
        addrs = []
        for bb in bbs:
            for addr, _ in bb.branches:
                if not (start_address <= addr and addr <= end_address):
                    addrs.append(addr)
        addrs = sorted(list(set(addrs)))

        # Process subrutines
        bbs_new = []
        for addr in addrs:
            bbs_new += self._find_candidate_bbs(addr, end_address, symbols=symbols)

        bbs = self._refine_bbs(bbs_new + bbs, symbols)

        return bbs

    def _find_candidate_bbs(self, start_address, end_address, mode=BARF_DISASM_RECURSIVE, symbols=None):
        if not symbols:
            symbols = {}

        bbs = []

        addrs_to_process = Queue()
        addrs_processed = set()

        addrs_to_process.put(start_address)

        while not addrs_to_process.empty():
            addr_curr = addrs_to_process.get()

            # Skip current address if:
            #   a. it has already been processed or
            #   b. it is not within range ([start_address, end_address]) or
            if  addr_curr in addrs_processed or \
                not (addr_curr >= start_address and addr_curr <= end_address):
                continue

            bb = self._disassemble_bb(addr_curr, end_address + 0x1, symbols)

            if bb.empty():
                continue

            # Add new basic block to the list.
            bbs += [bb]

            # Add current address to the list of processed addresses.
            addrs_processed.add(addr_curr)

            # Linear sweep mode: add next address to process queue.
            if mode == BARF_DISASM_LINEAR:
                next_addr = bb.address + bb.size

                if  not self._bb_ends_in_direct_jmp(bb) and \
                    not self._bb_ends_in_return(bb) and \
                    not next_addr in addrs_processed:
                    addrs_to_process.put(next_addr)

            # Recursive descent mode: add branches to process queue.
            if mode == BARF_DISASM_RECURSIVE:
                for addr, _ in bb.branches:
                    if not addr in addrs_processed:
                        addrs_to_process.put(addr)

        return bbs

    def _bb_ends_in_direct_jmp(self, bb):
        last_instr = bb.instrs[-1].ir_instrs[-1]

        return  last_instr.mnemonic == ReilMnemonic.JCC and \
                isinstance(last_instr.operands[0], ReilImmediateOperand) and \
                last_instr.operands[0].immediate == 0x1

    def _bb_ends_in_return(self, bb):
        last_instr = bb.instrs[-1].ir_instrs[-1]

        return last_instr.mnemonic == ReilMnemonic.RET

    def _refine_bbs(self, bbs, symbols):
        bbs.sort(key=lambda x: x.address)
        bbs_addrs = [bb.address for bb in bbs]

        bbs_new = []

        for bb1 in bbs:
            bb_divided = False

            lower = bisect.bisect_left(bbs_addrs, bb1.start_address)
            upper = bisect.bisect_right(bbs_addrs, bb1.end_address)

            for bb2 in bbs[lower:upper]:
                if bb1.contains(bb2.address) and bb1 != bb2:
                    bb_lower, bb_upper = self._split_bb(bb1, bb2.address, symbols)

                    if not bb_upper.empty() and bb_upper not in bbs_new:
                        bbs_new += [bb_upper]

                    bb1 = bb_lower

                    bb_divided = True

                    break

            if not bb_divided:
                if not bb1.empty() and not bb1 in bbs_new:
                    bbs_new += [bb1]

        return bbs_new

    def _split_bb(self, bb, address, symbols):
        bb_upper_half = self._disassemble_bb(bb.start_address, address, symbols)
        bb_lower_half = self._disassemble_bb(address, bb.end_address, symbols)

        bb_upper_half.direct_branch = address

        return bb_lower_half, bb_upper_half

    def _disassemble_bb(self, start_address, end_address, symbols):
        bb = BasicBlock()
        addr = start_address
        taken, not_taken, direct = None, None, None

        while addr < end_address:
            try:
                start, end = addr, min(addr + self._lookahead_max, end_address)
                data_chunk = self._mem[start:end]
            except Exception:
                # TODO: Log error.
                break

            asm = self._disasm.disassemble(data_chunk, addr)

            if not asm:
                break

            ir = self._ir_trans.translate(asm)

            bb.instrs.append(DualInstruction(addr, asm, ir))

            # TODO: Process instructions without resorting to
            # asm.mnemonic or asm.prefix.

            # If it is a RET instruction, break.
            if ir[-1].mnemonic == ReilMnemonic.RET:
                break

            # If it is a x86 hlt instruction, break.
            if asm.mnemonic == "hlt":
                break

            # If callee does not return, break.
            if  ir[-1].mnemonic == ReilMnemonic.JCC and \
                asm.mnemonic == "call" and \
                isinstance(ir[-1].operands[2], ReilImmediateOperand) and \
                (ir[-1].operands[2].immediate >> 0x8) in symbols and \
                not symbols[ir[-1].operands[2].immediate >> 0x8][2]:
                break

            # If it is a JCC instruction, process it and break.
            if  ir[-1].mnemonic == ReilMnemonic.JCC and \
                not asm.mnemonic == "call" and \
                not asm.prefix in ["rep", "repe", "repne", "repz"]:
                taken, not_taken, direct = self._extract_branches(asm, ir)
                break

            # Update instruction pointer and iterate.
            addr += asm.size

        bb.taken_branch = taken
        bb.not_taken_branch = not_taken
        bb.direct_branch = direct

        return bb

    def _resolve_branch_address(self, branch_instr, instrs):
        target = branch_instr.operands[2]

        if isinstance(target, ReilImmediateOperand):
            # branch address is an immediate
            # Transform Reil address back to source arch address
            return target.immediate >> 8
        else:
            # try to resolve branch address
            for instr in instrs[::-1]:
                if instr.mnemonic == ReilMnemonic.STR and \
                    isinstance(instr.operands[0], ReilImmediateOperand) and \
                    instr.operands[2] == target:

                    # Transform Reil address back to source arch address
                    return instr.operands[0].immediate >> 8

    def _extract_branches(self, asm, ir):
        taken_branch, not_taken_branch, direct_branch = None, None, None

        instr_last = ir[-1]

        if instr_last.mnemonic == ReilMnemonic.JCC:
            cond = instr_last.operands[0]

            branch_addr = self._resolve_branch_address(instr_last, ir)

            # Set branch address according to its type
            if isinstance(cond, ReilImmediateOperand):
                if cond.immediate == 0x0:
                    not_taken_branch = branch_addr

                if cond.immediate == 0x1:
                    if asm.mnemonic == 'call':
                        direct_branch = asm.address + asm.size

                    if asm.mnemonic != 'call':
                        direct_branch = branch_addr
            else:
                taken_branch = branch_addr
                not_taken_branch = asm.address + asm.size

        return taken_branch, not_taken_branch, direct_branch
