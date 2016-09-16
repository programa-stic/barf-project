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
import logging
import networkx

from Queue import Queue

from pydot import Dot
from pydot import Edge
from pydot import Node

from barf.arch.arm.armbase import ArmArchitectureInformation
from barf.arch.x86.x86base import X86ArchitectureInformation
from barf.core.bi import InvalidAddressError
from barf.core.disassembler import DisassemblerError
from barf.core.reil import DualInstruction
from barf.core.reil import ReilImmediateOperand
from barf.core.reil import ReilMnemonic

from pygments import highlight
from pygments.formatters import HtmlFormatter
from pygments.lexers.asm import NasmLexer


logger = logging.getLogger(__name__)


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

        self._label = None

        self._is_entry = False

        self._is_exit = False

    @property
    def label(self):
        """Get basic block label.
        """
        return self._label

    @label.setter
    def label(self, value):
        """Set basic block label.
        """
        self._label = value

    @property
    def is_entry(self):
        """Get basic block is_entry.
        """
        return self._is_entry

    @is_entry.setter
    def is_entry(self, value):
        """Set basic block is_entry.
        """
        self._is_entry = value

    @property
    def is_exit(self):
        """Get basic block is_exit.
        """
        return self._is_exit

    @is_exit.setter
    def is_exit(self, value):
        """Set basic block is_exit.
        """
        self._is_exit = value

    @property
    def instrs(self):
        """Get basic block instructions.
        """
        return self._instrs

    @property
    def address(self):
        """Get basic block start address.
        """
        if len(self._instrs) == 0:
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
        return self.address <= address <= self.end_address

    def empty(self):
        """Check if a basic block is empty.
        """
        return len(self._instrs) == 0

    def __str__(self):
        lines = ["Basic Block @ {:#x}".format(self.address if self.address else 0)]

        asm_fmt = "{:#x}    {}"
        reil_fmt = "{:#x}:{:02d} {}"

        for dinstr in self._instrs:
            asm_instr = dinstr.asm_instr

            lines += [asm_fmt.format(asm_instr.address, asm_instr)]

            for reil_instr in dinstr.ir_instrs:
                lines += [reil_fmt.format(reil_instr.address >> 0x8, reil_instr.address & 0xff, reil_instr)]

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

    def __getstate__(self):
        state = {}
        state['_instrs'] = self._instrs
        state['_address'] = self._address
        state['_taken_branch'] = self._taken_branch
        state['_not_taken_branch'] = self._not_taken_branch
        state['_direct_branch'] = self._direct_branch

        return state

    def __setstate__(self, state):
        self._instrs = state['_instrs']
        self._address = state['_address']
        self._taken_branch = state['_taken_branch']
        self._not_taken_branch = state['_not_taken_branch']
        self._direct_branch = state['_direct_branch']


class ControlFlowGraph(object):

    """Basic block graph representation.
    """

    def __init__(self, basic_blocks, name=None):

        # List of basic blocks sorted by address.
        self._basic_blocks = sorted(basic_blocks, key=lambda bb: bb.address)

        # Basic block accessed by address
        self._bb_by_addr = dict([(bb.address, bb) for bb in basic_blocks])

        # Basic block graph
        self._graph = self._build_graph()

        # List of entry basic blocks
        self._entry_blocks = [bb.address for bb in basic_blocks
                                if len(self._graph.in_edges(bb.address)) == 0]

        # List of exit basic blocks
        self._exit_blocks = [bb.address for bb in basic_blocks
                                if len(self._graph.out_edges(bb.address)) == 0]

        self._name = name

    @property
    def name(self):
        return self._name

    @name.setter
    def name(self, value):
        self._name = value

    @property
    def basic_blocks(self):
        return self._basic_blocks

    def get_basic_block(self, address):
        return self._bb_by_addr[address]

    @property
    def exit_basic_blocks(self):
        for bb_addr in self._exit_blocks:
            yield self._bb_by_addr[bb_addr]

    @property
    def entry_basic_blocks(self):
        for bb_addr in self._entry_blocks:
            yield self._bb_by_addr[bb_addr]

    @property
    def start_address(self):
        # TODO: Test.
        starts = [self._bb_by_addr[bb_addr].start_address for bb_addr in self._bb_by_addr.keys()]

        return min(starts)

    @property
    def end_address(self):
        # TODO: Test.
        ends = [self._bb_by_addr[bb_addr].end_address for bb_addr in self._bb_by_addr.keys()]

        return max(ends)

    def all_simple_bb_paths(self, start_address, end_address):
        """Return a list of path between start and end address.
        """
        bb_start = self._find_basic_block(start_address)
        bb_end = self._find_basic_block(end_address)

        paths = networkx.all_simple_paths(self._graph, source=bb_start.address, target=bb_end.address)

        return (map(lambda addr: self._bb_by_addr[addr], path) for path in paths)

    def save(self, filename, print_ir=False, format='dot'):
        # renderer = CFGSimpleRenderer()
        renderer = CFGSimpleRendererEx()

        renderer.save(self, filename, print_ir, format)

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
            if bb.address <= address <= bb.end_address:
                bb_rv = bb
                break

        return bb_rv

    def __getstate__(self):
        state = {}

        state['_basic_blocks'] = self._basic_blocks

        return state

    def __setstate__(self, state):
        basic_blocks = state['_basic_blocks']

        # List of basic blocks sorted by address.
        self._basic_blocks = sorted(basic_blocks, key=lambda bb: bb.address)

        # Basic block accessed by address
        self._bb_by_addr = dict([(bb.address, bb) for bb in basic_blocks])

        # Basic block graph
        self._graph = self._build_graph()

        # List of entry basic blocks
        self._entry_blocks = [bb.address for bb in basic_blocks
                                if len(self._graph.in_edges(bb.address)) == 0]

        # List of exit basic blocks
        self._exit_blocks = [bb.address for bb in basic_blocks
                                if len(self._graph.out_edges(bb.address)) == 0]


class CFGRecover(object):

    def __init__(self, disassembler, memory, translator, arch_info):

        # An instance of a disassembler.
        self._disasm = disassembler

        # An instance of a REIL translator.
        self._translator = translator

        # Memory of the program being analyze.
        self._memory = memory

        # Architecture information of the binary.
        self._arch_info = arch_info

    def build(self, start_address, end_address, symbols=None):
        """Return the list of basic blocks.

        @param start_address: Address of the first byte to start disassembling
        basic blocks.
        @param end_address: Address of the last byte (inclusive) to finish
        disassembling basic blocks.

        """
        symbols = {} if not symbols else symbols

        # Find candidates for basic blocks.
        bbs = self._recover_bbs(start_address, end_address, symbols)
        bbs = self._split_bbs(bbs, symbols)

        # Extract call targets for further processing.
        call_targets = []
        for bb in bbs:
            for target in self._extract_call_targets(bb):
                if isinstance(target, ReilImmediateOperand):
                    call_targets.append(target.immediate >> 8)

        return bbs, call_targets

    def _recover_bbs(self, start, end, symbols):
        raise NotImplementedError()

    def _split_bbs(self, bbs, symbols):
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

    def _is_function_nonreturn(self, address, symbols):
        return address in symbols and not symbols[address][2]

    def _disassemble_bb(self, start, end, symbols):
        bb = BasicBlock()
        addr = start
        taken, not_taken, direct = None, None, None

        while addr < end:
            try:
                data_end = addr + self._arch_info.max_instruction_size
                data_chunk = self._memory[addr:min(data_end, end)]
                asm = self._disasm.disassemble(data_chunk, addr)
            except (DisassemblerError, InvalidAddressError):
                logger.warn("Error while disassembling @ {:#x}".format(addr))
                break

            ir = self._translator.translate(asm)

            bb.instrs.append(DualInstruction(addr, asm, ir))

            # If it is a RET or HALT instruction, break.
            if self._arch_info.instr_is_ret(asm) or self._arch_info.instr_is_halt(asm):
                bb.is_exit = True
                break

            # If it is a CALL instruction and the callee does not return, break.
            if self._arch_info.instr_is_call(asm):
                target_oprnd = ir[-1].operands[2]

                if isinstance(target_oprnd, ReilImmediateOperand):
                    target_addr = target_oprnd.immediate >> 0x8

                    if self._is_function_nonreturn(target_addr, symbols):
                        bb.is_exit = True
                        break

            # If it is a BRANCH instruction, extract targets and break.
            if self._arch_info.instr_is_branch(asm):
                taken, not_taken, direct = self._extract_branch_targets(asm, ir)

                # Jump to a function?
                if direct in symbols:
                    bb.is_exit = True

                break

            # Update instruction pointer and iterate.
            addr += asm.size

        bb.taken_branch = taken
        bb.not_taken_branch = not_taken
        bb.direct_branch = direct

        return bb

    def _resolve_branch_target(self, branch_instr, instrs):
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

    def _extract_branch_targets(self, asm, ir):
        taken_branch, not_taken_branch, direct_branch = None, None, None

        instr_last = ir[-1]

        if instr_last.mnemonic == ReilMnemonic.JCC:
            cond = instr_last.operands[0]

            branch_addr = self._resolve_branch_target(instr_last, ir)

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

    def _extract_call_targets(self, bb):
        targets = []

        for dinstr in bb:
            if dinstr.asm_instr.mnemonic in ["call", "bl"]:
                assert dinstr.ir_instrs[-1].mnemonic == ReilMnemonic.JCC

                targets.append(dinstr.ir_instrs[-1].operands[2])

        return targets


class RecursiveDescent(CFGRecover):

    def __init__(self, disassembler, memory, translator, arch_info):
        super(RecursiveDescent, self).__init__(disassembler, memory, translator, arch_info)

    def _recover_bbs(self, start, end, symbols):
        bbs = []
        addrs_to_process = Queue()
        addrs_processed = set()

        addrs_to_process.put(start)

        while not addrs_to_process.empty():
            addr = addrs_to_process.get()

            # Skip current address if:
            #   a. it has already been processed or
            #   b. it is not within range ([start, end])
            if addr in addrs_processed or not start <= addr <= end:
                continue

            bb = self._disassemble_bb(addr, end + 0x1, symbols)

            if bb.empty():
                continue

            if bb.address == start:
                bb.is_entry = True

            # Add new basic block to the list.
            bbs.append(bb)

            # Add current address to the list of processed addresses.
            addrs_processed.add(addr)

            # Recursive descent mode: add branches to process queue.
            for addr, _ in bb.branches:
                if not addr in addrs_processed:
                    # Do not process other functions.
                    if not addr in symbols:
                        addrs_to_process.put(addr)

        return bbs


class LinearSweep(CFGRecover):

    def __init__(self, disassembler, memory, translator, arch_info):
        super(LinearSweep, self).__init__(disassembler, memory, translator, arch_info)

    def _recover_bbs(self, start, end, symbols):
        bbs = []
        addrs_to_process = Queue()
        addrs_processed = set()

        addrs_to_process.put(start)

        while not addrs_to_process.empty():
            addr = addrs_to_process.get()

            # Skip current address if:
            #   a. it has already been processed or
            #   b. it is not within range ([start, end])
            if addr in addrs_processed or not start <= addr <= end:
                continue

            bb = self._disassemble_bb(addr, end + 0x1, symbols)

            if bb.empty():
                continue

            if bb.address == start:
                bb.is_entry = True

            # Add new basic block to the list.
            bbs.append(bb)

            # Add current address to the list of processed addresses.
            addrs_processed.add(addr)

            # Linear sweep mode: add next address to process queue.
            addr_next = bb.address + bb.size

            if not self._bb_ends_in_direct_jmp(bb) and \
               not self._bb_ends_in_return(bb) and \
               not addr_next in addrs_processed:
                addrs_to_process.put(addr_next)

        return bbs

    def _bb_ends_in_direct_jmp(self, bb):
        last_instr = bb.instrs[-1].ir_instrs[-1]

        return last_instr.mnemonic == ReilMnemonic.JCC and \
            isinstance(last_instr.operands[0], ReilImmediateOperand) and \
            last_instr.operands[0].immediate == 0x1

    def _bb_ends_in_return(self, bb):
        # TODO: Process instructions without resorting to
        # asm.mnemonic or asm.prefix.
        last_instr = bb.instrs[-1].asm_instr

        return last_instr.mnemonic == "ret"


class CFGRecoverer(object):

    def __init__(self, strategy):
        self.strategy = strategy

    def build(self, start, end=None, symbols=None):
        return self.strategy.build(start, end, symbols)


class CFGRenderer(object):

    def save(self):
        raise NotImplementedError()

    def _get_bb_max_instr_width(self, basic_block):
        """Get maximum instruction mnemonic width
        """
        asm_mnemonic_max_width = 0

        for dinstr in basic_block:
            if len(dinstr.asm_instr.mnemonic) > asm_mnemonic_max_width:
                asm_mnemonic_max_width = len(dinstr.asm_instr.mnemonic)

        return asm_mnemonic_max_width

    def _get_bb_type(self, bb):
        if bb.is_entry:
            bb_type = "entry"
        elif bb.is_exit:
            bb_type = "exit"
        else:
            bb_type = "other"

        return bb_type


class CFGSimpleRenderer(CFGRenderer):

    fontname = 'monospace'

    graph_format = {
        'graph_type' : 'digraph',
        'rankdir'    : 'TB',
    }

    node_format = {
        'shape'    : 'Mrecord',
        'rankdir'  : 'LR',
        'fontname' : fontname,
        'fontsize' : '9.0',
    }

    node_color = {
        'entry' : 'black',
        'exit'  : 'black',
        'other' : 'black',
    }

    edge_format = {
        'fontname' : 'monospace',
        'fontsize' : '8.0',
    }

    edge_color = {
        'taken'     : 'green',
        'not-taken' : 'red',
        'direct'    : 'blue',
    }

    # Templates.
    bb_tpl = "{{<f0> {label} | {assembly}}}"

    asm_tpl = "{address:08x} [{size:02d}] {assembly}\\l"

    reil_tpl = " {index:02x} {assembly}\\l"

    def save(self, cfg, filename, print_ir=False, format='dot'):
        """Save basic block graph into a file.
        """
        try:
            dot_graph = Dot(**self.graph_format)

            # Add nodes.
            nodes = {}
            for bb in cfg.basic_blocks:
                nodes[bb.address] = self._create_node(bb, cfg.name, print_ir)

                dot_graph.add_node(nodes[bb.address])

            # Add edges.
            for bb_src in cfg.basic_blocks:
                for bb_dst_addr, branch_type in bb_src.branches:
                    edge = self._create_edge(nodes[bb_src.address], nodes[bb_dst_addr], branch_type)

                    dot_graph.add_edge(edge)

            # Save graph.
            dot_graph.write("{}.{}".format(filename, format), format=format)
        except Exception:
            logger.error("Failed to save basic block graph: %s (%s)", filename, format, exc_info=True)

    def _create_node(self, bb, name, print_ir):
        bb_dump = self._render_bb(bb, name, print_ir)
        bb_type = self._get_bb_type(bb)

        return Node(bb.address, label=bb_dump, color=self.node_color[bb_type], **self.node_format)

    def _create_edge(self, src, dst, branch_type):
        return Edge(src, dst, color=self.edge_color[branch_type], **self.edge_format)

    def _render_asm(self, instr, mnemonic_width, fill_char=""):
        oprnds_str = ", ".join([str(oprnd) for oprnd in instr.operands])

        asm_str  = instr.prefix + " " if instr.prefix else ""
        asm_str += instr.mnemonic + fill_char * (mnemonic_width - len(instr.mnemonic))
        asm_str += " " + oprnds_str if oprnds_str else ""

        # html-encode colon character
        html_entities = {
            "!" : "&#33;",
            "#" : "&#35;",
            ":" : "&#58;",
            "{" : "&#123;",
            "}" : "&#125;",
        }

        for char, encoding in html_entities.items():
            asm_str = asm_str.replace(char, encoding)

        return self.asm_tpl.format(address=instr.address, size=instr.size, assembly=asm_str)

    def _render_reil(self, instr):
        return self.reil_tpl.format(index=instr.address & 0xff, assembly=instr)

    def _render_bb(self, basic_block, name, print_ir):
        lines = []

        asm_mnemonic_max_width = self._get_bb_max_instr_width(basic_block)

        for dinstr in basic_block:
            asm_str = self._render_asm(dinstr.asm_instr, asm_mnemonic_max_width + 1, fill_char="\\ ")
            lines.append(asm_str)

            if print_ir:
                for ir_instr in dinstr.ir_instrs:
                    reil_str = self._render_reil(ir_instr)
                    lines.append(reil_str)

        bb_dump = "".join(lines)

        # Set node label
        bb_addr = basic_block.address

        if basic_block.is_entry:
            bb_label = "{} @ {:x}".format(name, bb_addr)
        else:
            bb_label = "loc_{:x}".format(bb_addr)

        return self.bb_tpl.format(label=bb_label, assembly=bb_dump)


class CFGSimpleRendererEx(CFGRenderer):

    fontname = 'Ubuntu Mono'
    # fontname = 'DejaVu Sans Mono'
    # fontname = 'DejaVu Sans Condensed'
    # fontname = 'DejaVu Sans Light'
    # fontname = 'Liberation Mono'
    # fontname = 'DejaVu Serif Condensed'
    # fontname = 'Ubuntu Condensed'

    graph_format = {
        'graph_type' : 'digraph',
        'nodesep'    : 1.2,
        'rankdir'    : 'TB',
        # 'splines'    : 'ortho', # NOTE This option brings up performance issues.
    }

    node_format = {
        'fontname'  : fontname,
        'fontsize'  : 9.0,
        'penwidth'  : 0.5,
        'rankdir'   : 'LR',
        'shape'     : 'plaintext',
    }

    edge_format = {
        'arrowhead' : 'vee',
        'arrowsize' : 0.6,
        'fontname'  : fontname,
        'fontsize'  : 8.0,
        'penwidth'  : 0.5,
    }

    node_color = {
        'entry' : 'orange',
        'exit'  : 'gray',
        'other' : 'black',
    }

    edge_color = {
        'direct'    : 'blue',
        'not-taken' : 'red',
        'taken'     : 'darkgreen',
    }

    # Templates.
    bb_tpl  = '<'
    bb_tpl += '<table border="1.0" cellborder="0" cellspacing="1" cellpadding="0" valign="middle">'
    bb_tpl += '  <tr><td align="center" cellpadding="1" port="enter"></td></tr>'
    bb_tpl += '  <tr><td align="left" cellspacing="1">{label}</td></tr>'
    bb_tpl += '  {assembly}'
    bb_tpl += '  <tr><td align="center" cellpadding="1" port="exit" ></td></tr>'
    bb_tpl += '</table>'
    bb_tpl += '>'

    asm_tpl = "<tr><td align='left'>{address:08x} [{size:02d}] {assembly} </td></tr>"

    reil_tpl = "<tr><td align='left'>              {assembly} </td></tr>"

    def save(self, cfg, filename, print_ir=False, format='dot'):
        """Save basic block graph into a file.
        """
        try:
            dot_graph = Dot(**self.graph_format)

            # Add nodes.
            nodes = {}
            for bb in cfg.basic_blocks:
                nodes[bb.address] = self._create_node(bb, cfg.name, print_ir)

                dot_graph.add_node(nodes[bb.address])

            # Add edges.
            for bb_src in cfg.basic_blocks:
                for bb_dst_addr, branch_type in bb_src.branches:
                    edge = self._create_edge(nodes[bb_src.address], nodes[bb_dst_addr], branch_type)

                    dot_graph.add_edge(edge)

            # Save graph.
            dot_graph.write("{}.{}".format(filename, format), format=format)
        except Exception:
            logger.error("Failed to save basic block graph: %s (%s)", filename, format, exc_info=True)

    def _create_node(self, bb, name, print_ir):
        bb_dump = self._render_bb(bb, name, print_ir)
        bb_type = self._get_bb_type(bb)

        return Node(bb.address, label=bb_dump, color=self.node_color[bb_type], **self.node_format)

    def _create_edge(self, src, dst, branch_type):
        return Edge(src, dst, color=self.edge_color[branch_type], **self.edge_format)

    def _render_asm(self, instr, mnemonic_width, fill_char=""):
        formatter = HtmlFormatter()
        formatter.noclasses = True
        formatter.nowrap = True

        oprnds_str = ", ".join([str(oprnd) for oprnd in instr.operands])

        asm_str  = instr.prefix + " " if instr.prefix else ""
        asm_str += instr.mnemonic + fill_char * (mnemonic_width - len(instr.mnemonic))
        asm_str += " " + oprnds_str if oprnds_str else ""

        asm_str = highlight(asm_str, NasmLexer(), formatter)
        asm_str = asm_str.replace("span", "font")
        asm_str = asm_str.replace('style="color: ', 'color="')

        return self.asm_tpl.format(address=instr.address, size=instr.size, assembly=asm_str)

    def _render_reil(self, instr):
        return self.reil_tpl.format(assembly=instr)

    def _render_bb(self, basic_block, name, print_ir):
        lines = []

        asm_mnemonic_max_width = self._get_bb_max_instr_width(basic_block)

        for dinstr in basic_block:
            asm_str = self._render_asm(dinstr.asm_instr, asm_mnemonic_max_width + 1, fill_char=" ")
            lines.append(asm_str)

            if print_ir:
                for ir_instr in dinstr.ir_instrs:
                    reil_str = self._render_reil(ir_instr)
                    lines.append(reil_str)

        bb_dump = "".join(lines)

        # Set node label
        bb_addr = basic_block.address

        if basic_block.is_entry:
            bb_label = "{} @ {:x}".format(name, bb_addr)
        else:
            bb_label = "loc_{:x}".format(bb_addr)

        return self.bb_tpl.format(label=bb_label, assembly=bb_dump)
