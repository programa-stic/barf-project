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

from barf.arch import helper
from barf.core.bi import InvalidAddressError
from barf.core.disassembler import DisassemblerError
from barf.core.disassembler import InvalidDisassemblerData
from barf.core.reil import DualInstruction

from pygments import highlight
from pygments.formatters import HtmlFormatter
from pygments.lexers.asm import NasmLexer


logger = logging.getLogger(__name__)


def func_is_non_return(address, symbols):
    return address in symbols and not symbols[address][2]


def bb_get_instr_max_width(basic_block):
    """Get maximum instruction mnemonic width
    """
    asm_mnemonic_max_width = 0

    for dinstr in basic_block:
        if len(dinstr.asm_instr.mnemonic) > asm_mnemonic_max_width:
            asm_mnemonic_max_width = len(dinstr.asm_instr.mnemonic)

    return asm_mnemonic_max_width


def bb_get_type(basic_block):
    if basic_block.is_entry:
        bb_type = "entry"
    elif basic_block.is_exit:
        bb_type = "exit"
    else:
        bb_type = "other"

    return bb_type


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
        state = {
            '_instrs': self._instrs,
            '_address': self._address,
            '_taken_branch': self._taken_branch,
            '_not_taken_branch': self._not_taken_branch,
            '_direct_branch': self._direct_branch,
        }

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

    def find_basic_block(self, start):
        bb_rv = None

        for bb in self._basic_blocks:
            if bb.address == start:
                bb_rv = bb
                break

        return bb_rv

    def save(self, filename, print_ir=False, format='dot', options=None):
        # renderer = CFGSimpleRenderer()
        renderer = CFGSimpleRendererEx()

        renderer.save(self, filename, print_ir=print_ir, format=format, options=options)

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
        state = {
            '_basic_blocks': self._basic_blocks,
        }

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

    def build(self, start, end, symbols=None):
        """Return the list of basic blocks.

        :int start: Start address of the disassembling process.
        :int end: End address of the disassembling process.

        """
        symbols = {} if not symbols else symbols

        # First pass: Recover BBs.
        bbs = self._recover_bbs(start, end, symbols)

        # Second pass: Split overlapping basic blocks introduced by backedges.
        bbs = self._split_bbs(bbs, symbols)

        # Third pass: Extract call targets for further analysis.
        call_targets = self._extract_call_targets(bbs)

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

    def _extract_call_targets(self, bbs):
        call_targets = []
        for bb in bbs:
            for dinstr in bb:
                if self._arch_info.instr_is_call(dinstr.asm_instr):
                    target = helper.extract_call_target(dinstr.asm_instr)

                    if target:
                        call_targets.append(target)

        return call_targets

    def _split_bb(self, bb, address, symbols):
        bb_upper_half = self._disassemble_bb(bb.start_address, address, symbols)
        bb_lower_half = self._disassemble_bb(address, bb.end_address, symbols)

        bb_upper_half.direct_branch = address

        return bb_lower_half, bb_upper_half

    def _disassemble_bb(self, start, end, symbols):
        bb = BasicBlock()
        addr = start
        taken, not_taken, direct = None, None, None

        while addr < end:
            try:
                data_end = addr + self._arch_info.max_instruction_size
                data_chunk = self._memory[addr:min(data_end, end)]
                asm = self._disasm.disassemble(data_chunk, addr)
            except (DisassemblerError, InvalidAddressError, InvalidDisassemblerData):
                logger.warn("Error while disassembling @ {:#x}".format(addr), exc_info=True)
                break

            ir = self._translator.translate(asm)

            bb.instrs.append(DualInstruction(addr, asm, ir))

            # If it is a RET or HALT instruction, break.
            if self._arch_info.instr_is_ret(asm) or \
               self._arch_info.instr_is_halt(asm):
                bb.is_exit = True
                break

            # If it is a CALL instruction and the callee does not return, break.
            if self._arch_info.instr_is_call(asm):
                target = helper.extract_call_target(asm)

                if target and func_is_non_return(target, symbols):
                    bb.is_exit = True
                    break

            # If it is a BRANCH instruction, extract target and break.
            if self._arch_info.instr_is_branch(asm):
                target = helper.extract_branch_target(asm)

                if self._arch_info.instr_is_branch_cond(asm):
                    taken = target
                    not_taken = asm.address + asm.size
                else:
                    direct = target

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
        last_instr = bb.instrs[-1].asm_instr

        return self._arch_info.instr_is_branch(last_instr) and \
               not self._arch_info.instr_is_branch_cond(last_instr)

    def _bb_ends_in_return(self, bb):
        last_instr = bb.instrs[-1].asm_instr

        return self._arch_info.instr_is_ret(last_instr)


class CFGRecoverer(object):

    def __init__(self, strategy):
        self.strategy = strategy

    def build(self, start, end=None, symbols=None):
        return self.strategy.build(start, end, symbols)


class CFGRenderer(object):

    def save(self):
        raise NotImplementedError()


class CFGSimpleRenderer(CFGRenderer):

    fontname = 'monospace'

    graph_format = {
        'graph_type': 'digraph',
        'rankdir': 'TB',
    }

    node_format = {
        'shape': 'Mrecord',
        'rankdir': 'LR',
        'fontname': fontname,
        'fontsize': '9.0',
    }

    node_color = {
        'entry': 'black',
        'exit': 'black',
        'other': 'black',
    }

    edge_format = {
        'fontname': fontname,
        'fontsize': '8.0',
    }

    edge_color = {
        'taken': 'green',
        'not-taken': 'red',
        'direct': 'blue',
    }

    # Templates.
    bb_tpl = "{{<f0> {label} | {assembly}}}"

    asm_tpl = "{address:08x} [{size:02d}] {assembly}\\l"

    reil_tpl = " {index:02x} {assembly}\\l"

    def save(self, cfg, filename, print_ir=False, format='dot', options=None):
        """Save basic block graph into a file.
        """
        if options is None:
            options = {}

        try:
            dot_graph = Dot(**self.graph_format)

            # Add nodes.
            nodes = {}
            for bb in cfg.basic_blocks:
                nodes[bb.address] = self._create_node(bb, cfg.name, print_ir, options)

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

    def _create_node(self, bb, name, print_ir, options):
        bb_dump = self._render_bb(bb, name, print_ir, options)
        bb_type = bb_get_type(bb)

        return Node(bb.address, label=bb_dump, color=self.node_color[bb_type], **self.node_format)

    def _create_edge(self, src, dst, branch_type):
        return Edge(src, dst, color=self.edge_color[branch_type], **self.edge_format)

    def _render_asm(self, instr, mnemonic_width, options, fill_char=""):
        oprnds_str = ", ".join([oprnd.to_string(**options) for oprnd in instr.operands])

        asm_str  = instr.prefix + " " if instr.prefix else ""
        asm_str += instr.mnemonic + fill_char * (mnemonic_width - len(instr.mnemonic))
        asm_str += " " + oprnds_str if oprnds_str else ""

        # html-encode colon character
        html_entities = {
            "!": "&#33;",
            "#": "&#35;",
            ":": "&#58;",
            "{": "&#123;",
            "}": "&#125;",
        }

        for char, encoding in html_entities.items():
            asm_str = asm_str.replace(char, encoding)

        return self.asm_tpl.format(address=instr.address, size=instr.size, assembly=asm_str)

    def _render_reil(self, instr):
        return self.reil_tpl.format(index=instr.address & 0xff, assembly=instr)

    def _render_bb(self, basic_block, name, print_ir, options):
        lines = []

        asm_mnemonic_max_width = bb_get_instr_max_width(basic_block)

        for dinstr in basic_block:
            asm_str = self._render_asm(dinstr.asm_instr, asm_mnemonic_max_width + 1, options, fill_char="\\ ")
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
        'graph_type': 'digraph',
        'nodesep': 1.2,
        'rankdir': 'TB',
        # 'splines': 'ortho', # NOTE This option brings up performance issues.
    }

    node_format = {
        'fontname': fontname,
        'fontsize': 9.0,
        'penwidth': 0.5,
        'rankdir': 'LR',
        'shape': 'plaintext',
    }

    edge_format = {
        'arrowhead': 'vee',
        'arrowsize': 0.6,
        'fontname': fontname,
        'fontsize': 8.0,
        'penwidth': 0.5,
    }

    node_color = {
        'entry': 'orange',
        'exit': 'gray',
        'other': 'black',
    }

    edge_color = {
        'direct': 'blue',
        'not-taken': 'red',
        'taken': 'darkgreen',
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

    reil_tpl = "<tr><td align='left'>         .{index:02x}  {assembly} </td></tr>"

    def save(self, cfg, filename, print_ir=False, format='dot', options=None):
        """Save basic block graph into a file.
        """
        if options is None:
            options = {}

        try:
            dot_graph = Dot(**self.graph_format)

            # Add nodes.
            nodes = {}
            for bb in cfg.basic_blocks:
                nodes[bb.address] = self._create_node(bb, cfg.name, print_ir, options)

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

    def _create_node(self, bb, name, print_ir, options):
        bb_dump = self._render_bb(bb, name, print_ir, options)
        bb_type = bb_get_type(bb)

        return Node(bb.address, label=bb_dump, color=self.node_color[bb_type], **self.node_format)

    def _create_edge(self, src, dst, branch_type):
        return Edge(src, dst, color=self.edge_color[branch_type], **self.edge_format)

    def _render_asm(self, instr, mnemonic_width, options, fill_char=""):
        formatter = HtmlFormatter()
        formatter.noclasses = True
        formatter.nowrap = True

        oprnds_str = ", ".join([oprnd.to_string(**options) for oprnd in instr.operands])

        asm_str  = instr.prefix + " " if instr.prefix else ""
        asm_str += instr.mnemonic + fill_char * (mnemonic_width - len(instr.mnemonic))
        asm_str += " " + oprnds_str if oprnds_str else ""

        # TODO Highlight for ARM too.
        asm_str = highlight(asm_str, NasmLexer(), formatter)
        asm_str = asm_str.replace("span", "font")
        asm_str = asm_str.replace('style="color: ', 'color="')
        asm_str = asm_str.replace('style="border: 1px solid ', 'color="')

        return self.asm_tpl.format(address=instr.address, size=instr.size, assembly=asm_str)

    def _render_reil(self, instr):
        return self.reil_tpl.format(index=instr.address & 0xff, assembly=instr)

    def _render_bb(self, basic_block, name, print_ir, options):
        lines = []

        asm_mnemonic_max_width = bb_get_instr_max_width(basic_block)

        for dinstr in basic_block:
            asm_str = self._render_asm(dinstr.asm_instr, asm_mnemonic_max_width + 1, options, fill_char=" ")
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
