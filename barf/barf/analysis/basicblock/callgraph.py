import logging
import networkx

from pydot import Dot
from pydot import Edge
from pydot import Node

from barf.arch.x86.x86base import X86ImmediateOperand

logger = logging.getLogger(__name__)


class CallGraph(object):

    """Call graph.
    """

    def __init__(self, cfgs):

        # List of CFGs sorted by address.
        self._cfgs = sorted(cfgs, key=lambda cfg: cfg.start_address)

        # CFGs accessed by address
        self._cfg_by_addr = dict([(cfg.start_address, cfg) for cfg in cfgs])

        self._edges = {}

        # Basic block graph
        self._graph = self._build_graph()

        # # List of entry basic blocks
        # self._entry_blocks = [bb.address for bb in basic_blocks
        #                         if len(self._graph.in_edges(bb.address)) == 0]

        # # List of exit basic blocks
        # self._exit_blocks = [bb.address for bb in basic_blocks
        #                         if len(self._graph.out_edges(bb.address)) == 0]

    # def all_simple_bb_paths(self, start_address, end_address):
    #     """Return a list of path between start and end address.
    #     """
    #     bb_start = self._find_basic_block(start_address)
    #     bb_end = self._find_basic_block(end_address)

    #     paths = networkx.all_simple_paths(self._graph, source=bb_start.address, target=bb_end.address)

    #     return (map(lambda addr: self._bb_by_addr[addr], path) for path in paths)

    # def save(self, filename, print_ir=False, format='dot'):
    #     """Save basic block graph into a file.
    #     """
    #     node_format = {
    #         'shape'    : 'Mrecord',
    #         'rankdir'  : 'LR',
    #         'fontname' : 'monospace',
    #         'fontsize' : '9.0',
    #     }

    #     edge_format = {
    #         'fontname' : 'monospace',
    #         'fontsize' : '8.0',
    #     }

    #     edge_colors = {
    #         'taken'     : 'green',
    #         'not-taken' : 'red',
    #         'direct'    : 'blue',
    #     }

    #     html_entities = {
    #         "!" : "&#33;",
    #         "#" : "&#35;",
    #         ":" : "&#58;",
    #         "{" : "&#123;",
    #         "}" : "&#125;",
    #     }

    #     try:
    #         dot_graph = Dot(graph_type="digraph", rankdir="TB")

    #         # Add nodes.
    #         nodes = {}
    #         for bb_addr in self._bb_by_addr:
    #             bb_dump = self._dump_bb(self._bb_by_addr[bb_addr], print_ir)

    #             # html-encode colon character
    #             for char, encoding in html_entities.items():
    #                 bb_dump = bb_dump.replace(char, encoding)

    #             label = "{{<f0> {:#010x} | {}}}".format(bb_addr, bb_dump)

    #             nodes[bb_addr] = Node(bb_addr, label=label, **node_format)

    #             dot_graph.add_node(nodes[bb_addr])

    #         # Add edges.
    #         for bb_src_addr in self._bb_by_addr:
    #             for bb_dst_addr, branch_type in self._bb_by_addr[bb_src_addr].branches:
    #                 # Skip jmp/jcc to sub routines.
    #                 if not bb_dst_addr in self._bb_by_addr:
    #                     continue

    #                 dot_graph.add_edge(
    #                     Edge(
    #                         nodes[bb_src_addr],
    #                         nodes[bb_dst_addr],
    #                         color=edge_colors[branch_type],
    #                         **edge_format))

    #         # Save graph.
    #         dot_graph.write("{}.{}".format(filename, format), format=format)
    #     except Exception:
    #         logger.error(
    #             "Failed to save basic block graph: %s (%s)",
    #             filename,
    #             format,
    #             exc_info=True
    #         )

    def save_ex(self, filename, print_ir=False, format='dot'):
        """Save basic block graph into a file.
        """

        fontname = 'Ubuntu Mono'
        # fontname = 'DejaVu Sans Mono'
        # fontname = 'DejaVu Sans Condensed'
        # fontname = 'DejaVu Sans Light'
        # fontname = 'Liberation Mono'
        # fontname = 'DejaVu Serif Condensed'
        # fontname = 'Ubuntu Condensed'

        node_format = {
            'shape'     : 'plaintext',
            'rankdir'   : 'LR',
            'fontname'  : fontname,
            'fontsize'  : 9.0,
            'penwidth'  : 0.5,
            # 'style'     : 'filled',
            # 'fillcolor' : 'orange',
        }

        edge_format = {
            'fontname'  : fontname,
            'fontsize'  : 8.0,
            'penwidth'  : 0.5,
            'arrowsize' : 0.6,
            'arrowhead' : 'vee',
        }

        edge_colors = {
            'taken'     : 'darkgreen',
            'not-taken' : 'red',
            'direct'    : 'blue',
            'indirect'  : 'cyan',
        }

        try:
            graph = Dot(graph_type="digraph", rankdir="TB", splines="ortho", nodesep=1.2)

            print("Number of Nodes: {}".format(len(self._graph.node.keys())))

            # add nodes
            nodes = {}
            for bb_addr in self._graph.node.keys():
                if bb_addr != "unknown":
                    # label  = '<'
                    # label += '<table border="1.0" cellborder="0" cellspacing="1" cellpadding="0" valign="middle">'
                    # label += '  <tr><td align="center" cellpadding="1" port="enter"></td></tr>'
                    # label += '  <tr><td align="left" cellspacing="1">sub_{address:x}</td></tr>'
                    # label += '  <tr><td align="center" cellpadding="1" port="exit" ></td></tr>'
                    # label += '</table>'
                    # label += '>'

                    # label = label.format(address=bb_addr)

                    label = "sub_{address:x}".format(address=bb_addr)

                    nodes[bb_addr] = Node(bb_addr, label=label, **node_format)
                else:
                    label = "unknown".format()

                    nodes[bb_addr] = Node(bb_addr, label=label, **node_format)

                graph.add_node(nodes[bb_addr])

            # add edges
            for bb_src_addr in self._graph.node.keys():
                branch_type = "direct"

                for bb_dst_addr in self._edges.get(bb_src_addr, []):
                    if bb_dst_addr == "unknown":
                        graph.add_edge(
                            Edge(nodes[bb_src_addr],
                            nodes[bb_dst_addr],
                            color=edge_colors["indirect"],
                            **edge_format))

                    else:
                        graph.add_edge(
                            Edge(nodes[bb_src_addr],
                            nodes[bb_dst_addr],
                            color=edge_colors[branch_type],
                            **edge_format))

            graph.write("%s.%s" % (filename, format), format=format)
        except Exception as err:
           logger.error(
                "Failed to save basic block graph: %s (%s)",
                filename,
                format,
                exc_info=True
            )

    # Auxiliary functions
    # ======================================================================== #
    def _build_graph(self):
        graph = networkx.DiGraph()

        # add nodes
        for cfg in self._cfgs:
            graph.add_node(cfg.start_address, address=cfg.start_address)

        graph.add_node("unknown", address="unknown")

        # add edges
        for cfg in self._cfgs:
            edges = self._edges.get(cfg.start_address, [])

            for bb in cfg.basic_blocks:
                for dinstr in bb:
                    if dinstr.asm_instr.mnemonic == "call":
                        if isinstance(dinstr.asm_instr.operands[0], X86ImmediateOperand):
                            target_addr = dinstr.asm_instr.operands[0].immediate

                            print("call : {:#010x}".format(target_addr))

                            edges.append(target_addr)

                            graph.add_edge(cfg.start_address, target_addr, branch_type="direct")
                        else:
                            edges.append("unknown")

                            graph.add_edge(cfg.start_address, "unknown", branch_type="indirect")

            self._edges[cfg.start_address] = edges

        return graph

    def _find_basic_block(self, address):
        bb_rv = None

        for bb in self._basic_blocks:
            if address >= bb.address and address <= bb.end_address:
                bb_rv = bb
                break

        return bb_rv

    def _dump_instr(self, instr, mnemonic_width):
        operands_str = ", ".join([str(oprnd) for oprnd in instr.operands])

        string  = instr.prefix + " " if instr.prefix else ""
        string += instr.mnemonic + "\\ " * (mnemonic_width - len(instr.mnemonic))
        string += " " + operands_str if operands_str else ""

        return string

    def _dump_bb(self, basic_block, print_ir=False):
        lines = []

        asm_fmt = "{:08x} [{:02d}] {}\\l"
        reil_fmt = " {:02x} {}\\l"

        asm_mnemonic_max_width = 0

        for dinstr in basic_block:
            if len(dinstr.asm_instr.mnemonic) > asm_mnemonic_max_width:
                asm_mnemonic_max_width = len(dinstr.asm_instr.mnemonic)

        for dinstr in basic_block:
            asm_instr_str = self._dump_instr(dinstr.asm_instr, asm_mnemonic_max_width + 1)

            lines += [asm_fmt.format(dinstr.address, dinstr.asm_instr.size, asm_instr_str)]

            if print_ir:
                for ir_instr in dinstr.ir_instrs:
                    lines += [reil_fmt.format(ir_instr.address & 0xff, ir_instr)]

        return "".join(lines)

    def _dump_bb_ex(self, basic_block, print_ir=False):
        lines = []

        base_addr = basic_block.instrs[0].address

        formatter = HtmlFormatter()
        formatter.noclasses = True
        formatter.nowrap = True

        for instr in basic_block.instrs:
            asm_instr = highlight(str(instr.asm_instr), NasmLexer(), formatter)
            # asm_instr = str(instr.asm_instr)

            asm_instr = asm_instr.replace("span", "font")
            asm_instr = asm_instr.replace('style="color: ', 'color="')

            lines += ["<tr><td align='left'>    %08x [%02d] %s </td></tr>" % (instr.address, instr.asm_instr.size, asm_instr)]

            if print_ir:
                for ir_instr in instr.ir_instrs:
                    lines += ["              " + str(ir_instr) + "\\l"]

        return "".join(lines)

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
        starts = [self._bb_by_addr[bb_addr].start_address for bb_addr in self._entry_blocks]

        return min(starts)

    @property
    def end_address(self):
        # TODO: Test.
        ends = [self._bb_by_addr[bb_addr].end_address for bb_addr in self._exit_blocks]

        return max(ends)

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
