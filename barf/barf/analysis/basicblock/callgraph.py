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

    def save_ex(self, filename, format='dot'):
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

            # print("Number of Nodes: {}".format(len(self._graph.node.keys())))

            # add nodes
            nodes = {}
            for bb_addr in self._graph.node.keys():
                if bb_addr != "unknown":
                    label  = '<'
                    label += '<table border="1.0" cellborder="0" cellspacing="1" cellpadding="0" valign="middle">'
                    label += '  <tr><td align="center" cellpadding="1" port="enter"></td></tr>'
                    if bb_addr in self._cfg_by_addr and not isinstance(self._cfg_by_addr[bb_addr], str) and self._cfg_by_addr[bb_addr].label:
                        label += '  <tr><td align="left" cellspacing="1">{}</td></tr>'.format(self._cfg_by_addr[bb_addr].label)
                    else:
                        label += '  <tr><td align="left" cellspacing="1">sub_{address:x}</td></tr>'
                    label += '  <tr><td align="center" cellpadding="1" port="exit" ></td></tr>'
                    label += '</table>'
                    label += '>'

                    label = label.format(address=bb_addr)

                    # label = "sub_{address:x}".format(address=bb_addr)

                    nodes[bb_addr] = Node(bb_addr, label=label, **node_format)
                else:
                    label = "unknown".format()

                    nodes[bb_addr] = Node(bb_addr, label=label, **node_format)

                graph.add_node(nodes[bb_addr])

            # add edges
            for bb_src_addr in self._graph.node.keys():

                for bb_dst_addr in self._edges.get(bb_src_addr, []):
                    if bb_dst_addr == "unknown":
                        branch_type = "indirect"
                    else:
                        branch_type = "direct"

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

                            # print("call : {:#010x}".format(target_addr))

                            edges.append(target_addr)

                            graph.add_edge(cfg.start_address, target_addr, branch_type="direct")
                        else:
                            edges.append("unknown")

                            graph.add_edge(cfg.start_address, "unknown", branch_type="indirect")

            self._edges[cfg.start_address] = edges

        return graph

    def __getstate__(self):
        state = {}

        state['_cfgs'] = self._cfgs

        return state

    def __setstate__(self, state):
        cfgs = state['_cfgs']

        # List of CFGs sorted by address.
        self._cfgs = sorted(cfgs, key=lambda cfg: cfg.start_address)

        # CFGs accessed by address
        self._cfg_by_addr = dict([(cfg.start_address, cfg) for cfg in cfgs])
