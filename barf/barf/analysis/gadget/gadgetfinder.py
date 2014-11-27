"""
This module implements a gadget finder based on the paper "The Geometry of
Innocent Flesh on the Bone: Return-into-libc without Function Calls
(on the x86)."

Some more work is needed to make this algorithm truly architecture
agnostic.

"""
import logging

from barf.analysis.gadget import GadgetType
from barf.analysis.gadget import RawGadget
from barf.arch.x86.x86instructiontranslator import FULL_TRANSLATION
from barf.arch.x86.x86instructiontranslator import LITE_TRANSLATION
from barf.core.reil import DualInstruction
from barf.core.reil import ReilMnemonic
from barf.core.reil import ReilRegisterOperand

logger = logging.getLogger("GadgetFinder")

class GadgetFinder(object):

    """Gadget Finder.
    """

    def __init__(self, disasm, mem, ir_trans):

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

    def find(self, start_address, end_address, byte_depth=20, instrs_depth=2):
        """Find gadgets.
        """
        self._max_bytes = byte_depth
        self._instrs_depth = instrs_depth

        trans_mode_old = self._ir_trans.translation_mode

        self._ir_trans.translation_mode = LITE_TRANSLATION

        candidates = self._find_candidates(start_address, end_address)

        self._ir_trans.translation_mode = trans_mode_old

        return candidates

    # Auxiliary functions
    # ======================================================================== #
    def _find_candidates(self, start_address, end_address):
        """Finds possible 'RET-ended' gadgets.
        """
        roots = []

        # find gadget tail
        for addr in xrange(start_address, end_address + 1):
            # TODO: Make this 'speed improvement' architecture-agnostic
            op_codes = [
                "\xc3",     # RET
                "\xc2",     # RET imm16
                "\xeb",     # JMP rel8
                "\xe8",     # CALL rel{16,32}
                "\xe9",     # JMP rel{16,32}
                "\xff",     # JMP/CALL r/m{16,32,64}
            ]

            if self._mem[addr] not in op_codes:
                continue

            asm_instr, asm_size = self._disasm.disassemble(
                self._mem[addr:min(addr+16, end_address + 1)],
                addr
            )

            if not asm_instr:
                continue

            # restarts ir register numbering
            self._ir_trans.reset()

            try:
                ins_ir = self._ir_trans.translate(asm_instr)
            except:
                logger.debug("[-] Error: GadgetFinder")
                logger.debug("asm: " + str(asm_instr))
                logger.debug("bytes: " + "".join("\\x%02x" % ord(b) for b in asm_instr.bytes))
                continue

            # build gadget
            if ins_ir[-1] and (ins_ir[-1].mnemonic == ReilMnemonic.RET \
                or (ins_ir[-1].mnemonic == ReilMnemonic.JCC and isinstance(ins_ir[-1].operands[2], ReilRegisterOperand))):

                root = GadgetTreeNode(DualInstruction(addr, asm_instr, ins_ir))

                roots.append(root)

                self._build_from(addr, root, start_address, self._instrs_depth)

        # filter roots with no children
        roots = [r for r in roots if len(r.get_children()) > 0]

        # build gadgets
        root_gadgets = [self._build_gadgets(r) for r in roots]

        # flatten root gadget list
        candidates = [item for l in root_gadgets for item in l]

        return candidates

    def _build_from(self, address, root, base_address, depth = 2):
        """Build gadget recursively.
        """
        if depth == 0:
            return

        end_addr = address

        for step in range(1, self._max_bytes + 1):
            start_addr = address - step

            if start_addr < 0 or start_addr < base_address:
                break

            raw_bytes = self._mem[start_addr:end_addr]

            asm_instr, asm_size = self._disasm.disassemble(
                raw_bytes,
                start_addr
            )

            if not asm_instr or asm_size != step:
                continue

            try:
                ir_instrs = self._ir_trans.translate(asm_instr)
            except:
                logger.debug("[-] Error: GadgetFinder")
                logger.debug("asm: " + str(asm_instr))
                logger.debug("bytes: " + "".join("\\x%02x" % ord(b) for b in asm_instr.bytes))
                continue

            if self._is_valid_ins(ir_instrs, asm_instr):
                child = GadgetTreeNode(DualInstruction(start_addr, asm_instr, \
                    ir_instrs))

                root.add_child(child)

                self._build_from(address - step, child, base_address, depth - 1)

    def _build_gadgets(self, gadget_tree_root):
        """Return a gadget list.
        """
        node_list = self._build_gadgets_rec(gadget_tree_root)

        return [RawGadget(n) for n in node_list]

    def _build_gadgets_rec(self, gadget_tree_root):
        """Build a gadget from a gadget tree.
        """
        root     = gadget_tree_root.get_root()
        children = gadget_tree_root.get_children()

        node_list = []

        root_gadget_ins = DualInstruction(root.address, root.asm_instr, \
            root.ir_instrs)

        if children == []:
            node_list += [[root_gadget_ins]]
        else:
            for child in children:
                node_list_rec = self._build_gadgets_rec(child)

                node_list += [n + [root_gadget_ins] for n in node_list_rec]

        return node_list

    def _is_valid_ins(self, ins_ir, ins_asm):
        """Check for instruction validity as a gadget.
        """
        invalid_instrs = [
            ReilMnemonic.JCC,
            ReilMnemonic.RET,
            ReilMnemonic.UNDEF,
            ReilMnemonic.UNKN,
        ]

        return not any([i.mnemonic in invalid_instrs for i in ins_ir])


class GadgetTreeNode(object):

    """Tree Data Structure.
    """

    def __init__(self, root):
        self._root     = root
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
