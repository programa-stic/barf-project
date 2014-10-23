"""GDB Debugger Interface.
"""
import gdb

from pybfd.bfd import Bfd

from barf.core.bi import Memory
from barf.core.dbg.debugger import Debugger

# TODO: See how to get this information from gdb.
def get_section_text_limits(filename):
    """Get setion .text limits.
    """
    bfd = Bfd(filename)

    section_name = ".text"

    section = bfd.sections.get(section_name)

    section_start = section.vma
    section_end = section.vma + len(section.content) - 1

    bfd.close()

    return section_start, section_end

class GDBDebugger(Debugger):

    """GDB Debugger Interface.
    """

    def __init__(self):
        super(GDBDebugger, self).__init__()

    def get_memory(self):
        """Get memory.
        """
        inf = gdb.selected_inferior()

        return Memory(inf.read_memory, inf.write_memory)

    def get_architecture(self):
        """Get architecture.
        """
        return "x86"

    def get_registers(self):
        """Get registers.
        """
        registers32 = ["eax", "ecx", "edx", "ebx", "esp", "ebp", "esi", "edi",
            "eip"]

        regs = {}

        for reg in registers32:
            regs[reg] = int(long(gdb.parse_and_eval("$" + reg)) & 0xffffffff)

        return regs

    def get_flags(self):
        """Get flags.
        """
        flags32 = ["af", "cf", "of", "pf", "sf", "zf"]

        eflags = str(gdb.parse_and_eval("$eflags"))[2:-2].lower().split(" ")

        flags = {}

        for flag in flags32:
            if flag in eflags:
                flags[flag] = 0x1
            else:
                flags[flag] = 0x0

        return flags

    def get_current_file(self):
        """Get current file name.
        """
        return gdb.current_progspace().filename

    def get_section_text_limits(self):
        """Get section .text limits.
        """
        text, start, end = get_section_text(self.get_current_file())

        self._section_text = text
        self._section_text_start = start
        self._section_text_end = end

        return self._section_text_start, self._section_text_end
