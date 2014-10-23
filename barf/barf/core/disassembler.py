"""Generic Disassembler Interface.
"""

class Disassembler(object):

    """Generic Disassembler Interface.
    """

    def disassemble(self, data, address):
        """Disassemble raw bytes into an instruction.
        """
        raise NotImplementedError()

    def disassemble_all(self, data, address):
        """Disassemble raw bytes into multiple instructions.
        """
        raise NotImplementedError()
