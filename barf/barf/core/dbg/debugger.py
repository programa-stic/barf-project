"""Generic Debugger Interface.
"""

class Debugger(object):

    """Generic Debugger Interface.
    """

    def __init__(self):
        pass

    def get_memory(self):
        """Get memory.
        """
        raise NotImplementedError()

    def get_architecture(self):
        """Get architecture name.
        """
        raise NotImplementedError()

    def get_registers(self):
        """Get registers.
        """
        raise NotImplementedError()

    def get_flags(self):
        """Get flags.
        """
        raise NotImplementedError()
