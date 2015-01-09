# Supported architectures

# Intel x86 architecture definition
ARCH_X86 = 0
ARCH_X86_MODE_32 = 0
ARCH_X86_MODE_64 = 1

# ARM architecture definition
ARCH_ARM = 1
ARCH_ARM_MODE_32 = 0
ARCH_ARM_MODE_64 = 1

class ArchitectureInformation(object):

    def __init__(self):
        pass

    @property
    def architecture_mode(self):
        raise NotImplementedError()

    @property
    def architecture_size(self):
        raise NotImplementedError()

    @property
    def operand_size(self):
        raise NotImplementedError()

    @property
    def address_size(self):
        raise NotImplementedError()

    @property
    def registers(self):
        raise NotImplementedError()
