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

# Supported architectures

# Intel x86 architecture definition
ARCH_X86 = 0
ARCH_X86_MODE_32 = 0
ARCH_X86_MODE_64 = 1

# ARM architecture definition
ARCH_ARM = 1
ARCH_ARM_MODE_ARM = 0
ARCH_ARM_MODE_THUMB = 1


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

    @property
    def max_instruction_size(self):
        raise NotImplementedError()

    def instr_is_ret(self, instruction):
        raise NotImplementedError()

    def instr_is_call(self, instruction):
        raise NotImplementedError()

    def instr_is_halt(self, instruction):
        raise NotImplementedError()

    def instr_is_branch(self, instruction):
        raise NotImplementedError()

    def instr_is_branch_cond(self, instruction):
        raise NotImplementedError()

    def instr_is_syscall(self, instruction):
        raise NotImplementedError()
