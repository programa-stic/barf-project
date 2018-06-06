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


class X86SystemVParameterManager(object):

    def __init__(self, emulator):
        self.__emulator = emulator

    def __getitem__(self, index):
        # NOTE: Only works if it is call before the stack frame is made.
        esp = self.__emulator.registers['esp']

        return self.__emulator.read_memory(esp + 4 * index + 0x4, 4)

    def __setitem__(self, index, value):
        # NOTE: Only works if it is call before the stack frame is made.
        esp = self.__emulator.registers['esp']

        return self.__emulator.write_memory(esp + 4 * index + 0x4, 4, value)


class X86SystemV(object):

    def __init__(self, emulator):
        self.__emulator = emulator
        self.__parameters = X86SystemVParameterManager(emulator)

    @property
    def parameters(self):
        return self.__parameters

    @property
    def return_value(self):
        return self.__emulator.registers['eax']

    @return_value.setter
    def return_value(self, value):
        self.__emulator.registers['eax'] = value


class X86_64SystemVParameterManager(object):

    def __init__(self, emulator):
        self.__emulator = emulator

    def __getitem__(self, index):
        if index == 0:
            return self.__emulator.registers['rdi']
        elif index == 1:
            return self.__emulator.registers['rsi']
        elif index == 2:
            return self.__emulator.registers['rdx']
        elif index == 3:
            return self.__emulator.registers['rcx']
        elif index == 4:
            return self.__emulator.registers['r8']
        elif index == 5:
            return self.__emulator.registers['r9']
        else:
            raise NotImplementedError()

    def __setitem__(self, index, value):
        if index == 0:
            self.__emulator.registers['rdi'] = value
        elif index == 1:
            self.__emulator.registers['rsi'] = value
        elif index == 2:
            self.__emulator.registers['rdx'] = value
        elif index == 3:
            self.__emulator.registers['rcx'] = value
        elif index == 4:
            self.__emulator.registers['r8'] = value
        elif index == 5:
            self.__emulator.registers['r9'] = value
        else:
            raise NotImplementedError()


class X86_64SystemV(object):

    def __init__(self, emulator):
        self.__emulator = emulator
        self.__parameters = X86_64SystemVParameterManager(emulator)

    @property
    def parameters(self):
        return self.__parameters

    @property
    def return_value(self):
        return self.__emulator.registers['rax']

    @return_value.setter
    def return_value(self, value):
        self.__emulator.registers['rax'] = value


class ArmSystemVParameterManager(object):

    def __init__(self, emulator):
        self.__emulator = emulator

    def __getitem__(self, index):
        if index == 0:
            return self.__emulator.registers['r0']
        elif index == 1:
            return self.__emulator.registers['r1']
        elif index == 2:
            return self.__emulator.registers['r2']
        elif index == 3:
            return self.__emulator.registers['r3']
        else:
            raise NotImplementedError()

    def __setitem__(self, index, value):
        if index == 0:
            self.__emulator.registers['r0'] = value
        elif index == 1:
            self.__emulator.registers['r1'] = value
        elif index == 2:
            self.__emulator.registers['r2'] = value
        elif index == 3:
            self.__emulator.registers['r3'] = value
        else:
            raise NotImplementedError()


class ArmSystemV(object):

    def __init__(self, emulator):
        self.__emulator = emulator
        self.__parameters = ArmSystemVParameterManager(emulator)

    @property
    def parameters(self):
        return self.__parameters

    @property
    def return_value(self):
        return self.__emulator.registers['r0']

    @return_value.setter
    def return_value(self, value):
        self.__emulator.registers['r0'] = value
