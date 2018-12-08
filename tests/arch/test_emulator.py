# Copyright (c) 2017, Fundacion Dr. Manuel Sadosky
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

from __future__ import absolute_import

import os
import unittest

from barf.arch import ARCH_ARM_MODE_ARM
from barf.arch import ARCH_ARM_MODE_THUMB
from barf.arch import ARCH_X86_MODE_32
from barf.arch import ARCH_X86_MODE_64
from barf.arch.arm import ArmArchitectureInformation
from barf.arch.arm.disassembler import ArmDisassembler
from barf.arch.arm.translator import ArmTranslator
from barf.arch.emulator import Emulator
from barf.arch.x86 import X86ArchitectureInformation
from barf.arch.x86.disassembler import X86Disassembler
from barf.arch.x86.translator import X86Translator
from barf.core.binary import BinaryFile
from barf.core.reil.emulator.emulator import ReilEmulator


def get_full_path(filename):
    return os.path.join(os.path.dirname(os.path.abspath(__file__)), filename)


class EmulatorTests(unittest.TestCase):

    def setUp(self):
        pass

    def test_emulate_x86(self):
        binary = BinaryFile(get_full_path("./samples/bin/loop-simple.x86"))
        arch_mode = ARCH_X86_MODE_32
        arch_info = X86ArchitectureInformation(arch_mode)
        ir_emulator = ReilEmulator(arch_info)
        disassembler = X86Disassembler(ARCH_X86_MODE_32)
        ir_translator = X86Translator(ARCH_X86_MODE_32)

        emu = Emulator(arch_info, ir_emulator, ir_translator, disassembler)

        emu.load_binary(binary)

        emu.emulate(0x080483db, 0x8048407, {}, None, False)

    def test_emulate_x86_64(self):
        binary = BinaryFile(get_full_path("./samples/bin/loop-simple.x86_64"))
        arch_mode = ARCH_X86_MODE_64
        arch_info = X86ArchitectureInformation(arch_mode)
        ir_emulator = ReilEmulator(arch_info)
        disassembler = X86Disassembler(ARCH_X86_MODE_64)
        ir_translator = X86Translator(ARCH_X86_MODE_64)

        emu = Emulator(arch_info, ir_emulator, ir_translator, disassembler)

        emu.load_binary(binary)

        emu.emulate(0x4004d6, 0x400507, {}, None, False)

    def test_emulate_arm(self):
        binary = BinaryFile(get_full_path("./samples/bin/loop-simple.arm"))
        arch_mode = ARCH_ARM_MODE_ARM
        arch_info = ArmArchitectureInformation(arch_mode)
        ir_emulator = ReilEmulator(arch_info)
        disassembler = ArmDisassembler(architecture_mode=ARCH_ARM_MODE_ARM)
        ir_translator = ArmTranslator(architecture_mode=ARCH_ARM_MODE_ARM)

        emu = Emulator(arch_info, ir_emulator, ir_translator, disassembler)

        emu.load_binary(binary)

        emu.emulate(0x10400, 0x10460, {}, None, True)

    def test_emulate_arm_thumb(self):
        binary = BinaryFile(get_full_path("./samples/bin/loop-simple.arm_thumb"))
        arch_mode = ARCH_ARM_MODE_THUMB
        arch_info = ArmArchitectureInformation(arch_mode)
        ir_emulator = ReilEmulator(arch_info)
        disassembler = ArmDisassembler(architecture_mode=ARCH_ARM_MODE_THUMB)
        ir_translator = ArmTranslator(architecture_mode=ARCH_ARM_MODE_THUMB)

        emu = Emulator(arch_info, ir_emulator, ir_translator, disassembler)

        emu.load_binary(binary)

        emu.emulate(0x10401, 0x10432, {}, None, True)
