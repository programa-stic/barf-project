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

from __future__ import absolute_import

import codecs
import logging

from barf.core.reil import ReilImmediateOperand
from barf.core.reil import ReilLabel
from barf.core.reil import ReilMnemonic
from barf.core.reil import ReilRegisterOperand
from barf.core.reil.builder import ReilBuilder
from barf.core.reil.helpers import to_reil_address
from barf.utils.utils import VariableNamer

logger = logging.getLogger(__name__)


class TranslationError(Exception):
    pass


class FlagTranslator(object):

    def __init__(self, arch):
        self.__arch = arch
        self.__flags = {}

    def __getattr__(self, flag):
        return self.__get_flag(flag)

    def __getitem__(self, flag):
        return self.__get_flag(flag)

    # Auxiliary functions
    # ======================================================================== #
    def __get_flag(self, flag):
        flag = flag.lower()

        if flag not in self.__arch.registers_flags:
            raise TranslationError("Invalid flag")

        if flag not in self.__flags:
            self.__flags[flag] = ReilRegisterOperand(flag, self.__arch.registers_size[flag])

        return self.__flags[flag]


class RegisterTranslator(object):

    def __init__(self, arch):
        self.__arch = arch
        self.__registers = {}

    def __getattr__(self, register):
        return self.__get_register(register)

    def __getitem__(self, register):
        return self.__get_register(register)

    # Auxiliary functions
    # ======================================================================== #
    def __get_register(self, register):
        register = register.lower()

        if register not in self.__arch.registers_gp_all:
            raise TranslationError("Invalid register")

        if register not in self.__registers:
            self.__registers[register] = ReilRegisterOperand(register, self.__arch.registers_size[register])

        return self.__registers[register]


class InstructionTranslator(object):

    def __init__(self):
        # An instance of a *VariableNamer*. This is used so all the
        # temporary REIL registers are unique.
        self._ir_name_generator = VariableNamer("t", separator="")

    def translate(self, instruction):
        """Return REIL representation of an instruction.
        """
        try:
            trans_instrs = self._translate(instruction)
        except Exception:
            self._log_translation_exception(instruction)

            raise TranslationError("Unknown error")

        return trans_instrs

    def reset(self):
        """Restart REIL register name generator.
        """
        self._ir_name_generator.reset()

    def _translate(self, instruction):
        raise NotImplementedError()

    # Auxiliary functions
    # ======================================================================== #
    def _log_not_supported_instruction(self, instruction):
        logger.warning("Instruction not supported: %s (%s [%s])",
                    instruction.mnemonic, instruction,
                    codecs.encode(instruction.bytes, 'hex'), exc_info=True)

    def _log_translation_exception(self, instruction):
        logger.error("Error translating instruction: %s (%s [%s])",
                     instruction.mnemonic, instruction,
                     codecs.encode(instruction.bytes, 'hex'), exc_info=True)


class TranslationBuilder(object):

    def __init__(self, ir_name_generator, architecture_information):
        self._ir_name_generator = ir_name_generator

        self._instructions = []

        self._builder = ReilBuilder()

        self._arch_info = architecture_information

    def add(self, instruction):
        self._instructions.append(instruction)

    def temporal(self, size):
        return ReilRegisterOperand(self._ir_name_generator.get_next(), size)

    def immediate(self, value, size):
        return ReilImmediateOperand(value, size)

    def label(self, name):
        return ReilLabel(name)

    def instanciate(self, address):
        return self.__resolve_loops(address, self._instructions)

    # Auxiliary functions
    # ======================================================================== #
    def __resolve_loops(self, address, instrs):
        # Collect labels.
        idx_by_labels = {}
        instrs_no_labels = []
        curr = 0

        for i in instrs:
            if isinstance(i, ReilLabel):
                idx_by_labels[i.name] = curr
            else:
                instrs_no_labels.append(i)
                curr += 1

        instrs[:] = instrs_no_labels

        # Resolve instruction addresses and JCC targets.
        for index, instr in enumerate(instrs):
            instr.address = to_reil_address(address, index)

            if instr.mnemonic == ReilMnemonic.JCC:
                target = instr.operands[2]

                if isinstance(target, ReilLabel):
                    addr = to_reil_address(address, idx_by_labels[target.name])
                    size = self._arch_info.address_size + 8

                    instr.operands[2] = ReilImmediateOperand(addr, size)

        return instrs
