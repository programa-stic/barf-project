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

from barf.arch.arm import ARM_LDM_STM_DA
from barf.arch.arm import ARM_LDM_STM_DB
from barf.arch.arm import ARM_LDM_STM_FD
from barf.arch.arm import ARM_LDM_STM_IA
from barf.arch.arm import ARM_LDM_STM_IB
from barf.arch.arm import ArmRegisterOperand
from barf.arch.arm import ldm_stack_am_to_non_stack_am
from barf.arch.arm import stm_stack_am_to_non_stack_am
from barf.arch.helper import add_to_reg
from barf.arch.helper import sub_to_reg
from barf.core.reil import ReilImmediateOperand
from barf.core.reil import ReilRegisterOperand


# "Load/store word and unsigned byte Instructions"
# ============================================================================ #
def _translate_ldr(self, tb, instruction):
    oprnd1 = self._reg_acc_translator.read(tb, instruction.operands[1])

    self._reg_acc_translator.write(tb, instruction.operands[0], oprnd1)


def _translate_str(self, tb, instruction):
    oprnd0 = self._reg_acc_translator.read(tb, instruction.operands[0])

    self._reg_acc_translator.write(tb, instruction.operands[1], oprnd0)


# TODO: Check if the byte suffix ('b') should be coded as extra information
# and removed from the mnemonic (handling all ldr/str translations in only
# two functions).
def _translate_ldrb(self, tb, instruction):
    op0_reil = ReilRegisterOperand(instruction.operands[0].name, instruction.operands[0].size)
    addr_reg = self._reg_acc_translator.compute_memory_address(tb, instruction.operands[1])
    byte_reg = tb.temporal(8)

    tb.add(tb._builder.gen_ldm(addr_reg, byte_reg))

    tb.add(self._builder.gen_str(byte_reg, op0_reil))


def _translate_strb(self, tb, instruction):
    reil_operand = ReilRegisterOperand(instruction.operands[0].name, instruction.operands[0].size)
    byte_reg = tb.temporal(8)

    tb.add(self._builder.gen_str(reil_operand, byte_reg))  # filter bits [7:0] part of result

    addr = self._reg_acc_translator.compute_memory_address(tb, instruction.operands[1])

    tb.add(self._builder.gen_stm(byte_reg, addr))


# TODO: Generalize LDR to handle byte and half word in a single function
def _translate_ldrh(self, tb, instruction):
    op0_reil = ReilRegisterOperand(instruction.operands[0].name, instruction.operands[0].size)
    addr_reg = self._reg_acc_translator.compute_memory_address(tb, instruction.operands[1])
    byte_reg = tb.temporal(16)

    tb.add(tb._builder.gen_ldm(addr_reg, byte_reg))

    tb.add(self._builder.gen_str(byte_reg, op0_reil))


def _translate_strh(self, tb, instruction):
    reil_operand = ReilRegisterOperand(instruction.operands[0].name, instruction.operands[0].size)
    half_word_reg = tb.temporal(16)

    tb.add(self._builder.gen_str(reil_operand, half_word_reg))  # filter bits [15:0] part of result

    addr = self._reg_acc_translator.compute_memory_address(tb, instruction.operands[1])

    tb.add(self._builder.gen_stm(half_word_reg, addr))


def _translate_ldrd(self, tb, instruction):
    if len(instruction.operands) > 2:  # Rd2 has been specified (UAL syntax)
        addr_reg = self._reg_acc_translator.compute_memory_address(tb, instruction.operands[2])
    else:
        addr_reg = self._reg_acc_translator.compute_memory_address(tb, instruction.operands[1])

    reil_operand = ReilRegisterOperand(instruction.operands[0].name, instruction.operands[0].size)

    tb.add(tb._builder.gen_ldm(addr_reg, reil_operand))

    addr_reg = add_to_reg(tb, addr_reg, ReilImmediateOperand(4, reil_operand.size))

    if len(instruction.operands) > 2:  # Rd2 has been specified (UAL syntax)
        reil_operand = ReilRegisterOperand(instruction.operands[1].name, instruction.operands[0].size)
    else:
        # TODO: Assuming the register is written in its number format
        # (no alias like lr or pc).
        reil_operand = ReilRegisterOperand('r' + str(int(reil_operand.name[1:]) + 1), reil_operand.size)

    tb.add(tb._builder.gen_ldm(addr_reg, reil_operand))


def _translate_strd(self, tb, instruction):
    if len(instruction.operands) > 2:  # Rd2 has been specified (UAL syntax)
        addr_reg = self._reg_acc_translator.compute_memory_address(tb, instruction.operands[2])
    else:
        addr_reg = self._reg_acc_translator.compute_memory_address(tb, instruction.operands[1])

    reil_operand = ReilRegisterOperand(instruction.operands[0].name, instruction.operands[0].size)

    tb.add(tb._builder.gen_stm(reil_operand, addr_reg))

    addr_reg = add_to_reg(tb, addr_reg, ReilImmediateOperand(4, reil_operand.size))

    if len(instruction.operands) > 2:  # Rd2 has been specified (UAL syntax)
        reil_operand = ReilRegisterOperand(instruction.operands[1].name, instruction.operands[0].size)
    else:
        # TODO: Assuming the register is written in its number format
        # (no alias like lr or pc).
        reil_operand = ReilRegisterOperand('r' + str(int(reil_operand.name[1:]) + 1), reil_operand.size)

    tb.add(tb._builder.gen_stm(reil_operand, addr_reg))


# "Load/store multiple Instructions"
# ============================================================================ #
def _translate_ldm(self, tb, instruction):
    _translate_ldm_stm(self, tb, instruction, True)


def _translate_stm(self, tb, instruction):
    _translate_ldm_stm(self, tb, instruction, False)


def _translate_ldm_stm(self, tb, instruction, load=True):
    # LDM and STM have exactly the same logic except one loads and the
    # other stores It is assumed that the disassembler (for example
    # Capstone) writes the register list in increasing order

    base = self._reg_acc_translator.read(tb, instruction.operands[0])
    reg_list = self._reg_acc_translator.read(tb, instruction.operands[1])

    if instruction.ldm_stm_addr_mode is None:
        instruction.ldm_stm_addr_mode = ARM_LDM_STM_IA  # default mode for load and store

    if load:
        load_store_fn = _load_value
        # Convert stack addressing modes to non-stack addressing modes
        if instruction.ldm_stm_addr_mode in ldm_stack_am_to_non_stack_am:
            instruction.ldm_stm_addr_mode = ldm_stack_am_to_non_stack_am[instruction.ldm_stm_addr_mode]
    else:  # Store
        load_store_fn = _store_value
        if instruction.ldm_stm_addr_mode in stm_stack_am_to_non_stack_am:
            instruction.ldm_stm_addr_mode = stm_stack_am_to_non_stack_am[instruction.ldm_stm_addr_mode]

    pointer = tb.temporal(base.size)
    tb.add(self._builder.gen_str(base, pointer))
    reg_list_size_bytes = ReilImmediateOperand(self._ws.immediate * len(reg_list), base.size)

    if instruction.ldm_stm_addr_mode == ARM_LDM_STM_IA:
        for reg in reg_list:
            load_store_fn(self, tb, pointer, reg)
            pointer = add_to_reg(tb, pointer, self._ws)
    elif instruction.ldm_stm_addr_mode == ARM_LDM_STM_IB:
        for reg in reg_list:
            pointer = add_to_reg(tb, pointer, self._ws)
            load_store_fn(self, tb, pointer, reg)
    elif instruction.ldm_stm_addr_mode == ARM_LDM_STM_DA:
        reg_list.reverse()  # Assuming the registry list was in increasing registry number
        for reg in reg_list:
            load_store_fn(self, tb, pointer, reg)
            pointer = sub_to_reg(tb, pointer, self._ws)
    elif instruction.ldm_stm_addr_mode == ARM_LDM_STM_DB:
        reg_list.reverse()
        for reg in reg_list:
            pointer = sub_to_reg(tb, pointer, self._ws)
            load_store_fn(self, tb, pointer, reg)
    else:
        raise Exception("Unknown addressing mode.")

    # Write-back
    if instruction.operands[0].wb:
        if instruction.ldm_stm_addr_mode == ARM_LDM_STM_IA or instruction.ldm_stm_addr_mode == ARM_LDM_STM_IB:
            tmp = add_to_reg(tb, base, reg_list_size_bytes)
        elif instruction.ldm_stm_addr_mode == ARM_LDM_STM_DA or instruction.ldm_stm_addr_mode == ARM_LDM_STM_DB:
            tmp = sub_to_reg(tb, base, reg_list_size_bytes)
        tb.add(self._builder.gen_str(tmp, base))


def _load_value(self, tb, mem_dir, value):
    tb.add(self._builder.gen_ldm(mem_dir, value))


def _store_value(self, tb, mem_dir, value):
    tb.add(self._builder.gen_stm(value, mem_dir))


def _translate_push_pop(self, tb, instruction, translate_fn):
    # PUSH and POP are equivalent to STM and LDM in FD mode with the SP
    # (and write-back) Instructions are modified to adapt it to the
    # LDM/STM interface

    sp_name = "r13"  # TODO: Use self._sp
    sp_size = instruction.operands[0].reg_list[0][0].size  # Infer it from the registers list
    sp_reg = ArmRegisterOperand(sp_name, sp_size)
    sp_reg.wb = True
    instruction.operands = [sp_reg, instruction.operands[0]]
    instruction.ldm_stm_addr_mode = ARM_LDM_STM_FD
    translate_fn(self, tb, instruction)


def _translate_push(self, tb, instruction):
    _translate_push_pop(self, tb, instruction, _translate_stm)


def _translate_pop(self, tb, instruction):
    _translate_push_pop(self, tb, instruction, _translate_ldm)


dispatcher = {
    'ldr': _translate_ldr,
    'str': _translate_str,
    'ldrb': _translate_ldrb,
    'strb': _translate_strb,
    'ldrh': _translate_ldrh,
    'strh': _translate_strh,
    'ldrd': _translate_ldrd,
    'strd': _translate_strd,
    'ldm': _translate_ldm,
    'stm': _translate_stm,
    'ldm_stm': _translate_ldm_stm,
    'push_pop': _translate_push_pop,
    'push': _translate_push,
    'pop': _translate_pop,
}
