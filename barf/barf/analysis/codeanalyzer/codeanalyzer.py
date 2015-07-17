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

import barf.core.smt.smtlibv2 as smtlibv2

from barf.core.reil import ReilMnemonic
from barf.core.reil import ReilRegisterOperand
from barf.core.reil import ReilImmediateOperand

class GenericRegister(object):

    """Generic register representation for code analyzer.
    """

    def __init__(self, name, size=None, value=None):

        # Name, size and value of the register
        self._name = name
        self._size = size
        self._value = value

    @property
    def name(self):
        """Get register name.
        """
        return self._name

    @name.setter
    def name(self, value):
        """Set register name.
        """
        self._name = value

    @property
    def size(self):
        """Get register size.
        """
        return self._size

    @size.setter
    def size(self, value):
        """Get register size.
        """
        self._size = value

    @property
    def value(self):
        """Get register value.
        """
        return self._value

    @value.setter
    def value(self, value):
        """Set register value.
        """
        self._value = value

    def __str__(self):
        return "%s : 0x%08x" % (self._name, self._value)


class GenericFlag(object):

    """Generic flag representation for code analyzer.
    """

    def __init__(self, name, value=None):

        # Name and value of the flag
        self._name = name
        self._value = value

    @property
    def name(self):
        """Get flag name.
        """
        return self._name

    @name.setter
    def name(self, value):
        """Set flag name.
        """
        self._name = value

    @property
    def value(self):
        """Get flag value.
        """
        return self._value

    @value.setter
    def value(self, value):
        """Set flag name.
        """
        self._value = value

    def __str__(self):
        return "%s : 0x%08x" % (self._name, self._value)


class GenericContext(object):

    """Generic context for code analyzer.
    """

    def __init__(self, registers, flags, memory):

        # Set of registers.
        self._registers = registers

        # Set of flags.
        self._flags = flags

        # A dictionary-based represetation of memory.
        self._memory = memory

    @property
    def registers(self):
        """Get context's registers.
        """
        return self._registers

    @registers.setter
    def registers(self, value):
        """Set context's registers.
        """
        self._registers = value

    @property
    def flags(self):
        """Get context's flags.
        """
        return self._flags

    @flags.setter
    def flags(self, value):
        """Set context's flags.
        """
        self._flags = value

    @property
    def memory(self):
        """Get context's memory.
        """
        return self._memory

    @memory.setter
    def memory(self, value):
        """Set context's memory.
        """
        self._memory = value

    def __str__(self):
        string = "[+] Context :\n"

        string += "    * Registers :\n"
        for _, gen_reg in self._registers.items():
            string += "        " + str(gen_reg) + "\n"

        string += "    * Flags :\n"
        for _, gen_flag in self._flags.items():
            string += "        " + str(gen_flag) + "\n"

        string += "    * Memory :\n"
        for addr, value in self._memory.items():
            string += "        0x%08x : 0x%08x" % (addr, value) + "\n"

        return string


class CodeAnalyzer(object):

    """Implements code analyzer using a SMT solver.
    """

    def __init__(self, solver, translator, arch):

        # A SMT solver instance
        self._solver = solver

        # A SMT translator instance
        self._translator = translator

        # A context (registers and memory)
        self._context = None

        self.read_addrs = []
        self.write_addrs = []

        self._arch_info = arch

    def set_context(self, context):
        """Set context for the SMT solver.
        """
        self._context = context

        # Add each register and its value to the context of the SMT
        # solver as an assertion.
        for _, gen_reg in self._context.registers.items():
            smt_reg = self._solver.mkBitVec(gen_reg.size, self._translator.get_init_name(gen_reg.name))
            self._solver.add(smt_reg == gen_reg.value)

        # Add each flag and its value to the context of the SMT solver
        # as an assertion.
        # TODO: Flag size should be 1 bit.
        for _, gen_flag in self._context.flags.items():
            smt_flag = self._solver.mkBitVec(32, self._translator.get_init_name(gen_flag.name))

            self._solver.add(smt_flag == gen_flag.value)

        # Add each memory location and its content to the SMT solver
        # as an assetion.
        mem = self._translator.get_memory()

        for addr, value in self._context.memory.items():
            self._solver.add(mem[addr] == value)

    def get_context(self):
        """Get context from the SMT solver.
        """
        # Get final values from the SMT solver for the registers set in
        # the initial context.
        registers = {}

        for reg_name, gen_reg in self._context.registers.items():
            value = self._solver.getvaluebyname(self._translator.get_curr_name(reg_name))
            registers[reg_name] = GenericRegister(reg_name, gen_reg.size, value)

        # Get final values from the SMT solver for the flags set in the
        # initial context.
        # TODO: Flag size should be 1 bit.
        flags = {}

        for flag_name, _ in self._context.flags.items():
            value = self._solver.getvaluebyname(self._translator.get_curr_name(flag_name))
            flags[flag_name] = GenericFlag(flag_name, value)

        # Get final values from the SMT solver for the memory locations
        # set in the initial context.
        memory = {}

        mem = self._translator.get_memory()

        for addr, _ in self._context.memory.items():
            value = self._solver.getvalue(mem[addr])
            memory[addr] = value

        return GenericContext(registers, flags, memory)

    def check_path_satisfiability(self, path, start_address, verbose=False):
        """Check satisfiability of a basic block path.
        """
        self._solver.reset()

        _memory_access = []

        start_instr_found = False

        # Traverse basic blocks, translate its instructions to SMT
        # expressions and add them as assertions.
        for bb_curr, bb_next in zip(path[:-1], path[1:]):
            if verbose:
                print("\n[+] BB @ 0x%08x :" % bb_curr.address)

            # For each dual instruction...
            for dinstr in bb_curr.instrs:
                # If the start instruction have not been found, keep
                # looking...
                if not start_instr_found:
                    if dinstr.address == start_address:
                        start_instr_found = True
                    else:
                        continue

                if verbose:
                    print("    0x%08x : %-30s" % (dinstr.address, dinstr.asm_instr))

                # For each REIL instruction...
                for instr in dinstr.ir_instrs:
                    # Keep track of memory addresses access for STORE.
                    if instr.mnemonic == ReilMnemonic.STM:
                        if isinstance(instr.operands[2], ReilRegisterOperand):
                            smt_mem_addr = self._solver.mkBitVec(32, self._translator.get_curr_name(instr.operands[2].name))
                        else:
                            smt_mem_addr = smtlibv2.BitVec(32, "#x%08x" % instr.operands[2].immediate)

                        _memory_access.append(smt_mem_addr)

                    # Keep track of memory addresses access for LOAD.
                    if instr.mnemonic == ReilMnemonic.LDM:
                        if isinstance(instr.operands[0], ReilRegisterOperand):
                            smt_mem_addr = self._solver.mkBitVec(32, self._translator.get_curr_name(instr.operands[0].name))
                        else:
                            smt_mem_addr = smtlibv2.BitVec(32, "#x%08x" % instr.operands[0].immediate)

                        _memory_access.append(smt_mem_addr)

                    if instr.mnemonic == ReilMnemonic.JCC:
                        # Check that the JCC is the last instruction of
                        # the basic block (skip CALL instructions.)
                        if dinstr.address + dinstr.asm_instr.size - 1 != bb_curr.end_address:
                            continue

                        # Make sure branch target address from current
                        # basic block is the start address of the next.
                        assert(bb_curr.taken_branch == bb_next.address or
                            bb_curr.not_taken_branch == bb_next.address or
                            bb_curr.direct_branch == bb_next.address)

                        # Set jump condition accordingly.
                        if bb_curr.taken_branch == bb_next.address:
                            branch_cond_goal = 0x1
                        elif bb_curr.not_taken_branch == bb_next.address:
                            branch_cond_goal = 0x0
                        else:
                            continue

                        # Add branch condition goal contraint.
                        branch_cond_curr = instr.operands[0]

                        if isinstance(branch_cond_curr, ReilRegisterOperand):
                            branch_cond_smt = self._solver.mkBitVec(32, self._translator.get_curr_name(branch_cond_curr.name))
                        else:
                            branch_cond_smt = smtlibv2.BitVec(32, "#x%08x" % branch_cond_curr.immediate)

                        goal = branch_cond_smt == branch_cond_goal

                        # Add jump condition constraint to the SMT s
                        # solver.
                        self._solver.add(goal)

                        if verbose:
                            print("                   %-25s" % (instr))
                            print("")
                            print("[+] BB take jump contraint : %s" % goal)

                        # The jump was the last instruction within the
                        # current basic block. End this iteration and
                        # start next one.
                        break

                    # Translate REIL instruction to SMT expression.
                    trans = self._translator.translate(instr)

                    # Add SMT expression to solver.
                    # if trans is not None:
                    for smt_expr in trans:
                        self._solver.add(smt_expr)

                    if verbose:
                        #print("                   %-35s > %-35s" % (instr, trans))
                        print("                   %-35s" % (instr))

            if verbose:
                print("\n" + "-" * 80 + "\n")

        # Check satisfiability.
        is_sat = self._solver.check() == 'sat'

        return is_sat

    def reset(self, full=False):
        """Reset current state of the analyzer.
        """
        self._solver.reset(full)

        if full:
            self._translator.reset()

            self.read_addrs = []
            self.write_addrs = []

    # ======================================================================== #
    def set_arch_info(self, arch_info):
        self._arch_info = arch_info

    def get_operand_var(self, operand):
        return self._translator._translate_src_oprnd(operand)

    def get_operand_expr(self, operand, mode="post"):
        if isinstance(operand, ReilRegisterOperand):
            if operand.name in self._arch_info.registers_flags:
                expr = self.get_register_expr(operand.name, mode=mode)
            else:
                expr = self.get_tmp_register_expr(
                        operand.name, operand.size, mode=mode)
        elif isinstance(operand, ReilRegisterOperand):
            expr = self.get_immediate_expr(operand.immediate, operand.size)
        else:
            raise Exception("Invalid operand: %s" % str(operand))

        return expr

    def get_register_expr(self, register_name, mode="post"):
        """Return a smt bit vector that represents a register.
        """
        reg_info = self._arch_info.alias_mapper.get(register_name, None)

        if reg_info:
            var_base_name, offset = reg_info

            if mode == "pre":
                var_name = self._translator.get_init_name(var_base_name)
            elif mode == "post":
                var_name = self._translator.get_curr_name(var_base_name)
            else:
                raise Exception()

            var_size = self._arch_info.registers_size[var_base_name]

            ret_val = self._translator._solver.mkBitVec(var_size, var_name)
            ret_val = smtlibv2.EXTRACT(
                ret_val,
                offset,
                self._arch_info.registers_size[register_name]
            )
        else:
            if mode == "pre":
                var_name = self._translator.get_init_name(register_name)
            elif mode == "post":
                var_name = self._translator.get_curr_name(register_name)
            else:
                raise Exception()

            var_size = self._arch_info.registers_size[register_name]

            ret_val = self._solver.mkBitVec(var_size, var_name)

        return ret_val

    def get_tmp_register_expr(self, register_name, register_size, mode="post"):
        """Return a smt bit vector that represents a register.
        """
        if mode == "pre":
            var_name = self._translator.get_init_name(register_name)
        elif mode == "post":
            var_name = self._translator.get_curr_name(register_name)
        else:
            raise Exception()

        var_size = register_size

        ret_val = self._solver.mkBitVec(var_size, var_name)

        return ret_val

    def get_memory_expr(self, address, size, mode="post"):
        """Return a smt bit vector that represents a memory location.
        """
        if mode == "pre":
            mem = self._translator.get_memory_init()
        elif mode == "post":
            mem = self._translator.get_memory()
        else:
            raise Exception()

        bytes_exprs = []

        for index in xrange(0, size):
            bytes_exprs.append(mem[address + index])

        ret_val = smtlibv2.CONCAT(8, *reversed(bytes_exprs))

        return ret_val

    def get_immediate_expr(self, immediate, size):
        """Return a smt bit vector that represents an immediate value.
        """
        return self._translator.translate_immediate_oprnd(ReilImmediateOperand(immediate, size))

    def get_memory(self, mode):
        """Return a smt bit vector that represents a memory location.
        """
        if mode == "pre":
            mem = self._translator.get_memory_init()
        elif mode == "post":
            mem = self._translator.get_memory()

        return mem

    def add_constraint(self, contraint):
        self._solver.add(contraint)

    def add_instruction(self, reil_instruction):
        """Add an instruction for analysis.
        """
        if reil_instruction.mnemonic == ReilMnemonic.LDM:
            addr = self._translator.convert_to_bitvec(reil_instruction.operands[0])

            self.read_addrs.append(addr)

        if reil_instruction.mnemonic == ReilMnemonic.STM:
            addr = self._translator.convert_to_bitvec(reil_instruction.operands[2])

            self.write_addrs.append(addr)

        smt_exprs = self._translator.translate(reil_instruction)

        #if not smt_form is None:
        for smt_expr in smt_exprs:
            self._solver.add(smt_expr)

    def check(self):
        """Check if the instruction and restrictions added so far are
        satisfiable.

        """
        return self._solver.check()

    def check_constraint(self, constraint):
        """Check if the instruction and restrictions added so far are
        satisfiable.

        """
        self._solver.push()

        self._solver.add(constraint)

        is_sat = self._solver.check()

        self._solver.pop()

        return is_sat

    def check_constraints(self, constraints):
        """Check if the instruction and restrictions added so far are
        satisfiable.

        """
        self._solver.push()

        for constraint in constraints:
            self._solver.add(constraint)

        is_sat = self._solver.check()

        self._solver.pop()

        return is_sat

    def set_precondition(self, condition):
        """Add a precondition to the analyzer.
        """
        self._solver.add(condition)

    def set_preconditions(self, conditions):
        """Add preconditions to the analyzer.
        """
        for cond in conditions:
            self._solver.add(cond)

    def set_postcondition(self, condition):
        """Add a postcondition to the analyzer.
        """
        self._solver.add(condition)

    def set_postconditions(self, conditions):
        """Add a postcondition to the analyzer.
        """
        for cond in conditions:
            self._solver.add(cond)

    def get_expr_value(self, expr):
        """Get a value for an expression.
        """
        return self._solver.getvalue(expr)
