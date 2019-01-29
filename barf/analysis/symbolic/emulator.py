# Copyright (c) 2016, Fundacion Dr. Manuel Sadosky
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

import copy
import logging
import sys

from queue import Queue

from barf.analysis.codeanalyzer import CodeAnalyzer
from barf.core.reil import ReilImmediateOperand
from barf.core.reil import ReilMnemonic
from barf.core.reil import ReilRegisterOperand
from barf.core.reil.container import ReilContainerInvalidAddressError
from barf.core.reil.container import ReilSequenceInvalidAddressError
from barf.core.reil.emulator.cpu import ReilCpu
from barf.core.reil.emulator.emulator import ReilEmulator
from barf.core.reil.emulator.memory import ReilMemoryEx
from barf.core.reil.emulator.tainter import ReilEmulatorTainter
from barf.core.reil.helpers import split_address
from barf.core.reil.helpers import to_reil_address
from barf.core.smt.smtsolver import Z3Solver
from barf.core.smt.smttranslator import SmtTranslator

logger = logging.getLogger("reilsymbolicemulator")
logger.setLevel(logging.DEBUG)
# formatter = logging.Formatter('%(asctime)s - %(name)s - %(levelname)s - %(message)s')
formatter = logging.Formatter('%(message)s')
ch = logging.StreamHandler(sys.stdout)
ch.setLevel(logging.DEBUG)
ch.setFormatter(formatter)
logger.addHandler(ch)


def _save_path(smt_solver, trace, index):
    logger.debug("[+] Saving trace... " + "trace_{:02d}.log".format(index))
    with open("trace_{:02d}.log".format(index), "w") as trace_file:
        for reil_instr, _ in trace:
            line = "{:08x}.{:02x}    {}\n".format(reil_instr.address >> 0x8, reil_instr.address & 0xff, reil_instr)
            trace_file.write(line)

    logger.debug("[+] Saving SMT formulas... " + "trace_{:02d}.smt2".format(index))
    with open("trace_{:02d}.smt2".format(index), "w") as smt_file:
        smt_file.write("{}\n".format(str(smt_solver)))
        smt_file.write("{}\n".format("(check-sat)"))


class SymExecResult(object):

    def __init__(self, arch, initial_state, path, final_state):
        self.__initial_state = initial_state
        self.__path = path
        self.__final_state = final_state

        self.__arch = arch

        self.__smt_solver = None
        self.__smt_translator = None

        self.__code_analyzer = None

        self.__initialize_analyzer()

        self.__setup_solver()

    def query_register(self, register):
        # TODO: This method should return an iterator.

        smt_expr = self.__code_analyzer.get_register_expr(register, mode="pre")
        value = self.__code_analyzer.get_expr_value(smt_expr)

        return value

    def query_memory(self, address, size):
        # TODO: This method should return an iterator.

        smt_expr = self.__code_analyzer.get_memory_expr(address, size, mode="pre")
        value = self.__code_analyzer.get_expr_value(smt_expr)

        return value

    # Auxiliary methods
    # ======================================================================== #
    def __initialize_analyzer(self):
        self.__smt_solver = Z3Solver()

        self.__smt_translator = SmtTranslator(self.__smt_solver, self.__arch.address_size)
        self.__smt_translator.set_arch_alias_mapper(self.__arch.alias_mapper)
        self.__smt_translator.set_arch_registers_size(self.__arch.registers_size)

        self.__code_analyzer = CodeAnalyzer(self.__smt_solver, self.__smt_translator, self.__arch)

    def __setup_solver(self):
        self.__set_initial_state(self.__initial_state)
        self.__add_trace_to_solver(self.__path)
        self.__set_final_state(self.__final_state)

        assert self.__code_analyzer.check() == "sat"

    def __set_initial_state(self, initial_state):
        # Set registers
        for reg, val in initial_state.get_registers().items():
            smt_expr = self.__code_analyzer.get_register_expr(reg, mode="pre")
            self.__code_analyzer.add_constraint(smt_expr == val)

        # Set memory
        for addr, val in initial_state.get_memory().items():
            smt_expr = self.__code_analyzer.get_memory_expr(addr, 1, mode="pre")
            self.__code_analyzer.add_constraint(smt_expr == val)

        # Set constraints
        for constr in initial_state.get_constraints():
            self.__code_analyzer.add_constraint(constr)

    def __set_final_state(self, final_state):
        # Set registers
        for reg, val in final_state.get_registers().items():
            smt_expr = self.__code_analyzer.get_register_expr(reg, mode="post")
            self.__code_analyzer.add_constraint(smt_expr == val)

        # Set memory
        for addr, val in final_state.get_memory().items():
            smt_expr = self.__code_analyzer.get_memory_expr(addr, 1, mode="post")
            self.__code_analyzer.add_constraint(smt_expr == val)

        # Set constraints
        for constr in final_state.get_constraints():
            self.__code_analyzer.add_constraint(constr)

    def __add_trace_to_solver(self, trace):
        for reil_instr, branch_taken in trace:
            if reil_instr.mnemonic == ReilMnemonic.JCC and isinstance(reil_instr.operands[0], ReilRegisterOperand):
                oprnd = reil_instr.operands[0]
                oprnd_expr = self.__code_analyzer.get_operand_expr(oprnd)

                branch_expr = oprnd_expr != 0x0 if branch_taken else oprnd_expr == 0x0

                # logger.debug("    Branch: {:#010x}:{:02x}  {:s} ({}) - {:s}".format(reil_instr.address >> 8, reil_instr.address & 0xff, reil_instr, branch_taken, branch_expr))

                self.__code_analyzer.add_constraint(branch_expr)
            else:
                self.__code_analyzer.add_instruction(reil_instr)


class State(object):

    def __init__(self, arch, mode=None):
        self._registers = {}
        self._memory = {}
        self._constraints = []
        self._mode = mode   # {"initial", "final"}

        self.__arch = arch

        self.__smt_solver = None
        self.__smt_translator = None

        self.__code_analyzer = None

        self.__initialize_analyzer()

    def read_register(self, register):
        return self._registers.get(register, None)

    def write_register(self, register, value):
        self._registers[register] = value

    def query_register(self, register):
        smt_expr = self.__code_analyzer.get_register_expr(register, mode="pre")

        return smt_expr

    def get_registers(self):
        return dict(self._registers)

    def read_memory(self, address, size):
        assert size == 1

        return self._memory.get(address, None)

    def write_memory(self, address, size, value):
        for i in range(0, size):
            self._memory[address + i] = (value >> (i * 8)) & 0xff

    def query_memory(self, address, size):
        smt_expr = self.__code_analyzer.get_memory_expr(address, size, mode="pre")

        return smt_expr

    def get_memory(self):
        return dict(self._memory)

    def add_constraint(self, constraint):
        self._constraints.append(constraint)

    def get_constraints(self):
        return list(self._constraints)

    # Auxiliary methods
    # ======================================================================== #
    def __initialize_analyzer(self):
        self.__smt_solver = Z3Solver()

        self.__smt_translator = SmtTranslator(self.__smt_solver, self.__arch.address_size)
        self.__smt_translator.set_arch_alias_mapper(self.__arch.alias_mapper)
        self.__smt_translator.set_arch_registers_size(self.__arch.registers_size)

        self.__code_analyzer = CodeAnalyzer(self.__smt_solver, self.__smt_translator, self.__arch)


class ReilSymbolicEmulator(object):

    def __init__(self, arch):
        self.__arch = arch

        self.__memory = ReilMemoryEx(self.__arch.address_size)

        self.__tainter = ReilEmulatorTainter(self, arch=self.__arch)

        self.__emulator = ReilEmulator(self.__arch)

        self.__cpu = ReilCpu(self.__memory, arch=self.__arch)

        self.__smt_solver = None
        self.__smt_translator = None

        self.__code_analyzer = None

        self.__initialize_analyzer()

    def find_address(self, container, start=None, end=None, find=None, avoid=None, initial_state=None):
        """Execute instructions.
        """
        # Set initial CPU state.
        self.__set_cpu_state(initial_state)

        # Convert input native addresses to reil addresses.
        start = to_reil_address(start) if start else None
        end = to_reil_address(end) if end else None
        find = to_reil_address(find) if find else None
        avoid = [to_reil_address(addr) for addr in avoid] if avoid else []

        # Load instruction pointer.
        ip = start if start else container[0].address

        execution_state = Queue()

        trace_current = []
        trace_final = []

        self.__fa_process_container(container, find, ip, end, avoid, initial_state, execution_state, trace_current,
                                    trace_final)

        # Only returns when all paths have been visited.
        assert execution_state.empty()

        return trace_final

    def find_state(self, container, start=None, end=None, avoid=None, initial_state=None, final_state=None):
        """Execute instructions.
        """
        self.__set_cpu_state(initial_state)

        # Convert input native addresses to reil addresses.
        start = to_reil_address(start) if start else None
        end = to_reil_address(end) if end else None
        avoid = [to_reil_address(addr) for addr in avoid] if avoid else []

        # Load instruction pointer.
        ip = start if start else container[0].address

        execution_state = Queue()

        trace_current = []
        trace_final = []

        self.__fs_process_container(container, final_state, ip, end, avoid, initial_state, execution_state,
                                    trace_current, trace_final)

        # Only returns when all paths have been visited.
        assert execution_state.empty()

        return trace_final

    # Read/Write methods
    # ======================================================================== #
    def read_operand(self, operand):
        return self.__cpu.read_operand(operand)

    def write_operand(self, operand, value):
        self.__cpu.write_operand(operand, value)

    def read_memory(self, address, size):
        return self.__memory.read(address, size)

    def write_memory(self, address, size, value):
        self.__memory.write(address, size, value)

    # Auxiliary methods.
    # ======================================================================== #
    def __process_branch_direct(self, trace_current, target_addr, avoid, instr, execution_state, initial_state, taken):
        taken_str = "TAKEN" if taken else "NOT TAKEN"

        if target_addr in avoid:
            logger.debug("[+] Avoiding target address ({:s}) : {:#08x}:{:02x}".format(taken_str, target_addr >> 8, target_addr & 0xff))
        else:
            logger.debug("[+] Checking target satisfiability ({:s}) : {:#08x}:{:02x} -> {:#08x}:{:02x}".format(taken_str, instr.address >> 8, instr.address & 0xff, target_addr >> 8, target_addr & 0xff))

            trace_current += [(instr, taken)]

            self.__reset_solver()
            self.__set_initial_state(initial_state)
            self.__add_trace_to_solver(trace_current)

            is_sat = self.__code_analyzer.check()

            logger.debug("[+] Target satisfiable? : {}".format(is_sat == 'sat'))

            if is_sat == 'sat':
                logger.debug("[+] Enqueueing target address ({:s}) : {:#08x}:{:02x}".format(taken_str, target_addr >> 8, target_addr & 0xff))

                execution_state.put((target_addr, trace_current, copy.deepcopy(self.__cpu.registers), copy.deepcopy(self.__cpu.memory)))

    def __process_branch_cond(self, instr, avoid, initial_state, execution_state, trace_current, not_taken_addr):
        # Direct branch (for example: JCC cond, empty, 0x12345678:00)
        if isinstance(instr.operands[2], ReilImmediateOperand):
            # TAKEN
            # ======================================================== #
            trace_current_bck = list(trace_current)

            target_addr = instr.operands[2].immediate

            self.__process_branch_direct(trace_current, target_addr, avoid, instr, execution_state, initial_state,
                                         True)

            # NOT TAKEN
            # ======================================================== #
            trace_current = trace_current_bck

            target_addr = not_taken_addr

            self.__process_branch_direct(trace_current, target_addr, avoid, instr, execution_state, initial_state,
                                         False)
            # ======================================================== #

            next_ip = None

        # Indirect branch (for example: JCC cond, empty, target)
        else:
            raise Exception("Indirect jump not supported yet.")

        return next_ip

    def __process_branch_uncond(self, instr, trace_current, not_taken_addr):
        # TAKEN branch (for example: JCC 0x1, empty, oprnd2).
        if instr.operands[0].immediate != 0x0:
            # Direct branch (for example: JCC 0x1, empty, INTEGER)
            if isinstance(instr.operands[2], ReilImmediateOperand):
                trace_current += [(instr, None)]

                next_ip = self.__cpu.execute(instr)

            # Indirect branch (for example: JCC 0x1, empty, REGISTER)
            else:
                raise Exception("Indirect jump not supported yet.")

        # NOT TAKEN branch (for example: JCC 0x0, empty, oprnd2).
        else:
            next_ip = not_taken_addr

        return next_ip

    def __process_instr(self, instr, avoid, next_addr, initial_state, execution_state, trace_current):
        """Process a REIL instruction.

        Args:
            instr (ReilInstruction): Instruction to process.
            avoid (list): List of addresses to avoid while executing the code.
            next_addr (int): Address of the following instruction.
            initial_state (State): Initial execution state.
            execution_state (Queue): Queue of execution states.
            trace_current (list): Current trace.

        Returns:
            int: Returns the next address to execute.
        """
        # Process branch (JCC oprnd0, empty, oprnd2).
        if instr.mnemonic == ReilMnemonic.JCC:
            not_taken_addr = next_addr
            address, index = split_address(instr.address)

            logger.debug("[+] Processing branch: {:#08x}:{:02x} : {}".format(address, index, instr))

            # Process conditional branch (oprnd0 is a REGISTER).
            if isinstance(instr.operands[0], ReilRegisterOperand):
                next_ip = self.__process_branch_cond(instr, avoid, initial_state, execution_state, trace_current, not_taken_addr)

            # Process unconditional branch (oprnd0 is an INTEGER).
            else:
                next_ip = self.__process_branch_uncond(instr, trace_current, not_taken_addr)

        # Process the rest of the instructions.
        else:
            trace_current += [(instr, None)]

            self.__cpu.execute(instr)

            next_ip = next_addr

        return next_ip

    # find_state's auxiliary methods
    # ======================================================================== #
    def __fs_process_container(self, container, final_state, start, end, avoid, initial_state, execution_state,
                               trace_current, trace_final):
        ip = start

        while ip:
            # Fetch next instruction.
            try:
                instr = container.fetch(ip)
            except ReilContainerInvalidAddressError:
                logger.debug("Exception @ {:#08x}".format(ip))

                raise ReilContainerInvalidAddressError

            # Compute the address of the following instruction to the fetched one.
            try:
                next_addr = container.get_next_address(ip)
            except Exception:
                logger.debug("Exception @ {:#08x}".format(ip))

                # TODO Should this be considered an error?

                raise ReilContainerInvalidAddressError

            # Process instruction
            next_ip = self.__process_instr(instr, avoid, next_addr, initial_state, execution_state, trace_current)

            # Check is final state holds.
            if instr.mnemonic == ReilMnemonic.JCC and isinstance(instr.operands[0], ReilRegisterOperand):
                # TODO Check only when it is necessary.
                self.__reset_solver()
                self.__set_initial_state(initial_state)
                self.__add_trace_to_solver(trace_current)
                self.__set_final_state(final_state)

                is_sat = self.__code_analyzer.check()

                if is_sat == "sat":
                    logger.debug("[+] Final state found!")

                    trace_final.append(list(trace_current))

                    next_ip = None

            # Check termination conditions.
            if end and next_ip and next_ip == end:
                logger.debug("[+] End address found!")

                next_ip = None

            # Update instruction pointer.
            ip = next_ip if next_ip else None

            while not ip:
                if not execution_state.empty():
                    # Pop next execution state.
                    ip, trace_current, registers, memory = execution_state.get()

                    if split_address(ip)[1] == 0x0:
                        logger.debug("[+] Popping execution state @ {:#x} (INTER)".format(ip))
                    else:
                        logger.debug("[+] Popping execution state @ {:#x} (INTRA)".format(ip))

                    # Setup cpu and memory.
                    self.__cpu.registers = registers
                    self.__cpu.memory = memory

                    logger.debug("[+] Next address: {:#08x}:{:02x}".format(ip >> 8, ip & 0xff))
                else:
                    logger.debug("[+] No more paths to explore! Exiting...")
                    break

                # Check termination conditions (AGAIN...).
                if end and ip == end:
                    logger.debug("[+] End address found!")

                    ip = None

    # find_address's auxiliary methods
    # ======================================================================== #
    def __fa_process_sequence(self, sequence, avoid, initial_state, execution_state, trace_current, next_addr):
        """Process a REIL sequence.

        Args:
            sequence (ReilSequence): A REIL sequence to process.
            avoid (list): List of address to avoid.
            initial_state: Initial state.
            execution_state: Execution state queue.
            trace_current (list): Current trace.
            next_addr: Address of the next instruction following the current one.

        Returns:
            Returns the next instruction to execute in case there is one, otherwise returns None.
        """
        # TODO: Process execution intra states.

        ip = sequence.address
        next_ip = None

        while ip:
            # Fetch next instruction in the sequence.
            try:
                instr = sequence.fetch(ip)
            except ReilSequenceInvalidAddressError:
                # At this point, ip should be a native instruction address, therefore
                # the index should be zero.
                assert split_address(ip)[1] == 0x0
                next_ip = ip
                break

            try:
                target_addr = sequence.get_next_address(ip)
            except ReilSequenceInvalidAddressError:
                # We reached the end of the sequence. Execution continues on the next native instruction
                # (it's a REIL address).
                target_addr = next_addr

            next_ip = self.__process_instr(instr, avoid, target_addr, initial_state, execution_state, trace_current)

            # Update instruction pointer.
            try:
                ip = next_ip if next_ip else sequence.get_next_address(ip)
            except ReilSequenceInvalidAddressError:
                break

        return next_ip

    def __fa_process_container(self, container, find, start, end, avoid, initial_state, execution_state, trace_current,
                               trace_final):
        """Process a REIL container.

        Args:
            avoid (list): List of addresses to avoid while executing the code.
            container (ReilContainer): REIL container to execute.
            end (int): End address.
            execution_state (Queue): Queue of execution states.
            find (int): Address to find.
            initial_state (State): Initial state.
            start (int): Start address.
            trace_current:
            trace_final:
        """
        ip = start

        while ip:
            # NOTE *ip* and *next_addr* variables can be, independently, either intra
            # or inter addresses.

            # Fetch next instruction.
            try:
                instr = container.fetch(ip)
            except ReilContainerInvalidAddressError:
                logger.debug("Exception @ {:#08x}".format(ip))

                raise ReilContainerInvalidAddressError

            # Compute the address of the following instruction to the fetched one.
            try:
                next_addr = container.get_next_address(ip)
            except Exception:
                logger.debug("Exception @ {:#08x}".format(ip))

                # TODO Should this be considered an error?

                raise ReilContainerInvalidAddressError

            # Process the instruction.
            next_ip = self.__process_instr(instr, avoid, next_addr, initial_state, execution_state, trace_current)

            # # ====================================================================================================== #
            # # NOTE This is an attempt to separate intra and inter instruction
            # # addresses processing. Here, *ip* and *next_addr* are always inter
            # # instruction addresses.
            #
            # assert split_address(ip)[1] == 0x0
            #
            # # Compute the address of the following instruction to the fetched one.
            # try:
            #     seq = container.fetch_sequence(ip)
            # except ReilContainerInvalidAddressError:
            #     logger.debug("Exception @ {:#08x}".format(ip))
            #
            #     raise ReilContainerInvalidAddressError
            #
            # # Fetch next instruction address.
            # try:
            #     next_addr = container.get_next_address(ip + len(seq))
            # except Exception:
            #     logger.debug("Exception @ {:#08x}".format(ip))
            #
            #     # TODO Should this be considered an error?
            #
            #     raise ReilContainerInvalidAddressError
            #
            # next_ip = self.__process_sequence(seq, avoid, initial_state, execution_state, trace_current, next_addr)
            #
            # if next_ip:
            #     assert split_address(next_ip)[1] == 0x0
            #
            # # ====================================================================================================== #

            # Check termination conditions.
            if find and next_ip and next_ip == find:
                logger.debug("[+] Find address found!")

                trace_final.append(list(trace_current))

                next_ip = None

            if end and next_ip and next_ip == end:
                logger.debug("[+] End address found!")

                next_ip = None

            # Update instruction pointer.
            ip = next_ip if next_ip else None

            while not ip:
                if not execution_state.empty():
                    # Pop next execution state.
                    ip, trace_current, registers, memory = execution_state.get()

                    if split_address(ip)[1] == 0x0:
                        logger.debug("[+] Popping execution state @ {:#x} (INTER)".format(ip))
                    else:
                        logger.debug("[+] Popping execution state @ {:#x} (INTRA)".format(ip))

                    # Setup cpu and memory.
                    self.__cpu.registers = registers
                    self.__cpu.memory = memory

                    logger.debug("[+] Next address: {:#08x}:{:02x}".format(ip >> 8, ip & 0xff))
                else:
                    logger.debug("[+] No more paths to explore! Exiting...")

                    break

                # Check termination conditions (AGAIN...).
                if find and ip == find:
                    logger.debug("[+] Find address found!")

                    trace_final.append(list(trace_current))

                    ip = None

                if end and ip == end:
                    logger.debug("[+] End address found!")

                    ip = None

    # Auxiliary methods
    # ======================================================================== #
    def __initialize_analyzer(self):
        self.__smt_solver = Z3Solver()

        self.__smt_translator = SmtTranslator(self.__smt_solver, self.__arch.address_size)
        self.__smt_translator.set_arch_alias_mapper(self.__arch.alias_mapper)
        self.__smt_translator.set_arch_registers_size(self.__arch.registers_size)

        self.__code_analyzer = CodeAnalyzer(self.__smt_solver, self.__smt_translator, self.__arch)

    def __reset_solver(self):
        self.__code_analyzer.reset()

    def __set_cpu_state(self, state):
        # Set registers
        for reg, val in state.get_registers().items():
            self.__cpu.registers[reg] = val

        # Set memory
        for addr, val in state.get_memory().items():
            self.__cpu.write_memory(addr, 1, val)

    def __set_initial_state(self, initial_state):
        # Set registers
        for reg, val in initial_state.get_registers().items():
            smt_expr = self.__code_analyzer.get_register_expr(reg, mode="pre")
            self.__code_analyzer.add_constraint(smt_expr == val)

        # Set memory
        for addr, val in initial_state.get_memory().items():
            smt_expr = self.__code_analyzer.get_memory_expr(addr, 1, mode="pre")
            self.__code_analyzer.add_constraint(smt_expr == val)

        # Set constraints
        for constr in initial_state.get_constraints():
            self.__code_analyzer.add_constraint(constr)

    def __set_final_state(self, final_state):
        # Set registers
        for reg, val in final_state.get_registers().items():
            smt_expr = self.__code_analyzer.get_register_expr(reg, mode="post")
            self.__code_analyzer.add_constraint(smt_expr == val)

        # Set memory
        for addr, val in final_state.get_memory().items():
            smt_expr = self.__code_analyzer.get_memory_expr(addr, 1, mode="post")
            self.__code_analyzer.add_constraint(smt_expr == val)

        # Set constraints
        for constr in final_state.get_constraints():
            self.__code_analyzer.add_constraint(constr)

    def __add_trace_to_solver(self, trace):
        for reil_instr, branch_taken in trace:
            if reil_instr.mnemonic == ReilMnemonic.JCC and isinstance(reil_instr.operands[0], ReilRegisterOperand):
                oprnd = reil_instr.operands[0]
                oprnd_expr = self.__code_analyzer.get_operand_expr(oprnd)

                branch_expr = oprnd_expr != 0x0 if branch_taken else oprnd_expr == 0x0

                # logger.debug("    Branch: {:#010x}:{:02x}  {:s} ({}) - {:s}".format(reil_instr.address >> 8, reil_instr.address & 0xff, reil_instr, branch_taken, branch_expr))

                self.__code_analyzer.add_constraint(branch_expr)
            else:
                self.__code_analyzer.add_instruction(reil_instr)
