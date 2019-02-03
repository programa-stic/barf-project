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

import logging

import barf.core.smt.smtfunction as smtfunction
import barf.core.smt.smtsymbol as smtsymbol

from barf.core.reil import ReilImmediateOperand
from barf.core.reil import ReilRegisterOperand

logger = logging.getLogger(__name__)


class CodeAnalyzer(object):

    """Implements code analyzer using a SMT solver.
    """

    def __init__(self, solver, translator, arch):

        # A SMT solver instance
        self._solver = solver

        # A SMT translator instance
        self._translator = translator

        # Architecture information of the binary.
        self._arch_info = arch

    def reset(self):
        """Reset current state of the analyzer.
        """
        self._translator.reset()    # It also resets the solver.

    def get_operand_expr(self, operand, mode="post"):
        """Return a smt bit vector that represents a register (architectural or
        temporal).
        """
        if isinstance(operand, ReilRegisterOperand):
            if operand.name in self._arch_info.registers_all:
                # Process architectural registers (eax, ebx, etc.)
                expr = self.get_register_expr(operand.name, mode=mode)
            else:
                # Process temporal registers (t0, t1, etc.)
                var_name = self._get_var_name(operand.name, mode)
                expr = self._translator.make_bitvec(operand.size, var_name)
        elif isinstance(operand, ReilImmediateOperand):
            expr = smtsymbol.Constant(operand.size, operand.immediate)
        else:
            raise Exception("Invalid operand: %s" % str(operand))

        return expr

    def get_register_expr(self, register_name, mode="post"):
        """Return a smt bit vector that represents an architectural (native)
        register.
        """
        reg_info = self._arch_info.alias_mapper.get(register_name, None)

        if reg_info:
            var_base_name, offset = reg_info
        else:
            var_base_name = register_name

        var_name = self._get_var_name(var_base_name, mode)
        var_size = self._arch_info.registers_size[var_base_name]

        ret_val = self._translator.make_bitvec(var_size, var_name)

        if reg_info:
            ret_val = smtfunction.extract(ret_val, offset, self._arch_info.registers_size[register_name])

        return ret_val

    def get_memory_expr(self, address, size, mode="post"):
        """Return a smt bit vector that represents a memory location.
        """
        mem = self.get_memory(mode)

        return smtfunction.concat(8, *reversed([mem[address + i] for i in range(size)]))

    def get_memory(self, mode):
        """Return a smt bit vector that represents a memory location.
        """
        mem = {
            "pre": self._translator.get_memory_init(),
            "post": self._translator.get_memory_curr(),
        }

        return mem[mode]

    def add_instruction(self, reil_instruction):
        """Add an instruction for analysis.
        """
        for expr in self._translator.translate(reil_instruction):
            self._solver.add(expr)

    def add_constraint(self, constraint):
        """Add constraint to the current set of formulas.
        """
        self._solver.add(constraint)

    def check(self):
        """Check if the instructions and restrictions added so far are
        satisfiable.

        """
        return self._solver.check()

    def get_expr_value(self, expr):
        """Get a value for an expression.
        """
        return self._solver.get_value(expr)

    # Auxiliary methods
    # ======================================================================== #
    def _get_var_name(self, register_name, mode):
        """Get variable name for a register considering pre and post mode.
        """
        var_name = {
            "pre": self._translator.get_name_init(register_name),
            "post": self._translator.get_name_curr(register_name),
        }

        return var_name[mode]
