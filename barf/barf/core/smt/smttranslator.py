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

"""
This module contains all the classes needed to translate form REIL to
SMTLIB language.

SmtTranslator
-------------

This class provides functionalities for REIL to SMT expressions
translation. The main method is **translate**, which takes a instruction
as a parameter. It interacts with a SMT solver (through the **smtlibv2**
module). When an instruction is translated, this translation is reflected
in the state of the SMT solver (this means, each expression is asserted
in the current context of SMT solver). Also, the translation is return
in form of a expression of BitVect. For example, the translation of
"ADD t0 (32), t1 (32), t2 (32)" returns the SMT expression
"(= t2_0 (bvadd t0_1 t1_0))". It also send the following commands to the
solver:

(declare-fun t0_0 () (_ BitVec 32))
(declare-fun t1_0 () (_ BitVec 32))
(declare-fun t2_0 () (_ BitVec 32))
(assert (= t2_0 (bvadd t1_0 t2_0)))

"""
import logging
import traceback

import barf.core.smt.smtlibv2 as smtlibv2

from barf.core.reil.reil import ReilImmediateOperand
from barf.core.reil.reil import ReilMnemonic
from barf.core.reil.reil import ReilRegisterOperand
from barf.utils.utils import VariableNamer

logger = logging.getLogger(__name__)

class SmtTranslator(object):

    """SMT Translator. This class provides functionalities for REIL to
    SMT expressions translation.

    """

    def __init__(self, solver, address_size):

        # A SMT solver instance.
        self._solver = solver

        # Memory address size of the underlying architecture.
        self._address_size = address_size

        # A SMT array that represents the memory.
        self._mem = self._solver.mkArray(address_size, "MEM_0")
        self._mem_instance = 0

        self._mem_init = self._solver.mkArrayNew(address_size, "MEM_0")

        # A variable name mapper maps variable names to its current
        # 'version' of the variable, e.i., 'eax' -> 'eax_3'
        self._var_name_mappers = {}

        self._arch_regs_size = {}
        self._arch_alias_mapper = {}

        # Intructions translators (from REIL to SMT expressions)
        self._instr_translators = {
            # Arithmetic Instructions
            ReilMnemonic.ADD : self._translate_add,
            ReilMnemonic.SUB : self._translate_sub,
            ReilMnemonic.MUL : self._translate_mul,
            ReilMnemonic.DIV : self._translate_div,
            ReilMnemonic.SDIV : self._translate_sdiv,
            ReilMnemonic.MOD : self._translate_mod,
            ReilMnemonic.SMOD : self._translate_smod,
            ReilMnemonic.BSH : self._translate_bsh,

            # Bitwise Instructions
            ReilMnemonic.AND : self._translate_and,
            ReilMnemonic.OR  : self._translate_or,
            ReilMnemonic.XOR : self._translate_xor,

            # Data Transfer Instructions
            ReilMnemonic.LDM : self._translate_ldm,
            ReilMnemonic.STM : self._translate_stm,
            ReilMnemonic.STR : self._translate_str,

            # Conditional Instructions
            ReilMnemonic.BISZ : self._translate_bisz,
            ReilMnemonic.JCC  : self._translate_jcc,

            # Other Instructions
            ReilMnemonic.UNDEF : self._translate_undef,
            ReilMnemonic.UNKN  : self._translate_unkn,
            ReilMnemonic.NOP   : self._translate_nop,

            # Ad hoc Instructions
            ReilMnemonic.RET : self._translate_ret,

            # Extensions
            ReilMnemonic.SEXT : self._translate_sext,
        }

    def translate(self, instr):
        """Return the SMT representation of a REIL instruction.
        """
        try:
            translator = self._instr_translators[instr.mnemonic]

            return translator(*instr.operands)
        except:
            error_msg = "Failed to translate instruction: %s"

            logger.error(error_msg, instr, exc_info=True)

            raise

    def get_init_name(self, name):
        """Get initial name of symbol.
        """
        self._register_name(name)

        return self._var_name_mappers[name].get_init()

    def get_curr_name(self, name):
        """Get current name of symbol.
        """
        self._register_name(name)

        return self._var_name_mappers[name].get_current()

    def get_memory(self):
        """Get SMT memory representation.
        """
        return self._mem

    def get_memory_init(self):
        """Get SMT memory representation.
        """
        return self._mem_init

    def reset(self):
        """Reset internal state.
        """
        self._solver.reset(full=True)

        # Memory versioning.
        self._mem = self._solver.mkArray(self._address_size, "MEM_0")
        self._mem_instance = 0

        self._mem_init = self._solver.mkArrayNew(self._address_size, "MEM_0")

        self._var_name_mappers = {}

    # Auxiliary functions
    # ======================================================================== #
    def _register_name(self, name):
        """Get register name.
        """
        if name not in self._var_name_mappers:
            self._var_name_mappers[name] = VariableNamer(name)

    def _get_var_name(self, name, fresh=False):
        """Get variable name.
        """
        if name not in self._var_name_mappers:
            self._var_name_mappers[name] = VariableNamer(name)

        if fresh:
            var_name = self._var_name_mappers[name].get_next()
        else:
            var_name = self._var_name_mappers[name].get_current()

        return var_name

    def _translate_src_oprnd(self, operand):
        """Translate source operand to a SMT expression.
        """
        if isinstance(operand, ReilRegisterOperand):

            ret_val = self._translate_src_register_oprnd(operand)

        elif isinstance(operand, ReilImmediateOperand):

            ret_val = self.translate_immediate_oprnd(operand)

        else:

            self._raise_invalid_type_oprnd(operand)

        return ret_val

    def _translate_dst_oprnd(self, operand):
        """Translate destination operand to a SMT expression.
        """
        if isinstance(operand, ReilRegisterOperand):

            ret_val, parent_reg_constrs = self._translate_dst_register_oprnd(operand)

        else:

            self._raise_invalid_type_oprnd(operand)

        return ret_val, parent_reg_constrs

    def _translate_src_register_oprnd(self, operand):
        """Translate source resgister operand to SMT expr.
        """
        reg_info = self._arch_alias_mapper.get(operand.name, None)

        if reg_info:
            var_base_name, offset = reg_info

            var_name = self._get_var_name(var_base_name)
            var_size = self._arch_regs_size[var_base_name]

            ret_val = self._solver.mkBitVec(var_size, var_name)
            ret_val = smtlibv2.EXTRACT(ret_val, offset, operand.size)
        else:
            var_name = self._get_var_name(operand.name)
            ret_val = self._solver.mkBitVec(operand.size, var_name)

        return ret_val

    def _translate_dst_register_oprnd(self, operand):
        """Translate destination resgister operand to SMT expr.
        """
        reg_info = self._arch_alias_mapper.get(operand.name, None)

        if reg_info:
            var_base_name, offset = reg_info

            old_var_name = self._get_var_name(var_base_name, fresh=False)

            var_name = self._get_var_name(var_base_name, fresh=True)
            var_size = self._arch_regs_size[var_base_name]

            ret_val = self._solver.mkBitVec(var_size, var_name)

            ret_val_cpy = ret_val

            ret_val = smtlibv2.EXTRACT(ret_val, offset, operand.size)

            old_ret_val = self._solver.mkBitVec(var_size, old_var_name)

            constrs = []

            if offset > 0 and offset < var_size - 1:
                lower_expr_1 = smtlibv2.EXTRACT(ret_val_cpy, 0, offset)
                lower_expr_2 = smtlibv2.EXTRACT(old_ret_val, 0, offset)

                constrs += [lower_expr_1 == lower_expr_2]

                upper_expr_1 = smtlibv2.EXTRACT(ret_val_cpy, offset+operand.size, var_size - offset - operand.size)
                upper_expr_2 = smtlibv2.EXTRACT(old_ret_val, offset+operand.size, var_size - offset - operand.size)

                constrs += [upper_expr_1 == upper_expr_2]
            elif offset == 0:
                upper_expr_1 = smtlibv2.EXTRACT(ret_val_cpy, offset+operand.size, var_size - offset - operand.size)
                upper_expr_2 = smtlibv2.EXTRACT(old_ret_val, offset+operand.size, var_size - offset - operand.size)

                constrs += [upper_expr_1 == upper_expr_2]
            elif offset == var_size-1:
                lower_expr_1 = smtlibv2.EXTRACT(ret_val_cpy, 0, offset)
                lower_expr_2 = smtlibv2.EXTRACT(old_ret_val, 0, offset)

                constrs += [lower_expr_1 == lower_expr_2]

            parent_reg_constrs = constrs
        else:
            var_name = self._get_var_name(operand.name, fresh=True)
            ret_val = self._solver.mkBitVec(operand.size, var_name)

            parent_reg_constrs = None

        return ret_val, parent_reg_constrs

    def translate_immediate_oprnd(self, operand):
        """Translate REIL immediate operand to SMT.
        """
        if operand.size >= 4:
            fmt = "#x%" + "%0003d" % (operand.size / 4) + "x"
        else:
            fmt = "#b%1d"

        return smtlibv2.BitVec(operand.size, fmt % operand.immediate)

    def _raise_invalid_type_oprnd(self, operand):
        """Raise exception for invalid operand type.
        """
        msg_fmt = "Invalid source type: {0} ({1})"

        raise Exception(msg_fmt.format(str(operand), type(operand)))

    def convert_to_bitvec(self, operand):
        """Convert operand to a BitVec
        """
        if isinstance(operand, ReilRegisterOperand):

            bitvec = self._solver.mkBitVec(
                operand.size,
                self.get_curr_name(operand.name)
            )

        elif isinstance(operand, ReilImmediateOperand):

            bitvec = self.translate_immediate_oprnd(operand)

        else:

            self._raise_invalid_type_oprnd(operand)

        return bitvec

    def set_arch_alias_mapper(self, alias_mapper):
        """Set native register alias mapper.

        This is necessary as some architecture has register alias. For
        example, in Intel x86 (32 bits), *ax* refers to the lower half
        of the *eax* register, so when *ax* is modified so it is *eax*.
        Then, this alias_mapper is a dictionary where its keys are
        registers (names, only) and each associated value is a tuple
        of the form (base register name, offset).
        This information is used to modified the correct register at
        the correct location (within the register) when a register alias
        value is changed.

        """
        self._arch_alias_mapper = alias_mapper

    def set_arch_registers_size(self, registers_size):
        """Set registers.
        """
        self._arch_regs_size = registers_size

    # Arithmetic Instructions
    # ======================================================================== #
    def _translate_add(self, oprnd1, oprnd2, oprnd3):
        """Return a formula representation of an ADD instruction.
        """
        assert oprnd1.size and oprnd2.size and oprnd3.size
        assert oprnd1.size == oprnd2.size

        op1_var = self._translate_src_oprnd(oprnd1)
        op2_var = self._translate_src_oprnd(oprnd2)
        op3_var, parent_reg_constrs = self._translate_dst_oprnd(oprnd3)

        if oprnd3.size > oprnd1.size:
            op1_var_zx = smtlibv2.ZEXTEND(op1_var, oprnd3.size)
            op2_var_zx = smtlibv2.ZEXTEND(op2_var, oprnd3.size)

            expr = (op3_var == (op1_var_zx + op2_var_zx))
        elif oprnd3.size < oprnd1.size:
            sum_extract = smtlibv2.EXTRACT(op1_var + op2_var, 0, oprnd3.size)

            expr = (op3_var == sum_extract)
        else:
            expr = (op3_var == (op1_var + op2_var))

        rv = [expr]

        if parent_reg_constrs:
            rv += parent_reg_constrs

        return rv

    def _translate_sub(self, oprnd1, oprnd2, oprnd3):
        """Return a formula representation of an SUB instruction.
        """
        assert oprnd1.size and oprnd2.size and oprnd3.size
        assert oprnd1.size == oprnd2.size

        op1_var = self._translate_src_oprnd(oprnd1)
        op2_var = self._translate_src_oprnd(oprnd2)
        op3_var, parent_reg_constrs = self._translate_dst_oprnd(oprnd3)

        if oprnd3.size > oprnd1.size:
            op1_var_zx = smtlibv2.ZEXTEND(op1_var, oprnd3.size)
            op2_var_zx = smtlibv2.ZEXTEND(op2_var, oprnd3.size)

            expr = (op3_var == (op1_var_zx - op2_var_zx))
        elif oprnd3.size < oprnd1.size:
            sub_extract = smtlibv2.EXTRACT(op1_var - op2_var, 0, oprnd3.size)

            expr = (op3_var == sub_extract)
        else:
            expr = (op3_var == (op1_var - op2_var))

        rv = [expr]

        if parent_reg_constrs:
            rv += parent_reg_constrs

        return rv

    def _translate_mul(self, oprnd1, oprnd2, oprnd3):
        """Return a formula representation of an MUL instruction.
        """
        assert oprnd1.size and oprnd2.size and oprnd3.size
        assert oprnd1.size == oprnd2.size

        op1_var = self._translate_src_oprnd(oprnd1)
        op2_var = self._translate_src_oprnd(oprnd2)
        op3_var, parent_reg_constrs = self._translate_dst_oprnd(oprnd3)

        if oprnd3.size > oprnd1.size:
            op1_var_zx = smtlibv2.ZEXTEND(op1_var, oprnd3.size)
            op2_var_zx = smtlibv2.ZEXTEND(op2_var, oprnd3.size)

            expr = (op3_var == op1_var_zx * op2_var_zx)
        elif oprnd3.size < oprnd1.size:
            mul_extract = smtlibv2.EXTRACT(op1_var * op2_var, 0, oprnd3.size)

            expr = (op3_var == mul_extract)
        else:
            expr = (op3_var == (op1_var * op2_var))

        rv = [expr]

        if parent_reg_constrs:
            rv += parent_reg_constrs

        return rv

    def _translate_div(self, oprnd1, oprnd2, oprnd3):
        """Return a formula representation of an DIV instruction.
        """
        assert oprnd1.size and oprnd2.size and oprnd3.size
        assert oprnd1.size == oprnd2.size
        assert oprnd2.size == oprnd3.size

        op1_var = self._translate_src_oprnd(oprnd1)
        op2_var = self._translate_src_oprnd(oprnd2)
        op3_var, parent_reg_constrs = self._translate_dst_oprnd(oprnd3)

        expr = (op3_var == (op1_var.udiv(op2_var)))

        rv = [expr]

        if parent_reg_constrs:
            rv += parent_reg_constrs

        return rv

    def _translate_sdiv(self, oprnd1, oprnd2, oprnd3):
        """Return a formula representation of an DIV instruction.
        """
        assert oprnd1.size and oprnd2.size and oprnd3.size
        assert oprnd1.size == oprnd2.size
        assert oprnd2.size == oprnd3.size

        op1_var = self._translate_src_oprnd(oprnd1)
        op2_var = self._translate_src_oprnd(oprnd2)
        op3_var, parent_reg_constrs = self._translate_dst_oprnd(oprnd3)

        expr = (op3_var == (op1_var / op2_var))

        rv = [expr]

        if parent_reg_constrs:
            rv += parent_reg_constrs

        return rv

    def _translate_mod(self, oprnd1, oprnd2, oprnd3):
        """Return a formula representation of an MOD instruction.
        """
        assert oprnd1.size and oprnd2.size and oprnd3.size
        assert oprnd1.size == oprnd2.size
        # assert oprnd2.size == oprnd3.size

        op1_var = self._translate_src_oprnd(oprnd1)
        op2_var = self._translate_src_oprnd(oprnd2)
        op3_var, parent_reg_constrs = self._translate_dst_oprnd(oprnd3)

        if oprnd1.size == oprnd3.size:
            expr = [(op3_var == (op1_var % op2_var))]
        elif oprnd3.size > oprnd1.size:
            op1_var_zx = smtlibv2.ZEXTEND(op1_var, oprnd3.size)
            op2_var_zx = smtlibv2.ZEXTEND(op2_var, oprnd3.size)

            expr = [(op3_var == (op1_var_zx % op2_var_zx))]
        else:
            raise Exception("Error")

        rv = expr

        if parent_reg_constrs:
            rv += parent_reg_constrs

        return rv

    def _translate_smod(self, oprnd1, oprnd2, oprnd3):
        """Return a formula representation of an MOD instruction.
        """
        assert oprnd1.size and oprnd2.size and oprnd3.size
        assert oprnd1.size == oprnd2.size
        assert oprnd2.size == oprnd3.size

        op1_var = self._translate_src_oprnd(oprnd1)
        op2_var = self._translate_src_oprnd(oprnd2)
        op3_var, parent_reg_constrs = self._translate_dst_oprnd(oprnd3)

        expr = (op3_var == (op2_var.smod(op1_var)))

        rv = [expr]

        if parent_reg_constrs:
            rv += parent_reg_constrs

        return rv

    def _translate_bsh(self, oprnd1, oprnd2, oprnd3):
        """Return a formula representation of a BSH instruction.
        """
        assert oprnd1.size and oprnd2.size and oprnd3.size
        assert oprnd1.size == oprnd2.size

        op1_var = self._translate_src_oprnd(oprnd1)
        op2_var = self._translate_src_oprnd(oprnd2)
        op3_var, parent_reg_constrs = self._translate_dst_oprnd(oprnd3)

        if oprnd3.size > oprnd1.size:
            op1_var_zx = smtlibv2.ZEXTEND(op1_var, oprnd3.size)
            op2_var_zx = smtlibv2.ZEXTEND(op2_var, oprnd3.size)

            op2_var_neg = (-op2_var)
            op2_var_neg_sx = smtlibv2.SEXTEND(op2_var_neg, oprnd2.size, oprnd3.size)

            shr = smtlibv2.EXTRACT(op1_var_zx >> op2_var_neg_sx, 0, op3_var.size)
            shl = smtlibv2.EXTRACT(op1_var_zx << op2_var_zx, 0, op3_var.size)
        elif oprnd3.size < oprnd1.size:
            shr = smtlibv2.EXTRACT(op1_var >> (-op2_var), 0, op3_var.size)
            shl = smtlibv2.EXTRACT(op1_var << op2_var, 0, op3_var.size)
        else:
            shr = op1_var >> (-op2_var)
            shl = op1_var << op2_var

        expr = (op3_var == smtlibv2.ITEBV(oprnd3.size, op2_var >= 0, shl, shr))

        rv = [expr]

        if parent_reg_constrs:
            rv += parent_reg_constrs

        return rv

    # Bitwise Instructions
    # ======================================================================== #
    def _translate_and(self, oprnd1, oprnd2, oprnd3):
        """Return a formula representation of a AND instruction.
        """
        assert oprnd1.size and oprnd2.size and oprnd3.size
        assert oprnd1.size == oprnd2.size

        op1_var = self._translate_src_oprnd(oprnd1)
        op2_var = self._translate_src_oprnd(oprnd2)
        op3_var, parent_reg_constrs = self._translate_dst_oprnd(oprnd3)

        if oprnd1.size < oprnd3.size:
            and_zx = smtlibv2.ZEXTEND(op1_var & op2_var, oprnd3.size)

            expr = (op3_var == and_zx)
        elif oprnd1.size > oprnd3.size:
            and_extract = smtlibv2.EXTRACT(op1_var & op2_var, 0, oprnd3.size)

            expr = (op3_var == and_extract)
        else:
            expr = (op3_var == (op1_var & op2_var))

        rv = [expr]

        if parent_reg_constrs:
            rv += parent_reg_constrs

        return rv

    def _translate_or(self, oprnd1, oprnd2, oprnd3):
        """Return a formula representation of a OR instruction.
        """
        assert oprnd1.size and oprnd2.size and oprnd3.size
        assert oprnd1.size == oprnd2.size

        op1_var = self._translate_src_oprnd(oprnd1)
        op2_var = self._translate_src_oprnd(oprnd2)
        op3_var, parent_reg_constrs = self._translate_dst_oprnd(oprnd3)

        if oprnd1.size < oprnd3.size:
            or_zx = smtlibv2.ZEXTEND(op1_var | op2_var, oprnd3.size)

            expr = (op3_var == or_zx)
        elif oprnd1.size > oprnd3.size:
            or_extract = smtlibv2.EXTRACT(op1_var | op2_var, 0, oprnd3.size)

            expr = (op3_var == or_extract)
        else:
            expr = (op3_var == (op1_var | op2_var))

        rv = [expr]

        if parent_reg_constrs:
            rv += parent_reg_constrs

        return rv

    def _translate_xor(self, oprnd1, oprnd2, oprnd3):
        """Return a formula representation of a AND instruction.
        """
        assert oprnd1.size and oprnd2.size and oprnd3.size
        assert oprnd1.size == oprnd2.size

        op1_var = self._translate_src_oprnd(oprnd1)
        op2_var = self._translate_src_oprnd(oprnd2)
        op3_var, parent_reg_constrs = self._translate_dst_oprnd(oprnd3)

        if oprnd1.size < oprnd3.size:
            xor_zx = smtlibv2.ZEXTEND(op1_var ^ op2_var, oprnd3.size)

            expr = (op3_var == xor_zx)
        elif oprnd1.size > oprnd3.size:
            xor_extract = smtlibv2.EXTRACT(op1_var ^ op2_var, 0, oprnd3.size)

            expr = (op3_var == xor_extract)
        else:
            expr = (op3_var == (op1_var ^ op2_var))

        rv = [expr]

        if parent_reg_constrs:
            rv += parent_reg_constrs

        return rv

    # Data transfer Instructions
    # ======================================================================== #
    def _translate_ldm(self, oprnd1, oprnd2, oprnd3):
        """Return a formula representation of a LDM instruction.
        """
        assert oprnd1.size == self._address_size
        assert oprnd3.size

        op1_var = self._translate_src_oprnd(oprnd1)
        op3_var, parent_reg_constrs = self._translate_dst_oprnd(oprnd3)

        size = oprnd3.size
        where = op1_var

        exprs = []

        bytes_exprs = []
        bytes_exprs_2 = []
        for i in reversed(xrange(0, size, 8)):
            bytes_exprs_1 = smtlibv2.ord(self._mem[where + i/8])
            bytes_exprs_2 = smtlibv2.EXTRACT(op3_var, i, 8)

            exprs += [bytes_exprs_1 == bytes_exprs_2]

        rv = exprs

        if parent_reg_constrs:
            rv += parent_reg_constrs

        return exprs

    def _translate_stm(self, oprnd1, oprnd2, oprnd3):
        """Return a formula representation of a STM instruction.
        """
        assert oprnd1.size and oprnd3.size
        assert oprnd3.size == self._address_size

        op1_var = self._translate_src_oprnd(oprnd1)
        op3_var = self._translate_src_oprnd(oprnd3)

        where = op3_var
        size = oprnd1.size

        for i in xrange(0, size, 8):
            self._mem[where + i/8] = smtlibv2.EXTRACT(op1_var, i, 8)

        # Memory versioning.
        self._mem_instance += 1

        mem_old = self._mem
        mem_new = self._solver.mkArray(self._address_size, "MEM_" + str(self._mem_instance))

        self._mem = mem_new

        return [mem_new == mem_old]

    def _translate_str(self, oprnd1, oprnd2, oprnd3):
        """Return a formula representation of a STR instruction.
        """
        assert oprnd1.size and oprnd3.size

        op1_var = self._translate_src_oprnd(oprnd1)
        op3_var, parent_reg_constrs = self._translate_dst_oprnd(oprnd3)

        dst_size = op3_var.size

        constrs = []

        if oprnd1.size == oprnd3.size:
            expr = (op1_var == op3_var)
        elif oprnd1.size < oprnd3.size:
            expr = (op1_var == smtlibv2.EXTRACT(op3_var, 0, op1_var.size))

			# Make sure that the values that can take dst operand
			# do not exceed the range of the source operand.
			# TODO: Find a better way to enforce this.
            fmt = "#b%0{0}d".format(op3_var.size - op1_var.size)
            imm = smtlibv2.BitVec(op3_var.size - op1_var.size, fmt % 0)

            constrs = [(imm == smtlibv2.EXTRACT(op3_var, op1_var.size, op3_var.size - op1_var.size))]
        else:
            expr = (smtlibv2.EXTRACT(op1_var, 0, op3_var.size) == op3_var)

        rv = [expr]

        if constrs:
            rv += constrs

        if parent_reg_constrs:
            rv += parent_reg_constrs

        return rv

    # Conditional Instructions
    # ======================================================================== #
    def _translate_bisz(self, oprnd1, oprnd2, oprnd3):
        """Return a formula representation of a BISZ instruction.
        """
        assert oprnd1.size and oprnd3.size

        op1_var = self._translate_src_oprnd(oprnd1)
        op3_var, parent_reg_constrs = self._translate_dst_oprnd(oprnd3)

        ite = smtlibv2.ITEBV(oprnd3.size, op1_var == 0x0, 0x1, 0x0)

        rv = [(op3_var == ite)]

        if parent_reg_constrs:
            rv += parent_reg_constrs

        return rv

    def _translate_jcc(self, oprnd1, oprnd2, oprnd3):
        """Return a formula representation of a JCC instruction.
        """
        # raise Exception("Unsupported instruction : JCC")

        return []

    # Other Instructions
    # ======================================================================== #
    def _translate_undef(self, oprnd1, oprnd2, oprnd3):
        """Return a formula representation of a UNDEF instruction.
        """
        # TODO: Support somehow.

        # raise Exception("Unsupported instruction : UNDEF")

        return []

    def _translate_unkn(self, oprnd1, oprnd2, oprnd3):
        """Return a formula representation of a UNKN instruction.
        """
        raise Exception("Unsupported instruction : UNKN")

    def _translate_nop(self, oprnd1, oprnd2, oprnd3):
        """Return a formula representation of a NOP instruction.
        """
        return []

    # Ad-hoc Instructions
    # ======================================================================== #
    def _translate_ret(self, oprnd1, oprnd2, oprnd3):
        """Return a formula representation of a RET instruction.
        """
        # raise Exception("Unsupported instruction : RET")

        return []

    # Extension
    # ======================================================================== #
    def _translate_sext(self, oprnd1, oprnd2, oprnd3):
        """Return a formula representation of a SEXT instruction.
        """
        assert oprnd1.size and oprnd3.size

        op1_var = self._translate_src_oprnd(oprnd1)
        op3_var, parent_reg_constrs = self._translate_dst_oprnd(oprnd3)

        dst_size = op3_var.size

        constrs = []

        if oprnd1.size == oprnd3.size:
            expr = (op1_var == op3_var)
        elif oprnd1.size < oprnd3.size:
            expr = (op3_var == smtlibv2.SEXTEND(op1_var, op1_var.size, op3_var.size))

            # Make sure that the values that can take dst operand
            # do not exceed the range of the source operand.
            # TODO: Find a better way to enforce this.

            # TODO: This should not be needed any more.
            # fmt = "#b%0{0}d".format(op3_var.size - op1_var.size)
            # imm = smtlibv2.BitVec(op3_var.size - op1_var.size, fmt % 0)

            # constrs = [(imm == smtlibv2.EXTRACT(op3_var, op1_var.size, op3_var.size - op1_var.size))]
        else:
            raise Exception("Invalid operand size: %d" % str(oprnd3))

        rv = [expr]

        if constrs:
            rv += constrs

        if parent_reg_constrs:
            rv += parent_reg_constrs

        return rv
