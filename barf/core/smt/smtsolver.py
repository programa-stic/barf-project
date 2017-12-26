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

import logging
from pysmt.shortcuts import Solver
from pysmt.exceptions import NoSolverAvailableError

logger = logging.getLogger(__name__)

class SmtSolverNotFound(Exception):
    pass

class PySMTSolver(object):
    def __init__(self, solver_name=None):
        self._name = solver_name
        self._status = "unknown"

        self._declarations = {}
        self._constraints = []

        self._process = None

        try:
            self._solver = Solver(name=self._name)
        except NoSolverAvailableError:
            raise SmtSolverNotFound("{} solver is not installed".format(self._name))

    def __str__(self):
        declarations = [d.declaration for d in self._declarations.values()]
        constraints = ["(assert {})".format(c) for c in self._constraints]
        return "\n".join(declarations + constraints)

    def add(self, constraint):
        self._solver.add_assertion(constraint)

    def check(self):
        assert self._status in ("sat", "unsat", "unknown")
        res = self._solver.solve()

        # if self._status == "unknown":
        #     self._write("(check-sat)")
        #     self._status = self._read()
        if res:
            self._status = "sat"
        else:
            self._status = "unsat"

        # TODO: Handling of unknown
        return self._status

    def reset(self):
        self._solver._reset_assertions()
        self._status = "unknown"
        self._declarations = {}
        self._constraints = []

    def get_value(self, expr):
        assert self._status == "sat"
        return self._solver.get_py_value(expr)

    def declare_fun(self, name, fun):
        if name in self._declarations:
            raise Exception("Symbol already declare.")
        self._declarations[name] = fun

    @property
    def declarations(self):
        return self._declarations
