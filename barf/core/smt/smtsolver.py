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

import logging
import re
import subprocess
import platform

from barf.core.smt.smtsymbol import Bool

logger = logging.getLogger(__name__)


def _check_solver_installation(solver):
    found = True
    try:
        if platform.system() == "Windows":
            _ = subprocess.check_output(["where", solver])
        else:
            _ = subprocess.check_output(["which", solver])
    except subprocess.CalledProcessError as e:
        if e.returncode == 0x1:
            found = False
    return found


class SmtSolverNotFound(Exception):
    pass


class Z3Solver(object):

    def __init__(self):
        self._name = "z3"

        self._status = "unknown"

        self._declarations = {}
        self._constraints = []

        self._process = None

        self._check_solver()

        self._start_solver()

    def _check_solver(self):
        if not _check_solver_installation(self._name):
            raise SmtSolverNotFound("{} solver is not installed".format(self._name))

    def _start_solver(self):
        self._process = subprocess.Popen("z3 -smt2 -in", shell=True, bufsize=0, stdin=subprocess.PIPE, stdout=subprocess.PIPE, universal_newlines=True)

        # Set z3 declaration scopes.
        self._write("(set-option :global-decls false)")
        self._write("(set-logic QF_AUFBV)")

    def _stop_solver(self):
        if self._process:
            self._process.stdin.close()
            self._process.stdout.close()

            self._process.kill()
            self._process.wait()

            self._process = None

    def _write(self, command):
        logger.debug("> %s", command)

        self._process.stdin.writelines(command + "\n")

    def _read(self):
        response = self._process.stdout.readline()[:-1]

        logger.debug("< %s", response)

        return response

    def __del__(self):
        self._stop_solver()

    def __str__(self):
        declarations = [d.declaration for d in self._declarations.values()]
        constraints = ["(assert {})".format(c) for c in self._constraints]

        return "\n".join(declarations + constraints)

    def add(self, constraint):
        assert isinstance(constraint, Bool)

        self._write("(assert {})".format(constraint))

        self._constraints.append(constraint)

        self._status = "unknown"

    def check(self):
        assert self._status in ("sat", "unsat", "unknown")

        if self._status == "unknown":
            self._write("(check-sat)")
            self._status = self._read()

        return self._status

    def reset(self):
        self._stop_solver()

        self._status = "unknown"

        self._declarations = {}
        self._constraints = []

        self._start_solver()

    def get_value(self, expr):
        assert self.check() == "sat"

        self._write("(get-value ({}))".format(expr))

        response = self._read()

        regex = r"\(\(([^\s]+|\(.*\))\s#x([^\s]+)\)\)"
        match = re.search(regex, response).groups()[1]

        return int(match, 16)

    def declare_fun(self, name, fun):
        if name in self._declarations:
            raise Exception("Symbol already declare.")

        self._declarations[name] = fun
        self._write(fun.declaration)

    @property
    def declarations(self):
        return self._declarations


class CVC4Solver(object):

    def __init__(self):
        self._name = "cvc4"

        self._status = "unknown"

        self._declarations = {}
        self._constraints = []

        self._process = None

        self._check_solver()

        self._start_solver()

    def _check_solver(self):
        if not _check_solver_installation(self._name):
            raise SmtSolverNotFound("{} solver is not installed".format(self._name))

    def _start_solver(self):
        self._process = subprocess.Popen("cvc4 --incremental --lang=smt2", shell=True,
                                         bufsize=0, stdin=subprocess.PIPE, stdout=subprocess.PIPE,
                                         universal_newlines=True)

        # Set CVC4 declaration scopes.
        self._write("(set-logic QF_AUFBV)")
        self._write("(set-option :produce-models true)")

    def _stop_solver(self):
        if self._process:
            self._process.kill()
            self._process.wait()

            self._process = None

    def _write(self, command):
        logger.debug("> %s", command)

        self._process.stdin.writelines(command + "\n")

    def _read(self):
        response = self._process.stdout.readline()[:-1]

        logger.debug("< %s", response)

        return response

    def __del__(self):
        self._stop_solver()

    def __str__(self):
        declarations = [d.declaration for d in self._declarations.values()]
        constraints = ["(assert {})".format(c) for c in self._constraints]

        return "\n".join(declarations + constraints)

    def add(self, constraint):
        assert isinstance(constraint, Bool)

        self._write("(assert {})".format(constraint))

        self._constraints.append(constraint)

        self._status = "unknown"

    def check(self):
        assert self._status in ("sat", "unsat", "unknown")

        if self._status == "unknown":
            self._write("(check-sat)")
            self._status = self._read()

        return self._status

    def reset(self):
        self._stop_solver()

        self._status = "unknown"

        self._declarations = {}
        self._constraints = []

        self._start_solver()

    def get_value(self, expr):
        assert self.check() == "sat"

        self._write("(get-value ({}))".format(expr))

        response = self._read()

        regex = r"\(\(([^\s]+|\(.*\))\s\(_\sbv([0-9]*)\s[0-9]*\)\)\)"
        match = re.search(regex, response).groups()[1]

        return int(match)

    def declare_fun(self, name, fun):
        if name in self._declarations:
            raise Exception("Symbol already declare.")

        self._declarations[name] = fun
        self._write(fun.declaration)

    @property
    def declarations(self):
        return self._declarations
