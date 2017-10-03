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
import re

from subprocess import PIPE
from subprocess import Popen

from barf.core.smt.smtsymbol import BitVec
from barf.core.smt.smtsymbol import BitVecArray
from barf.core.smt.smtsymbol import Bool

logger = logging.getLogger(__name__)


class Z3Solver(object):

    def __init__(self):
        self._status = "unknown"

        self._declarations = {}
        self._constraints = []

        self._process = None

        self._start_solver()

    def _start_solver(self):
        self._process = Popen("z3 -smt2 -in", shell=True, stdin=PIPE, stdout=PIPE)

        # Set z3 declaration scopes.
        self._write("(set-option :global-decls false)")
        self._write("(set-logic QF_AUFBV)")

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

        regex = r"\(\(([^\s]+|\(.*\))\s#x([^\s]+)\)\)"
        match = re.search(regex, response).groups()[1]

        return int(match, 16)

    def get_value_by_name(self, name):
        assert self.check() == "sat"

        self._write("(get-value ({}))".format(self._declarations[name]))

        response = self._read()

        regex = r"\(\(([^\s]*)\s#x([^\s]*)\)\)"
        match = re.search(regex, response).groups()[1]

        return int(match, 16)

    def make_bitvec(self, size, name):
        # TODO Refactor this method
        assert size in [1, 8, 16, 32, 40, 64, 72, 128, 256]

        if name in self._declarations:
            return self._declarations[name]

        bv = BitVec(size, name)

        self._declarations[name] = bv
        self._write(bv.declaration)

        return bv

    def make_array(self, size, name):
        # TODO Refactor this method
        assert size in [32, 64]

        if name in self._declarations:
            return self._declarations[name]

        arr = BitVecArray(size, 8, name)

        self._declarations[name] = arr
        self._write(arr.declaration)

        return arr


class CVC4Solver(object):

    def __init__(self):
        self._status = "unknown"

        self._declarations = {}
        self._constraints = []

        self._process = None

        self._start_solver()

    def _start_solver(self):
        self._process = Popen("cvc4 --incremental --lang=smt2", shell=True, stdin=PIPE, stdout=PIPE)

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

    def get_value_by_name(self, name):
        assert self.check() == "sat"

        self._write("(get-value ({}))".format(self._declarations[name]))

        response = self._read()

        regex = r"\(\(([^\s]*)\s\(_\sbv([0-9]*)\s[0-9]*\)\)\)"
        match = re.search(regex, response).groups()[1]

        return int(match)

    def make_bitvec(self, size, name):
        # TODO Refactor this method
        assert size in [1, 8, 16, 32, 40, 64, 72, 128, 256]

        if name in self._declarations:
            return self._declarations[name]

        bv = BitVec(size, name)

        self._declarations[name] = bv
        self._write(bv.declaration)

        return bv

    def make_array(self, size, name):
        # TODO Refactor this method
        assert size in [32, 64]

        if name in self._declarations:
            return self._declarations[name]

        arr = BitVecArray(size, 8, name)

        self._declarations[name] = arr
        self._write(arr.declaration)

        return arr
