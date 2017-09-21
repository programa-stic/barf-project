# Copyright (c) 2013, Felipe Andres Manzano
# All rights reserved.
#
# Redistribution and use in source and binary forms, with or without
# modification, are permitted provided that the following conditions are met:
#
#     * Redistributions of source code must retain the above copyright notice,
#       this list of conditions and the following disclaimer.
#     * Redistributions in binary form must reproduce the above copyright
#       notice,this list of conditions and the following disclaimer in the
#       documentation and/or other materials provided with the distribution.
#     * Neither the name of the copyright holder nor the names of its
#       contributors may be used to endorse or promote products derived from
#       this software without specific prior written permission.
#
# THIS SOFTWARE IS PROVIDED BY THE COPYRIGHT HOLDERS AND CONTRIBUTORS "AS IS"
# AND ANY EXPRESS OR IMPLIED CVC, INCLUDING, BUT NOT LIMITED TO, THE
# IMPLIED WARRANTIES OF MERCHANTABILITY AND FITNESS FOR A PARTICULAR PURPOSE
# ARE DISCLAIMED. IN NO EVENT SHALL THE COPYRIGHT OWNER OR CONTRIBUTORS BE
# LIABLE FOR ANY DIRECT, INDIRECT, INCIDENTAL, SPECIAL, EXEMPLARY, OR
# CONSEQUENTIAL DAMAGES (INCLUDING, BUT NOT LIMITED TO, PROCUREMENT OF
# SUBSTITUTE GOODS OR SERVICES; LOSS OF USE, DATA, OR PROFITS; OR BUSINESS
# INTERRUPTION) HOWEVER CAUSED AND ON ANY THEORY OF LIABILITY, WHETHER IN
# CONTRACT, STRICT LIABILITY, OR TORT (INCLUDING NEGLIGENCE OR OTHERWISE)
# ARISING IN ANY WAY OUT OF THE USE OF THIS SOFTWARE, EVEN IF ADVISED OF THE
# POSSIBILITY OF SUCH DAMAGE.

import copy
import logging

from subprocess import PIPE
from subprocess import Popen

logger = logging.getLogger("smtlibv2")


class Symbol(object):

    def __init__(self, value, *children):
        assert type(value) in [int, long, str, bool]
        assert all([isinstance(x, Symbol) for x in children])

        if len(children) > 0:
            self._value = '(' + str(value) + ' ' + ' '.join(map(str, children)) + ')'
        else:
            self._value = str(value)

    def __getstate__(self):
        state = {
            'value': self.value
        }

        return state

    def __setstate__(self, state):
        self._value = state['value']

    @property
    def value(self):
        return self._value

    def __str__(self):
        return str(self._value)


class BitVec(Symbol):
    """A symbolic bit vector"""

    def __init__(self, size, value, *children):
        super(BitVec, self).__init__(value, *children)

        self.size = size

    def __getstate__(self):
        state = super(BitVec, self).__getstate__()
        state['size'] = self.size

        return state

    def __setstate__(self, state):
        super(BitVec, self).__setstate__(state)

        self.size = state['size']

    def cast(self, val):
        if type(val) in (int, long):
            if self.size == 1:
                return BitVec(self.size, '#' + bin(val & 1)[1:])
            return BitVec(self.size, '#x%0*x' % (self.size / 4, val & ((1 << self.size) - 1)))
        elif type(val) is Bool:
            raise NotImplementedError()
        elif type(val) is str:
            assert len(val) == 1 and self.size == 8
            return BitVec(self.size, '#x%02x' % ord(val))

        assert type(val) == BitVec and val.size == self.size

        return val

    @property
    def declaration(self):
        return '(declare-fun %s () (_ BitVec %d))' % (self.value, self.size)

    # Arithmetic operators
    def __add__(self, other):
        return BitVec(self.size, 'bvadd', self, self.cast(other))

    def __sub__(self, other):
        return BitVec(self.size, 'bvsub', self, self.cast(other))

    def __mul__(self, other):
        return BitVec(self.size, 'bvmul', self, self.cast(other))

    def __div__(self, other):
        return BitVec(self.size, 'bvsdiv', self, self.cast(other))

    def __truediv__(self, other):
        return BitVec(self.size, 'bvsdiv', self, self.cast(other))

    def __mod__(self, other):
        return BitVec(self.size, 'bvsmod', self, self.cast(other))

    # Bitwise operators
    def __and__(self, other):
        return BitVec(self.size, 'bvand', self, self.cast(other))

    def __xor__(self, other):
        return BitVec(self.size, 'bvxor', self, self.cast(other))

    def __or__(self, other):
        return BitVec(self.size, 'bvor', self, self.cast(other))

    def __lshift__(self, other):
        return BitVec(self.size, 'bvshl', self, self.cast(other))

    def __rshift__(self, other):
        return BitVec(self.size, 'bvlshr', self, self.cast(other))

    def __invert__(self):
        return BitVec(self.size, 'bvnot', self)

    # Reverse arithmetic operators
    def __radd__(self, other):
        return BitVec(self.size, 'bvadd', self.cast(other), self)

    def __rsub__(self, other):
        return BitVec(self.size, 'bvsub', self.cast(other), self)

    def __rmul__(self, other):
        return BitVec(self.size, 'bvmul', self, self.cast(other))

    def __rdiv__(self, other):
        return BitVec(self.size, 'bvsdiv', self.cast(other), self)

    def __rtruediv__(self, other):
        return BitVec(self.size, 'bvsdiv', self.cast(other), self)

    def __rmod__(self, other):
        return BitVec(self.size, 'bvmod', self.cast(other), self)

    # Reverse bitwise operators
    def __rand__(self, other):
        return BitVec(self.size, 'bvand', self, self.cast(other))

    def __rxor__(self, other):
        return BitVec(self.size, 'bvxor', self, self.cast(other))

    def __ror__(self, other):
        return BitVec(self.size, 'bvor', self, self.cast(other))

    def __rlshift__(self, other):
        return BitVec(self.size, 'bvshl', self.cast(other), self)

    def __rrshift__(self, other):
        return BitVec(self.size, 'bvlshr', self.cast(other), self)

    # Comparison operators (signed)
    def __lt__(self, other):
        return Bool('bvslt', self, self.cast(other))

    def __le__(self, other):
        return Bool('bvsle', self, self.cast(other))

    def __eq__(self, other):
        return Bool('=', self, self.cast(other))

    def __ne__(self, other):
        return Bool('not', self == other)

    def __gt__(self, other):
        return Bool('bvsgt', self, self.cast(other))

    def __ge__(self, other):
        return Bool('bvsge', self, self.cast(other))

    def __neg__(self):
        return BitVec(self.size, 'bvneg', self)

    # Comparison operators (unsigned)
    def ult(self, other):
        return Bool('bvult', self, self.cast(other))

    def ule(self, other):
        return Bool('bvule', self, self.cast(other))

    def ugt(self, other):
        return Bool('bvugt', self, self.cast(other))

    def uge(self, other):
        return Bool('bvuge', self, self.cast(other))

    # Arithmetic operators (unsigned)
    def udiv(self, other):
        return BitVec(self.size, 'bvudiv', self, self.cast(other))

    def urem(self, other):
        return BitVec(self.size, 'bvurem', self, self.cast(other))

    # Reverse arithmetic operators (unsigned)
    def rudiv(self, other):
        return BitVec(self.size, 'bvudiv', self.cast(other), self)

    def rurem(self, other):
        return BitVec(self.size, 'bvurem', self.cast(other), self)

    # TODO __mod__ and smod use the same smtlib operator, which one is the correct one?
    def smod(self, other):
        return BitVec(self.size, 'bvsmod', self.cast(other), self)


class Bool(Symbol):

    def __init__(self, value, *children):
        super(Bool, self).__init__(value, *children)

    def cast(self, val):
        if isinstance(val, (int, long, bool)):
            return Bool(str(bool(val)).lower())

        assert isinstance(val, Bool)

        return val

    @property
    def declaration(self):
        return '(declare-fun %s () Bool)' % self.value

    # Comparison operators
    def __eq__(self, other):
        return Bool('=', self, self.cast(other))

    def __ne__(self, other):
        return Bool('not', self == other)

    # Logical operators
    def __and__(self, other):
        return Bool('and', self, self.cast(other))

    def __or__(self, other):
        return Bool('or', self, self.cast(other))

    def __xor__(self, other):
        return Bool('xor', self, self.cast(other))

    def __invert__(self):
        return Bool('not', self)

    # Reverse logical operators
    def __rand__(self, other):
        return Bool('and', self, self.cast(other))

    def __ror__(self, other):
        return Bool('or', self, self.cast(other))

    def __rxor__(self, other):
        return Bool('xor', self, self.cast(other))

    # Misc operator
    def __nonzero__(self):
        raise NotImplementedError()


class Array_(Symbol):

    def __init__(self, size, value, *children):
        super(Array_, self).__init__(value, *children)

        self.size = size

    def __getstate__(self):
        state = super(Array_, self).__getstate__()
        state['size'] = self.size

        return state

    def __setstate__(self, state):
        super(Array_, self).__setstate__(state)

        self.size = state['size']

    def cast_key(self, val):
        if type(val) in (int, long):
            return BitVec(self.size, '#x%0*x' % (self.size / 4, val & ((1 << self.size) - 1)))
        elif type(val) is Bool:
            raise NotImplementedError()
        elif type(val) is str:
            assert len(val) == 1 and self.size == 8
            return BitVec(self.size, '#x%02x' % ord(val))

        assert type(val) == BitVec and val.size == self.size

        return val

    def cast_value(self, val):
        if type(val) in (int, long):
            return BitVec(8, '#x%02x' % (val & ((1 << self.size) - 1)))
        elif type(val) is Bool:
            raise NotImplementedError()
        elif type(val) is str:
            assert len(val) == 1
            return BitVec(32, '#x%02x' % ord(val))

        assert type(val) == BitVec and val.size == 8

        return val

    def select(self, key):
        return BitVec(8, 'select', self, self.cast_key(key))

    def store(self, key, value):
        return Array_(self.size, '(store %s %s %s)' % (self, self.cast_key(key), self.cast_value(value)))

    # Comparison operators
    def __eq__(self, other):
        assert isinstance(other, Array_) and other.size == self.size

        return Bool('=', self, other)

    def __neq__(self, other):
        assert isinstance(other, Array_) and other.size == self.size

        return Bool('not', self.__eq__(other))


class Array(object):

    def __init__(self, size, name, *children):
        self.array = Array_(size, name, *children)
        self.name = name
        self.cache = {}
        self.declaration = '(declare-fun %s () (Array (_ BitVec %d) (_ BitVec 8)))' % (name, size)

    def __getstate__(self):
        state = {
            'declaration': self.declaration,
            'array': self.array,
            'name': self.name,
            'cache': self.cache
        }

        return state

    def __setstate__(self, state):
        self.array = state['array']
        self.name = state['name']
        self.cache = state['cache']
        self.declaration = state['declaration']

    def __getitem__(self, key):
        if key not in self.cache:
            self.cache[key] = self.array.select(key)

        return self.cache[key]

    def __setitem__(self, key, value):
        self.cache = {}
        self.array = self.array.store(key, value)

    # Comparison operators
    def __eq__(self, other):
        assert isinstance(other.array, Array_) and other.array.size == self.array.size

        return Bool('=', self.array, other.array)

    def __neq__(self, other):
        assert isinstance(other.array, Array_) and other.array.size == self.array.size

        return Bool('not', self.__eq__(other))


class Z3Solver(object):

    def __init__(self):
        """ Build a solver instance.
            This is implemented using an external native solver via a subprocess.
            Every time a new symbol or assertion is added a smtlibv2 command is
            sent to the solver.
            The actual state is also maintained in memory to be able to save and
            restore the state.
            The analysis may be saved to disk and continued after a while or
            forked in memory or even sent over the network.
        """
        self._status = 'unknown'
        self._sid = 0
        self._stack = []
        self._declarations = {}
        self._constraints = list()

        self._proc = Popen('z3 -smt2 -in', shell=True, stdin=PIPE, stdout=PIPE)

        # Fix z3 declaration scopes
        self._send("(set-option :global-decls false)")
        self._send("(set-logic QF_AUFBV)")

    def __getstate__(self):
        state = {
            'sid': self._sid,
            'declarations': self._declarations,
            'constraints': self._constraints,
            'stack': self._stack,
        }

        return state

    def __setstate__(self, state):
        self._status = None
        self._sid = state['sid']
        self._stack = state['stack']
        self._declarations = state['declarations']
        self._constraints = state['constraints']

        self._proc = Popen('z3 -smt2 -in', shell=True, stdin=PIPE, stdout=PIPE)

        # Fix z3 declaration scopes
        self._send("(set-option :global-decls false)")
        self._send("(set-logic QF_AUFBV)")

    def reset(self, full=False):
        self._send("(reset)")
        self._send("(set-option :global-decls false)")
        self._send("(set-logic QF_AUFBV)")

        if full:
            self._proc.kill()
            self._proc.wait()
            self._proc = None

            self._status = 'unknown'
            self._sid = 0
            self._stack = []
            self._declarations = {}
            self._constraints = list()

            self._proc = Popen('z3 -smt2 -in', shell=True, stdin=PIPE, stdout=PIPE)

            # Fix z3 declaration scopes
            self._send("(set-option :global-decls false)")
            self._send("(set-logic QF_AUFBV)")

        self._send(self)

        self._status = 'unknown'

    def __del__(self):
        self._proc.kill()
        self._proc.wait()

        self._proc = None

    def _get_sid(self):
        """ Returns an unique id. """
        self._sid += 1

        return self._sid

    def _send(self, cmd):
        """ Send a string to the solver.
            @param cmd: a SMTLIBv2 command (ex. (check-sat))
        """
        # logger.debug('>%s', cmd)
        self._proc.stdin.writelines((str(cmd), '\n'))

    def _recv(self):
        """ Reads the response from the solver """

        def readline():
            line = self._proc.stdout.readline()
            return line, line.count('('), line.count(')')

        bufl = []
        left = 0
        right = 0
        buf, l, r = readline()
        bufl.append(buf)
        left += l
        right += r
        while left != right:
            buf, l, r = readline()
            bufl.append(buf)
            left += l
            right += r
        buf = ''.join(bufl).strip()
        # logger.debug('<%s', buf)
        if '(error' in bufl[0]:
            print("Error in simplify: %s" % str(buf))
            raise Exception("Error in smtlib <" + str(self) + ">")
        return buf

    def __str__(self):
        """ Returns a smtlib representation of the current state """
        buf = ''
        for d in self._declarations.values():
            buf += d.declaration + '\n'
        for a in self.constraints:
            buf += '%s\n' % a
        return buf

    def getallvalues(self, x, maxcnt=30):
        """ Returns a list with all the possible values for the symbol x"""
        assert self.check() == 'sat'
        assert type(x) is BitVec
        result = []
        self.push()
        try:
            aux = self.mkBitVec(x.size)
            self.add(aux == x)
            r = self.check()
            while r != 'unsat':
                val = self.getvalue(aux)
                result.append(val)
                self.add(x != val)
                r = self.check()
                if len(result) > maxcnt:
                    raise Exception("Max number of different solutions hit")
        except Exception as e:
            raise e
        finally:
            self.pop()
        return result

    def push(self):
        """ Pushes and save the current state."""
        if self._status is None:
            self.reset()

        self._send('(push 1)')

        self._stack.append((self._sid, self._declarations, self._constraints))
        self._declarations = copy.copy(self._declarations)
        self._constraints = copy.copy(self._constraints)

    def pop(self):
        """ Recall the last pushed state. """
        self._send('(pop 1)')

        self._sid, self._declarations, self._constraints = self._stack.pop()
        self._status = 'unknown'

    def check(self):
        """ Check the satisfiability of the current state """
        if self._status is None:
            self.reset()
        if self._status == 'unknown':
            self._send('(check-sat)')
            self._status = self._recv()
        return self._status

    def getvalue(self, val):
        """ Ask the solver for one possible assignment for val using current set
            of constraints.
            The current set of assertions must be sat.
            @param val: an expression or symbol """
        if isconcrete(val):
            return val

        assert self.check() == 'sat'

        self._send('(get-value (%s))' % val)
        ret = self._recv()

        assert ret.startswith('((') and ret.endswith('))')

        return int(ret.split(' ')[-1][2:-2], 16)

    def getvaluebyname(self, name):
        """ Ask the solver for one possible assignment for val using current set
            of constraints.
            The current set of assertions must be sat.
        """
        val = self._declarations[name]

        assert self.check() == 'sat'

        self._send('(get-value (%s))' % val)
        ret = self._recv()

        assert ret.startswith('((') and ret.endswith('))')

        return int(ret.split(' ')[-1][2:-2], 16)

    def mkBitVec(self, size, name='V'):
        """ Creates a symbol in the constrains store and names it name"""
        assert size in [1, 8, 16, 32, 40, 64, 72, 128, 256]

        if name in self._declarations:
            return self._declarations[name]

        bv = BitVec(size, name)

        self._declarations[name] = bv
        self._send(bv.declaration)

        return bv

    def mkArray(self, size=32, name='A'):
        """ Creates a symbols array in the constrains store and names it name"""
        assert size in [8, 16, 32, 64]

        if name in self._declarations:
            return self._declarations[name]

        arr = Array(size, name)

        self._declarations[name] = arr
        self._send(arr.declaration)

        return arr

    def mkArrayNew(self, size=32, name='A'):
        """ Creates a symbols array in the constrains store and names it name"""
        assert size in [8, 16, 32, 64]

        arr = Array(size, name)

        return arr

    def mkBool(self, name='B'):
        """ Creates a symbols array in the constrains store and names it name"""
        if name in self._declarations:
            name = '%s_%d' % (name, self._get_sid())

        b = Bool(name)

        self._declarations[name] = b
        self._send(b.declaration)

        return b

    @property
    def declarations(self):
        declarations = []
        for _, var in self._declarations.items():
            declarations.append(var)
        return declarations

    def add(self, constraint, comment=None):
        if isinstance(constraint, bool):
            if not constraint:
                self._status = 'unsat'
            return

        assert isinstance(constraint, Bool)

        if comment:
            self._send('(assert %s) ; %s' % (constraint, comment))
        else:
            self._send('(assert %s)' % constraint)

        self._constraints.append((constraint, comment))
        self._status = 'unknown'

    @property
    def constraints(self):
        constraints = []
        for c, comment in self._constraints:
            if comment:
                constraints.append('(assert %s) ; %s' % (c, comment))
            else:
                constraints.append('(assert %s)' % c)
        return constraints


class CVC4Solver(object):

    def __init__(self):
        """ Build a solver instance.
            This is implemented using an external native solver via a subprocess.
            Every time a new symbol or assertion is added a smtlibv2 command is
            sent to the solver.
            The actual state is also maintained in memory to be able to save and
            restore the state.
            The analysis may be saved to disk and continued after a while or
            forked in memory or even sent over the network.
        """
        self._status = 'unknown'
        self._sid = 0
        self._stack = []
        self._declarations = {}
        self._constraints = list()

        self._proc = Popen('cvc4 --incremental --lang=smt2', shell=True, stdin=PIPE, stdout=PIPE)

        # Fix CVC4 declaration scopes
        self._send("(set-logic QF_AUFBV)")
        self._send("(set-option :produce-models true)")

    def __getstate__(self):
        state = {
            'sid': self._sid,
            'declarations': self._declarations,
            'constraints': self._constraints,
            'stack': self._stack,
        }

        return state

    def __setstate__(self, state):
        self._status = None
        self._sid = state['sid']
        self._stack = state['stack']
        self._declarations = state['declarations']
        self._constraints = state['constraints']

        self._proc = Popen('cvc4 --incremental --lang=smt2', shell=True, stdin=PIPE, stdout=PIPE)

        # Fix CVC4 declaration scopes
        self._send("(set-logic QF_AUFBV)")
        self._send("(set-option :produce-models true)")

    def reset(self, full=False):
        self._proc.kill()
        self._proc.wait()

        if full:
            self._status = 'unknown'
            self._sid = 0
            self._stack = []
            self._declarations = {}
            self._constraints = list()

        self._proc = Popen('cvc4 --incremental --lang=smt2', shell=True, stdin=PIPE, stdout=PIPE)

        # Fix CVC4 declaration scopes
        self._send("(set-logic QF_AUFBV)")
        self._send("(set-option :produce-models true)")

        self._send(self)

        self._status = 'unknown'

    def __del__(self):
        self._proc.kill()
        self._proc.wait()

        self._proc = None

    def _get_sid(self):
        """ Returns an unique id. """
        self._sid += 1

        return self._sid

    def _send(self, cmd):
        """ Send a string to the solver.
            @param cmd: a SMTLIBv2 command (ex. (check-sat))
        """
        # logger.debug('>%s', cmd)
        self._proc.stdin.writelines((str(cmd), '\n'))

    def _recv(self):
        """ Reads the response from the solver """

        def readline():
            line = self._proc.stdout.readline()
            return line, line.count('('), line.count(')')

        bufl = []
        left = 0
        right = 0
        buf, l, r = readline()
        bufl.append(buf)
        left += l
        right += r
        while left != right:
            buf, l, r = readline()
            bufl.append(buf)
            left += l
            right += r
        buf = ''.join(bufl).strip()
        # logger.debug('<%s', buf)
        if '(error' in bufl[0]:
            print("Error in simplify: %s" % str(buf))
            raise Exception("Error in smtlib <" + str(self) + ">")
        return buf

    def __str__(self):
        """ Returns a smtlib representation of the current state """
        buf = ''
        for d in self._declarations.values():
            buf += d.declaration + '\n'
        for a in self.constraints:
            buf += '%s\n' % a
        return buf

    def getallvalues(self, x, maxcnt=30):
        """ Returns a list with all the possible values for the symbol x"""
        assert self.check() == 'sat'
        assert type(x) is BitVec
        result = []
        self.push()
        try:
            aux = self.mkBitVec(x.size)
            self.add(aux == x)
            r = self.check()
            while r != 'unsat':
                val = self.getvalue(aux)
                result.append(val)
                self.add(x != val)
                r = self.check()
                if len(result) > maxcnt:
                    raise Exception("Max number of different solutions hit")
        except Exception as e:
            raise e
        finally:
            self.pop()
        return result

    def push(self):
        """ Pushes and save the current state."""
        if self._status is None:
            self.reset()

        self._send('(push 1)')

        self._stack.append((self._sid, self._declarations, self._constraints))
        self._declarations = copy.copy(self._declarations)
        self._constraints = copy.copy(self._constraints)

    def pop(self):
        """ Recall the last pushed state. """
        self._send('(pop 1)')

        self._sid, self._declarations, self._constraints = self._stack.pop()
        self._status = 'unknown'

    def check(self):
        """ Check the satisfiability of the current state """
        if self._status is None:
            self.reset()
        if self._status == 'unknown':
            self._send('(check-sat)')
            self._status = self._recv()
        return self._status

    def getvalue(self, val):
        """ Ask the solver for one possible assignment for val using current set
            of constraints.
            The current set of assertions must be sat.
            @param val: an expression or symbol """
        if isconcrete(val):
            return val

        assert self.check() == 'sat'

        self._send('(get-value (%s))' % val)
        ret = self._recv()

        assert ret.startswith('((') and ret.endswith('))')

        ret = ret[2:-2]
        _, ret = ret[:ret.rfind('(')], ret[ret.rfind('('):]

        assert ret.startswith('(') and ret.endswith(')')

        index = ret.rfind('(')
        var_value, _ = ret[index + 3:-1].split(' ', 1)

        assert var_value.startswith('bv')

        value = int(var_value[2:])

        return value

    def getvaluebyname(self, name):
        """ Ask the solver for one possible assignment for val using current set
            of constraints.
            The current set of assertions must be sat.
        """
        val = self._declarations[name]

        assert self.check() == 'sat'

        self._send('(get-value (%s))' % val)
        ret = self._recv()

        assert ret.startswith('((') and ret.endswith('))')

        _, ret = ret[2:-2].split(' ', 1)

        assert ret.startswith('(_') and ret.endswith(')')

        var_value, _ = ret[3:-1].split(' ', 1)

        assert var_value.startswith('bv')

        value = int(var_value[2:])

        return value

    def mkBitVec(self, size, name='V'):
        """ Creates a symbol in the constrains store and names it name"""
        assert size in [1, 8, 16, 32, 40, 64, 72, 128, 256]

        if name in self._declarations:
            return self._declarations[name]

        bv = BitVec(size, name)

        self._declarations[name] = bv
        self._send(bv.declaration)

        return bv

    def mkArray(self, size=32, name='A'):
        """ Creates a symbols array in the constrains store and names it name"""
        assert size in [8, 16, 32, 64]

        if name in self._declarations:
            return self._declarations[name]

        arr = Array(size, name)

        self._declarations[name] = arr
        self._send(arr.declaration)

        return arr

    def mkArrayNew(self, size=32, name='A'):
        """ Creates a symbols array in the constrains store and names it name"""
        assert size in [8, 16, 32, 64]

        arr = Array(size, name)

        return arr

    def mkBool(self, name='B'):
        """ Creates a symbols array in the constrains store and names it name"""
        if name in self._declarations:
            name = '%s_%d' % (name, self._get_sid())

        b = Bool(name)

        self._declarations[name] = b
        self._send(b.declaration)

        return b

    @property
    def declarations(self):
        declarations = []
        for _, var in self._declarations.items():
            declarations.append(var)
        return declarations

    def add(self, constraint):
        if isinstance(constraint, bool):
            if not constraint:
                self._status = 'unsat'
            return
        assert isinstance(constraint, Bool)
        self._send('(assert %s)' % constraint)
        self._constraints.append(constraint)
        self._status = 'unknown'

    @property
    def constraints(self):
        constraints = []
        for c in self._constraints:
            constraints.append('(assert %s)' % c)
        return constraints


def issymbolic(x):
    return isinstance(x, Symbol)


def isconcrete(x):
    return not issymbolic(x)


def UGT(a, b):
    return {
        (int, int): lambda: a > b if a >= 0 and b >= 0 else None,
        (long, int): lambda: a > b if a >= 0 and b >= 0 else None,
        (int, long): lambda: a > b if a >= 0 and b >= 0 else None,
        (long, long): lambda: a > b if a >= 0 and b >= 0 else None,
        (BitVec, int): lambda: a.ugt(b),
        (int, BitVec): lambda: not b.ule(a),
        (BitVec, long): lambda: a.ugt(b),
        (long, BitVec): lambda: not b.ule(a),
        (BitVec, BitVec): lambda: a.ugt(b),
    }[(type(a), type(b))]()


def UGE(a, b):
    return {
        (int, int): lambda: a >= b if a >= 0 and b >= 0 else None,
        (long, int): lambda: a >= b if a >= 0 and b >= 0 else None,
        (int, long): lambda: a >= b if a >= 0 and b >= 0 else None,
        (long, long): lambda: a >= b if a >= 0 and b >= 0 else None,
        (BitVec, int): lambda: a.uge(b),
        (BitVec, long): lambda: a.uge(b),
        (int, BitVec): lambda: not b.ult(a),
        (long, BitVec): lambda: not b.ult(a),
        (BitVec, BitVec): lambda: a.uge(b),
    }[(type(a), type(b))]()


def ULT(a, b):
    return {
        (int, int): lambda: a < b if a >= 0 and b >= 0 else None,
        (long, int): lambda: a < b if a >= 0 and b >= 0 else None,
        (int, long): lambda: a < b if a >= 0 and b >= 0 else None,
        (long, long): lambda: a < b if a >= 0 and b >= 0 else None,
        (BitVec, int): lambda: a.ult(b),
        (BitVec, long): lambda: a.ult(b),
        (int, BitVec): lambda: not b.uge(a),
        (long, BitVec): lambda: not b.uge(a),
        (BitVec, BitVec): lambda: a.ult(b),
    }[(type(a), type(b))]()


def ULE(a, b):
    return {
        (int, int): lambda: a <= b if a >= 0 and b >= 0 else None,
        (long, int): lambda: a <= b if a >= 0 and b >= 0 else None,
        (int, long): lambda: a <= b if a >= 0 and b >= 0 else None,
        (long, long): lambda: a <= b if a >= 0 and b >= 0 else None,
        (BitVec, int): lambda: a.ule(b),
        (BitVec, long): lambda: a.ule(b),
        (int, BitVec): lambda: not b.ugt(a),
        (long, BitVec): lambda: not b.ugt(a),
        (BitVec, BitVec): lambda: a.ule(b),
    }[(type(a), type(b))]()


def ZEXTEND(x, size):
    if isinstance(x, (int, long)):
        return x & ((1 << size) - 1)
    assert isinstance(x, BitVec) and size - x.size >= 0
    if size - x.size != 0:
        return BitVec(size, '(_ zero_extend %s)' % (size - x.size), x)
    else:
        return x


def SEXTEND(x, size_src, size_dest):
    if type(x) in (int, long):
        if x > (1 << (size_src - 1)):
            x -= 1 << size_src
        return x & ((1 << size_dest) - 1)
    return BitVec(size_dest, '(_ sign_extend %s)' % (size_dest - x.size), x)


def UDIV(a, b):
    if type(a) is BitVec:
        return a.udiv(b)
    elif type(b) is BitVec:
        return a.rudiv(b)
    if a < 0 or b < 0:
        raise Exception()
    return a / b


def UREM(a, b):
    if type(a) is BitVec:
        return a.urem(b)
    elif type(b) is BitVec:
        return b.rurem(a)
    if a < 0 or b < 0:
        raise Exception()
    return a % b


def EXTRACT(s, offset, size):
    if isinstance(s, BitVec):
        if offset == 0 and size == s.size:
            return s
        else:
            return BitVec(size, '(_ extract %d %d)' % (offset + size - 1, offset), s)
    else:
        return (s >> offset) & ((1 << size) - 1)


def ITEBV(size, cond, true, false):
    if type(cond) in (bool, int, long):
        if cond:
            return true
        else:
            return false
    assert type(cond) is Bool
    if type(true) in (int, long):
        if size == 1:
            true = BitVec(size, '#' + bin(true & 1)[1:])
        else:
            true = BitVec(size, '#x%0*x' % (size / 4, true & ((1 << size) - 1)))
    if type(false) in (int, long):
        if size == 1:
            false = BitVec(size, '#' + bin(false & 1)[1:])
        else:
            false = BitVec(size, '#x%0*x' % (size / 4, false & ((1 << size) - 1)))
    return BitVec(size, 'ite', cond, true, false)


def CONCAT(size, *args):
    if any([isinstance(x, Symbol) for x in args]):
        if len(args) > 1:
            def cast(e):
                if type(e) in (int, long):
                    if size == 1:
                        return BitVec(size, '#' + bin(e & 1)[1:])
                    return BitVec(size, '#x%0*x' % (size / 4, e & ((1 << size) - 1)))
                return e

            return BitVec(size * len(args), 'concat', *map(cast, args))
        else:
            return args[0]
    else:
        result = 0
        for arg in args:
            result = (result << size) | arg
        return result


_ord = ord


def ord(s):
    if isinstance(s, BitVec):
        if s.size == 8:
            return s
        else:
            return BitVec(8, '(_ extract 7 0)', s)
    elif isinstance(s, int):
        return s & 0xff
    else:
        return _ord(s)


_chr = chr


def chr(s):
    if isinstance(s, BitVec):
        if s.size == 8:
            return s
        else:
            return BitVec(8, '(_ extract 7 0)', s)
    else:
        return _chr(s & 0xff)
