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
import weakref

from functools import wraps
from subprocess import PIPE, Popen

logger = logging.getLogger("smtlibv2")


def goaux_bv(old_method):
    @wraps(old_method)
    def new_method(self, *args, **kw_args):
        bv = old_method(self, *args, **kw_args)
        # try:
        #     bv = self.solver.simplify(bv)
        # except Exception,e:
        #     print "EXCEPTION", e
        #     import sys,traceback
        #     print '-'*60
        #     traceback.print_exc(file=sys.stdout)
        #     print '-'*60
        #     sys.stdin.readline()
        #     pass

        # if isinstance(bv, Symbol) and len(str(bv.value)) > 200 and self.solver is not None:
        #     aux = self.solver.mkBitVec(bv.size)
        #     self.solver.add(aux == bv)
        #     return aux
        return bv
    return new_method

def goaux_bool(old_method):
    @wraps(old_method)
    def new_method(self, *args, **kw_args):
        b = old_method(self, *args, **kw_args)
        if False and self.solver is not None:
            aux = self.solver.mkBool()
            self.solver.add(aux == b)
            return aux
        return b
    return new_method


class Symbol(object):

    def __init__(self, value, *children, **kwargs):
        assert type(value) in [int, long, str, bool]
        assert all([isinstance(x, Symbol) for x in children])

        solver = kwargs.get('solver', None)
        if solver is not None:
            self._solver = weakref.ref(kwargs['solver'])
        else:
            self._solver = lambda: None

        if len(children) > 0:
            self._value = '('+ str(value) +' '+ ' '.join(map(str, children)) +')'
        else:
            self._value = str(value)

    def __getstate__(self):
        state = {}
        state['solver'] = self.solver
        state['value'] = self.value
        return state

    def __setstate__(self, state):
        solver = state['solver']
        if solver is not None:
            self._solver = weakref.ref(solver)
        else:
            self._solver = lambda: None
        self._value = state['value']

    @property
    def solver(self):
        return self._solver()

    @property
    def value(self):
        return self._value

    def __str__(self):
        return str(self._value)


class BitVec(Symbol):
    ''' A symbolic bitvector '''

    def __init__(self, size, value, *children, **kwargs):
        super(BitVec, self).__init__(value, *children, **kwargs)
        # assert size in [1, 8, 16, 32, 64, 128, 256]

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
                return BitVec(self.size, '#'+bin(val&1)[1:], solver=self.solver)
            return BitVec(self.size, '#x%0*x'%(self.size/4, val&((1<<self.size)-1)), solver=self.solver)
        elif type(val) is Bool:
            raise NotImplementedError()
        elif type(val) is str:
            assert len(val) == 1 and self.size == 8
            return BitVec(self.size, '#x%02x'%ord(val), solver=self.solver)

        assert type(val) == BitVec and val.size == self.size

        return val

    @property
    def declaration(self):
        return '(declare-fun %s () (_ BitVec %d))'%(self.value, self.size)

    # These methods are called to implement the binary arithmetic operations
    # (+, -, *, //, %, divmod(), pow(), **, <<, >>, &, ^, |). For instance, to
    # evaluate the expression x + y, where x is an instance of a class that
    # has an __add__() method, x.__add__(y) is called. The __divmod__() method
    # should be the equivalent to using __floordiv__() and __mod__(); it
    # should not be related  to __truediv__() (described below). Note that
    # __pow__() should be defined to accept an optional third argument if the
    # ternary version of the built-in pow() function is to be supported.

    @goaux_bv
    def __add__(self, other):
        return BitVec(self.size, 'bvadd', self, self.cast(other), solver=self.solver)

    @goaux_bv
    def __sub__(self, other):
        return BitVec(self.size, 'bvsub', self, self.cast(other), solver=self.solver)

    @goaux_bv
    def __mul__(self, other):
        return BitVec(self.size, 'bvmul', self, self.cast(other), solver=self.solver)

    @goaux_bv
    def __mod__(self, other):
        return BitVec(self.size, 'bvsmod', self, self.cast(other), solver=self.solver)

    @goaux_bv
    def __lshift__(self, other):
        return BitVec(self.size, 'bvshl', self, self.cast(other), solver=self.solver)

    @goaux_bv
    def __rshift__(self, other):
        return BitVec(self.size, 'bvlshr', self, self.cast(other), solver=self.solver)

    @goaux_bv
    def __and__(self, other):
        return BitVec(self.size, 'bvand', self, self.cast(other), solver=self.solver)

    @goaux_bv
    def __xor__(self, other):
        return BitVec(self.size, 'bvxor', self, self.cast(other), solver=self.solver)

    @goaux_bv
    def __or__(self, other):
        return BitVec(self.size, 'bvor', self, self.cast(other), solver=self.solver)

    # The division operator (/) is implemented by these methods. The
    # __truediv__()  method is used when __future__.division is in effect,
    # otherwise __div__()  is used. If only one of these two methods is
    # defined, the object will not  support division in the alternate context;
    # TypeError will be raised instead.

    @goaux_bv
    def __div__(self, other):
        return BitVec(self.size, 'bvsdiv', self, self.cast(other), solver=self.solver)

    @goaux_bv
    def __truediv__(self, other):
        return BitVec(self.size, 'bvsdiv', self, self.cast(other), solver=self.solver)

    # These methods are called to implement the binary arithmetic operations
    # (+, -, *, /, %, divmod(), pow(), **, <<, >>, &, ^, |) with reflected
    # (swapped) operands. These functions are only called if the left operand
    # does not support the corresponding operation and the operands are of
    # different types. [2] For instance, to evaluate the expression x - y,
    # where y is an instance of a class that has an __rsub__() method,
    # y.__rsub__(x) is called if x.__sub__(y) returns NotImplemented.

    @goaux_bv
    def __radd__(self, other):
        return BitVec(self.size, 'bvadd', self.cast(other), self, solver=self.solver)

    @goaux_bv
    def __rsub__(self, other):
        return BitVec(self.size, 'bvsub', self.cast(other), self, solver=self.solver)

    @goaux_bv
    def __rmul__(self, other):
        return BitVec(self.size, 'bvmul', self, self.cast(other), solver=self.solver)

    @goaux_bv
    def __rmod__(self, other):
        return BitVec(self.size, 'bvmod', self.cast(other), self, solver=self.solver)

    @goaux_bv
    def __rtruediv__(self, other):
        return BitVec(self.size, 'bvsdiv', self.cast(other), self, solver=self.solver)

    @goaux_bv
    def __rdiv__(self, other):
        return BitVec(self.size, 'bvsdiv', self.cast(other), self, solver=self.solver)

    @goaux_bv
    def __rlshift__(self, other):
        return BitVec(self.size, 'bvshl', self.cast(other), self, solver=self.solver)

    @goaux_bv
    def __rrshift__(self, other):
        return BitVec(self.size, 'bvlshr', self.cast(other), self, solver=self.solver)

    @goaux_bv
    def __rand__(self, other):
        return BitVec(self.size, 'bvand', self, self.cast(other), solver=self.solver)

    @goaux_bv
    def __rxor__(self, other):
        return BitVec(self.size, 'bvxor', self, self.cast(other), solver=self.solver)

    @goaux_bv
    def __ror__(self, other):
        return BitVec(self.size, 'bvor', self, self.cast(other), solver=self.solver)

    @goaux_bv
    def __invert__(self):
        return BitVec(self.size, 'bvnot', self, solver=self.solver)

    # These are the so-called "rich comparison" methods, and are called for
    # comparison operators in preference to __cmp__() below. The
    # correspondence between operator symbols and method names is as follows:
    # x<y calls x.__lt__(y), x<=y calls x.__le__(y), x==y calls x.__eq__(y),
    # x!=y and x<>y call x.__ne__(y), x>y calls x.__gt__(y), and x>=y calls
    # x.__ge__(y).

    @goaux_bool
    def __lt__(self, other):
        return Bool('bvslt', self, self.cast(other), solver=self.solver)

    @goaux_bool
    def __le__(self, other):
        return Bool('bvsle', self, self.cast(other), solver=self.solver)

    @goaux_bool
    def __eq__(self, other):
        return Bool('=', self, self.cast(other), solver=self.solver)

    @goaux_bool
    def __ne__(self, other):
        return Bool('not', self == other, solver=self.solver)

    @goaux_bool
    def __gt__(self, other):
        return Bool('bvsgt', self, self.cast(other), solver=self.solver)

    @goaux_bool
    def __ge__(self, other):
        return Bool('bvsge', self, self.cast(other), solver=self.solver)

    @goaux_bv
    def __neg__(self):
        return BitVec(self.size, 'bvneg', self, solver=self.solver)

    @goaux_bool
    def ugt(self, other):
        return Bool('bvugt', self, self.cast(other), solver=self.solver)

    @goaux_bool
    def uge(self, other):
        return Bool('bvuge', self, self.cast(other), solver=self.solver)

    @goaux_bool
    def ult(self, other):
        return Bool('bvult', self, self.cast(other), solver=self.solver)

    @goaux_bool
    def ule(self, other):
        return Bool('bvule', self, self.cast(other), solver=self.solver)

    @goaux_bv
    def udiv(self, other):
        return BitVec(self.size, 'bvudiv', self, self.cast(other), solver=self.solver)

    @goaux_bv
    def rudiv(self, other):
        return BitVec(self.size, 'bvudiv', self.cast(other), self, solver=self.solver)

    @goaux_bv
    def urem(self, other):
        return BitVec(self.size, 'bvurem', self, self.cast(other), solver=self.solver)

    @goaux_bv
    def rrem(self, other):
        return BitVec(self.size, 'bvurem', self.cast(other), self, solver=self.solver)

    @goaux_bv
    def smod(self, other):
        return BitVec(self.size, 'bvsmod', self.cast(other), self, solver=self.solver)


class Bool(Symbol):

    def __init__(self, value, *children, **kwargs):
        super(Bool, self).__init__(value, *children, **kwargs)

    def cast(self, val):
        if isinstance(val, (int, long, bool)):
            return Bool(str(bool(val)).lower(), solver=self.solver)

        assert isinstance(val, Bool)

        return val

    @property
    def declaration(self):
        return '(declare-fun %s () Bool)'%self.value

    @goaux_bool
    def __invert__(self):
        return Bool('not', self, solver=self.solver)

    @goaux_bool
    def __eq__(self, other):
        return Bool('=', self, self.cast(other), solver=self.solver)

    @goaux_bool
    def __ne__(self, other):
        return Bool('not', self == other, solver=self.solver)

    @goaux_bool
    def __xor__(self, other):
        return Bool('xor', self, self.cast(other), solver=self.solver)

    def __nonzero__(self):
        raise NotImplementedError()

    @goaux_bool
    def __and__(self, other):
        return Bool('and', self, self.cast(other), solver=self.solver)

    @goaux_bool
    def __or__(self, other):
        return Bool('or', self, self.cast(other), solver=self.solver)

    @goaux_bool
    def __rand__(self, other):
        return Bool('and', self, self.cast(other), solver=self.solver)

    @goaux_bool
    def __ror__(self, other):
        return Bool('or', self, self.cast(other), solver=self.solver)

    @goaux_bool
    def __rxor__(self, other):
        return Bool('xor', self, self.cast(other), solver=self.solver)


class Array_(Symbol):
    def __init__(self, size, value, *children, **kwargs):
        super(Array_, self).__init__(value, *children, **kwargs)

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
            return BitVec(self.size, '#x%0*x'%(self.size/4, val&((1<<self.size)-1)), solver=self.solver)
        elif type(val) is Bool:
            raise NotImplementedError()
        elif type(val) is str:
            assert len(val) == 1 and self.size == 8
            return BitVec(self.size, '#x%02x'%ord(val), solver=self.solver)

        assert type(val) == BitVec and val.size == self.size

        return val

    def cast_value(self, val):
        if type(val) in (int, long):
            return BitVec(8, '#x%02x'%(val&((1<<self.size)-1)), solver=self.solver)
        elif type(val) is Bool:
            raise NotImplementedError()
        elif type(val) is str:
            assert len(val) == 1
            return BitVec(32, '#x%02x'%ord(val), solver=self.solver)

        assert type(val) == BitVec and val.size == 8

        return val

    @goaux_bv
    def select(self, key):
        return BitVec(8, 'select', self, self.cast_key(key), solver=self.solver)

    @goaux_bv
    def store(self, key, value):
        return Array_(self.size, '(store %s %s %s)'%(self, self.cast_key(key), self.cast_value(value)), solver=self.solver)

    def __eq__(self, other):
        assert isinstance(other, Array_) and other.size == self.size

        return Bool('=', self, other, solver=self.solver)

    def __neq__(self, other):
        assert isinstance(other, Array_) and other.size == self.size

        return Bool('not', self.__eq__(other), solver=self.solver)


class Array(object):
    def __init__(self, size, name, *children, **kwargs):
        self.array = Array_(size, name, *children, **kwargs)
        self.name = name
        self.cache = {}
        self.declaration = '(declare-fun %s () (Array (_ BitVec %d) (_ BitVec 8)))'%(name, size)

    def __getstate__(self):
        state = {}
        state['declaration'] = self.declaration
        state['array'] = self.array
        state['name'] = self.name
        state['cache'] = self.cache

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

    def __eq__(self, other):
        assert isinstance(other.array, Array_) and other.array.size == self.array.size

        return Bool('=', self.array, other.array, solver=self.array.solver)

    def __neq__(self, other):
        assert isinstance(other.array, Array_) and other.array.size == self.array.size

        return Bool('not', self.__eq__(other), solver=self.array.solver)


class Z3Solver(object):
    def __init__(self):
        ''' Build a solver intance.
            This is implemented using an external native solver via a subprocess.
            Everytime a new symbol or assertion is added a smtlibv2 command is
            sent to the solver.
            The actual state is also mantained in memory to be able to save and
            restore the state.
            The analisys may be saved to disk and continued after a while or
            forked in memory or even sent over the network.
        '''
        self._status = 'unknown'
        self._sid = 0
        self._stack = []
        self._declarations = {}
        self._constraints = list()
        self.input_symbols = list()
        self._proc = Popen('z3 -smt2 -in', shell=True, stdin=PIPE, stdout=PIPE)

        # Fix z3 declaration scopes
        self._send("(set-option :global-decls false)")
        self._send("(set-logic QF_AUFBV)")

    def __getstate__(self):
        state = {}
        state['sid'] = self._sid
        state['declarations'] = self._declarations
        state['constraints'] = self._constraints
        state['stack'] = self._stack
        state['input_symbols'] = self.input_symbols
        return state

    def __setstate__(self, state):
        self._status = None
        self._sid = state['sid']
        self._declarations = state['declarations']
        self._constraints = state['constraints']
        self._stack = state['stack']
        self.input_symbols = state['input_symbols']
        self._proc = Popen('z3 -smt2 -in', shell=True, stdin=PIPE, stdout=PIPE)

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
            self.input_symbols = list()
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
        ''' Returns an unique id. '''
        self._sid += 1
        return self._sid

    def _send(self, cmd):
        ''' Send a string to the solver.
            @param cmd: a SMTLIBv2 command (ex. (check-sat))
        '''
        logger.debug('>%s', cmd)
        self._proc.stdin.writelines((str(cmd), '\n'))

    def _recv(self):
        ''' Reads the response from the solver '''
        def readline():
            buf = self._proc.stdout.readline()
            return buf, buf.count('('), buf.count(')')
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
        logger.debug('<%s', buf)
        if '(error' in bufl[0]:
            print("Error in simplify: %s" % str(buf))
            raise Exception("Error in smtlib <"+str(self)+">")
        return buf

    def __str__(self):
        ''' Returns a smtlib representation of the current state '''
        buf = ''
        for d in self._declarations.values():
            buf += d.declaration +'\n'
        for a in self.constraints:
            buf += '%s\n'%a
        return buf

    def getallvalues(self, x, maxcnt=30):
        ''' Returns a list with all the possible values for the symbol x'''
        assert self.check() == 'sat'
        assert type(x) is BitVec
        result = []
        self.push()
        try:
            aux = self.mkBitVec(x.size)
            self.add(aux == x)
            r = self.check()
            val = None
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

    def max(self, X, M=10000):
        ''' Iterativelly finds the maximum value for a symbol.
            @param X: a symbol or expression
            @param M: maximun number of iterations allowed
        '''
        assert self.check() == 'sat'
        assert type(X) is BitVec
        self.push()
        aux = self.mkBitVec(X.size)
        self.add(aux == X)
        try:
            last_value = None
            i = 0
            while True:
                r = self.check()
                if r == 'unsat':
                    if last_value != None:
                        return last_value
                    else:
                        raise Exception("max failed")
                elif r == 'sat':
                    last_value = self.getvalue(aux)
                    self.add(UGT(aux, last_value))
                    i = i + 1
                else:
                    raise Exception("solver failed %s"%r)
                if (i > M):
                    raise Exception("Maximum not found, maximum number of iterations was reached")
        finally:
            self.pop()

    def min(self, X, M=10000):
        ''' Iterativelly finds the minimum value for a symbol.
            @param X: a symbol or expression
            @param M: maximun number of iterations allowed
        '''
        assert self.check() == 'sat'
        assert type(X) is BitVec
        self.push()
        aux = self.mkBitVec(X.size)
        self.add(aux == X)
        try:
            last_value = None
            i = 0
            while True:
                r = self.check()
                if r == 'unsat':
                    if last_value != None:
                        return last_value
                    else:
                        raise Exception("max failed")
                elif r == 'sat':
                    last_value = self.getvalue(aux)
                    self.add(ULT(aux, last_value))
                    i = i + 1
                else:
                    raise Exception("solver failed")
                if (i > M):
                    raise Exception("Maximum not found, maximum number of iterations was reached")
        finally:
            self.pop()

    def minmax(self, x, iters=10000):
        ''' Returns the min and max possible values for x. '''
        if isconcrete(x):
            return x, x
        m = self.min(x, iters)
        M = self.max(x, iters)
        return m, M

    def push(self):
        ''' Pushes and save the current state.'''
        if self._status is None:
            self.reset()
        self._send('(push 1)')
        self._stack.append((self._sid, self._declarations, self._constraints))
        self._declarations = copy.copy(self._declarations)
        self._constraints = copy.copy(self._constraints)

    def pop(self):
        ''' Recall the last pushed state. '''
        self._send('(pop 1)')
        self._sid, self._declarations, self._constraints = self._stack.pop()
        self._status = 'unknown'

    def check(self):
        ''' Check the satisfiability of the current state '''
        if self._status is None:
            self.reset()
        if self._status == 'unknown':
            self._send('(check-sat)')
            self._status = self._recv()
        return self._status

    def getvalue(self, val):
        ''' Ask the solver for one possible assigment for val using currrent set
            of constraints.
            The current set of assertions must be sat.
            @param val: an expression or symbol '''
        if isconcrete(val):
            return val
        assert self.check() == 'sat'
        self._send('(get-value (%s))'%val)
        ret = self._recv()
        assert ret.startswith('((') and ret.endswith('))')
        return int(ret.split(' ')[-1][2:-2], 16)

    def getvaluebyname(self, name):
        ''' Ask the solver for one possible assigment for val using currrent set
            of constraints.
            The current set of assertions must be sat.
            @param val: an expression or symbol '''
        val = self._declarations[name]

        assert self.check() == 'sat'
        self._send('(get-value (%s))'%val)
        ret = self._recv()
        assert ret.startswith('((') and ret.endswith('))')
        return int(ret.split(' ')[-1][2:-2], 16)

    def simplify(self, val):
        ''' Ask the solver to try to simplify the expression val.
            This works only with z3.
            @param val: a symbol or expression.
        '''
        if self._status is None:
            self.reset()
        #file('simplifications.txt','a').write('(simplify %s  :expand-select-store true :pull-cheap-ite true )'%val+'\n')
        if not isinstance(val, (BitVec, Bool)):
            return val
        self._send('(simplify %s  :expand-select-store true :pull-cheap-ite true )'%val)
        result = self._recv()

        #TODO clean move casts somewhere else.  BitVec8, BitVec16, BitVec32, BitVec64, BitVec127 __new__() ?
        if type(val) is BitVec:
            if result.startswith('#x'):
                return int(result[2:], 16)
            return BitVec(val.size, result, solver=val.solver)
        elif type(val) is Bool:
            return {'false':False, 'true':True}.get(result, Bool(result, solver=val.solver))

    def mkBitVec(self, size, name='V', is_input=False):
        ''' Creates a symbol in the constrains store and names it name'''
        assert size in [1, 8, 16, 32, 40, 64, 72, 128, 256]
        if name in self._declarations:
            return self._declarations[name]

        bv = BitVec(size, name, solver=self)
        self._declarations[name] = bv
        self._send(bv.declaration)

        if is_input:
            self.input_symbols.append((bv,))

        return bv

    def mkArray(self, size=32, name='A', is_input=False, max_size=100):
        ''' Creates a symbols array in the constrains store and names it name'''
        assert size in [8, 16, 32, 64]
        if name in self._declarations:
            return self._declarations[name]

        arr = Array(size, name, solver=self)
        self._declarations[name] = arr
        self._send(arr.declaration)
        if is_input:
            self.input_symbols.append((arr, max_size))
        return arr

    def mkArrayNew(self, size=32, name='A'):
        ''' Creates a symbols array in the constrains store and names it name'''
        assert size in [8, 16, 32, 64]

        arr = Array(size, name, solver=self)

        return arr

    def mkBool(self, name='B', is_input=False):
        ''' Creates a symbols array in the constrains store and names it name'''
        if name in self._declarations:
            name = '%s_%d'%(name, self._get_sid())
        b = Bool(name, solver=self)
        self._declarations[name] = b
        self._send(b.declaration)
        if is_input:
            self.input_symbols.append((b,))
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
            self._send('(assert %s) ; %s'%(constraint, comment))
        else:
            self._send('(assert %s)'%constraint)
        self._constraints.append((constraint, comment))
        self._status = 'unknown'

    @property
    def constraints(self):
        constraints = []
        for c, comment in self._constraints:
            if comment:
                constraints.append('(assert %s) ; %s'%(c, comment))
            else:
                constraints.append('(assert %s)'%c)
        return constraints


class CVC4Solver(object):
    def __init__(self):
        ''' Build a solver intance.
            This is implemented using an external native solver via a subprocess.
            Everytime a new symbol or assertion is added a smtlibv2 command is
            sent to the solver.
            The actual state is also mantained in memory to be able to save and
            restore the state.
            The analisys may be saved to disk and continued after a while or
            forked in memory or even sent over the network.
        '''
        self._status = 'unknown'
        self._sid = 0
        self._stack = []
        self._declarations = {}
        self._constraints = list()
        self.input_symbols = list()
        self._proc = Popen('cvc4 --incremental --lang=smt2', shell=True, stdin=PIPE, stdout=PIPE)

        # Fix CVC4 declaration scopes
        self._send("(set-logic QF_AUFBV)")
        self._send("(set-option :produce-models true)")

    def __getstate__(self):
        state = {}
        state['sid'] = self._sid
        state['declarations'] = self._declarations
        state['constraints'] = self._constraints
        state['stack'] = self._stack
        state['input_symbols'] = self.input_symbols
        return state

    def __setstate__(self, state):
        self._status = None
        self._sid = state['sid']
        self._declarations = state['declarations'] #weakref.WeakValueDictionary(state['declarations'])
        self._constraints = state['constraints']
        self._stack = state['stack']
        self.input_symbols = state['input_symbols']
        self._proc = Popen('cvc4 --incremental --lang=smt2', shell=True, stdin=PIPE, stdout=PIPE)

        # Fix CVC4 declaration scopes
        self._send("(set-logic QF_AUFBV)")
        self._send("(set-option :produce-models true)")

    def reset(self, full=False):
        self._proc.kill()
        self._proc.wait()
        self._proc = Popen('cvc4 --incremental --lang=smt2', shell=True, stdin=PIPE, stdout=PIPE)

        if full:
            self._status = 'unknown'
            self._sid = 0
            self._stack = []
            self._declarations = {}
            self._constraints = list()
            self.input_symbols = list()

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
        ''' Returns an unique id. '''
        self._sid += 1
        return self._sid

    def _send(self, cmd):
        ''' Send a string to the solver.
            @param cmd: a SMTLIBv2 command (ex. (check-sat))
        '''
        logger.debug('>%s', cmd)
        self._proc.stdin.writelines((str(cmd), '\n'))

    def _recv(self):
        ''' Reads the response from the solver '''
        def readline():
            buf = self._proc.stdout.readline()
            return buf, buf.count('('), buf.count(')')
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
        logger.debug('<%s', buf)
        if '(error' in bufl[0]:
            print("Error in simplify: %s" % str(buf))
            raise Exception("Error in smtlib <"+str(self)+">")
        return buf

    def __str__(self):
        ''' Returns a smtlib representation of the current state '''
        buf = ''
        for d in self._declarations.values():
            buf += d.declaration +'\n'
        for a in self.constraints:
            buf += '%s\n'%a
        return buf

    def getallvalues(self, x, maxcnt=30):
        ''' Returns a list with all the possible values for the symbol x'''
        assert self.check() == 'sat'
        assert type(x) is BitVec
        result = []
        self.push()
        try:
            aux = self.mkBitVec(x.size)
            self.add(aux == x)
            r = self.check()
            val = None
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

    def max(self, X, M=10000):
        ''' Iterativelly finds the maximum value for a symbol.
            @param X: a symbol or expression
            @param M: maximun number of iterations allowed
        '''
        assert self.check() == 'sat'
        assert type(X) is BitVec
        self.push()
        aux = self.mkBitVec(X.size)
        self.add(aux == X)
        try:
            last_value = None
            i = 0
            while True:
                r = self.check()
                if r == 'unsat':
                    if last_value != None:
                        return last_value
                    else:
                        raise Exception("max failed")
                elif r == 'sat':
                    last_value = self.getvalue(aux)
                    self.add(UGT(aux, last_value))
                    i = i + 1
                else:
                    raise Exception("solver failed %s"%r)
                if (i > M):
                    raise Exception("Maximum not found, maximum number of iterations was reached")
        finally:
            self.pop()

    def min(self, X, M=10000):
        ''' Iterativelly finds the minimum value for a symbol.
            @param X: a symbol or expression
            @param M: maximun number of iterations allowed
        '''
        assert self.check() == 'sat'
        assert type(X) is BitVec
        self.push()
        aux = self.mkBitVec(X.size)
        self.add(aux == X)
        try:
            last_value = None
            i = 0
            while True:
                r = self.check()
                if r == 'unsat':
                    if last_value != None:
                        return last_value
                    else:
                        raise Exception("max failed")
                elif r == 'sat':
                    last_value = self.getvalue(aux)
                    self.add(ULT(aux, last_value))
                    i = i + 1
                else:
                    raise Exception("solver failed")
                if (i > M):
                    raise Exception("Maximum not found, maximum number of iterations was reached")
        finally:
            self.pop()

    def minmax(self, x, iters=10000):
        ''' Returns the min and max possible values for x. '''
        if isconcrete(x):
            return x, x
        m = self.min(x, iters)
        M = self.max(x, iters)
        return m, M

    def push(self):
        ''' Pushes and save the current state.'''
        if self._status is None:
            self.reset()
        self._send('(push 1)')
        self._stack.append((self._sid, self._declarations, self._constraints))
        self._declarations = copy.copy(self._declarations)
        self._constraints = copy.copy(self._constraints)

    def pop(self):
        ''' Recall the last pushed state. '''
        self._send('(pop 1)')
        self._sid, self._declarations, self._constraints = self._stack.pop()
        self._status = 'unknown'

    def check(self):
        ''' Check the satisfiability of the current state '''
        if self._status is None:
            self.reset()
        if self._status == 'unknown':
            self._send('(check-sat)')
            self._status = self._recv()
        return self._status

    def getvalue(self, val):
        ''' Ask the solver for one possible assigment for val using currrent set
            of constraints.
            The current set of assertions must be sat.
            @param val: an expression or symbol '''
        if isconcrete(val):
            return val
        assert self.check() == 'sat'
        self._send('(get-value (%s))'%val)
        ret = self._recv()
        assert ret.startswith('((') and ret.endswith('))')
        ret = ret[2:-2]
        _, ret = ret[:ret.rfind('(')], ret[ret.rfind('('):]
        assert ret.startswith('(') and ret.endswith(')')
        index = ret.rfind('(')
        var_value, _ = ret[index+3:-1].split(' ', 1)
        assert var_value.startswith('bv')
        value = int(var_value[2:])
        return value

    def getvaluebyname(self, name):
        ''' Ask the solver for one possible assigment for val using currrent set
            of constraints.
            The current set of assertions must be sat.
            @param val: an expression or symbol '''
        val = self._declarations[name]

        assert self.check() == 'sat'
        self._send('(get-value (%s))'%val)
        ret = self._recv()
        assert ret.startswith('((') and ret.endswith('))')

        _, ret = ret[2:-2].split(' ', 1)

        assert ret.startswith('(_') and ret.endswith(')')

        var_value, _ = ret[3:-1].split(' ', 1)

        assert var_value.startswith('bv')

        value = int(var_value[2:])

        return value

    def simplify(self, val):
        ''' Ask the solver to try to simplify the expression val.
            This works only with z3.
            @param val: a symbol or expression.
        '''
        if self._status is None:
            self.reset()
        if not isinstance(val, (BitVec, Bool)):
            return val
        self._send('(simplify %s  :expand-select-store true :pull-cheap-ite true )'%val)
        result = self._recv()

        if type(val) is BitVec:
            if result.startswith('#x'):
                return int(result[2:], 16)
            return BitVec(val.size, result, solver=val.solver)
        elif type(val) is Bool:
            return {'false':False, 'true':True}.get(result, Bool(result, solver=val.solver))

    def mkBitVec(self, size, name='V', is_input=False):
        ''' Creates a symbol in the constrains store and names it name'''
        assert size in [1, 8, 16, 32, 40, 64, 72, 128, 256]
        if name in self._declarations:
            return self._declarations[name]

        bv = BitVec(size, name, solver=self)
        self._declarations[name] = bv
        self._send(bv.declaration)

        if is_input:
            self.input_symbols.append((bv,))

        return bv

    def mkArray(self, size=32, name='A', is_input=False, max_size=100):
        ''' Creates a symbols array in the constrains store and names it name'''
        assert size in [8, 16, 32, 64]
        if name in self._declarations:
            return self._declarations[name]

        arr = Array(size, name, solver=self)
        self._declarations[name] = arr #.array
        self._send(arr.declaration)
        if is_input:
            self.input_symbols.append((arr, max_size))
        return arr

    def mkArrayNew(self, size=32, name='A'):
        ''' Creates a symbols array in the constrains store and names it name'''
        assert size in [8, 16, 32, 64]

        arr = Array(size, name, solver=self)

        return arr

    def mkBool(self, name='B', is_input=False):
        ''' Creates a symbols array in the constrains store and names it name'''
        if name in self._declarations:
            name = '%s_%d'%(name, self._get_sid())
        b = Bool(name, solver=self)
        self._declarations[name] = b
        self._send(b.declaration)
        if is_input:
            self.input_symbols.append((b,))
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
        self._send('(assert %s)'%constraint)
        self._constraints.append(constraint)
        self._status = 'unknown'

    @property
    def constraints(self):
        constraints = []
        for c in self._constraints:
            constraints.append('(assert %s)'%c)
        return constraints


def issymbolic(x):
    return isinstance(x, Symbol)

def isconcrete(x):
    return not issymbolic(x)

def AND(a, b):
    return a & b

def OR(a, b):
    return a | b

def UGT(a, b):
    return {
        (int, int)       : lambda: a > b if a >= 0 and b >= 0 else None,
        (long, int)      : lambda: a > b if a >= 0 and b >= 0 else None,
        (int, long)      : lambda: a > b if a >= 0 and b >= 0 else None,
        (long, long)     : lambda: a > b if a >= 0 and b >= 0 else None,
        (BitVec, int)    : lambda: a.ugt(b),
        (int, BitVec)    : lambda: b.ule(a) == False,
        (BitVec, long)   : lambda: a.ugt(b),
        (long, BitVec)   : lambda: b.ule(a) == False,
        (BitVec, BitVec) : lambda: a.ugt(b),
    }[(type(a), type(b))]()

def UGE(a, b):
    return {
        (int, int)       : lambda: a >= b if a >= 0 and b >= 0 else None,
        (long, int)      : lambda: a >= b if a >= 0 and b >= 0 else None,
        (int, long)      : lambda: a >= b if a >= 0 and b >= 0 else None,
        (long, long)     : lambda: a >= b if a >= 0 and b >= 0 else None,
        (BitVec, int)    : lambda: a.uge(b),
        (BitVec, long)   : lambda: a.uge(b),
        (int, BitVec)    : lambda: b.ult(a) == False,
        (long, BitVec)   : lambda: b.ult(a) == False,
        (BitVec, BitVec) : lambda: a.uge(b),
    }[(type(a), type(b))]()

def ULT(a, b):
    return {
        (int, int)       : lambda: a < b if a >= 0 and b >= 0 else None,
        (long, int)      : lambda: a < b if a >= 0 and b >= 0 else None,
        (int, long)      : lambda: a < b if a >= 0 and b >= 0 else None,
        (long, long)     : lambda: a < b if a >= 0 and b >= 0 else None,
        (BitVec, int)    : lambda: a.ult(b),
        (BitVec, long)   : lambda: a.ult(b),
        (int, BitVec)    : lambda: b.uge(a) == False,
        (long, BitVec)   : lambda: b.uge(a) == False,
        (BitVec, BitVec) : lambda: a.ult(b),
    }[(type(a), type(b))]()

def ULE(a, b):
    return {
        (int, int)       : lambda: a <= b if a >= 0 and b >= 0 else None,
        (long, int)      : lambda: a <= b if a >= 0 and b >= 0 else None,
        (int, long)      : lambda: a <= b if a >= 0 and b >= 0 else None,
        (long, long)     : lambda: a <= b if a >= 0 and b >= 0 else None,
        (BitVec, int)    : lambda: a.ule(b),
        (BitVec, long)   : lambda: a.ule(b),
        (int, BitVec)    : lambda: b.ugt(a) == False,
        (long, BitVec)   : lambda: b.ugt(a) == False,
        (BitVec, BitVec) : lambda: a.ule(b),
    }[(type(a), type(b))]()

def ZEXTEND(x, size):
    if isinstance(x, (int, long)):
        return x & ((1<<size)-1)
    assert isinstance(x, BitVec) and size-x.size >= 0
    if size-x.size != 0:
        return BitVec(size, '(_ zero_extend %s)'%(size-x.size), x, solver=x.solver)
    else:
        return x

def SEXTEND(x, size_src, size_dest):
    if type(x) in (int, long):
        if x > (1<<(size_src-1)):
            x -= 1<<size_src
        return x & ((1<<size_dest)-1)
    return BitVec(size_dest, '(_ sign_extend %s)'%(size_dest-x.size), x, solver=x.solver)

def UDIV(a, b):
    if type(a) is BitVec:
        return a.udiv(b)
    elif type(b) is BitVec:
        return a.rudiv(b)
    if a < 0 or b < 0:
        raise Exception()
    return a/b

def UREM(a, b):
    if type(a) is BitVec:
        return a.urem(b)
    elif type(b) is BitVec:
        return b.rurem(a)
    if a < 0 or b < 0:
        raise Exception()
    return a%b

def EXTRACT(s, offset, size):
    if isinstance(s, BitVec):
        if offset == 0 and size == s.size:
            return s
        else:
            return BitVec(size, '(_ extract %d %d)'%(offset+size-1, offset), s, solver=s.solver)
    else:
        return (s>>offset)&((1<<size)-1)

def ITEBV(size, cond, true, false):
    if type(cond) in (bool, int, long):
        if cond:
            return true
        else:
            return false
    assert type(cond) is Bool
    if type(true) in (int, long):
        if size == 1:
            true = BitVec(size, '#'+bin(true&1)[1:], solver=cond.solver)
        else:
            true = BitVec(size, '#x%0*x'%(size/4, true&((1<<size)-1)), solver=cond.solver)
    if type(false) in (int, long):
        if size == 1:
            false = BitVec(size, '#'+bin(false&1)[1:], solver=cond.solver)
        else:
            false = BitVec(size, '#x%0*x'%(size/4, false&((1<<size)-1)), solver=cond.solver)
    return BitVec(size, 'ite', cond, true, false, solver=cond.solver)

def CONCAT(size, *args):
    if any([isinstance(x, Symbol) for x in args]):
        if len(args) > 1:
            solver = None
            for x in args:
                if isinstance(x, Symbol):
                    solver = x.solver
                if solver is not None:
                    break
            def cast(x):
                if type(x) in (int, long):
                    if size == 1:
                        return BitVec(size, '#'+bin(x&1)[1:], solver=solver)
                    return BitVec(size, '#x%0*x'%(size/4, x&((1<<size)-1)), solver=solver)
                return x
            return BitVec(size*len(args), 'concat', *map(cast, args), solver=solver)
        else:
            return args[0]
    else:
        result = 0
        for arg in args:
            result = (result<<size) | arg
        return result

_ord = ord
def ord(s):
    if isinstance(s, BitVec):
        if s.size == 8:
            return s
        else:
            return BitVec(8, '(_ extract 7 0)', s, solver=s.solver)
    elif isinstance(s, int):
        return s&0xff
    else:
        return _ord(s)

_chr = chr
def chr(s):
    if isinstance(s, BitVec):
        if s.size == 8:
            return s
        else:
            return BitVec(8, '(_ extract 7 0)', s, solver=s.solver)
    else:
        return _chr(s&0xff)
