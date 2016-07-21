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


def extract_sign_bit(value, size):
    return value >> (size-1)

def twos_complement(value, size):
    return 2**size - value

def extract_value(main_value, offset, size):
    return (main_value >> offset) & 2**size-1

def insert_value(main_value, value_to_insert, offset, size):
    main_value &= ~((2**size-1) << offset)
    main_value |= (value_to_insert & 2**size-1) << offset

    return main_value

def to_reil_address(asm_address, offset=0x0):
    return (asm_address << 0x08) | (offset & 0xff)

def to_asm_address(reil_address):
    return reil_address >> 0x08

class VariableNamer(object):
    """Variable Name Generator."""

    def __init__(self, base_name, separator="_", counter=0):
        self._base_name = base_name
        self._counter_init = counter
        self._counter_curr = counter
        self._separator = separator

    def get_init(self):
        """Return initial name.
        """
        suffix = self._separator + "%s" % str(self._counter_init)

        return self._base_name + suffix

    def get_current(self):
        """Return current name.
        """
        suffix = self._separator + "%s" % str(self._counter_curr)

        return self._base_name + suffix

    def get_next(self):
        """Return next name.
        """
        self._counter_curr += 1

        suffix = self._separator + "%s" % str(self._counter_curr)

        return self._base_name + suffix

    def reset(self):
        """Restart name counter.
        """
        self._counter_curr = self._counter_init
