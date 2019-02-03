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


def func_is_non_return(address, symbols):
    return address in symbols and not symbols[address][2]


def bb_get_instr_max_width(basic_block):
    """Get maximum instruction mnemonic width
    """
    asm_mnemonic_max_width = 0

    for instr in basic_block:
        if len(instr.mnemonic) > asm_mnemonic_max_width:
            asm_mnemonic_max_width = len(instr.mnemonic)

    return asm_mnemonic_max_width


def bb_get_type(basic_block):
    if basic_block.is_entry:
        bb_type = "entry"
    elif basic_block.is_exit:
        bb_type = "exit"
    else:
        bb_type = "other"

    return bb_type


class BasicBlock(object):
    """Basic block representation.
    """

    def __init__(self):

        # List of instruction within the basic block.
        self._instrs = []

        # Start address of the basic block.
        self._address = None

        # Taken branch address. If a basic block ends in a conditional
        # instruction, this field has the address of the taken branch
        # (condition equals True)
        self._taken_branch = None

        # Similar to taken branch but it holds the target address of
        # the jump when the condition is false.
        self._not_taken_branch = None

        # If a basic block ends in a direct jump or in an instruction
        # different from a conditional jump, this fields holds the
        # address of the jump or next instruction.
        self._direct_branch = None

        self._label = None

        self._is_entry = False

        self._is_exit = False

    @property
    def label(self):
        """Get basic block label.
        """
        return self._label

    @label.setter
    def label(self, value):
        """Set basic block label.
        """
        self._label = value

    @property
    def is_entry(self):
        """Get basic block is_entry.
        """
        return self._is_entry

    @is_entry.setter
    def is_entry(self, value):
        """Set basic block is_entry.
        """
        self._is_entry = value

    @property
    def is_exit(self):
        """Get basic block is_exit.
        """
        return self._is_exit

    @is_exit.setter
    def is_exit(self, value):
        """Set basic block is_exit.
        """
        self._is_exit = value

    @property
    def instrs(self):
        """Get basic block instructions.
        """
        return self._instrs

    @property
    def address(self):
        """Get basic block start address.
        """
        if len(self._instrs) == 0:
            return None

        return self._instrs[0].address

    @property
    def start_address(self):
        """Get basic block start address.
        """
        if self._instrs is []:
            return None

        return self._instrs[0].address

    @property
    def end_address(self):
        """Get basic block end address.
        """
        if self._instrs is []:
            return None

        return self._instrs[-1].address + self._instrs[-1].size - 1

    @property
    def size(self):
        """Get basic block size.
        """
        if self._instrs is []:
            return None

        return sum([instr.size for instr in self._instrs])

    @property
    def taken_branch(self):
        """Get basic block taken branch.
        """
        return self._taken_branch

    @taken_branch.setter
    def taken_branch(self, value):
        """Set basic block taken branch.
        """
        self._taken_branch = value

    @property
    def not_taken_branch(self):
        """Get basic block not taken branch.
        """
        return self._not_taken_branch

    @not_taken_branch.setter
    def not_taken_branch(self, value):
        """Set basic block not taken branch.
        """
        self._not_taken_branch = value

    @property
    def direct_branch(self):
        """Get basic block direct branch.
        """
        return self._direct_branch

    @direct_branch.setter
    def direct_branch(self, value):
        """Set basic block direct branch.
        """
        self._direct_branch = value

    @property
    def branches(self):
        """Get basic block branches.
        """
        branches = []

        if self._taken_branch:
            branches += [(self._taken_branch, 'taken')]

        if self._not_taken_branch:
            branches += [(self._not_taken_branch, 'not-taken')]

        if self._direct_branch:
            branches += [(self._direct_branch, 'direct')]

        return branches

    def contains(self, address):
        """Check if an address is within the range of a basic block.
        """
        return self.address <= address <= self.end_address

    def empty(self):
        """Check if a basic block is empty.
        """
        return len(self._instrs) == 0

    def __key(self):
        return (self._instrs,
                self._address,
                self._taken_branch,
                self._not_taken_branch,
                self._direct_branch,
                self._label,
                self._is_entry,
                self._is_exit)

    def __str__(self):
        lines = ["Basic Block @ {:#x}".format(self.address if self.address else 0)]

        asm_fmt = "{:#x}    {}"
        reil_fmt = "{:#x}:{:02d} {}"

        for asm_instr in self._instrs:
            lines += [asm_fmt.format(asm_instr.address, asm_instr)]

            for reil_instr in asm_instr.ir_instrs:
                lines += [reil_fmt.format(reil_instr.address >> 0x8, reil_instr.address & 0xff, reil_instr)]

        return "\n".join(lines)

    def __eq__(self, other):
        # Assumes that you are comparing basic block from the same binary
        return self.address == other.address and self.end_address == other.end_address

    def __ne__(self, other):
        return not self.__eq__(other)

    def __hash__(self):
        return hash(self.__key())

    def __iter__(self):
        for instr in self._instrs:
            yield instr

    def __len__(self):
        return len(self._instrs)

    def __getstate__(self):
        state = {
            '_instrs': self._instrs,
            '_address': self._address,
            '_taken_branch': self._taken_branch,
            '_not_taken_branch': self._not_taken_branch,
            '_direct_branch': self._direct_branch,
        }

        return state

    def __setstate__(self, state):
        self._instrs = state['_instrs']
        self._address = state['_address']
        self._taken_branch = state['_taken_branch']
        self._not_taken_branch = state['_not_taken_branch']
        self._direct_branch = state['_direct_branch']
