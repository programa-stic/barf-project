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


# "Enter and Leave Instructions"
# ============================================================================ #
def _translate_leave(self, tb, instruction):
    # Flags Affected
    # None.

    tmp0 = tb.temporal(self._sp.size)

    tb.add(self._builder.gen_str(self._bp, self._sp))
    tb.add(self._builder.gen_ldm(self._sp, self._bp))
    tb.add(self._builder.gen_add(self._sp, self._ws, tmp0))
    tb.add(self._builder.gen_str(tmp0, self._sp))


# "Miscellaneous Instructions"
# ============================================================================ #
def _translate_hlt(self, tb, instruction):
    # Flags Affected
    # None.

    tb.add(self._builder.gen_unkn())


def _translate_lea(self, tb, instruction):
    # Flags Affected
    # None.

    oprnd1 = self._reg_acc_translator.resolve_memory_access(tb, instruction.operands[1])

    self._reg_acc_translator.write(tb, instruction.operands[0], oprnd1)


def _translate_nop(self, tb, instruction):
    # Flags Affected
    # None.

    tb.add(self._builder.gen_nop())


dispatcher = {
    # "Enter and Leave Instructions"
    'leave': _translate_leave,

    # "Miscellaneous Instructions"
    'hlt': _translate_hlt,
    'lea': _translate_lea,
    'nop': _translate_nop,
}
