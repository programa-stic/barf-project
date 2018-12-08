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


# "Logical Instructions"
# ============================================================================ #
def _translate_and(self, tb, instruction):
    # Flags Affected
    # The OF and CF flags are cleared; the SF, ZF, and PF flags are
    # set according to the result. The state of the AF flag is
    # undefined.

    oprnd0 = self._reg_acc_translator.read(tb, instruction.operands[0])
    oprnd1 = self._reg_acc_translator.read(tb, instruction.operands[1])

    tmp0 = tb.temporal(oprnd0.size * 2)

    tb.add(self._builder.gen_and(oprnd0, oprnd1, tmp0))

    # Flags : OF, CF
    self._flag_translator.clear_flag(tb, self._flags.of)
    self._flag_translator.clear_flag(tb, self._flags.cf)

    # Flags : SF, ZF, PF
    self._flag_translator.update_sf(tb, oprnd0, tmp0)
    self._flag_translator.update_zf(tb, oprnd0, tmp0)
    self._flag_translator.update_pf(tb, tmp0)

    # Flags : AF
    self._flag_translator.undefine_flag(tb, self._flags.af)

    self._reg_acc_translator.write(tb, instruction.operands[0], tmp0)


def _translate_not(self, tb, instruction):
    # Flags Affected
    # None.

    oprnd0 = self._reg_acc_translator.read(tb, instruction.operands[0])

    tmp0 = tb.temporal(oprnd0.size * 2)

    imm0 = tb.immediate((2 ** oprnd0.size) - 1, oprnd0.size)

    tb.add(self._builder.gen_xor(oprnd0, imm0, tmp0))

    self._reg_acc_translator.write(tb, instruction.operands[0], tmp0)


def _translate_or(self, tb, instruction):
    # Flags Affected
    # The OF and CF flags are cleared; the SF, ZF, and PF flags are
    # set according to the result. The state of the AF flag is
    # undefined.

    oprnd0 = self._reg_acc_translator.read(tb, instruction.operands[0])
    oprnd1 = self._reg_acc_translator.read(tb, instruction.operands[1])

    tmp0 = tb.temporal(oprnd0.size * 2)

    tb.add(self._builder.gen_or(oprnd0, oprnd1, tmp0))

    # Flags : OF, CF
    self._flag_translator.clear_flag(tb, self._flags.of)
    self._flag_translator.clear_flag(tb, self._flags.cf)

    # Flags : SF, ZF, PF
    self._flag_translator.update_sf(tb, oprnd0, tmp0)
    self._flag_translator.update_zf(tb, oprnd0, tmp0)
    self._flag_translator.update_pf(tb, tmp0)

    # Flags : AF
    self._flag_translator.undefine_flag(tb, self._flags.af)

    self._reg_acc_translator.write(tb, instruction.operands[0], tmp0)


def _translate_xor(self, tb, instruction):
    # Flags Affected
    # The OF and CF flags are cleared; the SF, ZF, and PF flags are set
    # according to the result. The state of the AF flag is
    # undefined.

    oprnd0 = self._reg_acc_translator.read(tb, instruction.operands[0])
    oprnd1 = self._reg_acc_translator.read(tb, instruction.operands[1])

    tmp0 = tb.temporal(oprnd0.size * 2)

    tb.add(self._builder.gen_xor(oprnd0, oprnd1, tmp0))

    # Flags : OF, CF
    self._flag_translator.clear_flag(tb, self._flags.of)
    self._flag_translator.clear_flag(tb, self._flags.cf)

    # Flags : SF, ZF, PF
    self._flag_translator.update_sf(tb, oprnd0, tmp0)
    self._flag_translator.update_zf(tb, oprnd0, tmp0)
    self._flag_translator.update_pf(tb, tmp0)

    # Flags : AF
    self._flag_translator.undefine_flag(tb, self._flags.af)

    self._reg_acc_translator.write(tb, instruction.operands[0], tmp0)


dispatcher = {
    'and': _translate_and,
    'not': _translate_not,
    'or': _translate_or,
    'xor': _translate_xor,
}
