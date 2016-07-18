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

import unittest

from barf.core.reil import ReilParser


class ReilParserTests(unittest.TestCase):

    def setUp(self):
        self._parser = ReilParser()

    def test_add(self):
        instrs  = ["str [eax, EMPTY, t0]"]
        instrs += ["str [ebx, EMPTY, t1]"]
        instrs += ["add [t0, t1, t2]"]
        instrs += ["str [t2, EMPTY, eax]"]

        instrs_parse = self._parser.parse(instrs)

        self.assertEqual(str(instrs_parse[0]), "str   [UNK eax, EMPTY, UNK t0]")
        self.assertEqual(str(instrs_parse[1]), "str   [UNK ebx, EMPTY, UNK t1]")
        self.assertEqual(str(instrs_parse[2]), "add   [UNK t0, UNK t1, UNK t2]")
        self.assertEqual(str(instrs_parse[3]), "str   [UNK t2, EMPTY, UNK eax]")

    def test_parse_operand_size(self):
        instrs  = ["str [DWORD eax, EMPTY, DWORD t0]"]
        instrs += ["str [eax, EMPTY, DWORD t0]"]
        instrs += ["str [eax, EMPTY, t0]"]

        instrs_parse = self._parser.parse(instrs)

        self.assertEqual(instrs_parse[0].operands[0].size, 32)
        self.assertEqual(instrs_parse[0].operands[1].size, 0)
        self.assertEqual(instrs_parse[0].operands[2].size, 32)

        self.assertEqual(instrs_parse[1].operands[0].size, None)
        self.assertEqual(instrs_parse[1].operands[1].size, 0)
        self.assertEqual(instrs_parse[1].operands[2].size, 32)

        self.assertEqual(instrs_parse[2].operands[0].size, None)
        self.assertEqual(instrs_parse[2].operands[1].size, 0)
        self.assertEqual(instrs_parse[2].operands[2].size, None)


def main():
    unittest.main()


if __name__ == '__main__':
    main()
