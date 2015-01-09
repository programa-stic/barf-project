import unittest

from barf.arch import ARCH_ARM_MODE_32
from barf.arch.arm.armparser import ArmParser


class ArmParser32BitsTests(unittest.TestCase):

    def setUp(self):
        self._parser = ArmParser(ARCH_ARM_MODE_32)

    def test_data_processing_instructions(self):
        
        inst_samples = [
            "add r0, r0, r1, lsl #4",
            "mov r0, #0",
            "add r3, r3, #1",
            "cmp r7, #1000",
            "bic r9, r8, #0xff00",
            "mov r2, r0",
            "add r4, r3, r2",
            "cmp r7, r8",
            "mov r2, r0, lsl #2",
            "add r9, r5, r5, lsl #3",
            "sub r10, r9, r8, lsr #4",
            "mov r12, r4, ror r3",
            "rsb r9, r5, r8, rrx"
        ]
        
        for i in inst_samples:
            asm = self._parser.parse(i)
            self.assertEqual(str(asm), i)

def main():
    unittest.main()


if __name__ == '__main__':
    main()
