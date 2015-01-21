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

    def test_load_store_instructions(self):
        
        inst_samples = [
            "ldr r2, [r3, #4]",
            "ldr r2, [r3, #-0x224]",
            "str r2, [r3, -r3]",
            "ldr r2, [r3, fp, ror #0x2]",
            "str r2, [r3, -#-0x3]",

            "ldr r2, [r3, #4]!",
            "str r1, [sp, #-0x2454]!",
            "ldr r2, [r0, -sp]!",
            "str r2, [r9, r12, lsr #0x33]!",
            "ldr r2, [r9, r12, rrx]!",

            "ldr r2, [r3], #4",
            "ldr r2, [sp], r0",
            "ldr r2, [r3], #-134314",
            "ldr r2, [r3], r3, lsl #0x12",
            
            #A3.11.4 (examples)
            "ldr r1, [r0]",
            "ldr r8, [r3, #4]",
            "ldr r12, [r13, #-4]",
            "str r2, [r1, #0x100]",
            "strb r4, [r10, #0x200]",
            "strb r10, [r7, -r4]",
            "ldr r11, [r3, r5, lsl #2]",
            "ldr r1, [r0, #4]!",
            "strb r7, [r6, #-1]!",
            "str r2, [r5], #8",
            "ldrh r12, [r13, #-6]",
            "ldrsb r4, [r10, #0xc1]",
            "strh r10, [r7, -r4]",
            "ldrsh r1, [r0, #2]!",
            "ldrsb r7, [r6, #-1]!",
            "strd r8, [r2, #0x2c]",
            "strh r2, [r5], #8",
            
            #A3.12.1 (examples of load/store multiple)
            "stmfd r13, {r0 - r12, lr}",
            "ldmfd r13, {r0 - r12, pc}",
            "ldmia r0, {r5 - r8}",
            "stmda r1, {r2, r5, r7, r11}",
            "stmda r1, {r1, r6 - r9, r11}",
        ]
        
        for i in inst_samples:
            asm = self._parser.parse(i)
            self.assertEqual(str(asm), i)

def main():
    unittest.main()


if __name__ == '__main__':
    main()
