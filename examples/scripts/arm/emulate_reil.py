#! /usr/bin/env python

import os
import sys

from barf.barf import BARF
from barf.arch import ARCH_ARM_MODE_ARM

if __name__ == "__main__":
    #
    # Open file
    #
    try:
        filename = os.path.abspath("../../bin/arm/loop2")
        barf = BARF(filename)
    except Exception, err:
        print "[-] Error opening file : %s" % filename

        sys.exit(1)

    # 00008390 <main>:
    #     8390:    e52db004     push    {fp}        ; (str fp, [sp, #-4]!)
    #     8394:    e28db000     add    fp, sp, #0
    #     8398:    e24dd00c     sub    sp, sp, #12
    #     839c:    e3a03000     mov    r3, #0
    #     83a0:    e50b3008     str    r3, [fp, #-8]
    #     83a4:    e3a0300a     mov    r3, #10
    #     83a8:    e50b300c     str    r3, [fp, #-12]
    #     83ac:    ea000005     b    83c8 <main+0x38>
    #     83b0:    e51b3008     ldr    r3, [fp, #-8]
    #     83b4:    e2833001     add    r3, r3, #1
    #     83b8:    e50b3008     str    r3, [fp, #-8]
    #     83bc:    e51b300c     ldr    r3, [fp, #-12]
    #     83c0:    e2433001     sub    r3, r3, #1
    #     83c4:    e50b300c     str    r3, [fp, #-12]
    #     83c8:    e51b300c     ldr    r3, [fp, #-12]
    #     83cc:    e3530000     cmp    r3, #0
    #     83d0:    1afffff6     bne    83b0 <main+0x20>
    #     83d4:    e51b3008     ldr    r3, [fp, #-8]
    #     83d8:    e1a00003     mov    r0, r3
    #     83dc:    e28bd000     add    sp, fp, #0
    #     83e0:    e8bd0800     ldmfd    sp!, {fp}
    #     83e4:    e12fff1e     bx    lr

    #
    # REIL emulation
    #
    context_in = {}
    context_out = barf.emulate_full(context_in, 0x8390, 0x83e0, arch_mode=ARCH_ARM_MODE_ARM)

    print "%s : %s" % ("r3", hex(context_out['registers']["r3"]))

    assert(context_out['registers']["r3"] == 0xa)
