#! /usr/bin/env python

from __future__ import absolute_import
from __future__ import print_function

from barf.barf import BARF

if __name__ == "__main__":
    # x86
    # ======================================================================= #
    #
    # Open file
    #
    barf = BARF("./samples/bin/loop2.x86")

    # 080483ec <main>:
    #  80483ec:       55                      push   ebp
    #  80483ed:       89 e5                   mov    ebp,esp
    #  80483ef:       83 ec 10                sub    esp,0x10
    #  80483f2:       c7 45 f8 00 00 00 00    mov    DWORD PTR [ebp-0x8],0x0
    #  80483f9:       c7 45 fc 0a 00 00 00    mov    DWORD PTR [ebp-0x4],0xa
    #  8048400:       eb 08                   jmp    804840a <main+0x1e>
    #  8048402:       83 45 f8 01             add    DWORD PTR [ebp-0x8],0x1
    #  8048406:       83 6d fc 01             sub    DWORD PTR [ebp-0x4],0x1
    #  804840a:       83 7d fc 00             cmp    DWORD PTR [ebp-0x4],0x0
    #  804840e:       75 f2                   jne    8048402 <main+0x16>
    #  8048410:       8b 45 f8                mov    eax,DWORD PTR [ebp-0x8]
    #  8048413:       c9                      leave
    #  8048414:       c3                      ret

    #
    # Code emulation
    #
    context_out = barf.emulate(start=0x080483ec, end=0x08048414)

    print("{}: {}".format("eax", hex(context_out['registers']["eax"])))

    assert context_out['registers']["eax"] == 0xa

    # ARM
    # ======================================================================= #
    #
    # Open file
    #
    barf = BARF("./samples/bin/loop2.arm")

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
    # Code emulation
    #
    context_out = barf.emulate(start=0x8390, end=0x83e0)  # ARM mode

    print("{}: {}".format("r3", hex(context_out['registers']["r3"])))

    assert context_out['registers']["r3"] == 0xa
