#! /usr/bin/env python

from barf.barf import BARF

if __name__ == "__main__":
    #
    # Open file
    #
    barf = BARF("../../samples/bin/loop2.x86")

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
    # REIL emulation
    #
    context_out = barf.emulate(start=0x080483ec, end=0x08048414)

    print("{}: {}".format("eax", hex(context_out['registers']["eax"])))

    assert context_out['registers']["eax"] == 0xa
