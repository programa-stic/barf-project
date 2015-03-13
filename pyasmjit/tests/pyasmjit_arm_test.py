#! /usr/bin/env python

import pyasmjit

code = """\

movs r8, r2, lsl #31
mov r7, #0x7FFFFFFF
mov r8, #0x7FFFFFFF
adds r7, r7, r8
#subs r10, r10, #0xFFFFFFFF
"""

context_in = {
    'r0' : 0x0,
    'r1' : 0x1,
    'r2' : 0x2,
    'r3' : 0x3,
    'r4' : 0x4,
    'r5' : 0x5,
    'r6' : 0x6,
    'r7' : 0x7,
    'r8' : 0x8,
    'r9' : 0x9,
    'r10' : 0xa,
    'r11' : 0xb,
    'r12' : 0xc,
    'apsr' : 0x0,
}

print code
print context_in

rv, context_out, mem = pyasmjit.arm_execute(code, context_in)

print context_out
