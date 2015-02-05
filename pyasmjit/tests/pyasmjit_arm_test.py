#! /usr/bin/env python

import pyasmjit
from pprint import pprint

code = """\

push {r0 - r12}


ldr r1, [r0, #(16 * 4)]
msr apsr_nzcvq, r1

# FALTA R0!!
add r0, r0, #4
ldm r0, {r1 - r12}
sub r0, r0, #4


# CODE:
add r1, r2, r3


add r0, r0, #4
stm r0, {r1 - r12}
sub r0, r0, #4

mrs r1, apsr
str r1, [r0, #(16 * 4)]

pop {r0 - r12}

blx lr
"""

context_in = {
    'r0' : 0x0,
    'r1' : 0x1,
    'r2' : 0x2,
    'r3' : 0x3,
    'r4' : 0x4,
    'r5' : 0x5,
    'apsr' : 0x0,
}

# print code
# print context_in

rv, context_out = pyasmjit.arm_execute(code, context_in)

# pprint({k: hex(v) for k, v in context_out.items()})

print("APSR: " + hex(context_out['apsr']))
