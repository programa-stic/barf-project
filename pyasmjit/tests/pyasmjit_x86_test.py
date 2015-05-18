#! /usr/bin/env python

import pyasmjit

code = """\
add rax, rbx
"""

# code = """\
# mov rax, 0x3
# mov rbx, 0x4
# imul rax, rbx
# """

context_in = {
    'rax' : 0x1,
    'rbx' : 0x2,
    'rcx' : 0x1,
    'rdx' : 0x1,
    'rdi' : 0x1,
    'rsi' : 0x1,
    'rflags' : 0x202,
}

print code
print context_in

rv, context_out = pyasmjit.x86_execute(code, context_in)

print context_out
