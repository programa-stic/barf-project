# PyAsmJIT

*PyAsmJIT* is a Python package for x86_64/ARM assembly code generation and
execution.

# History

This package was developed in order to test BARF instruction translation from
x86_64/ARM to REIL. The main idea is to be able to run fragments of code natively.
Then, the same fragment is translated to REIL and executed in a REIL VM. Finally,
both final contexts (the one obtained through native execution and the one from
emulation) are compare for differences.

# Installation

The following command installs the package:

```bash
$ sudo python setup.py install
```

# Dependecies

* [NASM] : the Netwide Assembler, a portable 80x86 assembler

# Quickstart

The following extract shows how to execute on-the-fly a fragment of
assembly code.

```python
import pyasmjit

code = """\
add rax, rbx
"""

context_in = {
    'rax' : 0x1,
    'rbx' : 0x2,
    'rcx' : 0x1,
    'rdx' : 0x1,
    'rdi' : 0x1,
    'rsi' : 0x1,
}

print code
print context_in

rv, context_out = pyasmjit.x86_execute(code, context_in)

print context_out
```

# Overview

The inner workings of the package is very simple. PyAsmJIT communicates with
*nasm* using the ``subprocess`` package. Once the machine code is generated, it
is place in a memory location previously reserved with the proper permissions
flags. Then, the code is executed as a thread.

# Limitations

Currently:

* It does not handle memory operations.
* It only works with 64-bits code.

[NASM]: http://nasm.us/
