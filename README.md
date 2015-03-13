# BARF Project

| **Latest Release:** | v0.1                                                            |
|--------------------:|:----------------------------------------------------------------|
|            **URL:** | https://github.com/programa-stic/barf-project/releases/tag/v0.1 |

So far the *BARF Project* is composed of the following packages:

* **BARF** : A multiplatform open source Binary Analysis and Reverse engineering Framework
* **BARFgadgets** : A tool built upon BARF that lets you *search*, *classifiy* and *verify* ROP gadgets inside a binary program.
* **PyAsmJIT** : A JIT for the Intel x86_64 architecture.

All packages were tested on Ubuntu 12.04 and 14.04 (x86_64).

## BARF

*BARF* is a Python package for binary analysis and reverse engineering. It can:

* Load binary programs in different formats (``ELF``, ``PE``, etc),
* It supports the Intel x86 architecture for 32 and 64 bits,
* It supports the ARM architecture for 32 bits,
* It operates on an intermediate language ([REIL]) thus all analysis algorithm are architecture-agnostic,
* It has integration with [Z3] and [CVC4] SMT solvers which means that you can express fragments of code as formulae and check restrictions on them.

For more information, see [README](./barf/README.md).

## BARFgadgets

``BARFgadgets`` is a Python script built upon BARF that lets you *search*,
*classifiy* and *verify* ROP gadgets inside a binary program. The *search*
stage finds all ``ret``-ended gadgets inside the binary. The *classification*
stage classifies previously found gadgets according to the following types:
No-Operation, Move Register, Load Constant, Arithmetic/Logical Operation, Load
Memory, Store Memory, Arithmetic/Logical Load, Arithmetic/Logical Store and
Undefined. This is done through instruction emulation. Finally, the
*verification* stage consists of using a SMT solver to verify the semantic
assigned to each gadget in the second stage.

For more information, see [README](./barf/tools/gadgets/README.md).

## PyAsmJIT

*PyAsmJIT* is a Python package for x86_64/ARM assembly code generation and
execution.

For more information, see [README](./pyasmjit/README.md).

# License

The BSD 2-Clause License. For more information, see [LICENSE](./LICENSE).

[Z3]: http://z3.codeplex.com
[CVC4]: http://cvc4.cs.nyu.edu/web/
[REIL]: http://www.usenix.org/legacy/event/woot10/tech/full_papers/Dullien.pdf
