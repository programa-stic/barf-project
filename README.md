# BARF Project

The analysis of binary code is a crucial activity in many areas of the
computer sciences and software engineering disciplines ranging from software
security and program analysis to reverse engineering. Manual binary analysis
is a difficult and time-consuming task and there are software tools that seek
to automate or assist human analysts. However, most of these tools have
several technical and commercial restrictions that limit access and use by a
large portion of the academic and practitioner communities. *BARF* is an open
source binary analysis framework that aims to support a wide range of binary
code analysis tasks that are common in the information security discipline.
It is a scriptable platform that supports instruction lifting from
multiple architectures, binary translation to an intermediate representation,
an extensible framework for code analysis plugins and interoperation with
external tools such as debuggers, SMT solvers and instrumentation tools. The
framework is designed primarily for human-assisted analysis but it can be
fully automated.

The *BARF project* includes *BARF* and related tools and packages. So far the
project is composed of the following items:

* **BARF** : A multiplatform open source Binary Analysis and Reverse engineering Framework
* **PyAsmJIT** : A JIT for the Intel x86_64 and ARM architecture.
* Tools:
    * **BARFgadgets** : A tool built upon BARF that lets you *search*, *classifiy* and *verify* ROP gadgets inside a binary program.

For more information, see:

* *BARF: A multiplatform open source Binary Analysis and Reverse engineering Framework* (Whitepaper) [[en](./documentation/papers/barf.pdf)]
* *BARFing Gadgets* (ekoparty2014 presentation) [[es](./documentation/presentations/barfing-gadgets.ekoparty2014.es.pdf)]

Current status:

| **Latest Release** | v0.2.1                                                                 |
|-------------------:|:-----------------------------------------------------------------------|
|            **URL** | https://github.com/programa-stic/barf-project/releases/tag/v0.2.1      |
|     **Change Log** | https://github.com/programa-stic/barf-project/blob/v0.2.1/CHANGELOG.md |

> All packages were tested on Ubuntu 12.04 and 14.04 (x86_64).

### BARF

*BARF* is a Python package for binary analysis and reverse engineering. It can:

* Load binary programs in different formats (``ELF``, ``PE``, etc),
* It supports the Intel x86 architecture for 32 and 64 bits,
* It supports the ARM architecture for 32 bits,
* It operates on an intermediate language ([REIL]) thus all analysis algorithm are architecture-agnostic,
* It has integration with [Z3] and [CVC4] SMT solvers which means that you can express fragments of code as formulae and check restrictions on them.

For more information, see [README](./barf/README.md).

### BARFgadgets

``BARFgadgets`` is a Python script built upon BARF that lets you *search*,
*classifiy* and *verify* ROP gadgets inside a binary program. The *search*
stage finds all ``ret``-, ``jmp``- and ``call``-ended gadgets inside the
binary. The *classification* stage classifies previously found gadgets
according to the following types:

* No-Operation,
* Move Register,
* Load Constant,
* Arithmetic/Logical Operation,
* Load Memory,
* Store Memory,
* Arithmetic/Logical Load,
* Arithmetic/Logical Store and
* Undefined.

This is done through instruction emulation. Finally, the
*verification* stage consists of using a SMT solver to verify the semantic
assigned to each gadget in the second stage.

For more information, see [README](./barf/tools/gadgets/README.md).

### PyAsmJIT

*PyAsmJIT* is a Python package for x86_64/ARM assembly code generation and
execution.

This package was developed in order to test BARF instruction translation from
x86_64/ARM to REIL. The main idea is to be able to run fragments of code
natively. Then, the same fragment is translated to REIL and executed in a REIL
VM. Finally, both final contexts (the one obtained through native execution
and the one from emulation) are compare for differences.

For more information, see [README](./pyasmjit/README.md).

## Change Log

Latest changes include:

### Added
- BARF: BARFgadgets now find gadgets in ARM binaries.
- BARF: Add support for the ARM architecture (32 bits).
- BARF: Add support for more x86 instructions.

### Changed
- BARF: Overall improvements to x86 arch package (major changes that ended up in performance increase of translation up to 3x!).
- BARF: Overall improvements to reil package (minor changes).
- BARF: New reil translation scheme for x86 instructions.

### Fixed
- BARF: Fix Python logging module setup issue.
- BARF: Fixes in x86 instruction translations (mostly flags update issues.)

For more information, see [README](./pyasmjit/CHANGELOG.md).

## License

The BSD 2-Clause License. For more information, see [LICENSE](./LICENSE).

[Z3]: http://z3.codeplex.com
[CVC4]: http://cvc4.cs.nyu.edu/web/
[REIL]: http://www.usenix.org/legacy/event/woot10/tech/full_papers/Dullien.pdf
