# BARF : Binary Analysis and reverse Engineering Framework

*BARF* is a Python package for binary analysis and reverse engineering. It can:

* Load binary programs in different formats (``ELF``, ``PE``, etc),
* It supports the Intel x86 architecture for 32 and 64 bits,
* It supports the ARM architecture for 32 bits,
* It operates on an intermediate language ([REIL]) thus all analysis algorithm are architecture-agnostic,
* It has integration with [Z3] and [CVC4] SMT solvers which means that you can express fragments of code as formulae and check restrictions on them.

It is currently *under development*.

## Installation

*BARF* depends on the following:

* [Capstone] : A lightweight multi-platform, multi-architecture disassembly framework.
* [Z3] : A high-performance theorem prover being developed at Microsoft Research.
* [CVC4] : An efficient open-source automatic theorem prover for satisfiability modulo theories (SMT) problems.
* [PyBFD] : A Python interface to the GNU Binary File Descriptor (BFD) library.

The following command installs *BARF* on your system:

```bash
$ sudo python setup.py install
```

For Debian-based system, you can use an installation script that first downloads
and installs all dependencies and then installs *BARF*:

```bash
$ sudo install.sh
```

### Notes

* The installer compiles both Z3 and CVC4 so it can take some time to finish (specially, CVC4).
* Only one SMT solver is needed in order to work. You may choose between Z3 and CVC4 or install both.
* The installer was tested on Ubuntu 12.04 and 14.04 (x86_64).
* To run some tests you need to install PyAsmJIT first.

## Quickstart

This is a very simple example which shows how to open a binary file and print
each instruction with its translation to the intermediate language (*REIL*).

```python
from barf import BARF

# Open binary file.
barf = BARF("samples/toy/x86/branch1")

# Print assembly instruction.
for addr, asm_instr, reil_instrs in barf.translate():
    print("0x{addr:08x} {instr}".format(addr=addr, instr=asm_instr))

    # Print REIL translation.
    for reil_instr in reil_instrs:
        print("{indent:11s} {instr}".format(indent="", instr=reil_instr))
```

We can also recover the CFG and save it to a ``.dot`` file.

```python
# Recover CFG.
cfg = barf.recover_cfg()

# Save CFG to a .dot file.
cfg.save("branch1_cfg")
```

We can check restrictions on code using a SMT solver. For instance, suppose you
have the following code:

```objdump
 80483ed:       55                      push   ebp
 80483ee:       89 e5                   mov    ebp,esp
 80483f0:       83 ec 10                sub    esp,0x10
 80483f3:       8b 45 f8                mov    eax,DWORD PTR [ebp-0x8]
 80483f6:       8b 55 f4                mov    edx,DWORD PTR [ebp-0xc]
 80483f9:       01 d0                   add    eax,edx
 80483fb:       83 c0 05                add    eax,0x5
 80483fe:       89 45 fc                mov    DWORD PTR [ebp-0x4],eax
 8048401:       8b 45 fc                mov    eax,DWORD PTR [ebp-0x4]
 8048404:       c9                      leave
 8048405:       c3                      ret
```

And you want to know what values you have to assign to memory locations
``ebp-0x4``, ``ebp-0x8`` and ``ebp-0xc`` in order to obtain a specific value
in ``eax`` register after executing the code.

First, we add the instructions to the analyzer component.

```python
from barf import BARF

# Open ELF file
barf = BARF("samples/toy/x86/constraint1")

# Add instructions to analyze.
for addr, asm_instr, reil_instrs in barf.translate(0x80483ed, 0x8048401):
    for reil_instr in reil_instrs:
        barf.code_analyzer.add_instruction(reil_instr)
```

Then, we generate expressions for each variable of interest

```python
# Get smt expression for eax and ebp registers
eap = barf.code_analyzer.get_register_expr("eax")
ebp = barf.code_analyzer.get_register_expr("ebp")

# Get smt expressions for memory locations (each one of 4 bytes)
a = barf.code_analyzer.get_memory_expr(ebp-0x8, 4)
b = barf.code_analyzer.get_memory_expr(ebp-0xc, 4)
c = barf.code_analyzer.get_memory_expr(ebp-0x4, 4)
```

And add the desired restrictions on them.

```python
# Set range for variables
barf.code_analyzer.set_preconditions([a >= 2, a <= 100])
barf.code_analyzer.set_preconditions([b >= 2, b <= 100])

# Set desired value for the result
barf.code_analyzer.set_postcondition(c == 13)
```

Finally, we check is the restrictions we establish can be resolved.

```python
# Check satisfiability.
if barf.code_analyzer.check() == 'sat':
    print("SAT!")

    # Get concrete value for expressions.
    eax_val = barf.code_analyzer.get_expr_value(eax)
    a_val = barf.code_analyzer.get_expr_value(a)
    b_val = barf.code_analyzer.get_expr_value(b)
    c_val = barf.code_analyzer.get_expr_value(c)

    # Print values.
    print("eax : 0x{0:%08x} ({0})".format(eax_val))
    print("ebp : 0x{0:%08x} ({0})".format(ebp_val))
    print("  a : 0x{0:%08x} ({0})".format(a_val))
    print("  b : 0x{0:%08x} ({0})".format(b_val))
    print("  c : 0x{0:%08x} ({0})".format(c_val))
else:
    print("UNSAT!")
```

You can see these and more examples in the ``examples`` directory.

## Overview

The framework is divided in three main components: **core**, **arch** and
**analysis**.

### Core

This component contains essential modules:

* ``REIL`` : Provides definitions for the REIL language. It, also, implements an *emulator* and a *parser*.

* ``SMT`` : Provides means to interface with *Z3* SMT solver. Also, it provides functionality to translate REIL instructions to SMT expressions.

* ``BI`` : The *Binary Interface* module is responsible for loading binary files for processing (it uses PyBFD.)

### Arch

Each supported architecture is provided as a subcomponent which contains the
following modules.

* ``Architecture`` : Describes the architecture, i.e., registers, memory address size.

* ``Translator`` : Provides translators to REIL for each supported instruction.

* ``Disassembler`` : Provides disassembling functionalities (it uses Capstone.)

* ``Parser`` : Transforms instruction in string to object form (provided by the *Instruction* module.)

### Analysis

So far this component consists of two modules: *Basic Block* and *Code Analyzer*.
The first, provides functionality for CFG recovery. The other, its a high-level
interface to the SMT-solver-related functionalities.

## Directory Structure

```
barf/       Framework's main directory.
doc/        Documentation.
samples/    Binaries samples for testing.
examples/   Example scripts that show various functionalities.
tools/      Tools build upon BARF.
```

## Tools

``BARFgadgets`` is a tool based on BARF for ROP gadget. It finds, classifies
according to different types (data transfer, arithmetic operations, etc) and
verifies gadgets.

```
usage: BARFgadgets [-h] [--version] [--bdepth BDEPTH] [--idepth IDEPTH] [-u]
                   [-c] [-v] [-o OUTPUT] [-t] [--sort {addr,depth}] [--color]
                   [--show-binary] [--show-classification]
                   filename

Tool for finding, classifying and verifying ROP gadgets.

positional arguments:
  filename              Binary file name.

optional arguments:
  -h, --help            show this help message and exit
  --version             Display version.
  --bdepth BDEPTH       Gadget depth in number of bytes.
  --idepth IDEPTH       Gadget depth in number of instructions.
  -u, --unique          Remove duplicate gadgets (in all steps).
  -c, --classify        Run gadgets classification.
  -v, --verify          Run gadgets verification (includes classification).
  -o OUTPUT, --output OUTPUT
                        Save output to file.
  -t, --time            Print time of each processing step.
  --sort {addr,depth}   Sort gadgets by address or depth (number of
                        instructions) in ascending order.
  --color               Format gadgets with ANSI color sequences, for output
                        in a 256-color terminal or console.
  --show-binary         Show binary code for each gadget.
  --show-classification
                        Show classification for each gadget.
```

For more information, see [README](./barf/tools/gadgets/README.md).

## Notes

SMT solver interfacing is provided by the file ``core/smt/smtlibv2.py`` taken
from [PySymEmu].

# License

The BSD 2-Clause License. For more information, see [LICENSE](./LICENSE).

[Capstone]: http://www.capstone-engine.org
[Z3]: http://z3.codeplex.com
[CVC4]: http://cvc4.cs.nyu.edu/web/
[PyBFD]: http://github.com/Groundworkstech/pybfd
[PySymEmu]: http://github.com/feliam/pysymemu
[REIL]: http://www.usenix.org/legacy/event/woot10/tech/full_papers/Dullien.pdf
