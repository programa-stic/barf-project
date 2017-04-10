# BARF : Binary Analysis and Reverse engineering Framework

The analysis of binary code is a crucial activity in many areas of the computer sciences and software engineering disciplines ranging from software security and program analysis to reverse engineering. Manual binary analysis is a difficult and time-consuming task and there are software tools that seek to automate or assist human analysts. However, most of these tools have several technical and commercial restrictions that limit access and use by a large portion of the academic and practitioner communities. *BARF* is an open source binary analysis framework that aims to support a wide range of binary code analysis tasks that are common in the information security discipline. It is a scriptable platform that supports instruction lifting from multiple architectures, binary translation to an intermediate representation, an extensible framework for code analysis plugins and interoperation with external tools such as debuggers, SMT solvers and instrumentation tools. The framework is designed primarily for human-assisted analysis but it can be fully automated.

The *BARF project* includes *BARF* and related tools and packages. So far the
project is composed of the following items:

* **BARF** : A multiplatform open source Binary Analysis and Reverse engineering Framework
* **PyAsmJIT** : A JIT for the Intel x86_64 and ARM architecture.
* Tools built upon *BARF*:
    * **BARFgadgets** : Lets you *search*, *classifiy* and *verify* ROP gadgets inside a binary program.
    * **BARFcfg** : Lets you recover the control-flow graph of the functions of a binary program.
    * **BARFcg** : Lets you recover the call graph of the functions of a binary program.

For more information, see:

* *BARF: A multiplatform open source Binary Analysis and Reverse engineering Framework* (Whitepaper) [[en](./doc/papers/barf.pdf)]
* *BARFing Gadgets* (ekoparty2014 presentation) [[es](./doc/presentations/barfing-gadgets.ekoparty2014.es.pdf)]

Current status:

| **Latest Release** | v0.4.0                                                                 |
|-------------------:|:-----------------------------------------------------------------------|
|            **URL** | https://github.com/programa-stic/barf-project/releases/tag/v0.4.0      |
|     **Change Log** | https://github.com/programa-stic/barf-project/blob/v0.4.0/CHANGELOG.md |

> All packages were tested on Ubuntu 16.04 (x86_64).

## BARF

*BARF* is a Python package for binary analysis and reverse engineering. It can:

* Load binary programs in different formats (``ELF``, ``PE``, etc),
* It supports the Intel x86 architecture for 32 and 64 bits,
* It supports the ARM architecture for 32 bits,
* It operates on an intermediate language ([REIL]) thus all analysis algorithm are architecture-agnostic,
* It has integration with [Z3] and [CVC4] SMT solvers which means that you can express fragments of code as formulae and check restrictions on them.

It is currently *under development*.

### Installation

*BARF* depends on the following SMT solvers:

* [Z3] : A high-performance theorem prover being developed at Microsoft Research.
* [CVC4] : An efficient open-source automatic theorem prover for satisfiability modulo theories (SMT) problems.

The following command installs *BARF* on your system:

```bash
$ sudo python setup.py install
```

You can also install it locally:

```bash
$ sudo python setup.py install --user
```

#### Notes

* Only one SMT solver is needed in order to work. You may choose between Z3 and CVC4 or install both. You can use the [``barf-install-solver.sh``](./scripts) script which downloads and install both solver.
* To run some tests you need to install PyAsmJIT first.
* You may need to install [Graphviz]: ``sudo apt-get install graphviz``

### Quickstart

This is a very simple example which shows how to open a binary file and print each instruction with its translation to the intermediate language (*REIL*).

```python
from barf import BARF

# Open binary file.
barf = BARF("examples/bin/x86/branch1")

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

We can check restrictions on code using a SMT solver. For instance, suppose you have the following code:

```
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

And you want to know what values you have to assign to memory locations ``ebp-0x4``, ``ebp-0x8`` and ``ebp-0xc`` in order to obtain a specific value in ``eax`` register after executing the code.

First, we add the instructions to the analyzer component.

```python
from barf import BARF

# Open ELF file
barf = BARF("examples/bin/x86/constraint1")

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

You can see these and more examples in the [examples](./examples) directory.

### Overview

The framework is divided in three main components: **core**, **arch** and **analysis**.

#### Core

This component contains essential modules:

* ``REIL`` : Provides definitions for the REIL language. It, also, implements an *emulator* and a *parser*.
* ``SMT`` : Provides means to interface with *Z3* SMT solver. Also, it provides functionality to translate REIL instructions to SMT expressions.
* ``BI`` : The *Binary Interface* module is responsible for loading binary files for processing (it uses [PEFile] and [PyELFTools].)

#### Arch

Each supported architecture is provided as a subcomponent which contains the following modules.

* ``Architecture`` : Describes the architecture, i.e., registers, memory address size.
* ``Translator`` : Provides translators to REIL for each supported instruction.
* ``Disassembler`` : Provides disassembling functionalities (it uses Capstone.)
* ``Parser`` : Transforms instruction in string to object form (provided by the *Instruction* module.)

#### Analysis

So far this component consists of two modules: *Control-Flow Graph*, *Call Graph* and *Code Analyzer*. The first two, provides functionality for CFG and CG recovery, respectively. The latter, its a high-level interface to the SMT-solver-related functionalities.

### Directory Structure

```
barf/       Framework's main directory.
doc/        Documentation.
examples/   Basic example scripts that show various functionalities.
scripts/    Installation scripts.
tests/      BARF package tests.
tools/      Tools build upon BARF.
```

### Notes

SMT solver interfacing is provided by the file ``core/smt/smtlibv2.py`` taken from [PySymEmu].

## Tools

### BARFgadgets

``BARFgadgets`` is a Python script built upon BARF that lets you *search*, *classifiy* and *verify* ROP gadgets inside a binary program. The *search* stage finds all ``ret``-, ``jmp``- and ``call``-ended gadgets inside the binary. The *classification* stage classifies previously found gadgets according to the following types:

* No-Operation,
* Move Register,
* Load Constant,
* Arithmetic/Logical Operation,
* Load Memory,
* Store Memory,
* Arithmetic/Logical Load,
* Arithmetic/Logical Store and
* Undefined.

This is done through instruction emulation. Finally, the *verification* stage consists of using a SMT solver to verify the semantic assigned to each gadget in the second stage.

```
usage: BARFgadgets [-h] [--version] [--bdepth BDEPTH] [--idepth IDEPTH] [-u]
                   [-c] [-v] [-o OUTPUT] [-t] [--sort {addr,depth}] [--color]
                   [--show-binary] [--show-classification] [--show-invalid]
                   [--summary SUMMARY] [-r {8,16,32,64}]
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
  --show-invalid        Show invalid gadget, i.e., gadgets that were
                        classified but did not pass the verification process.
  --summary SUMMARY     Save summary to file.
  -r {8,16,32,64}       Filter verified gadgets by operands register size.
```

For more information, see [README](./tools/gadgets/README.md).

### BARFcfg

``BARFcfg`` is a Python script built upon BARF that lets you recover the
control-flow graph of a binary program.

```
usage: BARFcfg [-h] [-s SYMBOL_FILE] [-f {txt,pdf,png,dot}] [-t]
               [-d OUTPUT_DIR] [-b] [--show-reil]
               [--immediate-format {hex,dec}] [-a | -r RECOVER]
               filename

Tool for recovering CFG of a binary.

positional arguments:
  filename              Binary file name.

optional arguments:
  -h, --help            show this help message and exit
  -s SYMBOL_FILE, --symbol-file SYMBOL_FILE
                        Load symbols from file.
  -f {txt,pdf,png,dot}, --format {txt,pdf,png,dot}
                        Output format.
  -t, --time            Print process time.
  -d OUTPUT_DIR, --output-dir OUTPUT_DIR
                        Output directory.
  -b, --brief           Brief output.
  --show-reil           Show REIL translation.
  --immediate-format {hex,dec}
                        Output format.
  -a, --recover-all     Recover all functions.
  -r RECOVER, --recover RECOVER
                        Recover specified functions by address (comma
                        separated).
```

For more information, see [README](./tools/cfg/README.md).

### BARFcg

``BARFcg`` is a Python script built upon BARF that lets you recover the
call graph of a binary program.

```
usage: BARFcg [-h] [-s SYMBOL_FILE] [-f {pdf,png,dot}] [-t] [-a | -r RECOVER]
              filename

Tool for recovering CG of a binary.

positional arguments:
  filename              Binary file name.

optional arguments:
  -h, --help            show this help message and exit
  -s SYMBOL_FILE, --symbol-file SYMBOL_FILE
                        Load symbols from file.
  -f {pdf,png,dot}, --format {pdf,png,dot}
                        Output format.
  -t, --time            Print process time.
  -a, --recover-all     Recover all functions.
  -r RECOVER, --recover RECOVER
                        Recover specified functions by address (comma
                        separated).
```

For more information, see [README](./tools/cg/README.md).

## PyAsmJIT

*PyAsmJIT* is a Python package for x86_64/ARM assembly code generation and execution.

This package was developed in order to test BARF instruction translation from x86_64/ARM to REIL. The main idea is to be able to run fragments of code natively. Then, the same fragment is translated to REIL and executed in a REIL VM. Finally, both final contexts (the one obtained through native execution and the one from emulation) are compare for differences.

For more information, see [PyAsmJIT].

## License

The BSD 2-Clause License. For more information, see [LICENSE](./LICENSE).

[CVC4]: http://cvc4.cs.nyu.edu/web/
[Capstone]: http://www.capstone-engine.org
[PyAsmJIT]: https://github.com/programa-stic/pyasmjit
[PySymEmu]: https://github.com/feliam/pysymemu
[REIL]: http://www.usenix.org/legacy/event/woot10/tech/full_papers/Dullien.pdf
[Z3]: https://github.com/Z3Prover/z3
[Graphviz]: http://graphviz.org/
