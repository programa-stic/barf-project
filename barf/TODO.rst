TODO
====

``core`` Package
~~~~~~~~~~~~~~~~

SMTTranslator:

* For each instruction type, check/verify operands size (do this in a way that leaves no doubt about the semantic of an instruction.)
* Check signess of REIL to SMT translations. REIL instructions are all unsigned but SMT operations are signed, for example, bvmul.

SMTLIBV2:

* This module needs refactoring/cleannig.
* The SMT solver should return an enumeration (SAT, UNSAT, TIMEOUT, ERROR)

REIL:

* Remove ReilInstructionBuilder. It is better to have each REIL instruction as a class.
* Rethink DualInstruction.
* Refactor ReilParser. Is pyparsing really necessary?
* Remove ad-hoc RET REIL instruction.
* Provide support for REIL metadata.
* Find a way to make sure no REIL instruction end up with an operand that acts as source and destination simultaneously.
* Write semantic of every REIL instruction precisely.

``arch`` Package
~~~~~~~~~~~~~~~~

General:

* Rename ArchitectureInformation to Architecture.
* Load architecture from a file.
* Improve instruction support.
* Improve translation tests.
* Review flags handling. Use {E/R}Flags as a register instead of flags aliases such as CF.

``analysis`` package
~~~~~~~~~~~~~~~~~~~~

Gadget:

* Refactor gadget module.
* Refactor out gadgets from analysis package (move it to tools/gadgets).
* Improve verification. Include modified registers, flags and memory locations where necessary (verify that they don't change.)
* Search for more gadgets type: sysenter, int 0x80.
* Add support for missing arithmetic operations: *, /, %, <<, >>.
* Rename Arithmetic Gadget a BinaryOps Gadget.
* Improve performance of the gadgetfinder module.
* Add support for semantic search of gadgets (create small language for the purpose.)
* Unify use of ArchitectureInformation class in gadget{classifier,verifier} modules.

Code Analyzer:

* Rethink module. Review coherence and cohesion.

Basic Block:

* Improve API. Refine basic block recovery.
* Fix CFG for complex instructions (the ones that contains loop such as x86 SAR instruction REIL translation.)

Miscellaneous
~~~~~~~~~~~~~

* Fix GDB integration.
* Improve documentation.
* Improve error logging.
* Improve testing.
* Use PyLint

* Capstone: Analyze and report issues with disassemble of incomplete x86 instructions. For instance, it disassembles prefixes like 'lock' and 'rep'.
* PyBFD: Fix .DLL loading functionality.
