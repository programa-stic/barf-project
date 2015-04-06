# Change Log

All notable changes to this project will be documented in this file.

## [Unreleased][unreleased]

## [0.2] 2015-04-06
### Added
- BARF: BARFgadgets now find gadgets in ARM binaries.
- PyAsmJIT: Memory allocation mechanism (alloc/free style).
- PyAsmJIT: Add support for the ARM architecture (32 bits).
- BARF: Add support for the ARM architecture (32 bits).
- BARF: Add support for more x86 instructions.
- BARF: Memory consumption reduction through the use of '__slots__'.
- BARF: BARFgadgets now supports gadgets ending in RET-imm16, JMP and CALL instructions.

### Changed
- BARF: Overall improvements to x86 arch package (major changes that ended up in performance increase of translation up to 3x!).
- BARF: Overall improvements to reil package (minor changes).
- BARF: New reil translation scheme for x86 instructions.
- BARF: x86Translator and x86InstructionTranslator modules were merged.
- BARF: Some methods of X86ArchitectureInformation class were renamed to improve naming consistency.
- BARF: x86 flags are now represented using a single bit (instead of one byte). Also, each flag (CF, ZF, etc.) is now an alias of the correspondent bit of the {e/r}flags register.

### Fixed
- BARF: Fixes in x86 instruction translations (mostly flags update issues.)
- BARF: Fix missing registers in X86ArchitectureInformation class.
- BARF: Fix SMT translation for STR instruction when dst operand is bigger than src operand.
- PyAsmJIT: Fix context saving for long ints.
- PyAsmJIT: Fix missing registers when loading and saving context.

### Removed
- BARF: x86instruction and x86intructiontranslator modules were removed.

[unreleased]: https://github.com/programa-stic/barf-project/compare/v0.2...develop
[0.2]: https://github.com/programa-stic/barf-project/compare/v0.1...v0.2
