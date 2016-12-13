# Change Log

All notable changes to this project will be documented in this file.

## [0.4][unreleased]
### Added
### Changed
### Fixed
### Removed

## [0.3] - 2016-12-13
### Added
- Add new BARF tool, BARFcg, for CG recovery.
- Add support for CG recovery (x86 and ARM).
- Add new BARF tool, BARFcfg, for CFG recovery.
- Add support for ARM CFG recovery.
- Add support for more ARM instructions.
- Add support for data tainting in ReilEmulator.
- Add support for pre/post instruction execution callback function in ReilEmulator.
- Add support for REIL extension instruction (SEXT, SDIV, SMOD).
- Add support for more x86 instructions.

### Changed
- Improve CFG recovery functionality.
- Refactor basickblock module.
- Replace PyBFD with PyELFTools.
- Improve SMT performace.
- Refactor smtlibv2 module.
- Overall directory restructure.
- Improve ARM disassembly integration to Capstone Engine.
- Overall improvements to CFG recovery and rendering.
- Refactor reilemulator module.
- Overall improvements to package's tests.

### Fixed
- Multiple bug fixes.

### Removed
- Remove PyAsmJIT package from the repository (move to its own repo).

## [0.2.1] - 2015-04-07
### Fixed
- Fix Python logging module setup issue.

## [0.2] - 2015-04-06
### Added
- BARFgadgets now find gadgets in ARM binaries.
- Add support for the ARM architecture (32 btis).
- Add support for more x86 instructions.
- Memory consumption reduction through the use of '__slots__'.
- BARFgadgets now supports gadgets ending in RET-imm16, JMP and CALL instructions.

### Changed
- Overall improvements to x86 arch package (major changes that ended up in performance increase of translation up to 3x!).
- Overall improvements to reil package (minor changes).
- New reil translation scheme for x86 instructions.
- x86Translator and x86InstructionTranslator modules were merged.
- Some methods of X86ArchitectureInformation class were renamed to improve naming consistency.
- x86 flags are now represented using a single bit (instead of one byte). Also, each flag (CF, ZF, etc.) is now an alias of the correspondent bit of the {e/r}flags register.

### Fixed
- Fixes in x86 instruction translations (mostly flags update issues.)
- Fix missing registers in X86ArchitectureInformation class.
- Fix SMT translation for STR instruction when dst operand is bigger than src operand.

### Removed
- x86instruction and x86intructiontranslator modules were removed.

[unreleased]: https://github.com/programa-stic/barf-project/compare/v0.3...develop
[0.3]: https://github.com/programa-stic/barf-project/compare/v0.2.1...v0.3
[0.2.1]: https://github.com/programa-stic/barf-project/compare/v0.2...v0.2.1
[0.2]: https://github.com/programa-stic/barf-project/compare/v0.1...v0.2
