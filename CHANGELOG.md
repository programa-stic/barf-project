# Change Log

All notable changes to this project will be documented in this file.

## [Unreleased]
### Added

### Changed

### Deprecated

### Removed

### Fixed

### Security

## [0.6.0] - 2019-11-24
### Added

- Add Python 3 compatibility.
- Add classes for managing call conventions.
- Add hook support to the `Emulator` class.
- Add `cconv` (calling convention) module.
- Add `ReilCpu` tests.
- Add `replay` tool to replay x86 execution traces.
- Add `x86.trace` module.
- Add `x86.helper` module.
- Add kao's toy project solution to the `examples` folder.
- Add flare-on 2015 challenge #2 solution to the `examples` folder.
- Add basic symbolic execution support.
- Add extra methods to `ReilSequence` and `ReilContainer` classes.
- Improve hook support of the `Emulator` class.
- Add support for `SHLD` instruction.

### Changed

- Refactor ARM package.
- Refactor ARM tests.
- Refactor x86 package.
- Refactor x86 tests.
- Improve `emulate-binary` example script.
- Refactor `ReilBuilder` class.
- Refactor instruction translators (both Intel and ARM). Group translators by category and create a module for each one.
- Improve `Emulator` class.
- Refactor `ReilCpu` tests.
- Rename `bi` module to `binary`.
- Refactor `Disassembler` class.
- Refactor `ReilEmulatorTainter` class.
- Refactor `ReilCpu` class.
- Refactor `reil.helpers` module.
- Refactor `ReilContainer` class.
- Refactor `ReilBuilder` class.
- Refactor `reil.tainter` module.
- Refactor `ReilCpu` class.
- Refactor `reil.parser` test module.
- Refactor `reil.emulator` test module.
- Rename `basicblock` package (and tests) to `graphs`.
- Rename `gadget` package (and tests) to `gadgets`.
- Rename `reilparser` module to `reil.parser`.
- Refactor `reilemulator` module. Split module into submodules: `emulator.cpu`, `emulator.emulator`, `emulator.memory`, and `emulator.tainter`.
- Refactor `arch.emulator` module.

### Deprecated

### Removed

- Remove `DualInstruction` class.

### Fixed

- Fix `RSB` ARM instruction.
- Fix control-flow graph rendering.
- Fix `SHRD` translation.
- Fix size of effective address calculation for Intel architecture.
- Fix `SHL` and `SHR` instruction translator.

### Security

## [0.5.0] - 2017-12-18
### Added
- Add architecture emulator class.
- Add support for Travis CI.
- Add tests for the `smt` package.
- Add svg ouput format for `BARFcfg` and `BARFcg` tools.
- Add `Dockerfile`.
- Add support for x86 instructions: `LAHF`, `XADD`.
- Add support for x86 sse instructions: `LDDQU`, `MOVAPS`, `MOVSD`.

### Changed
- Restructure `examples` directory and remove redundant examples.
- Restructure `tools` directory and move it into `barf` package.
- Overall code quality improvement in most modules.
- Revamp `smt` package.
- Refactor `codeanalyzer` module.
- Improve code quality of `basicblock` module.
- Restructure binary sample directory.
- Load all sections of a binary into memory by default.
- Update `ARM` architecural information.
- Refactor `emulate` method to support `x86_64`, `ARM` and `Thumb` code.

### Fixed
- Add `BAL` and `BGT` to the list of ARM branch instructions.
- Fix Capstone installation issues.
- Various fixes in the `smt` package.

### Removed
- Remove `translation_mode` parameter from x86/ARM translators.
- Remove deprecated `barf-install-solver.sh` script.
- Remove `smtlibv2.py` module dependency from `PySymEmu`.

## [0.4.0] - 2017-04-10
### Added
- Update `README` to include new command line options for all BARF tools.
- Add initial support for x86 `AVX` instruction set.
- Add support for x86 instructions: `BSF`, `BSWAP`, `BTS`, `CDQ`, `MOVSXD` and `SHRD`.
- Add support for x86 SSE instructions: `MOVD`, `MOVDQA`, `MOVDQU`, `MOVHPD`, `MOVLPD`, `MOVQ`, `PCMPEQB`, `PMINUB`, `PMOVMSKB`, `POR`, `PSHUFD`, `PSLLDQ`, `PSRLDQ`, `PSUBB`, `PUNPCKLBW`, `PUNPCKLWD`, `PUNPCKLQDQ` and `PXOR`.
- Add initial support for x86 `SSE` instruction set.
- Add support for `pdf`, `png` and `dot` output formats in `BARFcfg` and `BARFcg` tools.
- Add option to display immediate operand values in `hex` and `dec` to the CFG rendering.
- Add REIL instruction index to the CFG rendering.
- Add support for missing x86 flag translations: `AF` and `PF`.
- Add new method to the `ArchitectureInformation` class to retrieve information about syscall instructions.
- Add new x86 example for finding and executing functions.
- Add new methods to the `CallGraph` class.
- Add initial support for `GS` and `FS` segments access (x86).

### Changed
- Improve coding style and code quality of the `reil` module.
- Improve coding style and code quality of the `reilemulator` module.
- Remove SMT requirement (an exception is raised when trying to use related functionality).
- Improve coding style and code quality of the `x86` package.
- Improve `emulate_full` method to support any piece of code.
- Refactor `_open_elf` logic in the `BinaryFile` class by @Seraphime.

### Fixed
- Fix missing check on `recover_cfg` function parameters.
- Update missing branch instructions in the `X86ArchitectureInformation` class.
- Fix x86 instruction translation: `SAR`, `SHR`, `SHL`, `ROR`, `MOVZX` and `MOV`.
- Fix x86 gadget finding function.
- Fix various typos.
- Fix x86 `REP` prefix parsing.

## [0.3] - 2016-12-13
### Added
- Add new BARF tool, `BARFcg`, for CG recovery.
- Add support for CG recovery (x86 and ARM).
- Add new BARF tool, `BARFcfg`, for CFG recovery.
- Add support for ARM CFG recovery.
- Add support for more ARM instructions.
- Add support for data tainting in `ReilEmulator`.
- Add support for pre/post instruction execution callback function in `ReilEmulator`.
- Add support for REIL extension instruction (`SEXT`, `SDIV`, `SMOD`).
- Add support for more x86 instructions.

### Changed
- Improve CFG recovery functionality.
- Refactor `basickblock` module.
- Replace PyBFD with PyELFTools.
- Improve SMT performace.
- Refactor `smtlibv2` module.
- Overall directory restructure.
- Improve ARM disassembly integration to Capstone Engine.
- Overall improvements to CFG recovery and rendering.
- Refactor `reilemulator` module.
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
- `BARFgadgets` now find gadgets in ARM binaries.
- Add support for the ARM architecture (32 btis).
- Add support for more x86 instructions.
- Memory consumption reduction through the use of `__slots__`.
- `BARFgadgets` now supports gadgets ending in `RET imm16`, `JMP` and `CALL` instructions.

### Changed
- Overall improvements to `x86` package (major changes that ended up in performance increase of translation up to 3x!).
- Overall improvements to `reil` package (minor changes).
- New reil translation scheme for x86 instructions.
- `x86translator` and `x86instructiontranslator` modules were merged.
- Some methods of `X86ArchitectureInformation` class were renamed to improve naming consistency.
- x86 flags are now represented using a single bit (instead of one byte). Also, each flag (`CF`, `ZF`, etc.) is now an alias of the correspondent bit of the `{e/r}flags` register.

### Fixed
- Fixes in x86 instruction translations (mostly flags update issues.)
- Fix missing registers in `X86ArchitectureInformation` class.
- Fix SMT translation for `STR` instruction when dst operand is bigger than src operand.

### Removed
- `x86instruction` and `x86intructiontranslator` modules were removed.

## 0.1 - 2014-11-19
### Added
- First release.

[Unreleased]: https://github.com/programa-stic/barf-project/compare/v0.6.0...master
[0.6.0]: https://github.com/programa-stic/barf-project/compare/v0.5.0...v0.6.0
[0.5.0]: https://github.com/programa-stic/barf-project/compare/v0.4.0...v0.5.0
[0.4.0]: https://github.com/programa-stic/barf-project/compare/v0.3...v0.4.0
[0.3]: https://github.com/programa-stic/barf-project/compare/v0.2.1...v0.3
[0.2.1]: https://github.com/programa-stic/barf-project/compare/v0.2...v0.2.1
[0.2]: https://github.com/programa-stic/barf-project/compare/v0.1...v0.2
