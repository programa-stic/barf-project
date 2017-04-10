# Change Log

All notable changes to this project will be documented in this file.

## [Unreleased]
### Added
### Changed
### Deprecated
### Fixed
### Removed
### Security

## [0.4.0]
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

## [0.1] - 2014-11-19
### Added
- First release.

[Unreleased]: https://github.com/programa-stic/barf-project/compare/v0.4.0...master
[0.4.0]: https://github.com/programa-stic/barf-project/compare/v0.3...v0.4.0
[0.3]: https://github.com/programa-stic/barf-project/compare/v0.2.1...v0.3
[0.2.1]: https://github.com/programa-stic/barf-project/compare/v0.2...v0.2.1
[0.2]: https://github.com/programa-stic/barf-project/compare/v0.1...v0.2
