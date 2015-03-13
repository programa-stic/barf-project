# Change Log

All notable changes to this project will be documented in this file.

## [Unreleased][unreleased]
### Fixed
- Fixes in x86 instruction translations (mostly flags update issues.)
- Fix missing registers in X86ArchitectureInformation class.
- Fix SMT translation for STR instruction when dst operand is bigger than src operand.

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

### Removed
- x86instruction and x86intructiontranslator modules were removed.

[unreleased]: https://github.com/programa-stic/barf-project/compare/v0.1...develop
