# ARM

This document explains the framework developed to translate ARM instructions to REIL, which is located in ``barf/barf/arch/arm``.

Currently the target architecture is only ARM 32 bits, without Thumb.

The ARM port was implemented based on the x86 translation code (first ISA implemented), and this documentation primarily focuses on the differences between the two of them. This means that the BARF framework (with the x86 implementation) should to be understood before reading this (with a basic knowledge of the ARM architecture itself), it is not a standalone documentation.

As a reference, the ARM Architecture Reference Manual was used.

* http://infocenter.arm.com/help/index.jsp?topic=/com.arm.doc.subset.architecture.reference/index.html


# Extending the instruction set

This secion aims at describing the basic steps needed to add a new ARM instruction to the list (as of now only the most basic instructions are supported), without a thorough understanding of the ARM framework. Depending of the complexity of the instruction to be emulated, more knwoldege of the inner working will be needed.

The first step is to add the instruction template to the parser (``armparser.py``) in the ``mnemonic`` definition, the basic template is ``Combine(Literal("<inst_base>")("ins") + <inst_mod>),``, where ``<inst_base>`` is the mnemonic instruction without the modifiers like the conditional execution code (EQ, NE, etc.) or the update APSR flag (S). These are added in ``<inst_mod>``, they have to be previously defined. The condition codes and update flags are already defined as ``condition_code`` and ``update_flags``, and the combination of both as ``cc_plus_uf``. The modifiers are joined together with a plus sign (+).

Then the translation code is added to the translator (``armtranslator.py``). A new function has to be added to ``ArmTranslator`` with the pattern ``_translate_<inst_base>`` where ``<inst_base>`` is the one defined in the parser. The typical construction of a translation function is to read the ARM operands, process the instruction, write them back and update the flags if necessary. Good examples of this approach are ``_translate_add`` and ``_translate_and`` functions.

For more complex instructions (with addressing modes for example), the framework has to be studied in more depth.


# Base information

Located in ``armbase.py`` are the basic definitions of the ARM architecture. The ``ArmInstruction`` class was created, similar to the ``X86Instruction`` without the prefix, and several ARM operand classes. To the standard immediate, register and memory operand classes the ``ArmShiftedRegisterOperand`` and the ``ArmRegisterListOperand`` were added, to represent a register shifted by another register (or immediate), and the register list (e.g. ``{r0 - r4, lr}``) used for the LDM/STM instructions.

As only the ARM 32 bits was implemented, the ``registers_access_mapper`` and the registers itself are considerably simpler than the x86 counterparts (where there are alias to lower register parts).


# Disassembler

Located in ``armdisassembler.py``. Based on the Capstone engine, is pretty much the same as the x86 disassembler with the difference in how it handles unknown instructions. In the function ``_cs_disassemble_one`` if Capstone can't disassembled the instruction (possibly because it's a 32 bit constant) it returns an 32 bit ARM NOP instruction, so the disassembly process doesn't stop.

The reason behind this is that ARM 32 bits fixed instruction size doesn't allow to handle large constants, so these are normal stored in the ``.data`` section along with the ARM code (normally right below the function that references it). This means that there is data mixed with the ARM instructions. In a binary without symbols instructions and constants cannot be easily told apart.


# Parser

Located in ``armparser.py``. The basic logic is the same as in x86. Based on the ``pyparsing`` python package, with the instruction assumed to have the format ``<mnemonic> <operand_0>, <operand_1>, ..., <operand_n>``. The structure of the operands and the instruction are defined with the corresponding parsing functions ``parse_operand`` and ``parse_instruction``. There is a parsing function for every type of operand defined in the base information.

One key difference with the x86 parser is the use of the ``Group`` function from ``pyparsing`` that encapsulates a ``ParserElement`` definition, allowing it to be reused and with the internal names not mixed with the rest where the ``ParserElement`` is included (which is what happens if the ``Group`` function is not used when a ``ParserElement`` is included inside another).

The parser analyses the operands and the instruction mnemonic in separate instructions (and different moments, the operands are analyzed first), but some ARM instructions include flags encoded as different literal characters with the operands that really concern the instruction as a whole and not the operand itself. An example of that is the LDM instruction with the structure: ``LDM{<cond>}<addrsssing_mode> <Rn>{!}, <registers>`` where the exclamation signs indicates that the instruction will modify (*write-back*) the base register (``Rn``). This *flag* will be spotted by the parser when it's analyzing the first operand and has to pass this information somehow to the instructions, represented in the ``ArmInstruction`` class. The most convenient way found, without resorting to global variables, and due to the fact that the ``pyparsing`` functions don't have access to the ``ArmParser`` class, was to include flags like this in the respective operand classes, in this example the ``ArmRegisterOperand``. which has the ``wb`` (*write-back*) property specifically to code this flag in the LDM/STM instructions. This is not ideal as this property belongs more to the instruction class itself rather than the register operand class.

Many instructions can have a optional condition under which is executed, generally coded as ``MOV{condition_code}``. This condition expands the mnemonic itself, resulting in a new range of different mnemonics for the parser to analyze, all for the same instruction really. For example, the MOV instruction can be seen as MOV alone, but also MOVEQ (MOV if EQ -equal- condition is met), MOVNE, MOVLT and so on. Some similar happens with the ``S`` flag that is used to specify that the instruction updates the CPSR. This complicates the logic for the translation (which comes after the parsing phase) which has many more instructions to translate, when they are in fact the exactly same instruction with a conditional execution code.

To alleviate the work of the translator, a little more logic was added to the parser that has the right tools to pre-process this condition codes. This is done in the definition of the ``mnemonic`` in the parser. With the condition codes mnemonic extensions defined (EQ, NE, CS, CC, etc.) it is indicated which instruction can be extended this way (for example the data processing instructions) so the parser can split the full mnemonic into the base instruction and extensions such as the conditional execution and the CPSR updates, which are stored in the ``ArmInstruction`` as the properties ``condition_code`` and ``update_flags`` respectively. The same logic is used for the addressing modes of the LDM/STM instructions which also can extend the basic mnemonic.

Even though the ARM manual specifies that the update flags from the CPSR (``S``) extension goes after the condition code (e.g. MOV{<cond>}{S}) sometimes the Capstone engine inverts this order (e.g. ANDSEQ), so this exception was allowed in the parser in the definition of ``cc_plus_uf`` (condition codes plus update flags) where both arrangements are specified.


# Translator

Located in ``armtranslator.py``.

As with the parser the basic logic was copied from x86. In the ``TranslationBuilder`` the ``read``/``write`` functions were extended to handle the new operand types, as the ``_compute_<operand>`` were added to pre-process them. Several helper functions were added to manipulate REIL registers for common operations such as ``and``, ``or``, ``equal``, ``extract_bit``, etc.

The functionality of the conditional execution of instructions is exactly the same, meaning if the condition is not met the entire instructions is omitted (treated as a NOP), so the evaluation of the condition is done outside the translation of the specific instruction. This results in a common pre-proccesing stage in the ``_translate`` before the specific translation function is called for that particular instruction, simplifying the general logic (the parser already did the job of splitting the base mnemonic and the condition codes mnemonic extension).

Many ARM instructions have the possibility to perform a shift operation on its second operand, adding more complexity to the ARM operand processing (compared to the x86 counterpart). As of now only the logical shift left (LSL) was implemented as this by far the most common shift operation in the ARM instructions.

The helper functions in the ``TranslationBuilder`` greatly simplify the code of the translation at the cost of some inefficiency in the REIL translation itself, for example sometimes the same value is negated twice or even four times returning to its original value. For now this was an acceptable trade-off as the framework code is being prioritized over the resulting REIL translation code. In the future maybe a second stage of optimization (decoupled from the translation) can be added to improve this.

Although the translation functions follow a similar pattern (read operands, perform operation, write operands, update flags) there is a particular case worth mentioning in the update flags of the data-processing instructions. In the instructions that do not generate a carry per se (AND, OR, XOR, MOV), the carry flag (C) is updated with the result of the carry operation of the ``shifter_operand``. But as the operand is already processed outside the translation function (in the ``read`` of the``TranslationBuilder``), this information is lost when the control flow reaches the ``_update_flags_data_proc_other``. So in this particular case the original ARM operand is passed as an argument along with the REIL operands, so it can be analyzed to extract the ``shifter_carry_out`` (which is used to update the carry flag). This is not an ideal situation because at this point it would be desirable to abandon the ARM operands and only handle its REIL equivalents, but was the most practical way found so far.


# Tests

Located outside the ARM folder, in ``barf/barf/tests/armtests.py``.

This file holds all the ARM tests, including parsing, translation and gadget finding. The translation tests have to be run on a ARM native machine (it has been tested on a Raspberry Pi).

In the case of the gadget finding tests there is a particular gadget classification not supported right now, very common in ARM, which is to form a memory address with a base register plus an offset generated form a second (possibly shifted) register, not an immediate (the only current gadget memory classification so far).


# PyAsmJIT

Located outside the barf project, it has its own structure. No extra files were added, the ARM functions were created along the x86 ones for now, with the ``arm_`` prefix. The logic of the Python C interface was copied exactly from x86 (changing only the register names form the context). The difference resides only in the specific ARM assembly used to run the code to be tested. Due to the multiple load/store ARM instructions saving and restoring the context is done in a pretty straight forward way.

For simplicity the registers R13 (SP), R14 (LR), R15 (PC) are not modified, even though they are technically part of the context, but their value is not load nor stored.


# TODO

Extend to Thumb.
Extend to ARM64.
