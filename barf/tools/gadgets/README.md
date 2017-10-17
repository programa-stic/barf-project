# ROP Gadget Tool

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

This is done through instruction emulation. Finally, the *verification* stage
consists of using a SMT solver to verify the semantic assigned to each gadget
in the second stage.

This tool is based on [Q] and currently supports Intel x86 (32 and 64 bits)
and ARM (32 bits).

# Usage

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

# Example

The following command look for gadgets in the ``ls`` unix command. The ``-u``
option returns unique gadgets (i.e. filters duplicates) and the ``-v`` flag
turns on gadget classification and verification.

```bash
./BARFgadgets -u -v $(which ls)
```

Below you can see the output of the command for **x86**:

```
Raw Gadgets
===========

0x00403d4e: push 0xffffffff89480021L ; ret
0x00403d50: add byte ptr [rax+0xffffff89L], cl ; ret
0x00403dba: push rdx ; push 0xffffffff89480021L ; ret
0x00403ef4: add byte ptr [rax], al ; add byte ptr [rax+0xffffff89L], cl ; ret
0x004048d5: pop rbp ; ret

... continues ...

[+] Raw Gadgets : 231

Verified Gadgets
================

# Move Register (14 gadgets)
---------------------------------------------------------------------------------------------------------------
      Address       | Operation  | Clobbered Registers |                     Instructions
---------------------------------------------------------------------------------------------------------------
 0x0000000000404989 | eax <- edx | {rax}               | mov eax, edx ; ret
 0x00000000004058f4 | eax <- edx | {rbx; rax}          | add bl, al ; mov eax, edx ; ret
 0x0000000000407744 | eax <- ecx | {rbx; rax}          | add bl, al ; mov eax, ecx ; ret
 0x000000000040ac41 | rax <- rdi | {rsp}               | push qword ptr [rbp+0xffffff9cL] ; mov rax, rdi ; ret
 0x000000000040ac45 | eax <- edi | {rax}               | mov eax, edi ; ret

... continues ...

# Load Constant (18 gadgets)
------------------------------------------------------------------------------------------------------------------------
      Address       |     Operation     | Clobbered Registers |                      Instructions
------------------------------------------------------------------------------------------------------------------------
 0x0000000000404d3a | edi <- 0x89480000 | {rdi}               | mov edi, 0x89480000 ; ret
 0x00000000004058e3 | ebx <- 0x401f0f   | {rbx; rax}          | mov ebx, 0x401f0f ; mov eax, 0xffffffff ; ret
 0x00000000004058e3 | eax <- 0xffffffff | {rbx; rax}          | mov ebx, 0x401f0f ; mov eax, 0xffffffff ; ret
 0x0000000000405973 | ebp <- 0x401f0f   | {rbp; rax}          | mov ebp, 0x401f0f ; mov eax, 0xffffffff ; ret
 0x0000000000405973 | eax <- 0xffffffff | {rbp; rax}          | mov ebp, 0x401f0f ; mov eax, 0xffffffff ; ret

... continues ...

# Arithmetic (10 gadgets)
----------------------------------------------------------------------------------------------------------------------
      Address       |    Operation     | Clobbered Registers |                      Instructions
----------------------------------------------------------------------------------------------------------------------
 0x0000000000404944 | ebx <- ebx + esi | {rbx; rax}          | add eax, 0x215d0e ; add ebx, esi ; ret
 0x0000000000404947 | ebx <- ebx + esi | {rbx}               | and dword ptr [rax], eax ; add ebx, esi ; ret
 0x0000000000404d37 |  al <- al | ch   | {rdi; rax}          | or al, ch ; add edi, dword ptr [rdi+0x89480000L] ; ret
 0x0000000000405802 |  bl <- bl + dh   | {rbx}               | add dword ptr [rcx+0x21582b05], ecx ; add bl, dh ; ret
 0x00000000004058f4 |  bl <- al + bl   | {rbx; rax}          | add bl, al ; mov eax, edx ; ret

... continues ...

# Load Memory (42 gadgets)
-------------------------------------------------------------------------------------------------------------------------------------
      Address       |       Operation        | Clobbered Registers |                          Instructions
-------------------------------------------------------------------------------------------------------------------------------------
 0x00000000004048d5 | rbp <- mem[rsp]        | {rsp}               | pop rbp ; ret
 0x0000000000404a44 | r14 <- mem[rsp + 0x8]  | {r12; rsp}          | pop r12 ; pop r14 ; ret
 0x0000000000404a44 | r12 <- mem[rsp]        | {r14; rsp}          | pop r12 ; pop r14 ; ret
 0x0000000000404a47 | rsi <- mem[rsp]        | {rsp}               | pop rsi ; ret
 0x0000000000404d81 | r13 <- mem[rsp + 0x8]  | {r12; rsp}          | pop r12 ; pop r13 ; ret

... continues ...

# Store Memory (14 gadgets)
------------------------------------------------------------------------------------------------------------------------------------------------------
      Address       |              Operation               | Clobbered Registers |                            Instructions
------------------------------------------------------------------------------------------------------------------------------------------------------
 0x0000000000403dba | mem[rsp + 0xfffffffffffffff8] <- rdx | {rsp}               | push rdx ; push 0xffffffff89480021L ; ret
 0x000000000040a1df |           mem[rip + 0x210ff1] <- rdi | {}                  | nop ; mov qword ptr [rip+0x210ff1], rdi ; ret
 0x000000000040a1e1 |           mem[rip + 0x210ff1] <- edi | {}                  | mov dword ptr [rip+0x210ff1], edi ; ret
 0x000000000040a1e8 |           mem[rip + 0x210fd9] <- dil | {}                  | nop dword ptr [rax+rax*1] ; mov byte ptr [rip+0x210fd9], dil ; ret
 0x000000000040a1f1 |           mem[rip + 0x210fd9] <- bh  | {}                  | mov byte ptr [rip+0x210fd9], bh ; ret

... continues ...

# Arithmetic Load (8 gadgets)
------------------------------------------------------------------------------------------------------------------------------------------------------------------------
      Address       |                 Operation                  | Clobbered Registers |                                  Instructions
------------------------------------------------------------------------------------------------------------------------------------------------------------------------
 0x0000000000404d37 | edi <- edi + mem[rdi + 0xffffffff89480000] | {rdi; rax}          | or al, ch ; add edi, dword ptr [rdi+0x89480000L] ; ret
 0x0000000000404fad |  cl <- cl | mem[rax + 0x39]                | {rcx}               | or cl, byte ptr [rax+0x39] ; ret
 0x0000000000407529 | esi <- esi & mem[rax + 0x1f0fffff]         | {rsi}               | and esi, dword ptr [rax+0x1f0fffff] ; add byte ptr [rax+0xffffffffL], bh ; ret
 0x00000000004092d4 | ebx <- ebx | mem[rbx + 0x5d]               | {r12; rsp; rbx}     | or ebx, dword ptr [rbx+0x5d] ; pop r12 ; ret
 0x000000000040ac98 | rax <- rax + mem[rbx]                      | {rbx; rsp}          | add rax, qword ptr [rbx] ; pop rbx ; ret

... continues ...

[+] Verified Gadgets : 107

Non-verified Gadgets
====================

0x00403d4e: push 0xffffffff89480021L ; ret
0x00403d50: add byte ptr [rax+0xffffff89L], cl ; ret
0x00403ef4: add byte ptr [rax], al ; add byte ptr [rax+0xffffff89L], cl ; ret
0x00404985: div rsi ; mov rax, rdx ; ret
0x00404986: div esi ; mov rax, rdx ; ret

... continues ...

[+] Non-verified Gadgets : 93
```

And for **ARM**:

```
Raw Gadgets
===========

0x0000c4b0: mov r0, r2 ; popia r13, {r3, pc}
0x0000c4d4: popia r13, {r4, r5} ; bx lr
0x0000c540: mov r0, #1 ; popia r13, {r3, pc}
0x0000c724: str r4, [r3] ; popia r13, {r4, r5, r6, r7, r8, sb, sl} ; bx lr
0x0000ca84: str r0, [r3, #4] ; str r2, [r0, #4] ; popia r13, {r4, pc}

... continues ...

[+] Raw Gadgets : 85

Verified Gadgets
================

# Move Register (25 gadgets)
---------------------------------------------------------------------------------------------------------------------
  Address   | Operation | Clobbered Registers |                       Instructions
---------------------------------------------------------------------------------------------------------------------
 0x0000c4b0 | r0 <- r2  | {r15; r13; r3}      | mov r0, r2 ; popia r13, {r3, pc}
 0x0000d960 | r0 <- r3  | {}                  | mov r0, r3 ; bx lr
 0x00012114 | r0 <- r5  | {r4; r5; r13}       | mov r0, r5 ; popia r13, {r4, r5} ; bx lr
 0x0001248c | r0 <- r3  | {r15; r13; r3}      | mov r0, r3 ; popia r13, {r3, pc}
 0x000124bc | r0 <- r1  | {r15; r13; r3}      | mov r0, r1 ; popia r13, {r3, pc}

... continues ...

# Load Constant (22 gadgets)
---------------------------------------------------------------------------------------------------------------------
  Address   |   Operation    | Clobbered Registers |                              Instructions
---------------------------------------------------------------------------------------------------------------------
 0x00017dec |  r0 <- 0x0     | {r4; r15; r13}      | mov r0, #0 ; popia r13, {r4, pc}
 0x00011834 |  r0 <- 0x1     | {r4; r15; r13}      | mov r0, #1 ; add sp, sp, #8 ; popia r13, {r4, pc}
 0x000126f0 | r14 <- 0x126fc | {r0; r3}            | ldr r3, [r5, #0x1c] ; mov r0, r4 ; blx r3
 0x00012748 | r14 <- 0x12754 | {r0; r2}            | mov r0, r4 ; ldr r2, [r5, #0x1c] ; blx r2
 0x00012b54 | r14 <- 0x12b60 | {r0; r3}            | ldr r3, [r6, #0x1c] ; mov r0, r5 ; blx r3

... continues ...

# Arithmetic (2 gadgets)
---------------------------------------------------------------------------------------------
  Address   |   Operation   | Clobbered Registers |               Instructions
---------------------------------------------------------------------------------------------
 0x00019f30 | r1 <- r1 | r5 | {r4; r5; r15; r13}  | orr r1, r1, r5 ; popia r13, {r4, r5, pc}
 0x0001a274 | r0 <- r0 | r3 | {}                  | orr r0, r0, r3 ; bx lr

... continues ...

# Load Memory (195 gadgets)
----------------------------------------------------------------------------------------------------------------------------------
  Address   |         Operation          | Clobbered Registers |                     Instructions
----------------------------------------------------------------------------------------------------------------------------------
 0x0000c4b0 | r3 <- mem[r13]             | {r15; r0; r13}      | mov r0, r2 ; popia r13, {r3, pc}
 0x0000c4b0 | pc <- mem[r13 + 0x4]       | {r15; r0; r13; r3}  | mov r0, r2 ; popia r13, {r3, pc}
 0x0000c4d4 | r4 <- mem[r13]             | {r5; r13}           | popia r13, {r4, r5} ; bx lr
 0x0000c4d4 | r5 <- mem[r13 + 0x4]       | {r4; r13}           | popia r13, {r4, r5} ; bx lr
 0x0000ca84 | r4 <- mem[r13]             | {r15; r13}          | str r0, [r3, #4] ; str r2, [r0, #4] ; popia r13, {r4, pc}

... continues ...

# Store Memory (17 gadgets)
------------------------------------------------------------------------------------------------------------------------------------------------------
  Address   |      Operation       | Clobbered Registers |                                  Instructions
------------------------------------------------------------------------------------------------------------------------------------------------------
 0x00015bfc |  mem[r3 + 0x4] <- r1 | {r0}                | ldr r0, [r3, #4] ; str r1, [r3, #4] ; bx lr
 0x0000ca84 |  mem[r3 + 0x4] <- r0 | {r4; r15; r13}      | str r0, [r3, #4] ; str r2, [r0, #4] ; popia r13, {r4, pc}
 0x0000ca84 |  mem[r0 + 0x4] <- r2 | {r4; r15; r13}      | str r0, [r3, #4] ; str r2, [r0, #4] ; popia r13, {r4, pc}
 0x00012450 |        mem[r4] <- r2 | {r4; r15; r13}      | stmia r4, {r2, r3} ; add sp, sp, #8 ; popia r13, {r4, pc}
 0x00012450 |  mem[r4 + 0x4] <- r3 | {r4; r15; r13}      | stmia r4, {r2, r3} ; add sp, sp, #8 ; popia r13, {r4, pc}

... continues ...

[+] Verified Gadgets : 261

Non-verified Gadgets
====================

0x00011c78: ldr r3, [pc, #4] ; str r0, [r3] ; bx lr
0x00012930: ldr r0, [r0, #0xc] ; bx lr
0x00012938: ldr r0, [r0, #0x10] ; bx lr
0x00012d34: ldr r0, [r7] ; mov r1, sl ; blx r4
0x00012dc0: str r4, [ip] ; ldmia sp, {r4} ; bx lr
0x00014a38: mov fp, #0 ; mov r1, sl ; blx r5
0x00014a68: mov r1, sl ; mov r0, sb ; blx r5
0x00014ab8: mov r7, #0 ; mov r1, sl ; blx r5
0x00015be0: str r4, [r3, ip, lsl #2] ; ldmia sp, {r4} ; bx lr
0x00019df0: mul r3, r2, r0 ; sub r1, r1, r3 ; bx lr

[+] Non-verified Gadgets : 10
```

# Limitations

There are some limitations:

* Currently, BARF supports only a subset of the x86 and ARM instruction sets. If a gadget contains an instruction that is not supported, it is **discarded**.
* Not all binary operations are supported right now in the classification and verification stages. Supported one includes: ``+``, ``-``, ``^``, ``|``, ``&``.
* *Jump* gadgets are not supported yet.

[Q]: http://users.ece.cmu.edu/~ejschwar/papers/usenix11.pdf
