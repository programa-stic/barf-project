import os
import subprocess
import tempfile

import pyasmjit

template_assembly = """\
;; Make sure to compile in 64 bits
BITS 64

;; Build stack frame
push rbp
mov rbp, rsp

;; Allocate stack memory
sub rsp, 8

;; Save registers
push rax
push rbx
push rcx
push rdx
push rdi
push rsi
push r8
push r9
push r10
push r11
push r12
push r13
push r14
push r15

;; Save ptr to context
mov [rbp-0x08], rdi

;; Load context (flags)
push qword [rdi+6*8]
popfq

;; Load context (registers)
mov rax, [rdi+ 0*8]
mov rbx, [rdi+ 1*8]
mov rcx, [rdi+ 2*8]
mov rdx, [rdi+ 3*8]
mov rsi, [rdi+ 5*8]

;; TODO: Set rbp, rsp and rip registers

; mov rbp, [rdi+ 6*8]
; mov rsp, [rdi+ 7*8]
; mov rip, [rdi+ 8*8]

mov r8,  [rdi+ 9*8]
mov r9,  [rdi+10*8]
mov r10, [rdi+11*8]
mov r11, [rdi+12*8]
mov r12, [rdi+13*8]
mov r13, [rdi+14*8]
mov r14, [rdi+15*8]
mov r15, [rdi+16*8]

;; Load context (flags)
push qword [rdi+17*8]
popfq

;; Load rdi value
mov rdi, [rdi+ 4*8]

;; Run code
{code}

;; Save current rdi value and restore ptr to context
push rdi
mov rdi, [rbp-0x08]

;; Save context
mov [rdi+ 0*8], rax
mov [rdi+ 1*8], rbx
mov [rdi+ 2*8], rcx
mov [rdi+ 3*8], rdx
mov [rdi+ 5*8], rsi

; mov [rdi+ 6*8], rbp
; mov [rdi+ 7*8], rsp
; mov [rdi+ 8*8], rip

mov [rdi+ 9*8], r8
mov [rdi+10*8], r9
mov [rdi+11*8], r10
mov [rdi+12*8], r11
mov [rdi+13*8], r12
mov [rdi+14*8], r13
mov [rdi+15*8], r14
mov [rdi+16*8], r15

;; Save context (flags)
pushfq
pop qword [rdi+17*8]

;; Copy rdi to rsi
mov rsi, rdi

;; Restore current rdi value
pop rdi

;; Save rdi value
mov [rsi+ 4*8], rdi

;; Restore registers
pop r15
pop r14
pop r13
pop r12
pop r11
pop r10
pop r9
pop r8
pop rsi
pop rdi
pop rdx
pop rcx
pop rbx
pop rax

;; Free up stack memory
add rsp, 8

pop rbp
ret
"""

template_arm_assembly = """\
/* Save registers */
push {{r0 - r12, lr}}

/* Save flags (user mode) */
mrs r1, apsr
push {{r1}}

/* Save context pointer (redundant, it was saved before, but done for code clarity) */
push {{r0}}

/* Load context */
ldr r1, [r0, #(16 * 4)]
msr apsr_nzcvq, r1
ldm r0, {{r0 - r12}}

/* Run code */
{code}

/* TODO: lr is used as scratch register when saving the context so its value is not saved correctly */
/* Restore context pointer */
pop {{lr}}

/* Save context */
stm lr, {{r0 - r12}}
mrs r1, apsr
str r1, [lr, #(16 * 4)]

/* Restore flags */
pop {{r1}}
msr apsr_nzcvq, r1

/* Restore registers */
pop {{r0 - r12, lr}}

/* Return */
blx lr
"""

def execute(assembly, context):
    # Initialize return values
    rc  = 0
    ctx = {}

    # Instantiate assembly template.
    assembly = template_assembly.format(code=assembly)

    # Create temporary files for compilation.
    f_asm = tempfile.NamedTemporaryFile(delete=False)
    f_obj = tempfile.NamedTemporaryFile(delete=False)

    # Write assembly to a file.
    f_asm.write(assembly)
    f_asm.close()

    # Run nasm.
    cmd = "nasm -f bin -o {0} {1}".format(f_obj.name, f_asm.name)
    return_code = subprocess.call(cmd, shell=True)

    # Check for assembler errors.
    if return_code == 0:
        # Read binary code.
        binary = ""
        byte = f_obj.read(1)
        while byte:
            binary += byte
            byte = f_obj.read(1)
        f_obj.close()

        # Run binary code.
        rc, ctx = pyasmjit.jit(binary, context)
    else:
        rc = return_code

    # Remove temporary files.
    os.remove(f_asm.name)
    os.remove(f_obj.name)

    return rc, ctx

def arm_execute(assembly, context):
    # Initialize return values
    rc  = 0
    ctx = {}

    # Instantiate assembly template.
    assembly = template_arm_assembly.format(code=assembly)

    # Create temporary files for compilation.
    f_asm = tempfile.NamedTemporaryFile(delete=False)
    f_obj = tempfile.NamedTemporaryFile(delete=False)
    f_bin = tempfile.NamedTemporaryFile(delete=False)

    # Write assembly to a file.
    f_asm.write(assembly)
    f_asm.close()

    # Run nasm.
    cmd = "gcc -c -x assembler {asm} -o {obj}; objcopy -O binary {obj} {bin};".format( \
                asm = f_asm.name, obj = f_obj.name, bin = f_bin.name)
    return_code = subprocess.call(cmd, shell=True)
    
    # Check for assembler errors.
    if return_code == 0:
        # Read binary code.
        binary = ""
        byte = f_bin.read(1)
        while byte:
            binary += byte
            byte = f_bin.read(1)
        f_bin.close()

        # Run binary code.
        rc, ctx, mem = pyasmjit.arm_jit(binary, context)
    else:
        rc = return_code

    # Remove temporary files.
    os.remove(f_asm.name)
    os.remove(f_obj.name)
    os.remove(f_bin.name)

    return rc, ctx, mem

def arm_reserve():
    return pyasmjit.arm_reserve()


