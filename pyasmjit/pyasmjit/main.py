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

;; Save ptr to context
mov [rbp-0x08], rdi

;; Load context (flags)
push qword [rdi+6*8]
popfq

;; Load context (registers)
mov rax, [rdi+0*8]
mov rbx, [rdi+1*8]
mov rcx, [rdi+2*8]
mov rdx, [rdi+3*8]
mov rsi, [rdi+5*8]
mov rdi, [rdi+4*8]

;; Run code
{code}

;; Save current rdi value and restore ptr to context
push rdi
mov rdi, [rbp-0x08]

;; Save context
mov [rdi+0*8], rax
mov [rdi+1*8], rbx
mov [rdi+2*8], rcx
mov [rdi+3*8], rdx
mov [rdi+5*8], rsi

;; Save context (flags)
pushfq
pop qword [rdi+6*8]

;; Copy rdi to rsi
mov rsi, rdi

;; Restore current rdi value
pop rdi

;; Save rdi value
mov [rsi+4*8], rdi

;; Restore registers
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
