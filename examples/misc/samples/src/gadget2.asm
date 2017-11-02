global _start

; Gadgets: 59

_start:
    ; No Operation (Gadgets: 2)
    ; ------------------------------------------------------------------------ ;
    nop
    ret

    mov rax, rax
    ret

    ; Load Constant (Gadgets: 2)
    ; ------------------------------------------------------------------------ ;
    mov rax, 0
    ret

    sub rax, rax
    ret

    ; Register Copy (Gadgets: 1)
    ; ------------------------------------------------------------------------ ;
    mov rax, rbx
    ret

    ; Load Memory (Gadgets: 13)
    ; ------------------------------------------------------------------------ ;
    pop rax
    ret

    pop rbx
    ret

    pop rcx
    ret

    pop rdx
    ret

    pop rdi
    ret

    pop rsi
    ret

    pop rbp
    ret

    pop rsp
    ret

    mov rax, [rbx]
    ret

    mov rcx, [0xdeadbeef]
    ret

    mov rcx, [rax+0x100]
    ret

    mov rcx, [rcx]
    ret

    mov rcx, [rcx+0x100]
    ret

    ; Store Memory (Gadgets: 12)
    ; ------------------------------------------------------------------------ ;
    push rax
    ret

    push rbx
    ret

    push rcx
    ret

    push rdx
    ret

    push rdi
    ret

    push rsi
    ret

    push rbp
    ret

    mov [rax], rbx
    ret

    mov [0xdeadbeef], rcx
    ret

    mov [rax + 0x100], rcx
    ret

    mov [rcx], rcx
    ret

    mov [rcx + 0x100], rcx
    ret

    ; Arithmetic (Gadgets: 8)
    ; ------------------------------------------------------------------------ ;
    add rcx, rax
    ret

    add rdx, rbx
    ret

    add rcx, rdx
    ret

    add rax, rbx
    ret

    add rdx, rsi
    ret

    sub rcx, rdx
    ret

    sub rax, rbx
    ret

    sub rdi, rsi
    ret

    ; NOTE: Not supported yet.
;    mul rbx
;    ret
;
;    mul rcx
;    ret
;
;    div rbx
;    ret
;
;    div rcx
;    ret

    ; Arithmetic Load (Gadgets: 10)
    ; ------------------------------------------------------------------------ ;
    add rax, [rbx]
    ret

    add rax, qword [0xdeadbeef]
    ret

    add rax, [rbx + 0x100]
    ret

    add rcx, [rcx]
    ret

    add rcx, [rcx + 0x100]
    ret

    sub rax, [rbx]
    ret

    sub rax, [0xdeadbeef]
    ret

    sub rax, [rbx + 0x100]
    ret

    sub rcx, [rcx]
    ret

    sub rcx, [rcx + 0x100]
    ret

    ; Arithmetic Store (Gadgets: 5)
    ; ------------------------------------------------------------------------ ;
    add [rax], rbx
    ret

    add [0xdeadbeef], rcx
    ret

    add [rax + 0x100], rcx
    ret

    add [rcx], rcx
    ret

    add [rcx + 0x100], rcx
    ret

    ; Mixed (Gadgets: 6)
    ; ------------------------------------------------------------------------ ;
    ; Load Constant + Store Memory
    mov rcx, 0
    mov [rax], rbx
    ret

    ; Arithmetic Load : Load Constant + Store Memory
    mov rbx, [rbx]
    add rax, rbx
    ret

    ; Load Memory: Two memory accesses
    pop rax
    pop rbx
    ret

    ; Store Memory: Two memory accesses
    push rax
    push rbx
    ret

    ; Load Memory + Arithmetic Load: Two memory accesses
    mov rcx, [rcx]
    add rax, [rbx]
    ret

    ; Load Memory + Arithmetic Load: Two memory accesses (duplicate)
    mov rcx, [rcx]
    add rax, [rbx]
    ret

    ; Extra tests (from asterisk) (non-gadget)
    mov dword [rax+0x24], 0x0
    mov dword [rax+0x20], 0x0
    ret
