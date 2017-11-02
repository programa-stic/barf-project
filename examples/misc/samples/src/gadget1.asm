global _start

; Gadgets: 59

_start:
    ; No Operation (Gadgets: 2)
    ; ------------------------------------------------------------------------ ;
    nop
    ret

    mov eax, eax
    ret

    ; Load Constant (Gadgets: 2)
    ; ------------------------------------------------------------------------ ;
    mov eax, 0
    ret

    sub eax, eax
    ret

    ; Register Copy (Gadgets: 1)
    ; ------------------------------------------------------------------------ ;
    mov eax, ebx
    ret

    ; Load Memory (Gadgets: 13)
    ; ------------------------------------------------------------------------ ;
    pop eax
    ret

    pop ebx
    ret

    pop ecx
    ret

    pop edx
    ret

    pop edi
    ret

    pop esi
    ret

    pop ebp
    ret

    pop esp
    ret

    mov eax, [ebx]
    ret

    mov ecx, [0xdeadbeef]
    ret

    mov ecx, [eax+0x100]
    ret

    mov ecx, [ecx]
    ret

    mov ecx, [ecx+0x100]
    ret

    ; Store Memory (Gadgets: 12)
    ; ------------------------------------------------------------------------ ;
    push eax
    ret

    push ebx
    ret

    push ecx
    ret

    push edx
    ret

    push edi
    ret

    push esi
    ret

    push ebp
    ret

    mov [eax], ebx
    ret

    mov [0xdeadbeef], ecx
    ret

    mov [eax + 0x100], ecx
    ret

    mov [ecx], ecx
    ret

    mov [ecx + 0x100], ecx
    ret

    ; Arithmetic (Gadgets: 8)
    ; ------------------------------------------------------------------------ ;
    add ecx, eax
    ret

    add edx, ebx
    ret

    add ecx, edx
    ret

    add eax, ebx
    ret

    add edx, esi
    ret

    sub ecx, edx
    ret

    sub eax, ebx
    ret

    sub edi, esi
    ret

    ; NOTE: Not supported yet.
;    mul ebx
;    ret
;
;    mul ecx
;    ret
;
;    div ebx
;    ret
;
;    div ecx
;    ret

    ; Arithmetic Load (Gadgets: 10)
    ; ------------------------------------------------------------------------ ;
    add eax, [ebx]
    ret

    add eax, [0xdeadbeef]
    ret

    add eax, [ebx + 0x100]
    ret

    add ecx, [ecx]
    ret

    add ecx, [ecx + 0x100]
    ret

    sub eax, [ebx]
    ret

    sub eax, [0xdeadbeef]
    ret

    sub eax, [ebx + 0x100]
    ret

    sub ecx, [ecx]
    ret

    sub ecx, [ecx + 0x100]
    ret

    ; Arithmetic Store (Gadgets: 5)
    ; ------------------------------------------------------------------------ ;
    add [eax], ebx
    ret

    add [0xdeadbeef], ecx
    ret

    add [eax + 0x100], ecx
    ret

    add [ecx], ecx
    ret

    add [ecx + 0x100], ecx
    ret

    ; Mixed (Gadgets: 6)
    ; ------------------------------------------------------------------------ ;
    ; Load Constant + Store Memory
    mov ecx, 0
    mov [eax], ebx
    ret

    ; Arithmetic Load : Load Constant + Store Memory
    mov ebx, [ebx]
    add eax, ebx
    ret

    ; Load Memory: Two memory accesses
    pop eax
    pop ebx
    ret

    ; Store Memory: Two memory accesses
    push eax
    push ebx
    ret

    ; Load Memory + Arithmetic Load: Two memory accesses
    mov ecx, [ecx]
    add eax, [ebx]
    ret

    ; Load Memory + Arithmetic Load: Two memory accesses (duplicate)
    mov ecx, [ecx]
    add eax, [ebx]
    ret

    ; Extra tests (from asterisk) (non-gadget)
    mov dword [eax+0x24], 0x0
    mov dword [eax+0x20], 0x0
    ret
