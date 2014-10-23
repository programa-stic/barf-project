global _start

_start:
    mov eax, 0x0
    mov ebx, 0xa

    .loop:
        add eax, 0x1
        sub ebx, 0x1
        cmp ebx, 0x0
        jne .loop
