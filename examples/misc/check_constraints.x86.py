#! /usr/bin/env python

from __future__ import absolute_import
from __future__ import print_function

from barf import BARF

if __name__ == "__main__":
    #
    # Open file
    #
    barf = BARF("./samples/bin/constraint1.x86")

    #
    # Check constraint
    #

    # 80483ed:       55                      push   ebp
    # 80483ee:       89 e5                   mov    ebp,esp
    # 80483f0:       83 ec 10                sub    esp,0x10
    # 80483f3:       8b 45 f8                mov    eax,DWORD PTR [ebp-0x8]
    # 80483f6:       8b 55 f4                mov    edx,DWORD PTR [ebp-0xc]
    # 80483f9:       01 d0                   add    eax,edx
    # 80483fb:       83 c0 05                add    eax,0x5
    # 80483fe:       89 45 fc                mov    DWORD PTR [ebp-0x4],eax
    # 8048401:       8b 45 fc                mov    eax,DWORD PTR [ebp-0x4]
    # 8048404:       c9                      leave
    # 8048405:       c3                      ret

    print("[+] Adding instructions to the analyzer...")

    for addr, asm_instr, reil_instrs in barf.translate(start=0x80483ed, end=0x8048401):
        print("0x{0:08x} : {1}".format(addr, asm_instr))

        for reil_instr in reil_instrs:
            barf.code_analyzer.add_instruction(reil_instr)

    print("[+] Adding pre and post conditions to the analyzer...")

    ebp = barf.code_analyzer.get_register_expr("ebp", mode="post")

    # Preconditions: set range for variable a and b
    a = barf.code_analyzer.get_memory_expr(ebp-0x8, 4, mode="pre")
    b = barf.code_analyzer.get_memory_expr(ebp-0xc, 4, mode="pre")

    for constr in [a >= 2, a <= 100, b >= 2, b <= 100]:
        barf.code_analyzer.add_constraint(constr)

    # Postconditions: set desired value for the result
    c = barf.code_analyzer.get_memory_expr(ebp-0x4, 4, mode="post")

    for constr in [c >= 26, c <= 28]:
        barf.code_analyzer.add_constraint(constr)

    print("[+] Check for satisfiability...")

    if barf.code_analyzer.check() == 'sat':
        print("[+] Satisfiable! Possible assignments:")

        # Get concrete value for expressions
        a_val = barf.code_analyzer.get_expr_value(a)
        b_val = barf.code_analyzer.get_expr_value(b)
        c_val = barf.code_analyzer.get_expr_value(c)

        # Print values
        print("- a: {0:#010x} ({0})".format(a_val))
        print("- b: {0:#010x} ({0})".format(b_val))
        print("- c: {0:#010x} ({0})".format(c_val))

        assert a_val + b_val + 5 == c_val
    else:
        print("[-] Unsatisfiable!")
