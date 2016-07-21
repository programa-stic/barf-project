#! /usr/bin/env python

import os
import sys

from barf import BARF

if __name__ == "__main__":
    #
    # Open file
    #
    try:
        filename = os.path.abspath("../../bin/x86/constraint2")
        barf = BARF(filename)
    except Exception as err:
        print err

        print "[-] Error opening file : %s" % filename

        sys.exit(1)

    #
    # Check constraint
    #

    # 80483ed:       55                      push   ebp
    # 80483ee:       89 e5                   mov    ebp,esp
    # 80483f0:       83 ec 10                sub    esp,0x10
    # 80483f3:       8b 45 f4                mov    eax,DWORD PTR [ebp-0xc]
    # 80483f6:       0f af 45 f8             imul   eax,DWORD PTR [ebp-0x8]
    # 80483fa:       83 c0 05                add    eax,0x5
    # 80483fd:       89 45 fc                mov    DWORD PTR [ebp-0x4],eax
    # 8048400:       8b 45 fc                mov    eax,DWORD PTR [ebp-0x4]
    # 8048403:       c9                      leave
    # 8048404:       c3                      ret

    start_addr = 0x80483ed
    end_addr = 0x8048402

    # Add instructions to analyze
    print("[+] Adding instructions to the analyzer...")

    for addr, asm_instr, reil_instrs in barf.translate(start_addr, end_addr):
        print("0x{0:08x} : {1}".format(addr, asm_instr))

        for reil_instr in reil_instrs:
            print("{0:14}{1}".format("", reil_instr))

            barf.code_analyzer.add_instruction(reil_instr)

    # Get smt expressions and set pre and post conditions
    print("[+] Adding pre and post conditions to the analyzer...")

    # Get smt expression for eax and ebp registers
    eax = barf.code_analyzer.get_register_expr("eax", mode="post")
    ebp = barf.code_analyzer.get_register_expr("ebp", mode="post")

    # Get smt expressions for memory locations (each one of 4 bytes)
    a = barf.code_analyzer.get_memory_expr(ebp-0x8, 4)
    b = barf.code_analyzer.get_memory_expr(ebp-0xc, 4)
    c = barf.code_analyzer.get_memory_expr(ebp-0x4, 4)

    # Set range for variable a and b
    barf.code_analyzer.set_preconditions([a >= 2, a <= 100])
    barf.code_analyzer.set_preconditions([b >= 2, b <= 100])

    # Set desired value for the result
    barf.code_analyzer.set_postcondition(c == 15)

    # Check satisfiability
    print("[+] Check for satisfiability...")

    if barf.code_analyzer.check() == 'sat':
        print("    SAT! :: Possible assigments : ")

        # Get concrete value for expressions
        eax_val = barf.code_analyzer.get_expr_value(eax)
        a_val = barf.code_analyzer.get_expr_value(a)
        b_val = barf.code_analyzer.get_expr_value(b)
        c_val = barf.code_analyzer.get_expr_value(c)

        # Print values
        print("    eax : 0x{0:08x} ({0})".format(eax_val))
        print("      a : 0x{0:08x} ({0})".format(a_val))
        print("      b : 0x{0:08x} ({0})".format(b_val))
        print("      c : 0x{0:08x} ({0})".format(c_val))

        assert(a_val * b_val + 5 == c_val)
    else:
        print("    UNSAT!")
