#! /usr/bin/env python

import os
import sys

from barf import BARF

if __name__ == "__main__":
    #
    # Open file
    #
    try:
        filename = os.path.abspath("../../samples/toy/constraint1")
        barf = BARF(filename)
    except Exception as err:
        print err

        print "[-] Error opening file : %s" % filename

        sys.exit(1)

    #
    # Check constraint
    #

    # 00008444 <main>:
    #     8444:    e52db004     push    {fp}        ; (str fp, [sp, #-4]!)
    #     8448:    e28db000     add    fp, sp, #0
    #     844c:    e24dd014     sub    sp, sp, #20
    #     8450:    e51b2008     ldr    r2, [fp, #-8]
    #     8454:    e51b300c     ldr    r3, [fp, #-12]
    #     8458:    e0823003     add    r3, r2, r3
    #     845c:    e2833005     add    r3, r3, #5
    #     8460:    e50b3010     str    r3, [fp, #-16]
    #     8464:    e51b3010     ldr    r3, [fp, #-16]
    #     8468:    e1a00003     mov    r0, r3
    #     846c:    e24bd000     sub    sp, fp, #0
    #     8470:    e49db004     pop    {fp}        ; (ldr fp, [sp], #4)
    #     8474:    e12fff1e     bx    lr

    start_addr = 0x8444
    end_addr = 0x8474 - 4 # TODO SKIP BX

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
#     eax = barf.code_analyzer.get_register_expr("eax")
#     ebp = barf.code_analyzer.get_register_expr("ebp")
    fp = barf.code_analyzer.get_register_expr("fp")

    # Get smt expressions for memory locations (each one of 4 bytes)
    a = barf.code_analyzer.get_memory_expr(fp - 0x08, 4)
    b = barf.code_analyzer.get_memory_expr(fp - 0x0c, 4)
    c = barf.code_analyzer.get_memory_expr(fp - 0x10, 4)

    # Set range for variable a and b
    barf.code_analyzer.set_preconditions([a >= 2, a <= 100])
    barf.code_analyzer.set_preconditions([b >= 2, b <= 100])

    # Set desired value for the result
    barf.code_analyzer.set_postconditions([c >= 26, c <= 28])

    # Check satisfiability
    print("[+] Check for satisfiability...")

    if barf.code_analyzer.check() == 'sat':
        print("    SAT! :: Possible assigments : ")

        # Get concrete value for expressions
#         eax_val = barf.code_analyzer.get_expr_value(eax)
        a_val = barf.code_analyzer.get_expr_value(a)
        b_val = barf.code_analyzer.get_expr_value(b)
        c_val = barf.code_analyzer.get_expr_value(c)

        # Print values
#         print("    eax : 0x{0:08x} ({0})".format(eax_val))
        print("      a : 0x{0:08x} ({0})".format(a_val))
        print("      b : 0x{0:08x} ({0})".format(b_val))
        print("      c : 0x{0:08x} ({0})".format(c_val))

        assert(a_val + b_val + 5 == c_val)
    else:
        print("    UNSAT!")
