#! /usr/bin/env python

import os
import sys

from barf import BARF
from barf.arch import ARCH_ARM_MODE_ARM

if __name__ == "__main__":
    #
    # Open file
    #
    try:
        filename = os.path.abspath("../../bin/arm/constraint1")
        barf = BARF(filename)
    except Exception as err:
        print err

        print "[-] Error opening file : %s" % filename

        sys.exit(1)

    #
    # Check constraint
    #

    # 00008390 <main>:
    #     8390:    e52db004     push    {fp}        ; (str fp, [sp, #-4]!)
    #     8394:    e28db000     add    fp, sp, #0
    #     8398:    e24dd014     sub    sp, sp, #20
    #     839c:    e51b2008     ldr    r2, [fp, #-8]
    #     83a0:    e51b300c     ldr    r3, [fp, #-12]
    #     83a4:    e0823003     add    r3, r2, r3
    #     83a8:    e2833005     add    r3, r3, #5
    #     83ac:    e50b3010     str    r3, [fp, #-16]
    #     83b0:    e51b3010     ldr    r3, [fp, #-16]
    #     83b4:    e1a00003     mov    r0, r3
    #     83b8:    e28bd000     add    sp, fp, #0
    #     83bc:    e8bd0800     ldmfd    sp!, {fp}
    #     83c0:    e12fff1e     bx    lr

    start_addr = 0x8390
    end_addr = 0x83bc

    # Add instructions to analyze
    print("[+] Adding instructions to the analyzer...")

    for addr, asm_instr, reil_instrs in barf.translate(ea_start=start_addr, ea_end=end_addr, arch_mode=ARCH_ARM_MODE_ARM):
        print("0x{0:08x} : {1}".format(addr, asm_instr))

        for reil_instr in reil_instrs:
            print("{0:14}{1}".format("", reil_instr))

            barf.code_analyzer.add_instruction(reil_instr)

    # Get smt expressions and set pre and post conditions
    print("[+] Adding pre and post conditions to the analyzer...")

    # Get smt expression for eax and ebp registers
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
        a_val = barf.code_analyzer.get_expr_value(a)
        b_val = barf.code_analyzer.get_expr_value(b)
        c_val = barf.code_analyzer.get_expr_value(c)

        # Print values
        print("      a : 0x{0:08x} ({0})".format(a_val))
        print("      b : 0x{0:08x} ({0})".format(b_val))
        print("      c : 0x{0:08x} ({0})".format(c_val))

        assert(a_val + b_val + 5 == c_val)
    else:
        print("    UNSAT!")
