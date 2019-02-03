#! /usr/bin/env python

from __future__ import absolute_import
from __future__ import print_function

from barf import BARF

if __name__ == "__main__":
    #
    # Open file
    #
    barf = BARF("./samples/bin/constraint1.arm")

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

    print("[+] Adding instructions to the analyzer...")

    for addr, asm_instr, reil_instrs in barf.translate(start=0x8390, end=0x83bc):
        print("0x{0:08x} : {1}".format(addr, asm_instr))

        for reil_instr in reil_instrs:
            barf.code_analyzer.add_instruction(reil_instr)

    print("[+] Adding pre and post conditions to the analyzer...")

    fp = barf.code_analyzer.get_register_expr("fp", mode="post")

    # Preconditions: set range for variable a and b
    a = barf.code_analyzer.get_memory_expr(fp - 0x08, 4, mode="pre")
    b = barf.code_analyzer.get_memory_expr(fp - 0x0c, 4, mode="pre")

    for constr in [a >= 2, a <= 100, b >= 2, b <= 100]:
        barf.code_analyzer.add_constraint(constr)

    # Postconditions: set desired value for the result
    c = barf.code_analyzer.get_memory_expr(fp - 0x10, 4, mode="post")

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
