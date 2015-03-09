#! /usr/bin/env python

import os
import sys

from barf import BARF

if __name__ == "__main__":
    #
    # Open file
    #
    try:
        filename = os.path.abspath("../../samples/toy/arm/constraint3")
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
    #     839c:    e3a03001     mov    r3, #1
    #     83a0:    e50b3008     str    r3, [fp, #-8]
    #     83a4:    e51b200c     ldr    r2, [fp, #-12]
    #     83a8:    e59f3040     ldr    r3, [pc, #64]    ; 83f0 <main+0x60>
    #     83ac:    e1520003     cmp    r2, r3
    #     83b0:    1a000009     bne    83dc <main+0x4c>
    #     83b4:    e51b2010     ldr    r2, [fp, #-16]
    #     83b8:    e59f3034     ldr    r3, [pc, #52]    ; 83f4 <main+0x64>
    #     83bc:    e1520003     cmp    r2, r3
    #     83c0:    1a000005     bne    83dc <main+0x4c>
    #     83c4:    e51b2014     ldr    r2, [fp, #-20]
    #     83c8:    e59f3028     ldr    r3, [pc, #40]    ; 83f8 <main+0x68>
    #     83cc:    e1520003     cmp    r2, r3
    #     83d0:    1a000001     bne    83dc <main+0x4c>
    #     83d4:    e3a03000     mov    r3, #0
    #     83d8:    e50b3008     str    r3, [fp, #-8]
    #     83dc:    e51b3008     ldr    r3, [fp, #-8]
    #     83e0:    e1a00003     mov    r0, r3
    #     83e4:    e28bd000     add    sp, fp, #0
    #     83e8:    e8bd0800     ldmfd    sp!, {fp}
    #     83ec:    e12fff1e     bx    lr
    #     83f0:    41424344     .word    0x41424344
    #     83f4:    45464748     .word    0x45464748
    #     83f8:    00abcdef     .word    0x00abcdef

    start_addr = 0x8390
    end_addr = 0x83e8

    # Recover control flow graph
    print("[+] Recovering function CFG...")

    cfg = barf.recover_cfg(start_addr, end_addr)

    cfg.save("test", print_ir=True)

    # Set stack
    sp = barf.code_analyzer.get_register_expr("sp")

    barf.code_analyzer.set_precondition(sp == 0xffffceec)

    # Traverse paths and check satisfiability
    print("Checking path satisfiability...")

    for bb_path in cfg.all_simple_bb_paths(start_addr, end_addr):
        path_addrs = [hex(bb.address) for bb in bb_path]

        print("[+] Path : {0}".format(" -> ".join(path_addrs)))

        is_sat = barf.code_analyzer.check_path_satisfiability(bb_path, start_addr)

        print("    Satisfiable? : {0}".format(is_sat))

        if is_sat:
            fp = barf.code_analyzer.get_register_expr("fp")

            rv = barf.code_analyzer.get_memory_expr(fp - 0x8, 4)
            cookie1 = barf.code_analyzer.get_memory_expr(fp - 0xc, 4)
            cookie2 = barf.code_analyzer.get_memory_expr(fp - 0x10, 4)
            cookie3 = barf.code_analyzer.get_memory_expr(fp - 0x14, 4)

            sp_val = barf.code_analyzer.get_expr_value(sp)
            fp_val = barf.code_analyzer.get_expr_value(fp)

            rv_val = barf.code_analyzer.get_expr_value(rv)
            cookie1_val = barf.code_analyzer.get_expr_value(cookie1)
            cookie2_val = barf.code_analyzer.get_expr_value(cookie2)
            cookie3_val = barf.code_analyzer.get_expr_value(cookie3)

            print("      sp: 0x{0:08x}".format(sp_val))
            print("      fp: 0x{0:08x}".format(fp_val))

            print("      cookie1: 0x{0:08x} ({0})".format(cookie1_val))
            print("      cookie2: 0x{0:08x} ({0})".format(cookie2_val))
            print("      cookie3: 0x{0:08x} ({0})".format(cookie3_val))

            print("      rv: 0x{0:08x} ({0})".format(rv_val))
