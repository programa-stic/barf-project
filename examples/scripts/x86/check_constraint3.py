#! /usr/bin/env python

import os
import sys

from barf import BARF

if __name__ == "__main__":
    #
    # Open file
    #
    try:
        filename = os.path.abspath("../../bin/x86/constraint3")
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
    # 80483f3:       c7 45 f0 01 00 00 00    mov    DWORD PTR [ebp-0x10],0x1
    # 80483fa:       81 7d f4 44 43 42 41    cmp    DWORD PTR [ebp-0xc],0x41424344
    # 8048401:       75 19                   jne    804841c <main+0x2f>
    # 8048403:       81 7d f8 48 47 46 45    cmp    DWORD PTR [ebp-0x8],0x45464748
    # 804840a:       75 10                   jne    804841c <main+0x2f>
    # 804840c:       81 7d fc ef cd ab 00    cmp    DWORD PTR [ebp-0x4],0xabcdef
    # 8048413:       75 07                   jne    804841c <main+0x2f>
    # 8048415:       c7 45 f0 00 00 00 00    mov    DWORD PTR [ebp-0x10],0x0
    # 804841c:       8b 45 f0                mov    eax,DWORD PTR [ebp-0x10]
    # 804841f:       c9                      leave
    # 8048420:       c3                      ret

    start_addr = 0x80483ed
    end_addr = 0x8048420

    # Recover control flow graph
    print("[+] Recovering function CFG...")

    cfg = barf.recover_cfg(start_addr, end_addr)

    # Set stack
    esp = barf.code_analyzer.get_register_expr("esp")

    barf.code_analyzer.set_precondition(esp == 0xffffceec)

    # Traverse paths and check satisfiability
    print("Checking path satisfiability...")

    for bb_path in cfg.all_simple_bb_paths(start_addr, end_addr):
        path_addrs = [hex(bb.address) for bb in bb_path]

        print("[+] Path : {0}".format(" -> ".join(path_addrs)))

        is_sat = barf.code_analyzer.check_path_satisfiability(bb_path, start_addr)

        print("    Satisfiable? : {0}".format(is_sat))

        if is_sat:
            ebp = barf.code_analyzer.get_register_expr("ebp")

            rv = barf.code_analyzer.get_memory_expr(ebp-0x10, 4)
            cookie1 = barf.code_analyzer.get_memory_expr(ebp-0xc, 4)
            cookie2 = barf.code_analyzer.get_memory_expr(ebp-0x8, 4)
            cookie3 = barf.code_analyzer.get_memory_expr(ebp-0x4, 4)

            esp_val = barf.code_analyzer.get_expr_value(esp)
            ebp_val = barf.code_analyzer.get_expr_value(ebp)

            rv_val = barf.code_analyzer.get_expr_value(rv)
            cookie1_val = barf.code_analyzer.get_expr_value(cookie1)
            cookie2_val = barf.code_analyzer.get_expr_value(cookie2)
            cookie3_val = barf.code_analyzer.get_expr_value(cookie3)

            print("      esp: 0x{0:08x}".format(esp_val))
            print("      ebp: 0x{0:08x}".format(ebp_val))

            print("      cookie1: 0x{0:08x} ({0})".format(cookie1_val))
            print("      cookie2: 0x{0:08x} ({0})".format(cookie2_val))
            print("      cookie3: 0x{0:08x} ({0})".format(cookie3_val))

            print("      rv: 0x{0:08x} ({0})".format(rv_val))
