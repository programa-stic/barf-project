#! /usr/bin/env python

from __future__ import absolute_import
from __future__ import print_function

import logging

from barf import BARF

from barf.core.reil import ReilMnemonic

logger = logging.getLogger(__name__)


def check_path_satisfiability(code_analyzer, path, start_address):
        """Check satisfiability of a basic block path.
        """
        start_instr_found = False
        sat = False

        # Traverse basic blocks, translate its instructions to SMT
        # expressions and add them as assertions.
        for bb_curr, bb_next in zip(path[:-1], path[1:]):
            logger.info("BB @ {:#x}".format(bb_curr.address))

            # For each instruction...
            for instr in bb_curr:
                # If the start instruction have not been found, keep
                # looking...
                if not start_instr_found:
                    if instr.address == start_address:
                        start_instr_found = True
                    else:
                        continue

                logger.info("{:#x} {}".format(instr.address, instr))

                # For each REIL instruction...
                for reil_instr in instr.ir_instrs:
                    logger.info("{:#x} {:02d} {}".format(reil_instr.address >> 0x8, reil_instr.address & 0xff,
                                                         reil_instr))

                    if reil_instr.mnemonic == ReilMnemonic.JCC:
                        # Check that the JCC is the last instruction of
                        # the basic block (skip CALL instructions.)
                        if instr.address + instr.size - 1 != bb_curr.end_address:
                            logger.error("Unexpected JCC instruction: {:#x} {} ({})".format(instr.address,
                                                                                            instr,
                                                                                            reil_instr))

                            # raise Exception()

                            continue

                        # Make sure branch target address from current
                        # basic block is the start address of the next.
                        assert(bb_curr.taken_branch == bb_next.address or
                               bb_curr.not_taken_branch == bb_next.address or
                               bb_curr.direct_branch == bb_next.address)

                        # Set branch condition accordingly.
                        if bb_curr.taken_branch == bb_next.address:
                            branch_var_goal = 0x1
                        elif bb_curr.not_taken_branch == bb_next.address:
                            branch_var_goal = 0x0
                        else:
                            continue

                        # Add branch condition goal constraint.
                        code_analyzer.add_constraint(code_analyzer.get_operand_expr(reil_instr.operands[0]) == branch_var_goal)

                        # The JCC instruction was the last within the
                        # current basic block. End this iteration and
                        # start next one.
                        break

                    # Translate and add SMT expressions to the solver.
                    code_analyzer.add_instruction(reil_instr)

            sat = code_analyzer.check() == 'sat'

            logger.info("BB @ {:#x} sat? {}".format(bb_curr.address, sat))

            if not sat:
                break

        # Return satisfiability.
        return sat


if __name__ == "__main__":
    #
    # Open file
    #
    barf = BARF("./samples/bin/constraint3.x86")

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

    print("[+] Recovering function CFG...")

    cfg = barf.recover_cfg(start_addr, end_addr)

    print("[+] Checking path satisfiability...")

    # Preconditions: set stack
    # Note: this isn't strictly necessary but it helps reduce the time it
    # takes the solver find a solution.
    esp = barf.code_analyzer.get_register_expr("esp", mode="pre")

    barf.code_analyzer.add_constraint(esp == 0xffffceec)

    # Traverse paths and check satisfiability
    for bb_path in cfg.all_simple_bb_paths(start_addr, end_addr):
        print("[+] Path: {0}".format(" -> ".join([hex(bb.address) for bb in bb_path])))

        if check_path_satisfiability(barf.code_analyzer, list(bb_path), start_addr):
            print("[+] Satisfiable! Possible assignments:")

            ebp = barf.code_analyzer.get_register_expr("ebp", mode="post")
            rv = barf.code_analyzer.get_memory_expr(ebp-0x10, 4, mode="post")
            cookie1 = barf.code_analyzer.get_memory_expr(ebp-0xc, 4, mode="post")
            cookie2 = barf.code_analyzer.get_memory_expr(ebp-0x8, 4, mode="post")
            cookie3 = barf.code_analyzer.get_memory_expr(ebp-0x4, 4, mode="post")

            rv_val = barf.code_analyzer.get_expr_value(rv)
            cookie1_val = barf.code_analyzer.get_expr_value(cookie1)
            cookie2_val = barf.code_analyzer.get_expr_value(cookie2)
            cookie3_val = barf.code_analyzer.get_expr_value(cookie3)

            print("- cookie1: 0x{0:08x} ({0})".format(cookie1_val))
            print("- cookie2: 0x{0:08x} ({0})".format(cookie2_val))
            print("- cookie3: 0x{0:08x} ({0})".format(cookie3_val))
            print("- rv:      0x{0:08x} ({0})".format(rv_val))
        else:
            print("[-] Unsatisfiable!")
