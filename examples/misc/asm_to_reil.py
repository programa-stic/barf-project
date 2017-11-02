#! /usr/bin/env python

from barf.barf import BARF

if __name__ == "__main__":
    # x86
    # ======================================================================= #
    #
    # Open file
    #
    barf = BARF("./samples/bin/branch4.x86")

    #
    # Translate to REIL
    #
    print("[+] Translating: x86 -> REIL")

    for addr, asm_instr, reil_instrs in barf.translate():
        print("0x{0:08x} : {1}".format(addr, asm_instr))

        for reil_instr in reil_instrs:
            print("{0:14}{1}".format("", reil_instr))

    # ARM
    # ======================================================================= #
    #
    # Open file
    #
    barf = BARF("./samples/bin/branch4.arm")

    #
    # Translate to REIL
    #
    print("[+] Translating: x86 -> REIL")

    for addr, asm_instr, reil_instrs in barf.translate(start=0x000083c8, end=0x00008404):
        print("0x{0:08x} : {1}".format(addr, asm_instr))

        for reil_instr in reil_instrs:
            print("{0:14}{1}".format("", reil_instr))
