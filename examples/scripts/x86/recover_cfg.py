#! /usr/bin/env python

from barf.barf import BARF

if __name__ == "__main__":
    #
    # Open file
    #
    filename = "../../samples/bin/branch4.x86"
    barf = BARF(filename)

    #
    # Recover CFG
    #
    print("[+] Recovering program CFG...")

    cfg = barf.recover_cfg(ea_start=0x40052d, ea_end=0x400560)

    cfg.save(filename + "_cfg", print_ir=True)
