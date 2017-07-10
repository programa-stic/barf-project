#! /usr/bin/env python

from barf.barf import BARF
from barf.arch import ARCH_ARM_MODE_ARM

if __name__ == "__main__":
    #
    # Open file
    #
    filename = "../../samples/bin/branch4.arm"
    barf = BARF(filename)

    #
    # Recover CFG
    #
    print("[+] Recovering program CFG...")

    cfg = barf.recover_cfg(start=0x000083c8, end=0x00008404 + 0x4, arch_mode=ARCH_ARM_MODE_ARM)

    cfg.save(filename + "_cfg", print_ir=True)
