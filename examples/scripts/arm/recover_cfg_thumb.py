#! /usr/bin/env python

from barf.barf import BARF
from barf.arch import ARCH_ARM_MODE_THUMB

if __name__ == "__main__":
    #
    # Open file
    #
    filename = "../../samples/bin/branch4.arm_thumb"
    barf = BARF(filename)
    #
    # Recover CFG
    #
    print("[+] Recovering program CFG...")

    cfg = barf.recover_cfg(ea_start=0x00010434, ea_end=0x0001046a + 0x2, arch_mode=ARCH_ARM_MODE_THUMB)

    cfg.save(filename + "_cfg", print_ir=True)
