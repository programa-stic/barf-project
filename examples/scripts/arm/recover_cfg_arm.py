#! /usr/bin/env python

import os
import sys

from barf.barf import BARF
from barf.arch import ARCH_ARM_MODE_ARM

if __name__ == "__main__":
    #
    # Open file
    #
    try:
        # ARM MODE
        filename = os.path.abspath("../../bin/arm/branch4")
        barf = BARF(filename)
    except Exception as err:
        print err

        print "[-] Error opening file : %s" % filename

        sys.exit(1)

    #
    # Recover CFG
    #
    print("[+] Recovering program CFG...")

    cfg = barf.recover_cfg(ea_start=0x000083c8, ea_end=0x00008404 + 0x4, arch_mode=ARCH_ARM_MODE_ARM)

    cfg.save(filename + "_cfg", print_ir=True)
