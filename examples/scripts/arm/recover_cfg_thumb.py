#! /usr/bin/env python

import os
import sys

from barf.barf import BARF
from barf.arch import ARCH_ARM_MODE_THUMB

if __name__ == "__main__":
    #
    # Open file
    #
    try:
        # ARM THUMB
        filename = os.path.abspath("../../bin/arm/branch4-thumb")
        barf = BARF(filename)
    except Exception as err:
        print err

        print "[-] Error opening file : %s" % filename

        sys.exit(1)

    #
    # Recover CFG
    #
    print("[+] Recovering program CFG...")

    cfg = barf.recover_cfg(ea_start=0x00010434, ea_end=0x0001046a + 0x2, arch_mode=ARCH_ARM_MODE_THUMB)

    cfg.save(filename + "_cfg", print_ir=True)
