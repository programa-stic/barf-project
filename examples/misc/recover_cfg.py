#! /usr/bin/env python

from __future__ import absolute_import
from __future__ import print_function

from barf.arch import ARCH_ARM_MODE_ARM
from barf.arch import ARCH_ARM_MODE_THUMB
from barf.barf import BARF

if __name__ == "__main__":
    # x86
    # ======================================================================= #
    #
    # Open file
    #
    filename = "./samples/bin/branch4.x86"
    barf = BARF(filename)

    #
    # Recover CFG
    #
    print("[+] Recovering program CFG...")

    cfg = barf.recover_cfg(start=0x40052d, end=0x400560)

    cfg.save(filename + "_cfg", print_ir=True)

    # ARM
    # ======================================================================= #
    #
    # Open file
    #
    filename = "./samples/bin/branch4.arm"
    barf = BARF(filename)

    #
    # Recover CFG
    #
    print("[+] Recovering program CFG...")

    cfg = barf.recover_cfg(start=0x000083c8, end=0x00008404 + 0x4, arch_mode=ARCH_ARM_MODE_ARM)

    cfg.save(filename + "_cfg", print_ir=True)

    # ARM Thumb
    # ======================================================================= #
    #
    # Open file
    #
    filename = "./samples/bin/branch4.arm_thumb"
    barf = BARF(filename)

    #
    # Recover CFG
    #
    print("[+] Recovering program CFG...")

    cfg = barf.recover_cfg(start=0x00010434, end=0x0001046a + 0x2, arch_mode=ARCH_ARM_MODE_THUMB)

    cfg.save(filename + "_cfg", print_ir=True)
