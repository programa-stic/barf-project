#! /usr/bin/env python

import os
import sys

from barf.barf import BARF

if __name__ == "__main__":
    #
    # Open file
    #
    try:
        filename = os.path.abspath("../../bin/x86/loop2")
        barf = BARF(filename)
    except Exception, err:
        print "[-] Error opening file : %s" % filename

        sys.exit(1)

    #
    # REIL emulation
    #
    context_in = {}
    context_out = barf.emulate_full(context_in, 0x080483ec, 0x08048414)

    print "%s : %s" % ("eax", hex(context_out['registers']["eax"]))

    assert(context_out['registers']["eax"] == 0xa)
