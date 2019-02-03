# Copyright (c) 2015, Fundacion Dr. Manuel Sadosky
# All rights reserved.

# Redistribution and use in source and binary forms, with or without
# modification, are permitted provided that the following conditions are met:

# 1. Redistributions of source code must retain the above copyright notice, this
# list of conditions and the following disclaimer.

# 2. Redistributions in binary form must reproduce the above copyright notice,
# this list of conditions and the following disclaimer in the documentation
# and/or other materials provided with the distribution.

# THIS SOFTWARE IS PROVIDED BY THE COPYRIGHT HOLDERS AND CONTRIBUTORS "AS IS"
# AND ANY EXPRESS OR IMPLIED WARRANTIES, INCLUDING, BUT NOT LIMITED TO, THE
# IMPLIED WARRANTIES OF MERCHANTABILITY AND FITNESS FOR A PARTICULAR PURPOSE ARE
# DISCLAIMED. IN NO EVENT SHALL THE COPYRIGHT HOLDER OR CONTRIBUTORS BE LIABLE
# FOR ANY DIRECT, INDIRECT, INCIDENTAL, SPECIAL, EXEMPLARY, OR CONSEQUENTIAL
# DAMAGES (INCLUDING, BUT NOT LIMITED TO, PROCUREMENT OF SUBSTITUTE GOODS OR
# SERVICES; LOSS OF USE, DATA, OR PROFITS; OR BUSINESS INTERRUPTION) HOWEVER
# CAUSED AND ON ANY THEORY OF LIABILITY, WHETHER IN CONTRACT, STRICT LIABILITY,
# OR TORT (INCLUDING NEGLIGENCE OR OTHERWISE) ARISING IN ANY WAY OUT OF THE USE
# OF THIS SOFTWARE, EVEN IF ADVISED OF THE POSSIBILITY OF SUCH DAMAGE.

from __future__ import absolute_import
from __future__ import print_function

import argparse
import os
import sys
import time

from barf.analysis.graphs.callgraph import CallGraph
from barf.barf import BARF
from barf.core.symbols import load_symbols
from barf.tools.common import load_symbols_from_file, recover_cfg_all, recover_cfg_some


def init_parser():

    description = "Tool for recovering CG of a binary."

    parser = argparse.ArgumentParser(
        formatter_class=argparse.RawDescriptionHelpFormatter,
        description=description)

    parser.add_argument(
        "filename",
        type=str,
        help="Binary file name.")

    parser.add_argument(
        "-s", "--symbol-file",
        type=str,
        help="Load symbols from file.")

    parser.add_argument(
        "-f", "--format",
        type=str,
        default="dot",
        choices=["pdf", "png", "dot", "svg"],
        help="Output format.")

    parser.add_argument(
        "-t", "--time",
        action="store_true",
        help="Print process time.")

    group = parser.add_mutually_exclusive_group()

    group.add_argument(
        "-a", "--recover-all",
        action="store_true",
        help="Recover all functions.")

    group.add_argument(
        "-r", "--recover",
        type=str,
        help="Recover specified functions by address (comma separated).")

    return parser


def main():

    parser = init_parser()

    args = parser.parse_args()

    # Set default options.
    if not args.recover_all and not args.recover:
        args.recover_all = True

    process_start = time.time()

    filename = os.path.abspath(args.filename)

    if not os.path.isfile(filename):
        print("[-] File not found : {}".format(filename))

        sys.exit(1)

    # Create an instance of BARF.
    try:
        barf = BARF(filename)
    except Exception:
        print("[-] Error opening file : {}".format(filename))

        sys.exit(1)

    # Load symbols.
    print("[+] Parsing symbol table...")

    if args.symbol_file:
        symbols_by_addr = load_symbols_from_file(args.symbol_file)
    else:
        symbols_by_addr = load_symbols(filename)

    # Recover CFGs.
    print("[+] Recovering CFGs...")

    if args.recover_all:
        cfgs = recover_cfg_all(barf, symbols_by_addr)

    if args.recover:
        addresses = [int(addr, 16) for addr in args.recover.split(",")]

        cfgs = recover_cfg_some(barf, addresses, symbols_by_addr)

    print("[+] Number of CFGs recovered: {:d}".format(len(cfgs)))

    # Recover CG.
    print("[+] Recovering program CG...")

    cfgs_filtered = []
    for cfg in cfgs:
        if len(cfg.basic_blocks) == 0:
            print("[*] Ignoring empty CFG: {}".format(cfg.name))
            continue

        cfgs_filtered.append(cfg)

    cg = CallGraph(cfgs_filtered)

    cg.save(filename.split(os.path.sep)[-1] + "_cg", format=args.format)

    process_end = time.time()

    if args.time:
        process_time = process_end - process_start

        print("[+] Process time: {:.3f}s".format(process_time))


if __name__ == "__main__":

    main()
