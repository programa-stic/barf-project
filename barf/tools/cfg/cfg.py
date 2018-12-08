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

from barf.barf import BARF
from barf.core.symbols import load_symbols
from barf.tools.common import create_output_dir
from barf.tools.common import load_symbols_from_file
from barf.tools.common import recover_cfg_all
from barf.tools.common import recover_cfg_some


def save_cfg_graph(cfg, output_dir, show_reil, fmt, immediate_format):
    options = {
        "immediate_format": immediate_format
    }

    cfg.save(output_dir + os.path.sep + cfg.name, print_ir=show_reil, format=fmt, options=options)


def save_cfg_text(cfg, output_dir, show_reil, brief):
    fn_name = cfg.name
    fn_start = cfg.start_address
    fn_end = cfg.end_address

    with open(output_dir + os.path.sep + fn_name + ".txt", "w") as f:
        print("Function : {} [{:#x} - {:#x}]".format(fn_name, fn_start, fn_end), file=f)

        for bb in cfg.basic_blocks:
            branches = ", ".join(sorted(["{:#x}".format(a) for a, _ in bb.branches]))

            print("[basic block] {:#x}:{:#x} -> {}".format(bb.start_address, bb.end_address + 1, branches), file=f)

            if not brief:
                for instr in bb:
                    print("  {:#x}    {}".format(instr.address, instr), file=f)

                    if show_reil:
                        for reil_instr in instr.ir_instrs:
                            print("  {:#x}:{:02x}   {}".format(reil_instr.address >> 0x8, reil_instr.address & 0xFF, reil_instr), file=f)


def save_cfgs(cfgs, output_dir, output_format, show_reil, brief, immediate_format):
    for cfg in cfgs:
        if len(cfg.basic_blocks) == 0:
            print("[*] Ignoring empty CFG: {}".format(cfg.name))
            continue

        if output_format in ["pdf", "png", "dot", "svg"]:
            save_cfg_graph(cfg, output_dir, show_reil, output_format, immediate_format)

        if output_format == "txt":
            save_cfg_text(cfg, output_dir, show_reil, brief)


def init_parser():

    description = "Tool for recovering CFG of a binary."

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
        choices=["txt", "pdf", "png", "dot", "svg"],
        help="Output format.")

    parser.add_argument(
        "-t", "--time",
        action="store_true",
        help="Print process time.")

    parser.add_argument(
        "-d", "--output-dir",
        type=str,
        default=".",
        help="Output directory.")

    parser.add_argument(
        "-b", "--brief",
        default=False,
        action="store_true",
        help="Brief output.")

    parser.add_argument(
        "--show-reil",
        default=False,
        action="store_true",
        help="Show REIL translation.")

    parser.add_argument(
        "--immediate-format",
        type=str,
        default="hex",
        choices=["hex", "dec"],
        help="Output format.")

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

    output_dir = create_output_dir(args.output_dir + os.path.sep + filename.split(os.path.sep)[-1] + "_cfg")

    if args.recover_all:
        cfgs = recover_cfg_all(barf, symbols_by_addr)

    if args.recover:
        addresses = [int(addr, 16) for addr in args.recover.split(",")]

        cfgs = recover_cfg_some(barf, addresses, symbols_by_addr)

    print("[+] Number of CFGs recovered: {:d}".format(len(cfgs)))

    # Saving CFGs to files.
    print("[+] Saving CFGs...")

    save_cfgs(cfgs, output_dir, args.format, args.show_reil, args.brief, args.immediate_format)

    process_end = time.time()

    if args.time:
        process_time = process_end - process_start

        print("[+] Process time: {:.3f}s".format(process_time))


if __name__ == "__main__":

    main()
