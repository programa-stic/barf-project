#! /usr/bin/env python

# Copyright (c) 2014, Fundacion Dr. Manuel Sadosky
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

from __future__ import print_function

import argparse
import os
import sys
import time

from pygments import highlight
from pygments.formatters import TerminalFormatter
from pygments.lexers.asm import NasmLexer

from barf.analysis.gadget.gadget import GadgetType
from barf.barf import BARF

def filter_duplicates(candidates):

    gadgets = {}

    for cand in candidates:
        asm_instrs = " ; ".join([str(dinstr.asm_instr) for dinstr in cand.instrs])

        if asm_instrs not in gadgets:
            gadgets[asm_instrs] = cand

    return [cand for asm_instrs, cand in gadgets.items()]

def sort_gadgets_by_type(gadgets):
    # Sort gadgets by type.
    gadgets_by_type = {}

    for gadget in gadgets:
        if gadget.type not in gadgets_by_type:
            gadgets_by_type[gadget.type] = []

        gadgets_by_type[gadget.type] += [gadget]

    return gadgets_by_type

def sort_gadgets_by_address(gadgets):
    # Sort gadgets by address.
    gadgets_by_address = {}

    for gadget in gadgets:
        if gadget.address not in gadgets_by_address:
            gadgets_by_address[gadget.address] = []

        gadgets_by_address[gadget.address] += [gadget]

    return gadgets_by_address

def sort_gadgets_by_depth(gadgets):
    # Sort gadgets by depth (instructions number).
    gadgets_by_depth = {}

    for gadget in gadgets:
        instrs_count = len(gadget.instrs)

        if instrs_count not in gadgets_by_depth:
            gadgets_by_depth[instrs_count] = []

        gadgets_by_depth[instrs_count] += [gadget]

    return gadgets_by_depth

def print_gadgets_raw(gadgets, f, sort_mode, color, title, show_binary):
    # Print title
    print(title,            file=f)
    print("=" * len(title), file=f)
    print(" " * len(title), file=f)

    sort_methods = {
        'addr'  : sort_gadgets_by_address,
        'depth' : sort_gadgets_by_depth,
    }

    gadgets_sorted = sort_methods[sort_mode](gadgets)

    for key in sorted(gadgets_sorted.keys()):
        for gadget in gadgets_sorted[key]:
            asm_instrs = [str(dinstr.asm_instr) for dinstr in gadget.instrs]

            if color:
                asm_instrs = map(lambda s: highlight(s, NasmLexer(), TerminalFormatter()), asm_instrs)

            asm_instrs_str = " ; ".join(asm_instrs).replace("\n", "")

            if show_binary:
                try:
                    asm_bytes = ["%02x" % ord(b) for dinstr in gadget.instrs for b in dinstr.asm_instr.bytes]
                    asm_bytes_str = "".join(asm_bytes)

                    print("0x%08x: %32s | %s" % (gadget.address, asm_bytes_str, asm_instrs_str), file=f)
                except:
                    print("[+] Error!")
                    print("\t0x%08x: %s" % (gadget.address, asm_instrs_str), file=f)
            else:
                print("0x%08x: %s" % (gadget.address, asm_instrs_str), file=f)

        if sort_mode == "depth":
            print("", file=f)

    if sort_mode == "addr":
        print("", file=f)

    # Print summary.
    summary_item_fmt  = "[+] {name} : {value}"
    summary_ruler_fmt = "{0}"

    summary_item  = summary_item_fmt.format(name=title, value=len(gadgets))
    summary_ruler = summary_ruler_fmt.format(" " * len(summary_item))

    print(summary_item,  file=f)
    print(summary_ruler, file=f)

def print_gadgets_typed(gadgets, f, address_size, title):
    # Print title.
    print(title,            file=f)
    print("=" * len(title), file=f)
    print(" " * len(title), file=f)

    # Sort gadgets by type.
    by_type = sort_gadgets_by_type(gadgets)

    # Pretty print gadgets.
    for ty, gadget_list in by_type.items():
        gadgets_desc = {}
        lhands = []
        rhands = []
        instrs = []
        mods   = []

        # Prepare gadgets for printing.
        for gadget in gadget_list:
            g_str, mod_regs_str = str(gadget).split(" > ")
            lhand, rhand = g_str.split(" <- ")

            if gadget.address not in gadgets_desc:
                gadgets_desc[gadget.address] = []

            asm_instrs     = [str(dinstr.asm_instr) for dinstr in gadget.instrs]
            asm_instrs_str = " ; ".join(asm_instrs).replace("\n", "")

            gadgets_desc[gadget.address] += [{
                'addr'  : gadget.address,
                'lhand' : lhand,
                'rhand' : rhand,
                'mods'  : mod_regs_str,
                'instrs' : asm_instrs_str,
            }]

            lhands += [len(lhand)]
            rhands += [len(rhand)]
            mods   += [len(mod_regs_str)]
            instrs += [len(asm_instrs_str)]

        # Compute columns width.
        lhand_max  = max(lhands)
        rhand_max  = max(rhands)
        mods_max   = max(mods)
        instrs_max = max(instrs)

        # Tile and table formats.
        table_title_fmt  = "# {0} ({1} gadget{2})"
        table_ruler_fmt  = "{0}"
        table_header_fmt = " {0:^%ds} | {1:^%ds} | {2:^%ds} | {3:^%ds} " % (address_size / 4 + 2, lhand_max + rhand_max + 4, mods_max, instrs_max)
        table_footer_fmt = "{0}"
        table_row_fmt    = " 0x{addr:0%dx} | {lhand:>%ds} <- {rhand:<%ds} | {mods:<%ds} | {instrs} " % (address_size / 4, lhand_max, rhand_max, max(mods_max, len("Clobbered Registers")))

        table_title  = table_title_fmt.format(GadgetType.to_string(ty), len(gadget_list), "" if len(gadget_list) == 1 else "s")
        table_header = table_header_fmt.format("Address", "Operation", "Clobbered Registers", "Instructions")
        table_ruler  = table_ruler_fmt.format("-" * len(table_header))
        table_footer = table_footer_fmt.format(" " * len(table_header))

        print(table_title,        file=f)
        print(table_ruler,        file=f)
        print(table_header,       file=f)
        print(table_ruler,        file=f)

        # Pretty print each gadget.
        for address in sorted(gadgets_desc.keys()):
            for gadget_desc in gadgets_desc[address]:
                print(table_row_fmt.format(**gadget_desc), file=f)

        print(table_footer, file=f)

    # Print summary.
    summary_item_fmt  = "[+] {name} : {value}"
    summary_ruler_fmt = "{0}"

    summary_item  = summary_item_fmt.format(name=title, value=len(gadgets))
    summary_ruler = summary_ruler_fmt.format(" " * len(summary_item))

    print(summary_item,  file=f)
    print(summary_ruler, file=f)

def init_parser():

    description = "Tool for finding, classifying and verifying ROP gadgets."

    parser = argparse.ArgumentParser(
        formatter_class=argparse.RawDescriptionHelpFormatter,
        description=description)

    parser.add_argument(
        "filename",
        type=str,
        help="Binary file name.")

    parser.add_argument(
        "--version",
        action="store_true",
        help="Display version.")

    parser.add_argument(
        "--bdepth",
        type=int,
        default=10,
        help="Gadget depth in number of bytes.")

    parser.add_argument(
        "--idepth",
        type=int,
        default=2,
        help="Gadget depth in number of instructions.")

    parser.add_argument(
        "-u", "--unique",
        action="store_true",
        help="Remove duplicate gadgets (in all steps).")

    parser.add_argument(
        "-c", "--classify",
        action="store_true",
        help="Run gadgets classification.")

    parser.add_argument(
        "-v", "--verify",
        action="store_true",
        help="Run gadgets verification (includes classification).")

    parser.add_argument(
        "-o", "--output",
        type=str,
        default=None,
        help="Save output to file.")

    parser.add_argument(
        "-t", "--time",
        action="store_true",
        help="Print time of each processing step.")

    parser.add_argument(
        "--sort",
        type=str,
        default="addr",
        choices=["addr", "depth"],
        help="Sort gadgets by address or depth (number of instructions) in ascending order.")

    parser.add_argument(
        "--color",
        action="store_true",
        help="Format gadgets with ANSI color sequences, for output in a 256-color terminal or console.")

    parser.add_argument(
        "--show-binary",
        action="store_true",
        help="Show binary code for each gadget.")

    parser.add_argument(
        "--show-classification",
        action="store_true",
        help="Show classification for each gadget.")

    parser.add_argument(
        "--show-invalid",
        action="store_true",
        help="Show invalid gadget, i.e., gadgets that were classified but did not pass the verification process.")

    parser.add_argument(
        "--summary",
        type=str,
        default=None,
        help="Save summary to file.")

    parser.add_argument(
        "-r",
        type=int,
        choices=[8, 16, 32, 64],
        help="Filter verified gadgets by operands register size.")

    return parser

def do_find(bin, args):
    start = time.time()

    candidates = bin.gadget_finder.find(bin.binary.ea_start, bin.binary.ea_end, byte_depth=args.bdepth, instrs_depth=args.idepth)

    end = time.time()
    find_time = end - start

    # Filter duplicate gadgets.
    if args.unique:
        candidates = filter_duplicates(candidates)

        end = time.time()
        find_time = end - start

    return candidates, find_time

def do_classify(bin, gadgets, args):
    start = time.time()

    classified = []

    for gadget in gadgets:
        classified += bin.gadget_classifier.classify(gadget)

    end = time.time()

    classify_time = end - start

    return classified, classify_time

def do_verify(bin, classified, args):
    start = time.time()

    verified = []
    invalid = []

    for gadget in classified:
        valid = bin.gadget_verifier.verify(gadget)

        if valid:
            gadget.is_valid = True
            verified += [gadget]
        else:
            invalid += [gadget]

    end = time.time()

    verify_time = end - start

    discarded = []

    # Filter by operand size.
    if args.r:
        verified_temp = []

        for gadget in verified:
            if all([op.size == args.r for op in gadget.sources]) and \
                all([op.size == args.r for op in gadget.destination]):
                verified_temp += [gadget]

        verified = verified_temp

    # Filter duplicate gadgets.
    if args.unique:
        verified_by_type = {}

        for gadget in verified:
            if gadget.type not in verified_by_type:
                verified_by_type[gadget.type] = []

            gadgets = verified_by_type[gadget.type]

            if not any(gadget == another for another in gadgets):
                gadgets += [gadget]
            else:
                discarded += [gadget]

        verified_distinct = []

        for _, gadgets in verified_by_type.items():
            verified_distinct += gadgets

        verified = verified_distinct

        end = time.time()

        verify_time = end - start

    return verified, verify_time, discarded, invalid

def main():

    parser = init_parser()

    args = parser.parse_args()

    find_time = 0.0
    classify_time = 0.0
    verify_time = 0.0

    address_size = None

    output_fd = sys.stdout
    filename = os.path.abspath(args.filename)

    if not os.path.isfile(filename):
        print("[-] Error opening file : %s" % filename)

        sys.exit(1)

    # create an instance of BARF
    try:
        barf = BARF(filename)

        address_size = barf.arch_info.address_size
    except Exception as err:
        import traceback

        print(err)
        print(traceback.format_exc())

        sys.exit(1)

    # Open output file.
    if args.output:
        output_fd = open(args.output, "w")

    if args.verify:
        args.classify = True

    # Find gadgets.
    candidates, find_time = do_find(barf, args)

    print_gadgets_raw(candidates, output_fd, args.sort, args.color, "Raw Gadgets", args.show_binary)

    # Classify gadgets.
    if args.classify:
        classified, classify_time = do_classify(barf, candidates, args)

        if args.show_classification:
            print_gadgets_typed(classified, output_fd, address_size, "Classified Gadgets")

    # Verify gadgets.
    if args.verify:
        if barf.gadget_verifier:
            verified, verify_time, discarded, invalid = do_verify(barf, classified, args)

            print_gadgets_typed(verified, output_fd, address_size, "Verified Gadgets")

            if args.show_invalid:
                print_gadgets_typed(invalid, output_fd, address_size, "Invalid Gadgets (classified but didn't pass verification process)")

            # print non-verified
            candidates_by_addr = sort_gadgets_by_address(candidates)
            verified_by_addr   = sort_gadgets_by_address(verified)
            discarded_by_addr   = sort_gadgets_by_address(discarded)

            diff = []

            for addr in candidates_by_addr.keys():
                if not addr in verified_by_addr and not addr in discarded_by_addr:
                    diff += candidates_by_addr[addr]

            print_gadgets_raw(diff, output_fd, args.sort, args.color, "Non-verified Gadgets", args.show_binary)
        else:
            print("Gadget verification not available. Check the log file for more information.")

    # Print processing time.
    if args.time:
        total_time = find_time + classify_time + verify_time

        print("Time Report", file=output_fd)
        print("===========", file=output_fd)
        print("           ", file=output_fd)
        print("          Find Stage : {0:8.3f}s".format(find_time),     file=output_fd)
        print("Classification Stage : {0:8.3f}s".format(classify_time), file=output_fd)
        print("  Verification Stage : {0:8.3f}s".format(verify_time),   file=output_fd)
        print("               Total : {0:8.3f}s".format(total_time),    file=output_fd)

    if args.summary:
        summary_fd = open(args.summary, "a")

        fmt  = "{gadgets:d} {classify:d} {verify:d} {size:d} "   # basic stuff
        fmt += "{ftime:.3f} {ctime:.3f} {vtime:.3f} "            # time
        fmt += "{no_operation} {jump} {move_register} {load_constant} {arithmetic} {load_memory} {store_memory} {arithmetic_load} {arithmetic_store} {undefined}"

        by_type = sort_gadgets_by_type(verified)

        if GadgetType.NoOperation not in by_type: by_type[GadgetType.NoOperation] = []
        if GadgetType.Jump not in by_type: by_type[GadgetType.Jump] = []
        if GadgetType.MoveRegister not in by_type: by_type[GadgetType.MoveRegister] = []
        if GadgetType.LoadConstant not in by_type: by_type[GadgetType.LoadConstant] = []
        if GadgetType.Arithmetic not in by_type: by_type[GadgetType.Arithmetic] = []
        if GadgetType.LoadMemory not in by_type: by_type[GadgetType.LoadMemory] = []
        if GadgetType.StoreMemory not in by_type: by_type[GadgetType.StoreMemory] = []
        if GadgetType.ArithmeticLoad not in by_type: by_type[GadgetType.ArithmeticLoad] = []
        if GadgetType.ArithmeticStore not in by_type: by_type[GadgetType.ArithmeticStore] = []
        if GadgetType.Undefined not in by_type: by_type[GadgetType.Undefined] = []

        line = fmt.format(
            gadgets=len(candidates),
            classify=len(classified),
            verify=len(verified),
            size=barf.binary.ea_end-barf.binary.ea_start,
            ftime=find_time,
            ctime=classify_time,
            vtime=verify_time,
            no_operation=len(by_type[GadgetType.NoOperation]),
            jump=len(by_type[GadgetType.Jump]),
            move_register=len(by_type[GadgetType.MoveRegister]),
            load_constant=len(by_type[GadgetType.LoadConstant]),
            arithmetic=len(by_type[GadgetType.Arithmetic]),
            load_memory=len(by_type[GadgetType.LoadMemory]),
            store_memory=len(by_type[GadgetType.StoreMemory]),
            arithmetic_load=len(by_type[GadgetType.ArithmeticLoad]),
            arithmetic_store=len(by_type[GadgetType.ArithmeticStore]),
            undefined=len(by_type[GadgetType.Undefined])
        )

        summary_fd.write(line + "\n")

        summary_fd.close()

    # Close output file.
    if args.output:
        output_fd.close()

if __name__ == "__main__":

    main()
