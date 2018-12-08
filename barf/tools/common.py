# Copyright (c) 2017, Fundacion Dr. Manuel Sadosky
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

import os

def print_recovery_status(address, name, size):
    size = size if size != 0 else "?"

    print("    Processing {} @ {:#x} ({})".format(name, address, size))


def load_symbols_from_file(filename):
    symbols_by_addr = {}

    with open(filename, "r") as f:
        for line in f.readlines():
            # Remove trailing '\n'.
            line = line[:-1]

            # Skip blank lines and comments.
            if line == "" or line[0] == "#":
                continue

            # Process line.
            parts = line.split(' ')

            try:
                addr, name, size, returns = parts[0], " ".join(parts[1:-2]), parts[-2], parts[-1]
            except:
                raise Exception("Error processing symbol file.")

            symbols_by_addr[int(addr, 16)] = (name, int(size), returns == "True")

    return symbols_by_addr


def recover_cfg_some(barf, addresses, symbols_by_addr):
    cfgs = []

    for addr in sorted(addresses):
        cfg = barf.recover_cfg(start=addr, symbols=symbols_by_addr, callback=print_recovery_status)

        cfgs.append(cfg)

    return cfgs


def recover_cfg_all(barf, symbols_by_addr):
    if len(symbols_by_addr) > 0:
        print("[+] Recovering from symbols")

        entries = [addr for addr in sorted(symbols_by_addr.keys())]
    else:
        print("[+] Recovering from entry point")

        entries = [barf.binary.entry_point]

    cfgs = barf.recover_cfg_all(entries, symbols=symbols_by_addr, callback=print_recovery_status)

    return cfgs


def create_output_dir(name):
    if not os.path.exists(name):
        os.makedirs(name)

    return name
