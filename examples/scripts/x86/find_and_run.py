#! /usr/bin/env python

import sys

from barf.analysis.basicblock.callgraph import CallGraph
from barf.barf import BARF
from barf.core.symbols import load_symbols


if __name__ == "__main__":
    #
    # Open file
    #
    try:
        filename = "../../bin/x86/example1"
        arg = "hello!"
        barf = BARF(filename)
    except Exception:
        print("[-] Error opening file : {}".format(filename))
        sys.exit(1)

    #
    # Recover CFGs.
    #
    print("[+] Recovering control flow graphs...")
    symbols_by_addr = load_symbols(filename)
    entries = [addr for addr in sorted(symbols_by_addr.keys())]
    cfgs = barf.recover_cfg_all(entries, symbols=symbols_by_addr)

    #
    # Build CG.
    #
    print("[+] Building call graph...")
    cfgs_filtered = []
    for cfg in cfgs:
        if len(cfg.basic_blocks) == 0:
            continue
        cfgs_filtered.append(cfg)
    cg = CallGraph(cfgs_filtered)

    #
    # Find the desired functions.
    #
    cfg_start = cg.find_function_by_name("main")
    cfg_end = cg.find_function_by_name("function_of_interest")
    assert cfg_start and cfg_end

    #
    # Check if there is a path between the main function and the function of interest.
    #
    path_ok = False
    for path in cg.simple_paths_by_address(cfg_start.start_address, cfg_end.start_address):
        path_str = " -> ".join(["{} ({:#x})".format(cfg.name, cfg.start_address) for cfg in path])
        print("[+] There is a path between '{}' and '{}': {}".format(cfg_start.name, cfg_end.name, path_str))
        path_ok = True

    #
    # Execute.
    #
    if path_ok:
        reil_emulator = barf.ir_emulator

        # Set stack pointer.
        esp = 0x00001500

        # Set argv.
        argv_0_addr = 0x00001900
        argv_0_data = bytearray(filename + "\x00")
        for i, b in enumerate(argv_0_data):
            reil_emulator.write_memory(argv_0_addr + i, 1, b)

        argv_1_addr = argv_0_addr + len(argv_0_data)
        argv_1_data = bytearray(arg + "\x00")
        for i, b in enumerate(argv_1_data):
            reil_emulator.write_memory(argv_1_addr + i, 1, b)

        argv_base_addr = 0x00001800
        reil_emulator.write_memory(argv_base_addr + 0x00, 4, argv_0_addr)
        reil_emulator.write_memory(argv_base_addr + 0x04, 4, argv_1_addr)
        reil_emulator.write_memory(argv_base_addr + 0x08, 4, 0x00000000)

        # Set main parameters.
        argc = 0x2
        argv = argv_base_addr

        # Push parameters into the stack.
        reil_emulator.write_memory(esp + 0x00, 4, 0x41414141) # return address

        reil_emulator.write_memory(esp + 0x04, 4, argc) # argc
        reil_emulator.write_memory(esp + 0x08, 4, argv) # argv

        # Set registers.
        ctx_init = {
            'registers': {
                # Set eflags and stack pointer.
                'eflags': 0x202,
                'esp': esp,
            }
        }

        # Emulate code.
        print("[+] Executing from {:#x} to {:#x}".format(cfg_start.start_address, cfg_end.start_address))
        ctx_fini = barf.emulate_full(ctx_init, ea_start=cfg_start.start_address, ea_end=cfg_end.start_address)
