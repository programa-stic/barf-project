# Control-Flow Recovery Tool

``BARFcfg`` is a Python script built upon BARF that lets you recover the
control-flow graph of a binary program.

# Usage

```
usage: BARFcfg [-h] [-s SYMBOL_FILE] [-a] [-o RECOVER_ONE] [-f {graph,text}]
               [-t] [-d OUTPUT_DIR] [-b] [-r]
               filename

Tool for recovering CFG of a binary.


positional arguments:
  filename              Binary file name.

optional arguments:
  -h, --help            show this help message and exit
  -s SYMBOL_FILE, --symbol-file SYMBOL_FILE
                        Load symbols from file.
  -a, --recover-all     Recover all functions.
  -o RECOVER_ONE, --recover-one RECOVER_ONE
                        Recover specified function.
  -f {graph,text}, --format {graph,text}
                        Output format.
  -t, --time            Print process time.
  -d OUTPUT_DIR, --output-dir OUTPUT_DIR
                        Ouput directory.
  -b, --brief           Brief output.
  -r, --show-reil       Show REIL translation.

```
