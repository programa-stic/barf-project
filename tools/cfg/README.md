# Control-Flow Recovery Tool

``BARFcfg`` is a Python script built upon BARF that lets you recover the
control-flow graph of a binary program.

# Usage

```
usage: BARFcfg [-h] [-s SYMBOL_FILE] [-f {txt,pdf,png,dot}] [-t]
               [-d OUTPUT_DIR] [-b] [--show-reil]
               [--immediate-format {hex,dec}] [-a | -r RECOVER]
               filename

Tool for recovering CFG of a binary.

positional arguments:
  filename              Binary file name.

optional arguments:
  -h, --help            show this help message and exit
  -s SYMBOL_FILE, --symbol-file SYMBOL_FILE
                        Load symbols from file.
  -f {txt,pdf,png,dot}, --format {txt,pdf,png,dot}
                        Output format.
  -t, --time            Print process time.
  -d OUTPUT_DIR, --output-dir OUTPUT_DIR
                        Output directory.
  -b, --brief           Brief output.
  --show-reil           Show REIL translation.
  --immediate-format {hex,dec}
                        Output format.
  -a, --recover-all     Recover all functions.
  -r RECOVER, --recover RECOVER
                        Recover specified functions by address (comma
                        separated).
```
