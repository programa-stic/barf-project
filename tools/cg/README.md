# Call Graph Recovery Tool

``BARFcg`` is a Python script built upon BARF that lets you recover the
call graph of a binary program.

# Usage

```
usage: BARFcg [-h] [-s SYMBOL_FILE] [-a] [-t] filename

Tool for recovering CG of a binary.

positional arguments:
  filename              Binary file name.

optional arguments:
  -h, --help            show this help message and exit
  -s SYMBOL_FILE, --symbol-file SYMBOL_FILE
                        Load symbols from file.
  -a, --recover-all     Recover all functions.
  -t, --time            Print process time.

```
