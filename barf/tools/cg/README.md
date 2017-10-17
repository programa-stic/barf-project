# Call Graph Recovery Tool

``BARFcg`` is a Python script built upon BARF that lets you recover the
call graph of a binary program.

# Usage

```
usage: BARFcg [-h] [-s SYMBOL_FILE] [-f {pdf,png,dot}] [-t] [-a | -r RECOVER]
              filename

Tool for recovering CG of a binary.

positional arguments:
  filename              Binary file name.

optional arguments:
  -h, --help            show this help message and exit
  -s SYMBOL_FILE, --symbol-file SYMBOL_FILE
                        Load symbols from file.
  -f {pdf,png,dot}, --format {pdf,png,dot}
                        Output format.
  -t, --time            Print process time.
  -a, --recover-all     Recover all functions.
  -r RECOVER, --recover RECOVER
                        Recover specified functions by address (comma
                        separated).
```
