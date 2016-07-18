#! /bin/bash

# Set installation mode
# ---------------------------------------------------------------------------- #
if [ "$#" -eq 1 ] && [ "$1" == "local" ];
then
    echo "[+] BARF: Local installation..."
    # Install solvers
    # ------------------------------------------------------------------------ #
    ./install-solvers.sh local

    # Install BARF
    # ------------------------------------------------------------------------ #
    python setup.py install --user
else
    echo "[+] BARF: System installation..."
    # Install solvers
    # ------------------------------------------------------------------------ #
    ./install-solvers.sh

    # Install BARF
    # ------------------------------------------------------------------------ #
    sudo python setup.py install
fi
