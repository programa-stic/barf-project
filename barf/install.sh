#! /bin/bash

# Set installation mode
# ---------------------------------------------------------------------------- #
if [ "$#" -eq 1 ] && [ "$1" == "local" ];
then
    echo "[+] Local installation..."
    # Install solvers
    # ------------------------------------------------------------------------ #
    ./install-solvers.sh local

    # Install BARF
    # ------------------------------------------------------------------------ #
    sudo python setup.py install --user
else
    echo "[+] System installation..."
    # Install solvers
    # ------------------------------------------------------------------------ #
    ./install-solvers.sh

    # Install BARF
    # ------------------------------------------------------------------------ #
    sudo python setup.py install
fi
