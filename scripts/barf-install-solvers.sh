#! /bin/bash

temp_dir=$(mktemp -d)

# Set installation mode
# ---------------------------------------------------------------------------- #
if [ "$#" -eq 1 ] && [ "$1" == "local" ];
then
    echo "[+] SMT Solvers: Local installation..."
    SUDO=
    PREFIX=$(echo ~/.local/usr)
else
    echo "[+] SMT Solvers: System installation..."
    SUDO=sudo
    PREFIX=$(echo /usr)
fi

# Create temp directory
# ---------------------------------------------------------------------------- #
rm -rf $temp_dir
mkdir $temp_dir
cd $temp_dir

# Install z3 (if it is not installed...)
# ---------------------------------------------------------------------------- #
if ! type "z3" > /dev/null; then
    echo "[+] Installing z3..."

    sudo apt-get install -y g++

    Z3_DOWNLOAD_URL="https://github.com/Z3Prover/z3/archive/z3-4.4.0.tar.gz"

    wget $Z3_DOWNLOAD_URL
    tar xvfz z3-4.4.0.tar.gz
    rm -f z3-4.4.0.tar.gz

    cd z3-z3-4.4.0/
    ./configure --prefix=$PREFIX
    python scripts/mk_make.py
    cd build/
    make -j 4
    $SUDO make install
    cd ../..
fi

# Install CVC4 (if it is not installed...)
# ---------------------------------------------------------------------------- #
# TODO: Fix. There are some problems with boost library.
# if ! type "cvc4" > /dev/null; then
#     echo "[+] Installing cvc4..."

#     sudo apt-get install -y g++ libtool libboost-all-dev libantlr3c-dev libgmp-dev

#     CVC4_DOWNLOAD_URL="http://cvc4.cs.nyu.edu/builds/src/cvc4-1.4.tar.gz"

#     wget $CVC4_DOWNLOAD_URL
#     tar xvfz cvc4-1.4.tar.gz
#     rm -f cvc4-1.4.tar.gz

#     cd cvc4-1.4
#     ./configure --prefix=$PREFIX
#     make -j 4
#     $SUDO make install
#     cd ..
# fi

# Remove temp directory
# ---------------------------------------------------------------------------- #
cd ..
rm -rf $temp_dir
