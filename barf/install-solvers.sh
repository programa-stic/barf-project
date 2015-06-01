#! /bin/bash

temp_dir=dependencies

# Set installation mode
# ---------------------------------------------------------------------------- #
if [ "$#" -eq 1 ] && [ "$1" == "local" ];
then
    echo "[+] Local installation..."
    SUDO=
    PREFIX=$(echo ~/.local/usr)
else
    echo "[+] System installation..."
    SUDO=sudo
    PREFIX=$(echo /usr)
fi

# Create temp directory
# ---------------------------------------------------------------------------- #
rm -rf $temp_dir
mkdir $temp_dir
cd $temp_dir

# Install z3
# ---------------------------------------------------------------------------- #
sudo apt-get install -y g++

Z3_DOWNLOAD_URL="https://github.com/Z3Prover/z3/archive/z3-4.4.0.tar.gz"

wget $Z3_DOWNLOAD_URL
tar xvfz z3-4.4.0.tar.gz
rm -f z3-4.4.0.tar.gz

cd z3-z3-4.4.0/
./configure --prefix=$PREFIX
python scripts/mk_make.py
cd build/
make
$SUDO make install
cd ../..

# Install CVC4
# ---------------------------------------------------------------------------- #
sudo apt-get install -y g++ libtool libboost-all-dev libantlr3c-dev libgmp-dev

CVC4_DOWNLOAD_URL="http://cvc4.cs.nyu.edu/builds/src/cvc4-1.4.tar.gz"

wget $CVC4_DOWNLOAD_URL
tar xvfz cvc4-1.4.tar.gz
rm -f cvc4-1.4.tar.gz

cd cvc4-1.4
./configure --prefix=$PREFIX
make
$SUDO make install
cd ..

# Remove temp directory
# ---------------------------------------------------------------------------- #
cd ..
rm -rf $temp_dir
