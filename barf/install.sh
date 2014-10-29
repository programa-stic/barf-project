#! /bin/bash

temp_dir=dependencies

# Install basic stuff
sudo apt-get install -y binutils-dev build-essential g++ nasm
sudo apt-get install -y python-setuptools python-dev
sudo apt-get install -y graphviz xdot

# Create temp directory
rm -rf $temp_dir
mkdir $temp_dir
cd $temp_dir

# Install Capstone Core
git clone https://github.com/aquynh/capstone
cd capstone/
sudo ./make.sh install

# Install Capstone Python Bindings
cd bindings/python/
sudo make install
cd ../../..

# Install z3
git clone https://git.codeplex.com/z3
cd z3/
./configure
python scripts/mk_make.py
cd build/
make
sudo make install
cd ../..

# Install CVC4 dependencies
sudo apt-get install -y libboost-all-dev libantlr3c-dev libgmp-dev

# Install CVC4
wget http://cvc4.cs.nyu.edu/builds/src/cvc4-1.4.tar.gz
tar xfz cvc4-1.4.tar.gz
rm -f cvc4-1.4.tar.gz
cd cvc4-1.4/
./configure
make
sudo make install
cd ..

# Remove temp directory
cd ..
# rm -rf $temp_dir

# Install BARF
sudo python setup.py develop
