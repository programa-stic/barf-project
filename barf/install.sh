#! /bin/bash

# Update repository sources
sudo apt-get update

# Install basic stuff
sudo apt-get install python-setuptools
sudo apt-get install binutils-dev
sudo apt-get install python-dev

# Install complementary stuff
sudo apt-get install git-core
sudo apt-get install vim

# Create temp directory
rm -rf temp
mkdir temp
cd temp

# Install Capstone Core
git clone https://github.com/aquynh/capstone
cd capstone/
sudo ./make.sh install

# Install Capstone Python Bindings
cp bindings/python
sudo make install
cd ../../..

# Install z3
git clone https://git.codeplex.com/z3
cd z3/
autconf
./configure
python scripts/mk_make.py
cd build
make
sudo make install
cd ..
cd ..

# Remove temp directory
cd ..
rm -rf temp

# Install BARF
sudo python setup.py develop

# Install GDB plugin
# cat "source /tools/analyzer/analyze.gdb.plugin.py" >> ~/.gdbinit
