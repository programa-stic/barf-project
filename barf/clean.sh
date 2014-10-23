#! /bin/bash

base_dir=$(dirname $BASH_SOURCE[0])

find . -name '*.pyc' -exec rm {} \;

rm -rf $base_dir/barf/log/*.log
