#! /bin/bash

python -m unittest -v basicblocktests
python -m unittest -v codeanalyzertests
python -m unittest -v armgadgettests
python -m unittest -v x86gadgettests
python -m unittest -v reiltests
python -m unittest -v smttests
python -m unittest -v x86tests
# python -m unittest -v armtests
