# Copyright (c) 2014, Fundacion Dr. Manuel Sadosky
# All rights reserved.

# Redistribution and use in source and binary forms, with or without
# modification, are permitted provided that the following conditions are met:

# 1. Redistributions of source code must retain the above copyright notice, this
# list of conditions and the following disclaimer.

# 2. Redistributions in binary form must reproduce the above copyright notice,
# this list of conditions and the following disclaimer in the documentation
# and/or other materials provided with the distribution.

# THIS SOFTWARE IS PROVIDED BY THE COPYRIGHT HOLDERS AND CONTRIBUTORS "AS IS"
# AND ANY EXPRESS OR IMPLIED WARRANTIES, INCLUDING, BUT NOT LIMITED TO, THE
# IMPLIED WARRANTIES OF MERCHANTABILITY AND FITNESS FOR A PARTICULAR PURPOSE ARE
# DISCLAIMED. IN NO EVENT SHALL THE COPYRIGHT HOLDER OR CONTRIBUTORS BE LIABLE
# FOR ANY DIRECT, INDIRECT, INCIDENTAL, SPECIAL, EXEMPLARY, OR CONSEQUENTIAL
# DAMAGES (INCLUDING, BUT NOT LIMITED TO, PROCUREMENT OF SUBSTITUTE GOODS OR
# SERVICES; LOSS OF USE, DATA, OR PROFITS; OR BUSINESS INTERRUPTION) HOWEVER
# CAUSED AND ON ANY THEORY OF LIABILITY, WHETHER IN CONTRACT, STRICT LIABILITY,
# OR TORT (INCLUDING NEGLIGENCE OR OTHERWISE) ARISING IN ANY WAY OUT OF THE USE
# OF THIS SOFTWARE, EVEN IF ADVISED OF THE POSSIBILITY OF SUCH DAMAGE.

import logging
import pefile

from elftools.elf.elffile import ELFFile

from elftools.elf.sections import SymbolTableSection
from elftools.elf.descriptions import (
    describe_symbol_type,
    describe_symbol_shndx)


logger = logging.getLogger(__name__)


def load_symbols_pe(filename):
    # TODO: Implement this
    pe = pefile.PE(filename)

    pe.parse_data_directories()

    pe.close()

    return {}

def load_symbols_elf(filename):
    """ Load the symbol tables contained in the file
    """
    f = open(filename, 'rb')

    elffile = ELFFile(f)

    symbols = []

    for section in elffile.iter_sections():
        if not isinstance(section, SymbolTableSection):
            continue

        if section['sh_entsize'] == 0:
            logger.warn("Symbol table {} has a sh_entsize of zero.".format(section.name))

            continue

        logger.info("Symbol table {} contains {} entries.".format(section.name, section.num_symbols()))

        for _, symbol in enumerate(section.iter_symbols()):
            if describe_symbol_shndx(symbol['st_shndx']) != "UND" and \
                describe_symbol_type(symbol['st_info']['type']) == "FUNC":
                symbols.append((symbol['st_value'], symbol['st_size'], symbol.name))

    f.close()

    symbols_by_addr = {
        addr : (name, size, True)
            for addr, size, name in symbols
    }

    return symbols_by_addr

def load_symbols(filename):
    try:
        fd = open(filename, 'rb')
        signature = fd.read(4)
        fd.close()
    except:
        raise Exception("Error loading file.")

    if signature[:4] == "\x7f\x45\x4c\x46":
        symbols = load_symbols_elf(filename)
    elif signature[:2] == b'\x4d\x5a':
        symbols = load_symbols_pe(filename)
    else:
        raise Exception("Unkown file format.")

    return symbols
