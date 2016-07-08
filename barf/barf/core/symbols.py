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

    return symbols

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
