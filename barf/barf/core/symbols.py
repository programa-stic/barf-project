import logging

from elftools.elf.elffile import ELFFile

from elftools.elf.sections import SymbolTableSection
from elftools.elf.descriptions import (
    describe_symbol_type,
    describe_symbol_shndx)


logger = logging.getLogger(__name__)


def load_symbol_tables(f):
    """ Load the symbol tables contained in the file
    """
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

    return symbols
