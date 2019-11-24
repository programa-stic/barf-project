#! /usr/bin/env python

from __future__ import absolute_import

from setuptools import setup
from setuptools import find_packages

__version__ = '0.6.0'

setup(
    author           = 'Christian Heitman',
    author_email     = 'barfframework@gmail.com',
    description      = 'A multiplatform open source Binary Analysis and Reverse engineering Framework',
    download_url     = 'https://github.com/programa-stic/barf-project/tarball/v' + __version__,
    install_requires = [
        'capstone>=3.0.5rc2',
        'future',
        'networkx',
        'pefile',
        'pydot',
        'pyelftools',
        'pygments',
        'pyparsing',
    ],
    license          = 'BSD 2-Clause',
    name             = 'barf',
    classifiers      = [
        'Development Status :: 3 - Alpha',
        'License :: OSI Approved :: BSD License',
        'Natural Language :: English',
        'Programming Language :: Python :: 2.7',
        'Programming Language :: Python :: 3.6',
        'Topic :: Scientific/Engineering :: Information Analysis',
        'Topic :: Security',
        'Topic :: Software Development :: Disassemblers',
        'Topic :: Software Development :: Interpreters',
        'Topic :: Software Development :: Libraries :: Python Modules',
    ],
    packages         = find_packages(exclude=['tests', 'tests.*']),
    url              = 'http://github.com/programa-stic/barf-project',
    entry_points = {
        "console_scripts": [
            "BARFcfg = barf.tools.cfg.cfg:main",
            "BARFcg = barf.tools.cg.cg:main",
            "BARFgadgets = barf.tools.gadgets.gadgets:main",
            "BARFreplay = barf.tools.replay.replay:main",
        ]
    }    ,
    version          = __version__,
    zip_safe         = False
)
