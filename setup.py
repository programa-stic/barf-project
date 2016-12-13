#! /usr/bin/env python

from setuptools import setup
from setuptools import find_packages

__version__ = '0.3'

# https://github.com/aquynh/capstone/issues/583
def fix_setuptools():
    """Work around bugs in setuptools.

    Some versions of setuptools are broken and raise SandboxViolation for normal
    operations in a virtualenv. We therefore disable the sandbox to avoid these
    issues.
    """
    try:
        from setuptools.sandbox import DirectorySandbox

        def violation(operation, *args, **_):
            print "SandboxViolation: %s" % (args,)

        DirectorySandbox._violation = violation
    except ImportError:
        pass

# Fix bugs in setuptools.
fix_setuptools()

setup(
    author           = 'Christian Heitman',
    author_email     = 'cnheitman@fundacionsadosky.org.ar',
    description      = 'A multiplatform open source Binary Analysis and Reverse engineering Framework',
    download_url     = 'https://github.com/programa-stic/barf-project/tarball/v0.3',
    install_requires = [
        'capstone',
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
        'Topic :: Scientific/Engineering :: Information Analysis',
        'Topic :: Security',
        'Topic :: Software Development :: Disassemblers',
        'Topic :: Software Development :: Interpreters',
        'Topic :: Software Development :: Libraries :: Python Modules',
    ],
    packages         = find_packages(exclude=['tests', 'tests.*']),
    url              = 'http://github.com/programa-stic/barf-project',
    scripts          = [
        'scripts/barf-install-solvers.sh',
        'tools/cfg/BARFcfg',
        'tools/cg/BARFcg',
        'tools/gadgets/BARFgadgets',
    ],
    version          = __version__,
    zip_safe         = False
)
