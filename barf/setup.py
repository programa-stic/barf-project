#! /usr/bin/env python

from setuptools import setup
from setuptools import find_packages


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
    install_requires = [
        'capstone',
        'networkx',
        'pefile',
        'pybfd',
        'pydot',
        'pygments',
        'pyparsing',
        'sphinx',
    ],
    license          = 'BSD 2-Clause',
    name             = 'barf',
    packages         = find_packages(),
    url              = 'http://github.com/programa-stic/barf-project',
    scripts          = [
        'tools/gadgets/BARFgadgets'
    ],
    version          = '0.2',
    zip_safe         = False
)
