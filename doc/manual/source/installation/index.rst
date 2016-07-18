Instalación
===========

Sistemas Debian
---------------

Se cuenta con un *script* de instalación que realiza todo el proceso.

.. code-block:: bash

    $ ./install.sh

Este script primero instala las dependencias, **z3** y **capstone**, y, luego,
el framework.

Otros sistemas
--------------

Para otros sistemas, la instalación de las dependencias es manual. La
instalación del framework es:

.. code-block:: bash

    $ sudo python setup.py install
