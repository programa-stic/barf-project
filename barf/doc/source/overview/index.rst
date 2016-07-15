Estructura de BARF
=================

*BARF* está estructurado en 3 componentes principales, i.e. **Core**,
**Arch** y **Analysis**. El módulo ``barf``, que contiene a la clase
``BARF``, es el encargado de unir todos los componentes y brinda una
interfáz de fácil uso para las tareas más comunes.

A continuación se describe cada uno de los componentes y, por último,
se detalla el módulo ``barf``.

Componentes
-----------

Core
^^^^

Es el componente que tienen las funcionalidades básicas que, luego, el resto del
framework usará. Está conformado por módulos que describen el lenguage REIL,
una interfáz para cargar un binario, módulos para el manejo de un *SMT solver*,
etc.

Para cargar un binario se utiliza la librería **PyBFD**. Esta permite cargar
distintos tipos de formatos de ejecutable, entre ellos *ELF* y *PE*. Mediante
esta se obtiene la sección de texto del ejecutable para poder operar sobre él.

Este *componente* está formado por los siguientes paquetes:

* **dbg**

    Describe interfaces con *debuggers*.

* **reil**

    Este *paquete* describe al lenguaje de representación intermedia *REIL*,
    utilizado por *BARF*. Entre las clases que definen están: las instrucciones
    de REIL, un emulador de código y un *parser*.

* **smt**

    Contiene todo lo referente a los *SMT solvers*, entre ellos está la
    clase que interactúa con el *solver* **z3** y los traductores entre
    las instrucciones REIL a expresiones SMT.

Además, cuenta con los siguientes módulos:

* **binaryfile**

    Provee funcionalidades para cargar binario para ser analizados.

* **disassembler**

    Interfáz para los desensambladores de cada arquitectura.

Arch
^^^^

El objetivo de este *paquete* es describir las architecturas soportadas por
*BARF*. Este es el punto de inicio para extender el framework. Las clases que
conforman a una architectura son las siguientes:

* **ArchitectureInformation**

    Describe a la architectura. Indica los registros que posee, cuáles son
    de proposito general, cuál es el tamaño de las direcciones de memoria, etc.

* **Disassembler**

    Implementa un desensamblador para la arquitectura en cuestión. En este
    caso se utiliza como motor desensamblador a **capstone**, sin embargo,
    una vez obtenida la instrucción desensamblada, esta se *parsea* de modo
    de representar a cada instrucción con una clase que brinda más información
    sobre la instrucción.

* **Instruction**

    Cada instrucción de la arquitectura es modelada con una clase. En motivo
    de esto es poder describir adecuadamente a cada instrucción, indicando
    cuáles son sus operandos fuente y destino, si son escribibles o solo
    lectura, etc. Esto, por ejemplo, tiene en cuenta si hay registros
    implícitos y el modo de operación (por ejemplo, en x86, si está operando
    en 32 o 64 bits).

* **InstructionTranslator**

    Cada instrucción de la architectura tiene asociada una función de traducción
    a REIL. En este módulo se describe cada una de ellas.

* **Parser**

    Este módulo cuenta con la funcionalidad para *parsear* el *string* de una
    instrucción desensamblada y retornar el *objeto* instrucción.

Los módulos comentados son los mínimos necesarios para describir una
arquitectura.

Actualmente, la única arquitectura implementada es la **x86** para los
modos de operación 32 y 64 bits.

Analysis
^^^^^^^^

Este *paquete* contiene todos los algoritmos genéricos que operan sobre
el código intermedio REIL.

Este *componente* está formado por el siguientes *subpaquetes*:

* **basicblock**

    Encapsula toda la lógica que permite reconstruir el
    *Control Flow Graph* de un binario. Las clases principales que se
    exportan son:

        * ``BasicBlock``
        * ``BasicBlockBuilder``
        * ``ControlFlowGraph``

* **codeanalyzer**

    Encapsula toda la lógica que permite realizar análisis semántico de
    código. Las clases principales que se exportan son:

        * ``CodeAnalyzer``
        * ``GenericContext``
        * ``GenericRegister``

* **gadget**

    Contiene varios módulos cuyo objetivo es *encontrar*, *clasificar* y
    *verificar* gadgets. Las clases principales que se exportan son:

        * ``Gadget``
        * ``GadgetFinder``
        * ``GadgetClassifier``
        * ``GadgetVerifier``

Interfaz
--------

El módulo *barf* contiene una sola clase ``BARF`` y actúa como pegamento
de todas las demás clases y funciones.

La idea de esta clase es permitir cargar un binario de modo simple y
exponer todos los servicios disponibles para analizar el binario
cargado.

La clase ``BARF`` está compuesta por las siguientes clases:

* **SmtSolver**

    Clase que permite interactuar con un *SMT solver*.

* **SmtTranslator**

    Clase que realiza la traducción de instrucciones REIL a expresiones
    *SMT*.

* **Disassembler**

    Clase que permite desensamblar código máquina de manera genérica. Al
    cargar un binario, se instancia en con la architectura para la que
    fue compilado el mismo.

* **Translator**

    Esta clase permite traducir el set de instrucciones de una architectura
    particular a instrucciones REIL. Se instancia del mismo modo que
    **Disassembler**.

* **ReilEmulator**

    Clase que permite emular código REIL.

* **ArchitectureInformation**

    Clase que brinda toda la información necesaria sobre una
    arquitectura específica. Se instancia con la arquitectura del
    binario cargado.

Además, cuenta con los módulos de análisis: **BasicBlockBuilder**,
**CodeAnalyzer** y **Gadget**.
