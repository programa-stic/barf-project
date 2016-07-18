Tutorial
========

El uso del framework es sencillo. El módulo *barf* actúa como interfáz. A
través de este se accede a todos los servicios que ofrece el framework.

Uso básico
----------

El primer paso para poder analizar un binario es *cargarlo* utilizando *BARF*.
La manera de hacer esto es la siguiente:

.. code-block:: python

    >>> from barf import BARF

    >>> # Open ELF file
    >>> barf = BARF("x86-elf-exec-example")

Aquí ``barf`` es una instancia de *BARF* cargada con el binario
``x86-elf-exec-example``. Una vez abierto el binario se pueden realizar
consultas sencillas como las siguientes:

.. code-block:: python

    >>> # Get file format
    >>> print(hex(barf.binary.file_format))

    >>> # Get address of section .text
    >>> print(hex(barf.binary.ea_start))

Operaciones avanzadas
---------------------

Traducción a REIL
^^^^^^^^^^^^^^^^^

En primer lugar, se debe cargar el binario sobre el que va a trabajar. Una vez
hecho esto, se puede comenzar a traducir a *REIL* de manera casi directa,
invocando al método ``translate`` de la clase ``BARF``:

.. code-block:: python

    from barf import BARF

    # Open ELF file
    barf = BARF("x86-elf-exec-example")

    # Translate to REIL
    for addr, asm_instr, reil_instrs in barf.translate():
        print "0x%08x : %s" % (addr, asm_instr)

        for reil_instr in reil_instrs:
            print "\t" + str(reil_instr)

Emulación de REIL
^^^^^^^^^^^^^^^^^

Como en el caso anterior, primero, debe *cargarse* el binario. Luego, debe
crearse un contexto compuesto por los valores de los *registros* y la *memoria*.
Finalmente, se invoca al método ``emulate_full`` pasando como parámetros el
contexto creado y las direcciones de *inicio* y *fin* de la porción de código
que se quiere emular.

.. code-block:: python

    from barf import BARF

    # Open ELF file
    barf = BARF("x86-elf-exec-example")

    # REIL emulation
    context_in = {}
    context_out = barf.emulate(context_in, 0x080483ec, 0x08048414)

    # Print content of EAX
    print "%s : %s" % ("eax", hex(context_out["registers"]["eax"]))

En el ejemplo, se crea un contexto *vacío* y se utilizan las direcciones
``0x080483ec`` y ``0x08048414`` como principio y fin, respectivamente, de
la porción de código a ejecutar. El método retorna el contexto final, dónde
se puede consultar el valor que tienen los registros y la memoria. En este, caso
se inspecciona el valor en el que quedó registro ``eax`` al finalizar la
ejecución.

Internamente, el método ``emulate_full`` opera de la siguiente manera. En
primer lugar desensambla la primera instrucción a emular. Luego, la traduce al
lenguaje intermedio y, finalmente, la *ejecuta*. Calcula cuál es la siguiente
instrucción a ejecutar y repite el proceso anterior.

Recuperación del CFG
^^^^^^^^^^^^^^^^^^^^

Obtener el *CFG* de un binario implica, simplemente, invocar el método
``recover_cfg``.

.. code-block:: python

    from barf import BARF

    # Open ELF file
    barf = BARF("x86-elf-exec-example")

    # Recover CFG
    cfg = barf.recover_cfg()

    # Save CFG to a .dot file
    cfg.save("%s_recover_cfg" % filename)

Chequeo de Restricciones
^^^^^^^^^^^^^^^^^^^^^^^^

Dado el siguiente código:

.. code-block:: objdump

     80483ed:       55                      push   ebp
     80483ee:       89 e5                   mov    ebp,esp
     80483f0:       83 ec 10                sub    esp,0x10
     80483f3:       8b 45 f8                mov    eax,DWORD PTR [ebp-0x8]
     80483f6:       8b 55 f4                mov    edx,DWORD PTR [ebp-0xc]
     80483f9:       01 d0                   add    eax,edx
     80483fb:       83 c0 05                add    eax,0x5
     80483fe:       89 45 fc                mov    DWORD PTR [ebp-0x4],eax
     8048401:       8b 45 fc                mov    eax,DWORD PTR [ebp-0x4]
     8048404:       c9                      leave
     8048405:       c3                      ret

se necesita saber qué valores deben setearse en memoria para que ``eax``
termine con un valor específico al final de la execución del mismo.

Esto se logra de la siguiente manera. En primer lugar se carga el archivo y,
luego, se agregan las instrucciones a analizar.

.. code-block:: python

    from barf import BARF

    # Open ELF file
    barf = BARF("x86-elf-exec-example")

    # add instructions to analyze
    for addr, asm_instr, reil_instrs in barf.translate(0x80483ed, 0x8048401):
        print "%s : %s" % (hex(addr), asm_instr)

        for reil_instr in reil_instrs:
            print "\t%s" % str(reil_instr)

            barf.code_analyzer.add_instruction(reil_instr)

Después, se crean las expresiones sobre las que se van a especificar
condiciones.

.. code-block:: python

    # Get smt expression for ebp register
    eap = barf.code_analyzer.get_register_expr("eax")
    ebp = barf.code_analyzer.get_register_expr("ebp")

    # Get smt expressions for memory locations (each one of 4 bytes)
    a = barf.code_analyzer.get_memory_expr(ebp - 0x8, 4)
    b = barf.code_analyzer.get_memory_expr(ebp - 0xc, 4)
    c = barf.code_analyzer.get_memory_expr(ebp - 0x4, 4)

Se establecen las condiciones sobre las expresiones calculadas.

.. code-block:: python

    # Set range for variable a
    barf.code_analyzer.set_precondition(a >= 2)
    barf.code_analyzer.set_precondition(a <= 100)

    # Set range for variable b
    barf.code_analyzer.set_precondition(b >= 2)
    barf.code_analyzer.set_precondition(b <= 100)

    # Set desire value for the result
    barf.code_analyzer.set_postcondition(c == 13)

Finalmente, se verifica la satisfacibilidad de las restricciones sobre el
código dado.

.. code-block:: python

    # check satisfiability
    if barf.code_analyzer.check() == 'sat':
        print("SAT!")

        # Get concrete value for expressions
        eax_val = barf.code_analyzer.get_expr_value(eax)
        a_val = barf.code_analyzer.get_expr_value(a)
        b_val = barf.code_analyzer.get_expr_value(b)
        c_val = barf.code_analyzer.get_expr_value(c)

        # Print values
        print("eax : 0x%08x (%d)" % (eax_val, eax_val))
        print("ebp : 0x%08x (%d)" % (ebp_val, ebp_val))
        print("  a : 0x%08x (%d)" % (a_val, a_val))
        print("  b : 0x%08x (%d)" % (b_val, b_val))
        print("  c : 0x%08x (%d)" % (c_val, c_val))
    else:
        print("UNSAT!")

Satisfacibilidad de Caminos
^^^^^^^^^^^^^^^^^^^^^^^^^^^

.. code-block:: objdump

     80483ed:       55                      push   ebp
     80483ee:       89 e5                   mov    ebp,esp
     80483f0:       83 ec 10                sub    esp,0x10
     80483f3:       c7 45 f0 01 00 00 00    mov    DWORD PTR [ebp-0x10],0x1
     80483fa:       81 7d f4 44 43 42 41    cmp    DWORD PTR [ebp-0xc],0x41424344
     8048401:       75 19                   jne    804841c <main+0x2f>
     8048403:       81 7d f8 48 47 46 45    cmp    DWORD PTR [ebp-0x8],0x45464748
     804840a:       75 10                   jne    804841c <main+0x2f>
     804840c:       81 7d fc ef cd ab 00    cmp    DWORD PTR [ebp-0x4],0xabcdef
     8048413:       75 07                   jne    804841c <main+0x2f>
     8048415:       c7 45 f0 00 00 00 00    mov    DWORD PTR [ebp-0x10],0x0
     804841c:       8b 45 f0                mov    eax,DWORD PTR [ebp-0x10]
     804841f:       c9                      leave
     8048420:       c3                      ret

En la figura de abajo se puede ver el grafo de control de flujo del código
expuesto.

.. figure:: images/constraint3_cfg.png
   :scale: 70 %
   :alt: Control Flow Graph
   :align: center

   Control Flow Graph

Se puede ver que hay varios caminos que para llegar desde el primer al último
nodo. Una pregunta que surge es: son todos estos caminos posibles de realizarse?
En caso de que se puedan recorrer, qué valores deben setearse en memoria o en
los registros para recorrerlos?

Para responder estas preguntas podemos hacer lo siguiente. En primer lugar,
se debe recuperar el grafo de control de flujo del código que se está
analizando.

.. code-block:: python

    from barf import BARF

    # Open ELF file
    barf = BARF("x86-elf-exec-example")

    # Recover control flow graph
    cfg = barf.recover_cfg(0x80483ed, 0x8048420)

Luego, se establece un valor acorde para el *stack* (esto no es estrictamente
necesario).

.. code-block:: python

    esp = barf.code_analyzer.get_register_expr("esp")

    barf.code_analyzer.set_precondition(esp == 0xffffceec)

Finalmente, se itera sobre todos los caminos entre el nodo *inicial*
(``0x080483ed``) y el final (``0x08048420``), y se chequea la satisfacibilidad
del mismo. En caso de ser satisfacible, se pide al analizador que retorne los
uno de posibles valores que pueden tomar las direcciones de memoria involucradas
para retorrer ese camino en particular.

.. code-block:: python

    for bb_path in cfg.all_simple_bb_paths(start_address, end_address):
        print("    [+] Path : %s" % " -> ".join((map(lambda o : hex(o.address), bb_path))))

        is_sat = barf.code_analyzer.check_path_satisfiability(bb_path, start_address, verbose=False)

        print("        Satisfiable ? : %s" % str(is_sat))

        if is_sat:
            ebp = barf.code_analyzer.get_register_expr("ebp")

            rv = barf.code_analyzer.get_memory_expr(ebp - 0x10, 4)
            cookie1 = barf.code_analyzer.get_memory_expr(ebp - 0xc, 4)
            cookie2 = barf.code_analyzer.get_memory_expr(ebp - 0x8, 4)
            cookie3 = barf.code_analyzer.get_memory_expr(ebp - 0x4, 4)

            rv_val = barf.code_analyzer.get_expr_value(rv)
            cookie1_val = barf.code_analyzer.get_expr_value(cookie1)
            cookie2_val = barf.code_analyzer.get_expr_value(cookie2)
            cookie3_val = barf.code_analyzer.get_expr_value(cookie3)

            print("          esp : 0x%08x" % barf.code_analyzer.get_expr_value(esp))
            print("          ebp : 0x%08x" % barf.code_analyzer.get_expr_value(ebp))

            print("          cookie1: 0x%08x (%d)" % (cookie1_val, cookie1_val))
            print("          cookie2: 0x%08x (%d)" % (cookie2_val, cookie2_val))
            print("          cookie3: 0x%08x (%d)" % (cookie3_val, cookie3_val))

            print("          rv: 0x%08x (%d)" % (rv_val, rv_val))

        print("")
