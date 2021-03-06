


Generating C Code
#################

As an experimental feature, Specware provides the possibility to
generate C code from constructive |Metaslang| specs. The C generator
has been tested to work under Linux as well as Windows, the latter
using the Cygwin DLL (see ``www.cygwin.com``). The C code generator
can either be called from the |SShell| or using the |Metaslang|
``generate`` construct inside a ``.sw`` file. In both cases, an
additional parameter can be supplied specifying the basename of the C
source and header files constituting the generated C code.

.. index::
   pair: shell-command; gen-c

The shell command is::

   gen-c <spec-term> [ <c-file-basename> ]
   
where the result of elaborating the spec term gives the spec to be
translated into C and the second optional argument is the basename.

For example::

   gen-c SortImpl Quicksort
   
takes the spec in file ``SortImpl.sw`` and translates it into the C
files ``Quicksort.h`` and ``Quicksort.c``

.. COMMENT: <para>Inside a .sw file:
            .. code-block:: specware
               generate c <spec-term> in "<c-file-basename>"
            Example contents of a .sw file generating c code:
            .. code-block:: specware
               generate c QuickSort in "QuickSort.c"
            This would have the same result as the above command line variant. The
            suffix ``.c`` can be omitted or not.</para>

Generating, Compiling and Running the generated C code using "make"
===================================================================

.. index::
   pair: shell-command; make

The easiest and recommended way of generating C code and compiling it
is by using the |SShell| command

   make <spec-term>
   
This requires that the GNU utilities ``make`` and ``gcc`` (or
equivalent utilities) are installed. The ``make`` utility must reside
in a directory on the Windows system path, or be referenced by the
environment variable ``SPECWARE4_MAKE`` (see below). The ``gcc``
utility must likewise reside in a directory on the Windows system
path, or alternatively the definitions of make variables ``CC`` and
``LD`` in the ``Makerules`` file (see below) must be made to reference
the name or pathname of an installed C compiler.

The |SShell| ``make`` command does the following things:

- it invokes the ``gen-c`` command on the given spec term and uses the
  name of the unit-id as file name for the generated C code (``#``'s are
  replaced by ``_``'s). For example::

     make Layout#Multi

  would invoke ``gen-c Layout#Multi Layout_Multi.c``

- if the C code generation has been successful, a customized Makefile is
  generated into ``swcmake.mk``. This file will include references to
  the built-in Makerules and define the targets and dependencies in a
  way that it compiles and executable with the same name as the
  generated C files with their suffixes removed; e.g., for the above
  example the name of the executable would be ``Layout_Multi``.
  By convention, if a file named *B*\ ``_main.c`` or *B*\ ``_test.c``
  exists, where *B* is a the basename for the generated C files, it will
  be automatically included in the build process; *B*\ ``_test.c`` is only
  used if *B*\ ``_main.c`` does not exist. For the above example this
  would mean that, if a file named ``Layout_Multi_main.c`` exists, it
  will be included in the build.
  In addition to the built-in Makerules file, the generated Makefile
  ``swcmake.mk`` will also include a unit-specific Makefile in the
  current directory called *B* ``.mk`` if such a file exists; e.g., in
  the above example, ``Layout_Multi.mk``. This file can be used to set
  the make variables ``CFLAGS`` and ``USERFILES``, which are used as
  follows:

    +--------------------+--------------------------+
    |one                 |two                       |
    +--------------------+--------------------------+
    |`CFLAGS`            |the value of the          |
    |                    |``CFLAGS`` variable is    |
    |                    |used in calls to the C    |
    |                    |compiler (gcc) and usually|
    |                    |contains example-specific |
    |                    |flags, e.g., optimizer    |
    |                    |flags. Example: ``CFLAGS =|
    |                    |-O3``                     |
    |                    |                          |
    |                    |                          |
    |                    |                          |
    |                    |                          |
    |                    |                          |
    +--------------------+--------------------------+
    |``USERFILES``       |the value of the          |
    |                    |``USERFILES``             |
    |                    |make-variable is used in  |
    |                    |calls for the final       |
    |                    |compilation and linking of|
    |                    |the executable. It usually|
    |                    |lists additional C files  |
    |                    |(``.o`` and/or ``.c``     |
    |                    |files) that the example   |
    |                    |needs to be a fully       |
    |                    |stand-alone application.  |
    |                    |                          |
    +--------------------+--------------------------+


  Other make variables that are used in the generated/predefined rules
  are ``LDFLAGS`` (which can be used to add addtional libraries, etc.),
  ``CPPFLAGS`` (see below), and ``USEGC`` (see below).

- Finally, the Unix "make" command is called with the generated Makefile
  ``swcmake.mk`` as top-level Makefile. By default, the command called
  is "``make``", which requires a program with this name to be available
  in the current system path setting. The system environment variable
  ``SPECWARE4_MAKE`` can be used to overwrite this default behavior: if
  ``SPECWARE4_MAKE`` is set, its value is used as the command to be
  called.

Compiling and Running the generated C code without using "make"
===============================================================

The generated C code is designed to contain as few references outside
the generated code as possible, but there are still some built-in
routines that are referred to. For that reason, the C compiler needs a
few extra arguments specifying system include paths and the location
of the garbage collector library that is used in the generated code.
The easiest way of compiling the generated code is by using a Makefile
and including the supplied C generator system Makefile in it. The
corresponding include statement in a user Makefile would then be as
follows::

   include $(SPECWARE4)/Library/Clib/Makerules
   
where environment variable ``SPECWARE4`` is set to the installation
directory of |Specware|, e.g., ``C:/progra~1/Specware4.2``. This
Makerules file sets the ``CPPFLAGS`` and ``CFLAGS`` make variables to
include the paths and library necessary for successfully compiling the
generated code. If additions to these variables need to be made, one
can either define the augmented variable before the above include
statement in the Makefile, or use the ``:=`` assignment after the
include statement to prevent "make" from recursively processing the
variable. For example::

   CPPFLAGS := -g -pg $(CPPFLAGS)
   
is a valid statement for augmenting the ``CPPFLAGS`` variable after
the include statement. See::

   %SPECWARE4%\Languages\MetaSlang\CodeGen\C\Examples\Makefile
   
for an annotated example Makefile.

Garbage Collector
=================

By default, the generated C code generates calls to the public-domain
Boehm garbage collector (see
``www.hpl.hp.com/personal/Hans_Boehm/gc/``). The library needs to be
built once on a fresh Specware4 tree and will then be used by the
Specware-generated C code. The easiest way to build the gc-library is
described in the example Makefile mentioned above: simple add the
variable ``$(GCLIB)`` to the list of dependencies in the main
Makefile target. Alternatively, this can be done by hand by changing
to the directory
``%SPECWARE4%\Languages\MetaSlang\CodeGen\C\Clib\gc6.6`` and then
running "make". After successful completion of this command, a file
named ``gc.a`` should be present in that directory.

To disable the garbage collector, simply put the variable definition::

   USEGC = no
   
in front of the line including the above Makerules file. This will
prevent the generated code from calling the allocation function of the
garbage collector and the garbage collector library will not be bound
to the executable.

Supplying a C "main" function
=============================

To create a stand-alone C application using the Specware-generated
code, the user has to supply a main function. This can be done either
by directly defining an unqualified |Metaslang| operator ``main`` like
this::

   op main: () -> ()
   def main () ...
   
or by hand-coding a C function ``main()`` in a separate C file, from
where the Specware-generated code is called. Passing command-line
arguments is not yet supported when defining a |Metaslang| ``main``
operator directly. See the Examples directory for examples of both a
hand-written "main" C function that calls the generated code, and a
|Metaslang| definition of op ``main``.

