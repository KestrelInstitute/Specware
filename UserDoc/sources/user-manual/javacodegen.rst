

Generating Java Code
####################

As an experimental feature, Specware provides the possibility to
generate Java code from constructive |Metaslang| specs. The Java code
generator can either be called from the |SShell| or using the
``generate`` construct inside a ``.sw`` file. In both cases, an
additional "option" spec can be supplied, which is used to specify
certain parameters that govern aspects of code generation. For the
format of the option spec, see `The Option Spec`_.

.. index::
   pair: shell-command; gen-java


The command has the form:

.. code-block:: specware

   gen-java <spec-term> [<option-spec-term>]
   
where the result of elaborating the spec term gives the spec to be
translated into Java and the second spec term gives the option spec
(see below).

.. COMMENT: <para>Inside a ``.sw`` file:
            .. code-block:: specware
               generate Java <spec-term> with <option spec-id>
            Example contents of a ``.sw`` file generating Java code: 
            .. code-block:: specware
               let myspec = spec 
                ...
               endspec
               in
               let myoptions = spec
                   def package = "com.mycompany.myapp"
                   ...
               endspec
               in
               generate java myspec with myoptions
            </para>


The Option Spec
===============

The option spec is used as an attribute store to be able to control
certain parameters used by the Java code generator. The option spec is
a regular |Metaslang| spec. The parameters are given by constant ops
defined inside the option spec. The following list contains the op
names and types that are currently interpreted as parameters by the
Java code generator:

.. list-table::
   :widths: 200 200 200
   :header-rows: 1

   *  - Op name |amp| type
      - Used as
      - Default value
   *  - \ ``package : String``\
      - Name of the Java package for all generated Java class files.
        The package name also determines the relative path of the
        generated ``.java`` files (see the ``basedir`` parameter)
      - \ ``"specware.generated"``\
   *  - \ ``basedir : String``\
      - The base directory used for the generated Java class files.
        The full path is determine by this parameter and the relative
        path derived from the package name. For instance, if the value
        of ``basedir`` is the string ``"/a/b"`` and the package name
        is ``c.d.e``, then the generated Java class files would go
        into the directory ``/a/b/c/d/e``.
      - ``"."``
   *  - ``public : List String``
      - The list of op names that are to be declared as ``public`` in
        the generated Java code. Only unqualified identifiers can be
        used in this list. The ops in this list determine the "entry
        points" into the generated Java code, if it is embedded in
        another Java application.
      - ``[]``
   *  - ``"imports : List String"``
      - The list of imports that are to be used for all generated Java
        class files. Each element of this list has the usual format of
        the argument used by Java's import statement; e.g.,
        ``"java.util.*"``
      - ``[]``

Example option spec:

.. code-block:: specware

   spec
     def package = "test.sw.gen"
     def imports = ["java.util.*"]
     def public = ["test2"]
     def basedir = "~/myjavaapps"
   endspec
   
If no option spec is specified in the ``gen-java`` command, default
values are used for all option parameters.

Translation of Inbuilt Ops
==========================

The following table shows the translation of some inbuilt |Metaslang|
ops into Java:

.. list-table::
   :widths: 200 200
   :header-rows: 1

   *  - |Metaslang|
      - Java
   *  - ``String.writeLine(t)``
        ``String.toScreen(t)``
      - ``System.out.println(t)``
   *  - ``String.concat(t1,t2)``
        ``t1 ++ t2``
      - ``t1 + t2``
   *  - ``String.newline``
      -  ``System.getProperty ("line.separator")``
   *  - ``String.length``
      - ``t.length()``
   *  - ``String.substring(s,n1,n2)``
      - ``s.substring(n1,n2)``
   *  - ``Nat.toString(n)``
        ``Nat.natToString(n)``
        ``Nat.show(n)``
        ``Integer.toString(n)``
        ``Integer.intToString(n)``
        ``Integer.show(n)``
      - ``String.valueOf(n)``
   *  - ``Nat.stringToNat(s)``
        ``Integer.stringToInt(s)``
      - ``Integer.parseInt(s)``
   *  - ``t1 && t2``
      - ``t1 && t2``
   *  - ``t1 || t2``
      - ``t1 || t2``
   *  - ``t1 =< t2``
      - ``t1 ? t2 : true``
   *  - ``t1 <=< t2``
      - ``t1 ? t2 : !t2``

|Metaslang|/Java Interface
==========================

In order to use Java methods and classes inside a |Metaslang| spec,
the following conventions are used by the Java code generator:

Java Classes
  In order to use Java classes as types inside |Metaslang|, you have
  to declare the type without a definition and add corresponding Java
  import statements using the option spec (see above).  Example: use
  of the Java class ``java.util.Vector`` In the spec for which code is
  generated::

     ...
     type Vector
     ...
     op myvectorop: Vector -> Nat
     def myvectorop(v) = ...
     ...

  In the option spec::

     ...
     def imports = [ ..., "java.util.*", ... ]
     ...

  The code generator interprets all types without a definition as base
  types, so that in this case the op ``myvectorop`` becomes a static
  method in the generated ``Primitive`` class.


Accessing External Java Instance Methods 
  Instance methods as well as static class methods can be accessed
  from inside |Metaslang| specs using the following convention:
  Assume, we want to use some instance method ``epi(args)`` defined in
  Java class ``Tecton``. First, the class must be made known to
  |Metaslang| by providing a type declaration for the class. Then, an
  op ``epi`` must be declared with a signature that corresponds to the
  method's signature, but with an additional parameter preceeding the
  others. The type of that parameter must be the class type::

     type Tecton
     op epi: Tecton * T1 * ... * Tn -> T

  where ``T1 * ... * Tn -> T`` is the original signature of ``epi``
  without the additional parameter. The ``Ti``\ 's are the translated
  |Metaslang| types that correspond to the Java types occurring in
  ``epi``\ 's signature; see the table below for the type
  correspondence. In the |Metaslang| code, a call to the instance method
  is created by the Java code generator whenever ``epi`` is applied::

     def mycode(...) =
       ...
       let b : Tecton = ... in
         ...
         ... epi(b,arg1,...argn) ...

  Note, that a definition term must not be given for ``epi``.
  Limitation: using ``epi`` as a function symbol in higher-order
  contexts will not yield the expected result.

Accessing External Java Class Methods 
  Accessing Java class methods is very similar to instance methods,
  with the difference that instead of the type of the first argument,
  the qualifier of the op declaration is used to determine the class
  name. Therefore, in general, it is not necessary to declare the
  class as a type. Assume we want to access to class method
  ``Math.abs()`` from the Java library. We therefore declare the
  ``abs`` operator in |Metaslang| as follows::

     op Math.abs: Integer -> Nat

  The code generator will then generate a call to the static method
  ``Math.abs()`` whenever it is used in the |Metaslang| spec. The
  access to static methods has lower priority than the access to
  instance methods: if the first argument is a user type that is not
  defined in the spec, than the instance call is generated. In other
  words, a static method in *class* ``A`` with a first argument of
  *type* ``A`` will not be accessible from |Metaslang|. The latter
  situation is not very common, and in practice this does not
  constitute a limitation of the |Metaslang|-Java interface.

Accessing Java Constructors
  Accessing Java constructors follows the same principle as for class
  methods. The difference is that on the |Metaslang| side, an op with
  a name having the prefix ``new`` and an appropriate result type must
  be declared. For instance, the Java class ``Vector`` declares a
  constructor with no arguments. If we want to use that in
  |Metaslang|, we have to provide the following declarations::

     type Vector
     op Vector.new: () -> Vector

  Whenever ``Vector.new()`` is used as a term in the |Metaslang| spec, a
  call to the corresponding Java constructor in the ``Vector`` class is
  generated. If the class has multiple constructors with different
  parameter lists, multiple ``new`` ops can be declared in the
  |Metaslang| spec with different suffixes (e.g., ``new_2``\ ) The Java
  code ignores the suffixes, but they are essential for |Metaslang|,
  which does not allow the redefinition of ops with different
  signatures.
  In general, if multiple methods and constructors from a class in the
  Java library need to be accessed in a |Metaslang| spec, it is a good
  idea to structure them using the ``qualifying`` feature of
  |Metaslang|. For instance::

     Vector qualifying spec 
           type Vector
           op new: () -> Vector
           op add: [a] Vector * a -> Vector
           op size: Vector -> Nat
     endspec
     Math qualifying spec
           op max: Integer * Integer -> Integer
           op min: Integer * Integer -> Integer
           ....
     endspec

  and then importing the specs into the application spec that uses it.
  Future versions of the Specware system will provide a utility to
  convert a given Java class into a spec following the above
  conventions.

Type Conversion between Java and |Metaslang|
============================================

The following table shows the conversion of Java types to |Metaslang|,
which can be used when accessing Java methods from |Metaslang|

.. list-table::
   :widths: 200 200
   :header-rows: 1

   *  - Java
      - |Metaslang|
   *  - \ ``int``\
      - \ ``Integer``\
   *  - \ ``boolean``\
      - \ ``Bool``\
   *  - \ ``char``\
      - \ ``Char``\
   *  - \ ``void``\
      - \ ``()``\
   *  - byte
        short
        float
        double
      - not implemented
   *  - Any Java class name
      - |Metaslang| type with the same name (type must be declared in
        the spec)

