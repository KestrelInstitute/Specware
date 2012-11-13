

==============================
Lisp Code Generated from Specs
==============================

The translation of executable specs to Lisp code is straightforward
for the most part as Lisp is a higher-order functional language.
Functional expressions go to lambda expressions and most |Specware|
types are implemented as Lisp lists and vectors apart from the
strings, numbers, characters and booleans which are implemented by the
corresponding Lisp datatypes. This guide is meant primarily to help
the user in calling and debugging the functions generated from a spec,
so we concentrate on the translation of op names to Lisp names and the
implementation of types. The implementation details of procedural
constructs such as pattern-matching are omitted. The interested user
is free to examine the Lisp code itself, which is simple but verbose
for pattern-matching constructs.

Translation of |Specware| Names to Lisp Names
#############################################

|Specware| ops are implemented using Lisp ``defun``\ s if they are
functions, ``defparameter``\ s otherwise. Their names are upper-cased
and put in the package with the same name as the qualifier, or ``SW-
USER`` if unqualified. However, if the name is that of a built-in Lisp
symbol, the name is prepended with the character "\ ``!``\ " and not
upper-cased. If the qualifier of the op is the same as a built-in Lisp
package then "\ ``-SPEC``\ " is appended to the spec name to get the
package name. For example, the Lisp code for the spec:

.. code-block:: specware

   Z qualifying spec
     def two: Nat = 2
     def add1(x:Nat): Nat = x + 1
   endspec
   

is

.. code-block:: common-lisp

   (DEFPACKAGE "Z")
   (IN-PACKAGE "Z")
   
   (DEFPARAMETER TWO 2)
   (DEFUN ADD1 (X) (INTEGER-SPEC::+-2 X 1))
   

Arity and Currying Normalization
################################

All |Specware| functions are unary. Multiple argument functions are
modeled using either functions with product domains, or curried
functions. For efficiency we wish to exploit Common Lisp's support of
n-ary functions. Arity normalization aims to minimize unpacking and
packing of products when passing arguments to functions with product
domains, and currying normalization aims to minimize closure creation
when calling curried functions. The saving is particularly important
for recursive functions where there is saving at each recursive call,
and in addition, currying normalization may permit the Common Lisp
compiler to do tail recursion optimization. The naming scheme does not
require knowledge of the definition of a function when generating
calls to the function.

For each function whose argument is a product, two entry points are
created: a unary function whose name is derived from the op as
described above, and an n-ary function whose name has "\ ``-``\
*n*"
appended. Fir example, for 

.. code-block:: specware

   op min : Integer * Integer -> Integer
   

there are two Lisp functions, ``#'MIN-2`` and ``#'|!min|``\ . A call
with an explicit product is translated to the n-ary version, otherwise
the unary version is used. For example, ``min(1,2)`` translates to
``(MIN-2 1 2)``\ , and ``foldr min inf l`` translates to
``(FOLDR-1-1-1 #'|!min| INF L)``\ . When generating Lisp for a
definition, the form is examined to see whether the definition is
naturally n-ary. If it is, then the primary definition is n-ary and
the unary function is defined in terms of the n-ary function,
otherwise the situation is reversed. For example, given the definition

.. code-block:: specware

   def min(x,y) = if x <= y then x else y
   

we get the two Common Lisp definitions:

.. code-block:: common-lisp

   (DEFUN MIN-2 (X Y) (if (<= x y) x y))
   (DEFIN |!min| (X) (MIN-2 (CAR X) (CDR X)))
   

and given the definition

.. code-block:: specware

   def multFG(x: Nat * Nat) = (F x) * (G x)
   

we get the two Common Lisp definitions:

.. code-block:: common-lisp

   (DEFUN MULTFG-2 (X Y) (MULTFG (CONS X Y)))
   (DEFUN MULTFG (X) (* (F X) (G X)))
   

For each curried function (i.e. for each function whose codomain is a
function) there is an additional uncurried version of the function
with "\ ``-1``\ " added
*n*  times to
the name where *n*  is the number of curried
arguments. For example, for

.. code-block:: specware

   op foldr: [key,a,b] (a * b -> b) -> b -> map(key,a) -> b
   

there are two Lisp functions, ``#'FOLDR`` and ``#'FOLDR-1-1-1``\ .

As with arity normalization, the definition of a curried function is
examined to see whether it should be used to generate the curried or
the uncurried version, with the other being defined in terms of this
primary version.

As well as producing more efficient code, the currying normalization
makes code easier to debug using the Common Lisp trace facility. For
example if a function has a call of the form ``foldr x y z``\ , this
call is implemented as ``(FOLDR-1-1-1 x y z)``\ , so you can trace
``FOLDR-1-1-1`` to find out how it is being called and what it is
returning.

Representation of Other Types
#############################

``Character`` and ``String`` types are represented as Lisp characters
and strings, ``Nat`` and ``Integer`` as Lisp integers, lists are
represented using Lisp lists, and ``Boolean`` \ ``true`` and ``false``
by the symbols ``T`` and ``NIL``\ .

Sums are represented as the cons of the constructor name in keyword
package and the fields of the constructor.

Binary products are implemented as cons cells (except for function
arguments which are described in the previous section): ``CONS`` to
construct and ``CAR`` and ``CDR`` to access the first and second
fields. Non-binary products are implemented as vectors: constructed
using ``VECTOR`` and the ith element accessed by ``(SVREF x i-1)``\ .

Records are implemented the same as products with the order of the
fields being alphabetic in the field names.

Restrictions and comprehensions are implemented using their supersort.

A quotient is represented as as a vector of three elements: the
quotient tag (which is the value of the Lisp variable ``SLANG-BUILT-IN
::QUOTIENT-TAG``\ ), the representation of the quotient relation, and
the actual value in the underlying type.

