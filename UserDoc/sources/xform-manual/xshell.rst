

============
The |XShell|
============

Entering and leaving the |XShell|
#################################

The |XShell| is entered from within the |SShell| by the command


.. parsed-literal:: 

   transform <spec>
   

The ``<spec>`` argument is optional; the zero-argument version means: use
the last argument of the kind "unit" last used for a |SShell| command.
It must, specifically, be a unit defining a spec.

The normal way to leave the |XShell| is the command

.. code-block:: specware

   done
   

which returns processing to the interactive |SShell| loop. Before
handing back control to the |SShell|, the |XShell| reports the
:token:`transformation_list` corresponding to the transformations
performed, or "\ ``No transformations``\ " if none were performed. The
command ``exit`` and its alias ``quit`` -- actually |SShell|
commands -- terminate the whole |Specware| session immediately,
without reporting any transformations performed.

Focus and navigation
####################

Most transformations are only applied to a restricted part of the
spec, called the (transformation) `focus`. The 
focusing command

.. code-block:: specware

   at <op>
   
puts the focus on the defining expression for an op.

It is possible to navigate by moving the focus around by issuing a
move command

.. code-block:: specware

   move <m1> <m2> <m3> ...
   

in which each navigation directive ``<m1>``, ``<m2>``, ..., is one of
``first``\ , ``last``\ , ``previous``\ , ``next``\ , ``widen``\ ,
``search <token>``, ``reverse-search <token>`` and ``all``. The keyword
``move`` is optional, and each navigation directive may be abbreviated
by its first letter; for example, the command ``p`` is equivalent to
``move previous``.

Assuming the focus has been set ``at x``, where op ``x`` is defined
by

.. code-block:: specware

   op x: Nat = (1 + 2) * (if 3 = 4 then 5 else 6)
   

the subsequent effect of these navigation commands is as follows:

.. code-block:: specware

   (1 + 2) * (if 3 = 4 then 5 else 6)
   ** first
   1 + 2
   ** last
   2
   ** previous
   1
   ** next
   2
   ** widen
   1 + 2
   ** search if
   if 3 = 4 then 5 else 6
   ** reverse-search +
   1 + 2
   ** all
   (1 + 2) * (if 3 = 4 then 5 else 6)
   

So ``first`` focuses on the first child of the
*current*  focus that is an ``expression``, ``last`` focuses on the last child,
``previous`` and ``next`` on the previous and next sibling, while ``widen``
widens the focus to the encompassing ``expression``.
The effect of ``search`` and ``reverse-search`` should be obvious.
Finally, ``all`` widens the focus to the original one.

Rewrite, unfold, fold
#####################

In the following two |XShell| commands, ``<claim>`` is the name of an
axiom or theorem occurring in the spec, including any imported specs,
whose ``expression`` is a possibly universally quantified
equation. For example, the ``expression`` can be

.. code-block:: specware

   [a] fa (x: List a) x ++ [] = x
   

In particular, all theorems in the Base library can be used.

The left-to-right rewrite command

.. code-block:: specware

   lr <claim>
   

applies the equation, viewed as a rewrite rule, in the left-to-right
direction. More precisely, the first subexpression of the focus is
found that matches the left-hand side of the equation. The
substitution that made the left-hand side match is applied to the
right-hand side of the equation,and the result replaces the matched
subexpression. The matching algorithm uses higher-order matching; for
example, ``1 + 1`` matches ``f(i, i)`` by the substitution

.. code-block:: specware

   (f, i) := (fn x -> x + x, 1)
   

The matching algorithm takes account of the types, which should also
match.

The right-to-left rewrite command

.. code-block:: specware

   rl <claim>
   

applies the equation as a rewrite rule in the right-to-left direction:
the first subexpression of the focus is found that matches the right-
hand side of the equation, which then is replaced by the left-hand
side after applying the matching substitution.

In the following two |XShell| commands, ``<op>`` is the name of an op that
has a definition in the spec, including any imported specs. The
definition can occur as an :token:`op_definition`, as in

.. code-block:: specware

   op [a] twice: (a -> a) -> a -> a
   def twice f x = f(f x)
   

or in the equivalent form of an :token:`op_declaration`:

.. code-block:: specware

   op [a] twice (f: a -> a) (x: a): a = f(f x)


The unfold command
==================

.. code-block:: specware

   unfold <op>
   

`unfolds` the first occurrence of :token:`op_name` ``<op>`` in the
focus, replacing it by the ``expression`` defining ``<op>``. So the
definition is used as if it were an axiom used by an ``lr``
rewrite command. For example, in the context of a definition for op
``twice`` as above, ``unfold twice`` applied to the focus 
``posNat?(twice pred n)`` results in ``posNat?(pred(pred n))``.

The fold command
================

.. code-block:: specware

   fold <op>
   

`folds` the first occurrence matching the defining expression for
<op>, replacing it by <op>.

Note. Folding may introduce circularity in definitions, and the result
may therefore be an ill-formed spec. Formally, this means that the
proof obligation cannot be discharged for the requirement that the
defining equation have a unique solution.

Simplification
##############

The simplify command

.. code-block:: specware

   simplify <r1> <r2> <r3> ...
   

applies a rewriting simplifier with the supplied rules ``<r1>``
``<r2>`` ``<r3>`` `` ...``\ , which must be given in the form of rewrite
commands or (un)fold commands.

For example, instead of giving a sequence of rewrite commands

.. code-block:: specware

   lr commutative_+
   lr neutral_+_0
   lr commutative_+
   lr neutral_+_0
   lr neutral_+_0


a user can issue a single simplify command

.. code-block:: specware

   simplify lr commutative_+ lr neutral_+_0
   

If any of the rules is found to apply, the simplify command will try
to reapply all rules on the whole resulting new contents of the focus,
as well as its repertoire of some standard simplification rules.

The simplify-standard command
=============================

.. code-block:: specware

   simp-standard
   

applies a standard simplifier, without additional rules. The keyword
``simp-standard`` may be abbreviated to ``ss``\ .

The partial-evaluation command
==============================

.. code-block:: specware

   partial-eval
   

evaluates the closed subexpressions of the focus -- that is,
expressions not containing unbound variables. 
The keyword ``partial-eval`` may be abbreviated to ``pe``.

The abstract-common-subexpressions command
==========================================

.. code-block:: specware

   abstract-cse
   

abstracts common (repeated) subexpressions in the focus expression. For
example, applying it to

.. code-block:: specware

   ("object " ++ obj, "object " ++ obj ++ newline))
   

results in

.. code-block:: specware

   let cse1 = "object " ++ obj in 
   (cse1, cse1 ++ newline)
   

The keyword ``abstract-cse`` may be abbreviated to ``cse``.

Miscellaneous
#############

The undo command

.. code-block:: specware

   undo <n>
   

undoes the last ``<n>`` commands performed by the |XShell| The ``<n>``
parameter is optional, with default 1.

The print-current-focus command

.. code-block:: specware

   pc
   

print the current focus expression.

In the course of interactively applying transformations using the
|XShell|, a user may need to modify the spec being processed in order
to proceed, for example by adding a theorem needed for rewriting. The
process command

.. code-block:: specware

   proc <unit-term>
   

elaborates the ``<unit-term>`` as possibly modified by the user, and
restarts the |XShell| on the processed spec, re-applying any earlier
effectful transformation commands. The ``<unit-term>`` is optional; the
zero-argument version means: use the same spec as before.

The trace-rewrites command

.. code-block:: specware

   trace-rewrites

starts a print trace for individual rewrites. The keyword
``trace-rewrites`` may be abbreviated to ``trr``.

The untrace-rewrites command

.. code-block:: specware

   untrace-rewrites
   

turns off printing a trace for individual rewrites. The keyword
``untrace-rewrites`` may be abbreviated to ``untrr``.

