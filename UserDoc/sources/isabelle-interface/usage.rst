

=====
Usage
=====

Starting Up
###########

|Specware| and |Isabelle| can both be started up normally, each
running under their own XEmacs job, but it convenient to run them
under the same XEmacs. To do this run ``Isabelle_Specware``.

Currently Isabelle does not run under Windows except with cygwin so
this script is not available there. However, the translator can run
from |Specware| even if |Isabelle| is not running.

Using The Translator
####################

The translator is called using the emacs command ``Generate Isabelle
Obligation Theory`` from the |Specware| menu (with keyboard shortcuts
``c-c c-i`` or ``c-c TAB``). The translation is written to a file in
the ``Isa`` sub-directory of the current directory and the file is
visited in a buffer. The user may then process the |Isabelle| theory
providing proof steps as necessary. These proofs may then be copied
back to the |Specware| spec so that the next time it is translated,
the translation will include the proofs.

The translator may also be called using the |Specware| Shell command
``gen-obligations`` (or the abbreviation ``gen-obligs``) applied to
a unit id.

Proof Scripts in Specs
######################

An embedded |Isabelle| proof script in a |Specware| spec consists of
an introductory line beginning with ``proof Isa``, the actual
|Isabelle| script on subsequent lines terminated by the string
``end-proof``. For example, the simple proof script ``apply(auto)``
can be embedded as follows:

.. code-block:: specware

   proof Isa
     apply(auto)
   end-proof
   

If the last command before end-proof is not ``done``, ``sorry``,
``qed``, or ``by``, the command ``done`` is inserted.

The proof script should occur immediately after the theorem or
definition that it applies to. If the script applies to a proof
obligation that is not explicit in the spec, then the name of the
obligation should appear after ``proof Isa``, on the same line.
There are rare cases where an obligation is inserted between a
definition and an immediately following proof script, which causes the
proof script to be ignored. If this happens, then the name of the op
should be explicitly given.

If the user does not supply a proof script for a theorem, then the
translator will supply the script ``by auto`` which may be all that is
required to prove simple theorems.

Annotations for theorems may be included on the ``proof Isa`` line.
For example,

.. code-block:: specware

   theorem Simplify_valif_normif is
     fa(b,env,t,e) valif (normif b t e) env = valif (IF(b, t, e)) env
     proof Isa [simp]
       apply(induct_tac b)
       apply(auto)
     end-proof
   

translates to

.. code-block:: specware

   theorem Simplify_valif_normif [simp]: 
     "valif (normif b t e) env = valif (IF b t e) env"
       apply(induct_tac b)
       apply(auto)
     done
   

In this example we see that universal quantification in |Specware|
becomes, by default, implicit quantification in |Isabelle|. This is
normally what the user wants, but not always. The user may specify the
variables that should be explicitly quantified by adding a clause like
``fa t e.`` to the ``proof Isa`` line. For example,

.. code-block:: specware

   theorem Simplify_valif_normif is
     fa(b,env,t,e) valif (normif b t e) env = valif (IF(b, t, e)) env
     proof Isa [simp] fa t e.
       apply(induct_tac b)
       apply(auto)
     end-proof
   

translates to

.. code-block:: specware

   theorem Simplify_valif_normif [simp]: 
     "\<forall> t e. valif (normif b t e) env = valif (IF b t e) env"
       apply(induct_tac b)
       apply(auto)
     done
   

The ``\<forall>`` will be displayed as a universal quantification
symbol using X-Symbol mode in |Isabelle|. Note that instead of
``fa`` in the ``proof Isa`` line the user may use the X-Symbol for
universal quantification.

Recursive functions that are translated to ``recdefs`` can have a
measure function specified on the ``proof Isa`` line, by including it
between double-quotes. For example:

.. code-block:: specware

   proof Isa "measure (\<lambda>(wrd,sym). length wrd)" end-proof
   

Translation Tables
##################

A translation table for |Specware| types and ops is introduced by a
line beginning ``proof Isa Thy_Morphism`` followed optionally by an
|Isabelle| theory (which will be imported into the translated spec),
and terminated by the string ``end-proof``. Each line gives the
translation of a type or op. For example, for the |Specware| Integer
theory we have:

.. code-block:: specware

   proof Isa Thy_Morphism Presburger
     type Integer.Int -> int
     type Integer.Integer -> int
     type Nat.Nat     -> nat (int,nat) [+,*,div,rem,mod,<=,<,>=,>,abs,min,max]
     Integer.zero     -> 0
     Integer.one      -> 1
     Integer.ipred    -> pred
     Integer.isucc    -> succ
     IntegerAux.-     -> -
     Integer.+        -> +     Left 65
     Integer.-        -> -     Left 65
     Integer.*        -> *     Left 70
     Integer.<=       -> \<le> Left 50
     Integer.<        -> <     Left 50
     Integer.>=       -> \<ge> Left 50
     Integer.>        -> >     Left 50
     Integer.sign     -> sign
     Integer./        -> div   Left 70
     Integer.div      -> div   Left 70
     Integer.mod      -> mod   Left 70
     Integer.min      -> min           curried
     Integer.max      -> max           curried
   end-proof
   

A type translation begins with the word ``type`` followed by the
fully-qualified |Specware| name, ``->``, and the |Isabelle| name. If
the |Specware| type is a sub-type, you can specify coercion functions
to and from the super-type in parentheses separated by commas. Note
that by default, sub-types are represented by their super-type, so you
would only specify a translation if you wanted them to be different,
in which case coercion functions are necessary. Following the
coercion functions can appear a list of overloaded functions within
square brackets. These are used to minimize coercions back and forth
between the two types.

An op translation begins with the fully-qualified |Specware| name,
followed by ``->`` and the |Isabelle| constant name. If the Isabelle
constant is an infix operator, then it should be followed by ``Left``
or ``Right`` depending on whether it is left or right associative and
a precedence number. Note that the precedence number is relative to
|Isabelle|'s precedence ranking, not |Specware|'s. Also, an uncurried
|Specware| op can be mapped to a curried |Isabelle| constant by
putting ``curried`` after the |Isabelle| name, and a binary op can be
mapped with the arguments reversed by appending ``reversed`` to the
line.

