

============
Introduction
============

Experimental nature
###################

The "|XShell|" is an experimental addition to the |Specware| system,
currently under active development. This manual records a snapshot,
and is probably already outdated as you read it.

No guarantees should be expected concerning the correct operation of
the |XShell|. Assurance, as can be provided by the "correct by
construction paradigm", depends on properly discharging the proof
obligations engendered by specs and refinements, which is independent
of the operation of the |XShell|.

Transformations
###############

|SpecwareV| has a new construct in its "spec calculus" fragment of
|Metaslang|, not yet documented in the language manual. To the
productions of ``spec_term``, add a new construct
:token:`spec_transformation`, with grammar rule:

.. productionlist::
  spec_transformation: transform `spec_term` by `transformation_list`
  transformation_list: "{" [ `transformation_step` 
                     :  { , `transformation_step` }* ] "}"

Transformations are refinements that transform specs by means of
rewriting techniques, possibly combining automated strategies with ad
hoc rewrite steps, based on higher-order pattern matching so as to
apply generic and domain-specific theorems and equational logic. The
|XShell| can be viewed as an interactive tool for constructing
:token:`transformation_lists` for :token:`spec_transformations`.

Interaction
###########

The |XShell| is started from within the |SShell|, and operates
likewise in a read-command -- perform-command -- report-back cycle.
The commands issued by the user correspond to
:token:`transformation_steps` as occuring in
:token:`transformation_lists`, but have a simplified syntax, reducing
the number of keystrokes required for entering them. At any time, the
|XShell| can be made to produce a :token:`transformation_list` in
proper |Metaslang| syntax that can be used as is in a ``.sw`` file.

Most |SShell| commands are also available from the |XShell| and can be
invoked directly without need to leave the |XShell|. The ``proc``
command for processing a unit is available, but has additional effects
as described in the next chapter. The abbreviation ``p`` for ``proc``
is not available; it has been shadowed by the abbreviation ``p`` for
the new |XShell| command ``move previous``.

A (very) simple example
#######################

The following example has been chosen for extreme simplicity, rather
than for being realistic or illustrating the potential of
transformations. Consider the following spec:

.. code-block:: specware

   spec
     theorem commutative_+ is
       fa (i: Integer, j : Integer) i + j = j + i
   
     theorem neutral_+_0 is
       fa (i: Integer) i + 0 = i
   
     op double : Integer -> Integer
     def double i = 0 + 2 * i
   endspec
   

The two theorems are proof obligations; under the assumption that they
have been or will be discharged, it is safe to apply them in
simplifying the definition of op ``double``. Assuming that the spec
goes by the name ``Example``, the user can enter the |XShell| by
issuing the (|SShell|) command

.. code-block:: specware

   * transform Example
   

The |XShell| responds with

.. code-block:: specware

   Entering Transformation Construction Shell
   **
   

Note the slightly different prompt: two asterisks instead of a single
one. We give the rest of the dialogue, followed by an explanation:

.. code-block:: specware

   ** at double
   (fn i -> 0 + 2 * i)
   ** lr commutative_+
   (fn i -> 2 * i + 0)
   ** lr neutral_+_0
   (fn i -> 2 * i)
   ** done
    {at double,
       lr commutative_+,
       lr neutral_+_0}
   * 
   

and the user is back in the |SShell|, as indicated by the prompt.

The ``at`` :token:`op-name` command puts the focus of the |XShell| on an
:token:`op_definition`; the effect of most transformations is limited
to the current focus. By way of feedback, the contents of the focus is
printed whenever there is a change. As can be seen by the fact that we
have a ``lambda_form``, the ``expression`` the |XShell| is
operating on may be different from the ``expressions`` recorded
in a :token:`spec_form`. The ``lr`` :token:`claim-name` command applies the
axiom or theorem, the essence of whose ``expression`` must be an
equality, as a left-to-right rewrite rule. At the ``done`` command,
the list of transformations is given in |Metaslang| syntax; the
elaboration of

.. code-block:: specware

   transform Example by
    {at double,
       lr commutative_+,
       lr neutral_+_0}
   

results in a spec that is identical to ``Example`` except that the
definition of op ``double`` is now

.. code-block:: specware

   def double i = 2 * i
   

