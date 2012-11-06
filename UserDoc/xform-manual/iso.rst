

==========================
Isomorphic type refinement
==========================

The following transformation is not available through the |XShell| but
only through the "spec calculus" of |Metaslang|. One of the
alternatives for a :token:`transformation_step` is an
:token:`isomorphic_type_refinement`, which takes the form

.. code-block:: specware

   isomorphism(<f>, <g>)
   

It operates on a whole spec. The parameters ``<f>`` and ``<g>`` must be ops
that constitute the witnesses of an isomorphism between two types, say
``T`` and ``T'``, so that

.. code-block:: specware

   <f> : T  -> T'
   

and

.. code-block:: specware

   <g> : T' -> T
   

are each other's inverse (and therefore bijections). The effect is
that for each :token:`op_declaration` and :token:`op_definition` in
the spec for an op having some type ``F(T)`` involving ``T``, a modified
copy is added for an op having type ``F(T')``.

