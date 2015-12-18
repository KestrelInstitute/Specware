========================
Defining Transformations
========================


Transforming Expressions
########################


To add an expression transformation that can be invoked from the
transformation shell, add a new definition to the `MetaRules` spec
found in `Languages/MetaSlang/Transformations/MetaRules`::

    op testTransform (spc: Spec) (tm: MSTerm ) : Option MSTerm =
      let _ = writeLine "Pop quiz bub."
      in (Some tm)


The transformation `op` takes a spec `spc` which contains the term
`tm` that is to be transformed. The user will use the transformation
navigation commands (e.g. `at`, `move`, etc.) to focus a term, and
then apply the given transformation. The transformation metaprogram
interpreter will then apply the given transform to each subterm
(starting with and including the top-most term under focus) until the
`op` defining the transformation returns `Some t`, with the `MSTerm`
`t` being the new term [#nochange]_. This transformed term will be
substituted in the position of the input term in the focused term. In
the case that the transformation returns `None` for a given subterm,
the transformation script will continue to apply the transformation to
other subterms of the currently focused term.

.. [#nochange] If the transformation op returns `Some t`, but the
               returned term `t` is the same as the original `tm`,
               then the transformation script will issue a warning.

After rebuilding Specware, this transform can be invoked from the
transformation shell using the `apply` command::

    at someDef { testTransform }

Transforming Specifications
###########################

There are some example transformations defined in
`Languages/MetaSlang/Transformations/Simple.sw`. This section uses
those as examples for defining specification transformations.

Defining a new transformation is a relatively straightforward
process. Create a new specware spec, preferably in a file under
the `Languages/MetaSlang/Transformations/` directory::

    SimpleTransform = spec

Import supporting code as necessary. As the transformation be
manipulating MetaSlang ASTs, the specs imported below should be
useful::

    import ../Specs/AnnSpec
    import ../Specs/MSTerm
    import ../Specs/Position
    import ../Specs/QualifierMap
    import ../AbstractSyntax/QualifiedId

    import /Languages/SpecCalculus/Semantics/Evaluate/UnitId/Utilities
    import /Languages/SpecCalculus/AbstractSyntax/UnitId


Next, define an `op` that takes a `Spec` as input, and produces a
`Spec`. It is crucial that the `op` be qualified with the
`SpecTransform` qualifier. This qualifier is necessary to allow the
transformation to be identified when building Specware itself, which
will in turn allow the transformation to be used in a Specware
metaprogram using the unqualified name of the `op`. The following example
transformation simply does a shallow copy of the input specification::

    op SpecTransform.copySpec (spc : Spec) : Spec =
      {types=spc.types,
       ops=spc.ops,
       elements=spc.elements,
       qualifier=spc.qualifier}


If the transformation that you are defining is more sophisticated, and
needs typing or other contextual information, it may be useful to
define the transformation `op` within the `Env` [#Env]_ monad, which
provides access to `op` type and definition information from the
context in which the input specification is defined.


.. [#Env] Found in `/Languages/SpecCalculus/Semantics/Monad` and
          `/Languages/SpecCalculus/Semantics/Environment`.

::

   import /Languages/SpecCalculus/Semantics/Monad
   import /Languages/SpecCalculus/Semantics/Environment
   op SpecTransform.copySpecM (spc : Spec) : Env Spec =
      return {types=spc.types,
              ops=spc.ops,
              elements=spc.elements,
              qualifier=spc.qualifier}

Specification transformations can also be defined to take arguments
in addition to the spec to transform. To define such a transformation,
simply add the extra arguments to the transformation in curried form::

  op SpecTransform.exArgs(spc: Spec) (tm: MSTerm): Env Spec =
    let _ = writeLine "Using transform on: " ^ printTerm tm
    in return spc

  end-spec


Integrating Transformations
---------------------------

To integrate new transformations into specware, you must import the
module defining the transformation into the
`Languages/SpecCalculus/Semantics/Evaluate/Transform` spec. Open
that spec and add the following to the list of imports::

    import SimpleTransform

Then rebuild specware::

    $SPECWARE4> make

After the Specware build finishes, the new transform is available for
manipulating specs::

    S0 = spec
      op inc : Nat -> Nat
    end-spec

    S1 = transform S0 by { copySpec }

    S2 = transform S1 by { copySpecM }

    S3 = transform S2 by { exArgs 1 }
