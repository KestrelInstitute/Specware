\section{Abstract Specs}

\begin{spec}
Spec qualifying spec
  import Sort
  import Op
  import Property
\end{spec}

Intuitively, a spec consists of a set of sorts, operators and axioms
(properties).

We want a true abstract data-type in the sense that
we should not be able to build a spec by explicitly constructing
a record. The sort might be isomorphic to a product,
but we should never be obliged to represent it as a particular
product.

If we update the ops, the update function may perform much
more than change a record.

Should the user see the references?

We import two copies of monomorphic sets. One for sets of ops and the
other for sets of sorts. We may choose to implement them differently.
Some of the operations on specs need to be monadic so they can raise
exceptions. Hence we import a locally extended version of \Spec{Set}
with a monadic fold operation. Note that the monad operations other than
the \Op{fold}s are shared and uniformly requalified with \Qualifier{Env}.

The translate also instantiates the element type in each monomorphic instance of \UnitId{Sets}.

Should we get rid of the Op in OpInfo? Or should we get rid of the Info?

\begin{spec}
  import translate (translate MonadicSets by {Elem.Elem +-> Op.OpInfo}) by {
      Elem._ +-> Op._,
      MonadFold._ +-> OpSetEnv._,
      _ +-> OpSet._
    }

  import translate (translate MonadicSets by {Elem.Elem +-> Sort.SortInfo}) by {
      Elem._ +-> Sort._,
      MonadFold._ +-> SortSetEnv._,
      _ +-> SortSet._
    }
\end{spec}

Define an abstract \Sort{Spec} sort. Later this will be refined to a concrete
record.

\begin{spec}
  sort Spec
\end{spec}

A key difference between what we have now is that the collection of ops
and sorts are now sets rather than maps. This is to deal with the aliasing
that we have now and the full-overloading to come later.

When will I want to look at the ops in isolation? Do they may sense outside
the scope of a spec? But if I have a spec 's' and I project the ops,
then I know the context!

Who is using this API? 

So a concrete implementation would be a record will a collection of maps
and inserting an op may mean updating a bunch of records.

So with ops would be inserting ops? Is the identity of the op, part of
the op?

How would we do a merge, for example?

So we are constructing the join of two specs? Is that in the api or is
that mean to be implemented in terms of the api?

fold over the sorts in one


:w


What about updating the ops en-masse?

\begin{spec}
  op ops : Spec -> OpSet.Set
  op withOps infixl 17 : Spec -> OpSet.Set -> Spec

  op sorts : Spec -> SortSet.Set
  op withSorts infixl 17 : Spec -> SortSet.Set -> Spec

  op properties : Spec -> List Property
\end{spec}

\begin{spec}
  op Op.find : Spec -> Id -> Option OpInfo
  op Sort.find : Spec -> Id -> Option SortInfo
\end{spec}

Later might need the following. Or they could return a TakeResult.

\begin{verbatim}
  op Op.find : Spec -> Id -> Op.Set
  op Sort.find : Spec -> Id -> Sort.Set
\end{verbatim}

Note that the find operation takes a qualified id. In the current code
there are lookup operations where there are two keys (qualifier/id
pairs) and lookup operations that takes a single qualified id as a key. I
think this should be made uniform and I think the former should be
eliminated. Whenever possible, an identifier should be handled abstractly
as I believe some problems remain with the notion of qualified identifier
and that the notion may need extending.

There might be a need for monadic versions of the \Op{find} operations.
Thus far this has not been the case.

It might be necessary to write \Op{find} functions for other keys. Eg
\Op{findOpByType}.

Stephen added the ability to distinguish local names from those arising
from imports. This is useful for typechecking and seems like a great idea.

\begin{spec}
  op Op.local : Spec -> OpSet.Set
  op Op.isLocal? : Spec -> OpInfo -> Boolean

  op Sort.local : Spec -> SortSet.Set
  op Sort.isLocal? : Spec -> SortInfo -> Boolean
\end{spec}

Perhaps there needs to be two fold operations. The most common fold
operations exclude the hidden names. Then there might be fold family that
includes the hidden names. The ops above, as they stand mey not be useful.

Controlling visibility of sorts and ops. Perhaps the predicates should
be monadic. The name \Op{hide} is a keyword so we munge it until it
becomes allowed as a op name.

\begin{spec}
  op Op.hyde : Spec -> OpInfo -> Env Spec
  op Op.isHidden? : Spec -> OpInfo -> Boolean

  op Sort.hyde : Spec -> SortInfo -> Env Spec
  op Sort.isHidden? : Spec -> SortInfo -> Boolean
\end{spec}

Typechecking.

\begin{spec}
  op elaborate : Spec -> Env Spec
\end{spec}

The following add a sort or op to a spec.  Adding an op or sort is
deliberately separated from constucting an op or sort value. Perhaps this
is wrong.  These replace the \Op{addOp} and \Op{addSort} operations
which take many arguments and construct the sort and operator info
and insert it into a spec. The non-monadic versions are probably
not very useful.

It might be necessary to have insertion functions that do not check
for errors. Perhaps that could be the behaviour of the non-monadic versions.

The the use of \Qualifier{OpSpec} as a qualifier in the following is to avoid
a clash with the insert operation in \UnitId{Sets}.

Disambiguating the names with qualifiers may not be sufficient.
Either the names should be extended (eg \Op{insertOp}) or
there may be many instances when the user will have to provide
type information. Maybe the latter is the better way.

\begin{spec}
  op OpSpec.insert : Spec -> OpInfo -> Spec
  op SortSpec.insert : Spec -> SortInfo -> Spec
  op SpecProperty.insert : Spec -> Property -> Spec
\end{spec}

There needs to be monadic versions of these to handle the case
where exceptions are raised.

\begin{spec}
  op OpSpecEnv.insert : Spec -> OpInfo -> Env Spec
  op SortSpecEnv.insert : Spec -> SortInfo -> Env Spec
  op SpecPropertyEnv.insert : Spec -> Property -> Env Spec
\end{spec}

The following functions fold an operation over the sorts or ops of
a spec.  These functions take their arguments in the order I prefer and
are curried. This is not essential (but certainly religious), but however
the arguments are passed, there should be uniformity with \Op{fold} in
\UnitId{Sets}.

Not clear that the overloading of \Op{fold} in the following is
a good thing and we might be better with different names such as
\Op{foldOverOps}. But then again, one can just use the qualifier
or give the sorts. Needs thought.

\begin{spec}
  op OpSpec.fold : fa(a) (a -> OpInfo -> a) -> a -> Spec -> a
  def OpSpec.fold f unit spc = OpSet.fold f unit (ops spc)

  op SortSpec.fold : fa(a) (a -> SortInfo -> a) -> a -> Spec -> a
  def SortSpec.fold f unit spc = fold f unit (sorts spc)
\end{spec}

I suspect it might be better if the the fold operations are applied to
a spec rather than a set of operators or sorts. So the implementation
above is probably a bad idea. Think of them as characterizations of
the respective fold operations rather than ideal implementations.
By applying the fold operations to the specs, we may be able to avoid
building intermediate data structures. In particular, the concrete
representation for specs might not use sets at all.

The same points can be made about the next two.

\begin{spec}
  op OpSpecEnv.fold : fa(a) (a -> OpInfo -> Env a) -> a -> Spec -> Env a
  def OpSpecEnv.fold f unit spc = OpSetEnv.fold f unit (ops spc)

  op SortSpecEnv.fold : fa(a) (a -> SortInfo -> Env a) -> a -> Spec -> Env a
  def SortSpecEnv.fold f unit spc = SortSetEnv.fold f unit (sorts spc)
\end{spec}

Map operations. These are problematic as that may only from op
to op or sort to sort.

\begin{verbatim}
  op OpSpecEnv.map : (OpInfo -> Env OpInfo) -> Spec -> Env Spec
  def OpSpecEnv.map f spc = OpSetEnv.map f (ops spc)

  op SortSpecEnv.map : (SortInfo -> Env SortInfo) -> Spec -> Env Spec
  def SortSpecEnv.map f spc = SortSetEnv.map f (sorts spc)
\end{verbatim}

\section{Operator and Sort References}

In the concrete syntax, when one wishes to refer to an operator or sort
one uses its name. The question is: what should these names become during
elaboration (type checking).

One option is that the name should be elaborated to an \Sort{OpInfo}. In
other words, operator names in a MetaSlang term become \Sort{OpInfo}'s
when the spec containing that term is elaborated. The problem is
that the information associated with an op may change. For instance,
the operator may get refined. If the \Sort{OpInfo}'s appear in terms,
then when an op changes, we must traverse the terms that refer to that
op and change all the \Sort{OpInfo}s.

The bigger problem is that we are limited to constructing only well-founded
ops and terms in the sense that we cannot construct an op $f$ with a term that
refers to an op $g$ where the definition of $g$ refers to $f$.

An alternative is to introduce a level of indirection and give each
\Sort{OpInfo} a unique identifier. When a term is elaborated, a
reference to an op by name is replaced by that identifier. Changes to
the \Sort{OpInfo} may not require changes to the terms.

The latter is what happens now. The unique identifier is the 
name of the operator but fully qualified. However, the former
approach is also useful (and faster) in some contexts.

To avoid committing one way or the other, we define the sorts \Sort{Op.Ref}, for
operator references, and \Sort{Sort.Ref}, for sort references.

Each \Sort{Op.Ref} is in one-to-one correspondence with an instances
of \Sort{OpInfo}. We then provide a pair of functions that witness the
correspondence. One dereferences an \Sort{OpRef} to an \Sort{OpInfo}. The
other maps an \Sort{OpInfo} to its \verb{OpRef}.

These sorts and functions can then be refined in the following ways.

To obtain something like the current implementation, \Sort{Op.Ref} becomes a
\Sort{QualifiedId}. deref becomes a call to \Op{find} (defined above) and the name
of an operator can be any of the names in the current \Sort{OpInfo} structure.
(This might not give the identity .. but no matter.)

Downstream, to accommodate full overloading, we might refine \Sort{Op.Ref}
to something other than \Sort{QualifiedId}, say \Sort{Nat}, Then dereferencing
might become an array or hash table lookup.

Finally, \Sort{Op.Ref} may refine to \Sort{OpInfo} in which case the two
witness functions become essentially the identity.

Need to provide a substitution operator on terms. Op substitution becomes
the identity in the case that we have indirection.

\begin{spec}
  sort Op.Ref
  sort Sort.Ref

  op Op.deref : Spec -> Op.Ref -> OpInfo
  op Sort.deref : Spec -> Sort.Ref -> SortInfo
\end{spec}

\begin{spec}
  op Op.refOf : OpInfo -> Op.Ref
  op Sort.refOf : SortInfo -> Sort.Ref
\end{spec}

The we need to decide if it is more convenient for the \Op{find}
operations to return a reference or information associated with an op
or sort.

Why not handle variables and let bound names in the same way?

How do we insert a new operator? Do we create the id when we create
the op information then check to see if the operator can be inserted?
Or do we check first?  The former seems to make more sense if we aim
to have ops introduced by an import to be the same as ops introduced in
the body of the spec.

Should the creation of an op be independent of the spec. That is, should we
be obliged to pass the spec as an argument when we make an operator?
I would prefer to keep things separate .. but perhaps it makes sense.
Perhaps there should be two make steps.

How do we create a new reference? If we wish to refine this
to code where \Sort{OpRef} is \Sort{QualifiedId} then
we need to pass an argument to any \Op{newRef} operator.

\begin{spec}
endspec
\end{spec}
