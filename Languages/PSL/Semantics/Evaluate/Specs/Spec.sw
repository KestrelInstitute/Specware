\section{Abstract Specs}

\begin{spec}
Spec qualifying spec
  import SortSets
  import OpSets
  import ClaimSets
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

Should we get make Op.OpInfo into Op?

Here \Qualifier{OpSetEnv} is the qualifier for the monadic fold. The fold
has a single polymorphic variable. The other type is monomorphic and
in this case it is \Type{OpInfo}.

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

So a concrete implementation would be a record will a collection of maps
and inserting an op may mean updating a bunch of maps.

So with ops would be inserting ops? Is the identity of the op, part of
the op?

How would we do a merge, for example?

So we are constructing the join of two specs? Is that in the api or is
that meant to be implemented in terms of the api?

What about updating the ops en-masse?

\begin{spec}
  op ops : Spec -> OpSet.Set
  % op withOps infixl 17 : Spec * OpSet.Set -> Spec

  op sorts : Spec -> SortSet.Set
  % op withSorts infixl 17 : Spec * SortSet.Set -> Spec

  op properties : Spec -> List Claim
\end{spec}

  op findOp : Spec -> Id.Id -> Option Op.OpInfo
  op findSort : Spec -> Id.Id -> Option Sort.SortInfo

\begin{spec}
  op SpecEnv.findOp : Spec -> Id.Id -> Env OpSet.Set
  op SpecEnv.findSort : Spec -> Id.Id -> Env SortSet.Set

  op SpecEnv.findTheOp : Spec -> Id.Id -> Env Op.OpInfo
%   def findTheOp spc id = {
%       opInfoSet <- findOp spc id;
%       case (size opInfoSet) of
%         | 0 -> fatalError ("findTheOp: id does not exist: " ^ (show id))
%         | 1 -> return (theSingleton opInfoSet)
%         | _ -> fatalError ("findTheOp id is ambiguous : " ^ (show id))
%     }

  op SpecEnv.findTheSort : Spec -> Id.Id -> Env Sort.SortInfo
%   def findTheSort spc id = {
%       sortInfoSet <- findSort spc id;
%       case (size sortInfoSet) of
%         | 0 -> fatalError ("findTheSort: id does not exist: " ^ (show id))
%         | 1 -> return (theSingleton sortInfoSet)
%         | _ -> fatalError ("findTheSort id is ambiguous : " ^ (show id))
%     }
\end{spec}

Later might need the following. Or they could return a TakeResult.

\begin{verbatim}
  op Op.findOp : Spec -> Id.Id -> Op.Set
  op Sort.findSort : Spec -> Id.Id -> Sort.Set
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
  op Op.isLocal? : Spec -> Op.OpInfo -> Boolean

  op Sort.local : Spec -> SortSet.Set
  op Sort.isLocal? : Spec -> Sort.SortInfo -> Boolean
\end{spec}

Perhaps there needs to be two fold operations. The most common fold
operations exclude the hidden names. Then there might be fold family that
includes the hidden names. The ops above, as they stand mey not be useful.

Controlling visibility of sorts and ops. Perhaps the predicates should
be monadic. The name \Op{hide} is a keyword so we munge it until it
becomes allowed as a op name.

\begin{spec}
  op Op.hyde : Spec -> Op.OpInfo -> Env Spec
  op Op.isHidden? : Spec -> Op.OpInfo -> Boolean

  op Sort.hyde : Spec -> Sort.SortInfo -> Env Spec
  op Sort.isHidden? : Spec -> Sort.SortInfo -> Boolean
\end{spec}

Typechecking.

\begin{spec}
  op elaborate : Spec -> Env Spec
\end{spec}

The empty specification.

\begin{spec}
  op empty : Spec
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
Either the names should be extended (eg \Op{insertOp}) or there may be
many instances when the user will have to provide type information. Maybe
the latter is the better way.

\begin{verbatim}
  op Spec.addOp : Spec -> Op.OpInfo -> Spec
  op Spec.addSort : Spec -> Sort.SortInfo -> Spec
  op Spec.addClaim : Spec -> Claim.Claim -> Spec
\end{verbatim}

There needs to be monadic versions of these to handle the case
where exceptions are raised.

\begin{spec}
  op SpecEnv.addOp : Spec -> Op.OpInfo -> Position -> Env Spec
  op SpecEnv.addSort : Spec -> Sort.SortInfo -> Position -> Env Spec
  op SpecEnv.addClaim : Spec -> Claim.Claim -> Position -> Env Spec
\end{spec}

The following functions fold an operation over the sorts or ops of
a spec.  These functions take their arguments in the order I prefer and
are curried. This is not essential (but certainly religious), but however
the arguments are passed, there should be uniformity with \Op{fold} in
\UnitId{Sets}.

\begin{spec}
  op Spec.foldOps : fa(a) (a -> Op.OpInfo -> a) -> a -> Spec -> a
  % def Spec.foldOps f unit spc = OpSet.fold f unit (ops spc)

  op Spec.foldSorts : fa(a) (a -> Sort.SortInfo -> a) -> a -> Spec -> a
  % def Spec.foldSorts f unit spc = fold f unit (sorts spc)
\end{spec}

The fold operations are applied to a spec rather than a set of operators
or sorts. So the definition above is better seen as a specification of the
fold operations rather than than as an ideal implementation. Depending
on the representation of specs, the expression \Term{(ops spc)} may
have to construct the a set and there may be no need to construct the
intermediate data structure.

The same points can be made about the next two.

\begin{spec}
  op SpecEnv.foldOps : fa(a) (a -> Op.OpInfo -> Env a) -> a -> Spec -> Env a
  % def SpecEnv.foldOps f unit spc = OpSetEnv.fold f unit (ops spc)

  op SpecEnv.foldSorts : fa(a) (a -> Sort.SortInfo -> Env a) -> a -> Spec -> Env a
  % def SpecEnv.foldSorts f unit spc = SortSetEnv.fold f unit (sorts spc)
\end{spec}

Map operations. These are are monomorphic and hence less general than
one might like as they map only from op to op or sort to sort.

\begin{verbatim}
  op SpecEnv.mapOps : (Op.OpInfo -> Env Op.OpInfo) -> Spec -> Env Spec
  def SpecEnv.mapOps f spc = OpSetEnv.map f (ops spc)

  op SpecEnv.mapSorts : (Sort.SortInfo -> Env Sort.SortInfo) -> Spec -> Env Spec
  def SpecEnv.mapSorts f spc = SortSetEnv.map f (sorts spc)
\end{verbatim}

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
  op pp : Spec -> Doc

  op show : Spec -> String
  def show spc = ppFormat (pp spc)
\end{spec}

\begin{spec}
  op subtract : Spec -> Spec -> Spec
  op union : Spec -> Spec -> Env Spec
\end{spec}

The next few operations are only monadic. It is likely that they
will need state to control there operation.

\begin{spec}
  op simplifyOp : Spec -> Op.Ref -> Env Spec
  op simplifySort : Spec -> Sort.Ref -> Env Spec
  op simplifyClaim : Spec -> Claim.Ref -> Env Spec
\end{spec}

What does it mean to simplify a sort? Perhaps there should be different
Id sorts for ops, sorts and axioms. Op.Id, Sort.Id etc.
Perhaps the above belong in the op, sort claim specs respectively.

The next operation is speculative. The assumption is that some or all terms
might be assigned an identifier (even if only visible internally).

\begin{spec}
  op simplifyTerm : Spec -> Id.Id -> Env Spec
\end{spec}

\begin{spec}
endspec
\end{spec}
