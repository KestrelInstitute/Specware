\section{Abstract Specs}

\begin{spec}
Spec qualifying spec
  import Sort
  import Op
  import Property
\end{spec}

Intuitively, a spec consists of a set of sorts, operators and axioms
(properties).

We import two copies of monomorphic sets. One for sets of ops and the
other for sets of sorts. We may choose to implement them differently.
Some of the operations on specs need to be monadic so they can raise
exceptions. Hence we import a locally extended version of \verb+Set+
with a monadic fold operation. Note that the monad operations other than
\verb+foldMonad+ are shared and uniformly qualified with \verb+Monad+.

The translate also instantiates the element type in each monomorphic instance of \verb+Sets+.

Should we get rid of the Op in OpInfo? Or should we get rid of the Info?

\begin{spec}
  import translate (Op qualifying MonadicSet) by {
      Elem.Elem +-> Op.OpInfo,
      Elem.pp +-> Op.pp,
      Op.mapMonad +-> OpMonad.map
      Op.foldMonad +-> OpMonad.fold
    }
  import translate (Sort qualifying MonadicSet) by {
      Elem.Elem +-> Sort.SortInfo,
      Elem.pp +-> Sort.pp,
      Sort.mapMonad +-> SortMonad.map
      Sort.foldMonad +-> SortMonad.fold
    }
\end{spec}

The following are temporary so the spec goes through.

\begin{spec}
  sort Position
\end{spec}

Define an abstract \verb+Spec+ sort. Later this will be refined to a concrete
record.

\begin{spec}
  sort Spec
\end{spec}

A key difference between what we have now is that the collection of ops
and sorts are now sets rather than maps. This is to deal with the aliasing
that we have now and the full-overloading to come later.

\begin{spec}
  op ops : Spec -> Op.Set
  op withOps infixl 17 : Spec -> Op.Set -> Spec

  op sorts : Spec -> Sort.Set
  op withSorts infixl 17 : Spec -> Sort.Set -> Spec

  op properties : Spec -> List Property
\end{spec}

\begin{spec}
  op Op.find : Spec -> QualifiedId -> Option OpInfo
  op Sort.find : Spec -> QualifiedId -> Option SortInfo
\end{spec}

Later might need the following. Or they could return a TakeResult.

\begin{verbatim}
  op Op.find : Spec -> QualifiedId -> Op.Set
  op Sort.find : Spec -> QualifiedId -> Sort.Set
\end{verbatim}

Note that the find operation takes a qualified id. In the current code
there are lookup operations where there are two keys (qualifier/id
pairs) and lookup operations that takes a single qualified id as a key. I
think this should be made uniform and I think the former should be
eliminated. Whenever possible, an identifier should be handled abstractly
as I believe some problems remain with the notion of qualified identifier
and that the notion may need extending.

There might be a need for monadic versions of the \verb+find+ operations.
Thus far this has not been the case.

It might be necessary to write \verb+find+ functions for other keys. Eg
\verb+findOpByType+.

Stephen added the ability to distinguish local names from those arising
from imports. This is useful for typechecking and seems like a great idea.

\begin{spec}
  op Op.local : Spec -> Op.Set
  op Op.isLocal? : Spec -> OpInfo -> Boolean

  op Sort.local : Spec -> Sort.Set
  op Sort.isLocal? : Spec -> SortInfo -> Boolean
\end{spec}

Controlling visibility of sorts and ops. Perhaps the predicates
should be monadic. The name \verb+hide+ is a keyword so
we munge it until it becomes allowed as a op name.

\begin{spec}
  op Op.hyde : Spec -> OpInfo -> Monad Spec
  op Op.isHidden? : Spec -> OpInfo -> Boolean

  op Sort.hyde : Spec -> SortInfo -> Monad Spec
  op Sort.isHidden? : Spec -> SortInfo -> Boolean
\end{spec}

Typechecking.

\begin{spec}
  op elaborate : Spec -> Monad Spec
\end{spec}

The following add a sort or op to a spec.  Adding an op or sort is
deliberately separated from constucting an op or sort value. Perhaps this
is wrong.  These replace the \verb+addOp+ and \verb+addSort+ operations
which take many arguments and construct the sort and operator info
and insert it into a spec. The non-monadic versions are probably
not very useful.

It might be necessary to have insertion functions that do not check
for errors. Perhaps that could be the behaviour of the non-monadic versions.

The the use of \verb+SpecOp+ as a qualifier in the following is to avoid
a clash with the insert operation in \verb+Sets+.

Disambiguating the names with qualifiers may not be sufficient.
Either the names should be extended (eg \verb+insertOp+) or
there may be many instances when the user will have to provide
type information. Maybe the latter is the better way.

\begin{spec}
  op SpecOp.insert : Spec -> OpInfo -> Spec
  op SpecSort.insert : Spec -> SortInfo -> Spec
  op SpecProperty.insert : Spec -> Property -> Spec
\end{spec}

There needs to be monadic versions of these to handle the case
where exceptions are raised.

\begin{spec}
  op SpecOpMonad.insert : Spec -> OpInfo -> Monad Spec
  op SpecSortMonad.insert : Spec -> SortInfo -> Monad Spec
  op SpecPropertyMonad.insert : Spec -> Property -> Monad Spec
\end{spec}

The following functions fold an operation over the sorts or ops of
a spec.  These functions take their arguments in the order I prefer and
are curried. This is not essential (but certainly religious), but however
the arguments are passed, there should be uniformity with \verb+fold+ in
\verb+Sets+.

Not clear that the overloading of \verb+fold+ in the following is
a good thing and we might be better with different names such as
\verb+foldOverOps+. But then again, one can just use the qualifier
or give the sorts. Needs thought.

\begin{spec}
  op SpecOp.fold : fa(a) (a -> OpInfo -> a) -> a -> Spec -> a
  def SpecOp.fold f unit spc = Op.fold f unit (ops spc)

  op SpecSort.fold : fa(a) (a -> SortInfo -> a) -> a -> Spec -> a
  def SpecSort.fold f unit spc = Sort.fold f unit (sorts spc)
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
  op OpSpecMonad.fold : fa(a) (a -> OpInfo -> Monad a) -> a -> Spec -> Monad a
  def OpSpecMonad.fold f unit spc = OpMonad.fold f unit (ops spc)

  op SortSpecMonad.fold : fa(a) (a -> SortInfo -> Monad a) -> a -> Spec -> Monad a
  def SortSpecMonad.fold f unit spc = SortMonad.fold f unit (sorts spc)
\end{spec}

Map operations.

\begin{spec}
  op OpSpecMonad.map : (OpInfo -> Monad OpInfo) -> Spec -> Monad Spec
  def OpSpecMonad.map f spc = OpMonad.map f (ops spc)

  op SortSpecMonad.map : (SortInfo -> Monad SortInfo) -> Spec -> Monad Spec
  def SortSpecMonad.map f spc = SortMonad.map f (sorts spc)
\end{spec}

\begin{spec}
endspec
\end{spec}
