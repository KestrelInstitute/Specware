\section{Qualified Ids}

This defines the sort \Sort{Id} and sets of such things. There is some
inconsistency here since, elsewhere, it is the user of the sets that
creates the instance.

This should be enriched with constructors and destructors (projections)
for getting qualifiers etc.

As elsewhere, there may be a win in renaming \Op{make} to \Op{makeId}.
Cast your vote. The references to sort \Op{String} should probably be
made abstract.

The qualifier \Qualifier{IdSet} is needed because \UnitId{Sets} imports
\UnitId{Elem} and both have show and pp operations. We want to overload
those operations and the only way to do so right now is to qualify
them apart.

In the end, the goal is to end up with as much as possible qualified
by \Qualifier{Id}.

\begin{spec}
let
  Set = translate (translate MonadicSets by {Elem.Elem +-> Id.Id}) by {
      Elem._ +-> Id._,
      MonadFold._ +-> IdSetEnv._,
      _ +-> IdSet._
    }

  Id = spec
    import Set 

    op makeId : String -> String -> Id
    op UnQualifiedId.makeId : String -> Id

    op IdEnv.makeId : String -> String -> Env Id
    op UnQualifiedIdEnv.makeId : String -> Env Id
    
    op pp : Id -> Doc
    op show : Id -> String
  endspec
in
  Id qualifying Id
\end{spec}
