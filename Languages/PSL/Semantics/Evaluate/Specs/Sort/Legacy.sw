\section{Refinement of spec defining MetaSlang sorts}

\begin{spec}
Sort qualifying spec
  import ../Sort
  import ../Id/Legacy
  import ../MetaSlang/Legacy
  import /Languages/MetaSlang/Specs/AnnSpec
  import /Languages/MetaSlang/Specs/SimplePrinter
  import ../Spec

  sort Sort.SortInfo = AnnSpec.ASortInfo Position

  % op Sort.idOf : SortInfo -> Id
  def Sort.idOf info =
    case info.names of
      | [] -> fail "Sort.idOf: sort with empty list of ids"
      | [name] -> name
      | _::_ -> fail "Sort.idOf: sort with more than one id"

  % op ids : SortInfo -> IdSet.Set

  % op Sort.sortinfo_type : SortInfo -> Type
  def Sort.sortinfo_type info =
    case info.dfn of
      | [] -> fail "Sort.sortinfo_type: sort with empty list of sort schemes"
      | [si_type] -> si_type
      | _::_ -> fail "Sort.sortinfo_type: sort with more than one sort scheme"

  % op withId infixl 18 : SortInfo * Id -> SortInfo
  % op withIds infixl 18 : SortInfo * IdSet.Set -> SortInfo
  % op withType infixl 18 : SortInfo * Type -> SortInfo

  % op makeSort : Id -> Type -> SortInfo
  def Sort.makeSort id (si_type as (tvs, _)) = 
    {names = [id],
     tvs   = tvs,
     dfn   = [si_type]}

  def SortNoType.makeSort id = 
    {names = [id], 
     tvs   = [], 
     dfn   = []}

  % op join : SortInfo -> SortInfo -> Env SortInfo

  % op pp : SortInfo -> Doc
  def Sort.pp = ppASortInfo

  % op show : SortInfo -> String
  def Sort.show sortInfo = ppFormat (pp sortInfo)

  sort Sort.Ref = Id.Id

  % op SortRef.pp : Sort.Ref -> Doc
  def SortRef.pp = Id.pp

  % op deref : Spec -> Ref -> Env SortInfo
  def SortEnv.deref spc ref = findTheSort spc ref
    
  % op refOf : SortInfo -> Ref
  def Sort.refOf sortInfo = idOf sortInfo

  % op refOf : SortInfo -> Env Ref
  def SortEnv.refOf sortInfo = return (idOf sortInfo)
endspec
\end{spec}

Above we introduce \Sort{Type} where there was \Sort{SortScheme}
before. The idea is that in the near term, we can refine \Sort{Type}
in that way, and then later add polymorphism to the available types.

That being the case, we don't need an explicit set \verb{TypeVars}. 
as found in the current \verb{SortInfo}.

There is an argument for restoring a list of type variables
and making them parameters to the type and obliging a user
to declare when a type is polymorphic.

So for example,
\begin{verbatim}
  sort List Elem
\end{verbatim}
would not be valid unless \Sort{Elem} had previously
been declared as a sort. This might address something
that Alessandro had been requesting.

The \Op{with} operators are meant as a temporary measure until syntax
for updating formal products and maps is introduced. In the case of
records, such an update is straightforward. For abstract sorts it seems
trickier to me.
