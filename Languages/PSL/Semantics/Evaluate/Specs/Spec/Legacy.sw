\section{Refinement of abstract specs to legacy structures}

\begin{spec}
Spec qualifying spec
  import ../Spec
  import ../Id/Legacy
  import ../Sort/Legacy
  import ../Op/Legacy
  import ../Claim/Legacy
  import ../MetaSlang/Legacy
  % import ../Env
  import /Languages/SpecCalculus/Semantics/Evaluate/Spec/Utilities
  import /Languages/MetaSlang/Specs/AnnSpec
  import /Languages/MetaSlang/Specs/SimplePrinter
  import /Languages/MetaSlang/Specs/Elaborate/TypeChecker
  import /Languages/SpecCalculus/Semantics/Evaluate/Spec/SpecUnion
\end{spec}

\begin{spec}
  sort Spec.Spec = AnnSpec.ASpec Position
\end{spec}

\begin{spec}
  % op SpecEnv.findOp : Spec -> Id -> Env OpSet.Set
  % op SpecEnv.findSort : Spec -> Id -> Env SortSet.Set
  def SpecEnv.findTheOp spc id =
    case AnnSpec.findTheOp (spc,id) of
      | None -> specError ("findTheOp: id " ^ (Id.show id) ^ " is not defined")
      | Some opInfo -> return opInfo

  def SpecEnv.findTheSort spc id =
    case AnnSpec.findTheSort (spc,id) of
      | None -> specError ("findTheSort: id " ^ (Id.show id) ^ " is not defined")
      | Some sortInfo -> return sortInfo
\end{spec}

\begin{spec}
  % op Op.local : Spec -> OpSet.Set
  % op Op.isLocal? : Spec -> OpInfo -> Boolean

  % op Sort.local : Spec -> SortSet.Set
  % op Sort.isLocal? : Spec -> SortInfo -> Boolean
\end{spec}

\begin{spec}
  % op Spec.elaborate : Spec -> Env Spec
  def Spec.elaborate spc =
    case elaboratePosSpec (spc, "internal") of
      | Spec elabSpc -> return elabSpc
      | Errors errors -> raise (TypeCheckErrors errors)
\end{spec}

The empty specification.

\begin{spec}
  % op empty : Spec
  def Spec.empty = AnnSpec.emptySpec
\end{spec}

There needs to be monadic versions of these to handle the case
where exceptions are raised.

\begin{spec}
  % op SpecEnv.addOp : Spec -> OpInfo -> Env Spec
  % def SpecEnv.addOp spc opInfo position =
  % SpecCalc.addOp [idOf opInfo] (fixity opInfo) (type opInfo) [term opInfo] spc position
  def SpecEnv.addOp spc info position =
    SpecCalc.addOp info.names info.fixity info.dfn spc position

  % op SpecEnv.addSort : Spec -> SortInfo -> Position -> Env Spec
  % def SpecEnv.addSort spc sortInfo position =
  %   SpecCalc.addSort [idOf sortInfo] [] [type sortInfo] spc position
  def SpecEnv.addSort spc info position =
    SpecCalc.addSort info.names info.dfn spc position

  % op SpecEnv.addClaim : Spec -> Claim -> Position -> Env Spec
  def SpecEnv.addClaim spc claim position = return (AnnSpec.addProperty (claim,spc))
\end{spec}

\begin{spec}
  % op Spec.foldOps : fa(a) (a -> OpInfo -> a) -> a -> Spec -> a
  def Spec.foldOps f unit spc = foldriAQualifierMap (fn (qual,id,opInfo,x) -> f x opInfo) unit spc.ops

  % op Spec.foldSorts : fa(a) (a -> SortInfo -> a) -> a -> Spec -> a
  def Spec.foldSorts f unit spc = foldriAQualifierMap (fn (qual,id,sortInfo,x) -> f x sortInfo) unit spc.sorts
\end{spec}

\begin{spec}
  % op SpecEnv.foldOps : fa(a) (a -> OpInfo -> Env a) -> a -> Spec -> Env a
  def SpecEnv.foldOps f unit spc = foldOverQualifierMap (fn (qual,id,opInfo,x) -> f x opInfo) unit spc.ops

  % op SpecEnv.foldSorts : fa(a) (a -> SortInfo -> Env a) -> a -> Spec -> Env a
\end{spec}

Map operations. These are are monomorphic and hence less general than
one might like as they map only from op to op or sort to sort.

\begin{verbatim}
  op SpecEnv.mapOps : (OpInfo -> Env OpInfo) -> Spec -> Env Spec
  def SpecEnv.mapOps f spc = OpSetEnv.map f (ops spc)

  op SpecEnv.mapSorts : (SortInfo -> Env SortInfo) -> Spec -> Env Spec
  def SpecEnv.mapSorts f spc = SortSetEnv.map f (sorts spc)
\end{verbatim}

\begin{spec}
  % op pp : Spec -> Doc
  def Spec.pp spc = ppASpec spc
  def Spec.subtract = subtractSpec
  def Spec.union s1 s2 = SpecUnion.specUnion [s1,s2]

  def OpEnv.deref (spc,ref) = SpecEnv.findTheOp spc ref

  def Op.deref (spc,ref) =
    case AnnSpec.findTheOp (spc,ref) of
      | None -> fail ("findTheOp: id " ^ (Id.show ref) ^ " is not defined")
      | Some opInfo -> opInfo
\end{spec}

\begin{spec}
endspec
\end{spec}
