\section{Refinement of abstract specs to legacy structures}

\begin{spec}
Spec qualifying spec
  import ../Spec
  import ../Id/Legacy
  import ../Type/Legacy
  import ../Op/Legacy
  import ../Claim/Legacy
  import ../MetaSlang/Legacy
  % import ../Env
  import /Languages/SpecCalculus/Semantics/Evaluate/Spec/AddSpecElements
  import /Languages/MetaSlang/Specs/AnnSpec
  import /Languages/MetaSlang/Specs/SimplePrinter
  import /Languages/MetaSlang/Specs/Elaborate/TypeChecker
  import /Languages/SpecCalculus/Semantics/Evaluate/SpecUnion
\end{spec}

\begin{spec}
  type Spec.Spec = AnnSpec.ASpec Position
\end{spec}

\begin{spec}
  % op SpecEnv.findOp : Spec -> Id -> Env OpSet.Set
  % op SpecEnv.findType : Spec -> Id -> Env TypeSet.Set
  def SpecEnv.findTheOp spc id =
    case AnnSpec.findTheOp (spc,id) of
      | None -> specError ("findTheOp: id " ^ (Id.show id) ^ " is not defined")
      | Some opInfo -> return opInfo

  def SpecEnv.findTheType spc id =
    case AnnSpec.findTheType (spc,id) of
      | None -> specError ("findTheType: id " ^ (Id.show id) ^ " is not defined")
      | Some typeInfo -> return typeInfo
\end{spec}

\begin{spec}
  % op Op.local : Spec -> OpSet.Set
  % op Op.isLocal? : Spec -> OpInfo -> Bool

  % op Type.local : Spec -> TypeSet.Set
  % op Type.isLocal? : Spec -> TypeInfo -> Bool
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

  % op SpecEnv.addType : Spec -> TypeInfo -> Position -> Env Spec
  % def SpecEnv.addType spc typeInfo position =
  %   SpecCalc.addType [idOf typeInfo] [] [type typeInfo] spc position
  def SpecEnv.addType spc info position =
    SpecCalc.addType info.names info.dfn spc position

  % op SpecEnv.addClaim : Spec -> Claim -> Position -> Env Spec
  def SpecEnv.addClaim spc claim position = return (SpecCalc.addProperty (claim,spc))
\end{spec}

\begin{spec}
  % op Spec.foldOps : fa(a) (a -> OpInfo -> a) -> a -> Spec -> a
  def Spec.foldOps f unit spc = foldriAQualifierMap (fn (qual,id,opInfo,x) -> f x opInfo) unit spc.ops

  % op Spec.foldTypes : fa(a) (a -> TypeInfo -> a) -> a -> Spec -> a
  def Spec.foldTypes f unit spc = foldriAQualifierMap (fn (qual,id,typeInfo,x) -> f x typeInfo) unit spc.types
\end{spec}

\begin{spec}
  % op SpecEnv.foldOps : fa(a) (a -> OpInfo -> Env a) -> a -> Spec -> Env a
  def SpecEnv.foldOps f unit spc = foldOverQualifierMap (fn (qual,id,opInfo,x) -> f x opInfo) unit spc.ops

  % op SpecEnv.foldTypes : fa(a) (a -> TypeInfo -> Env a) -> a -> Spec -> Env a
\end{spec}

Map operations. These are are monomorphic and hence less general than
one might like as they map only from op to op or type to type.

\begin{verbatim}
  op SpecEnv.mapOps : (OpInfo -> Env OpInfo) -> Spec -> Env Spec
  def SpecEnv.mapOps f spc = OpSetEnv.map f (ops spc)

  op SpecEnv.mapTypes : (TypeInfo -> Env TypeInfo) -> Spec -> Env Spec
  def SpecEnv.mapTypes f spc = TypeSetEnv.map f (types spc)
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
