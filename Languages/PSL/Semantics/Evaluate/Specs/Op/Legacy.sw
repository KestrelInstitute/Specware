\section{Refinement of abstract Op to Legacy Structures}

\begin{spec}
Op qualifying spec
  import ../Op
  import ../Id/Legacy
  import ../MetaSlang/Legacy
  import /Languages/MetaSlang/Specs/AnnSpec
  import /Languages/MetaSlang/Specs/SimplePrinter

  sort Op.OpInfo = AOpInfo Position
  sort Op.Fixity = MetaSlang.Fixity

  % op Op.idOf : Op.OpInfo -> Id
  def Op.idOf (names,fxty as _,srtScheme as _,termSchemes as _) =
    case names of
      | [] -> fail "idOf: op with empty list of ids"
      | [name] -> name
      | _::_ -> fail "idOf: op with more than one id"

  % op Op.ids : Op.OpInfo -> IdSet.Set
  % def ids opInfo =

  % op Op.fixity : OpInfo -> Fixity
  def Op.fixity (names as _,fxty,srtScheme as _,termSchemes as _) = fxty

  % op type : OpInfo -> Type
  def Op.type (names as _,fxty as _,srtScheme,termSchemes as _) = srtScheme

  % op term : OpInfo -> Option MS.Term
  def Op.term (names as _,fxty as _,srtScheme as _,termSchemes) =
    case termSchemes of
      | [] -> None
      | [(tyVars,trm)] -> Some trm
      | _::_ -> fail "term: op with more than one term"

  % op withId infixl 18 : OpInfo * Id -> OpInfo
  def Op.withId ((names,fxty,srtScheme,termSchemes),id) = ([id],fxty,srtScheme,termSchemes)
  % op withIds infixl 18 : OpInfo * IdSet.Set -> OpInfo
  % op withFixity infixl 18 : OpInfo * Fixity -> OpInfo
  % op withType infixl 18 : OpInfo * Type -> OpInfo
  % op withTerm infixl 18 : OpInfo * MS.Term -> OpInfo

  % ## Why are there type variables associated with terms???
  % ## Here we set the term but assume that there are no type vars!!
  def Op.withTerm ((names,fxty,srtScheme,termSchemes),newTerm) = (names,fxty,srtScheme,[([],newTerm)])

  % op makeOp : Id * Fixity * MSlang.Term * Type -> OpInfo
  def Op.makeOp (id,fixity,term,type as (tyVars,_)) = ([id],fixity,type,[(tyVars,term)])

  % op OpNoTerm.makeOp : Id * Fixity * Type -> OpInfo
  def OpNoTerm.makeOp (id,fixity,type) = ([id],fixity,type,[])

  % op join : OpInfo -> OpInfo -> Env OpInfo

  % op pp : OpInfo -> Doc
  def Op.pp = ppAOpInfo
  def Op.ppShort opInfo =
    ppConcat [
      ppQualifiedId (idOf opInfo),
      case (term opInfo) of
        | None -> ppNil
        | Some trm -> ppConcat [
            pp " = ",
            ppATerm trm
          ]
    ]

  % op show : OpInfo -> String
  def Op.show opInfo = ppFormat (Op.pp opInfo)

  sort Op.Ref = Id.Id

  % op OpRef.pp : Ref -> Doc
  def OpRef.pp = Id.pp
  def OpRef.show ref = ppFormat (Id.pp ref)

  % op deref : Spec.Spec * Ref -> Env OpInfo

  % op Op.refOf : OpInfo -> Ref
  def Op.refOf opInfo = idOf opInfo
  def OpEnv.refOf opInfo = return (refOf opInfo)

  def Op.nonFix = Nonfix
endspec
\end{spec}
