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
  def Op.idOf info =
    case info.names of
      | [] -> fail "idOf: op with empty list of ids"
      | [name] -> name
      | _::_ -> fail "idOf: op with more than one id"

  % op Op.ids : Op.OpInfo -> IdSet.Set
  % def ids opInfo =

  % op Op.fixity : OpInfo -> Fixity
  def Op.fixity info = info.fixity

  % op opinfo_type : OpInfo -> Type
  def Op.opinfo_type info = 
    let (tvs, typ, _) = unpackOpDef info.dfn in
    (tvs, typ)

  % op term : OpInfo -> Option MS.Term
  def Op.term info =
    case opDefs info.dfn of
      | [] -> None
      | [trm] -> Some trm
      | _::_ -> fail "term: op with more than one term"

  % op withId infixl 18 : OpInfo * Id -> OpInfo
  def Op.withId (info, id) = info << {names = [id]}

  % op withIds infixl 18 : OpInfo * IdSet.Set -> OpInfo
  % op withFixity infixl 18 : OpInfo * Fixity -> OpInfo
  % op withType infixl 18 : OpInfo * Type -> OpInfo
  % op withTerm infixl 18 : OpInfo * MS.Term -> OpInfo

  % ## Why are there type variables associated with terms???
  % ## Here we set the term but assume that there are no type vars!!
  def Op.withTerm (info, newTerm) = info << {dfn = newTerm}

  % op makeOp : Id * Fixity * MSlang.Term * Type -> OpInfo
  def Op.makeOp (id, fixity, term, (tvs,typ)) = 
    {names  = [id],
     fixity = fixity,
     dfn    = maybePiTerm (tvs, SortedTerm (term, typ, termAnn term))}

  % op OpNoTerm.makeOp : Id * Fixity * Type -> OpInfo
  def OpNoTerm.makeOp (id, fixity, (tvs, typ)) =
    {names  = [id],
     fixity = fixity,
     dfn    = maybePiTerm (tvs, SortedTerm (Any noPos, typ, noPos))}

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
