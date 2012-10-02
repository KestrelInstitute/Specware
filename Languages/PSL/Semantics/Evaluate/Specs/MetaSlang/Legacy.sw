\section{Refinement of MetaSlang to Legacy types }

Points to make:

- A type is identified with a type scheme. In some cases the type variables
  get ignored and in other cases we introduce a empty list (though we might
  be better off to compute the free type variables.)

- The field names in record types are identifiers (like those of ops and types)
  Later we will makes ops out of them anyway.

\begin{spec}
MSlang qualifying spec
  import ../MetaSlang
  import ../Id/Legacy
  import /Languages/MetaSlang/Specs/AnnSpec
  import /Languages/MetaSlang/Specs/Printer
  import /Languages/MetaSlang/Specs/Elaborate/Utilities % for freshMetaTyVar

  % type MSlang.Term = MetaSlang.ATerm Position.Position
  type MSlang.Type = MetaSlang.ATypeScheme Position
  type MSlang.Fun = MetaSlang.AFun Position 
  type MSlang.TypeVars = MetaSlang.TyVars

  % op boolType : Position -> Type
  % op natType : Position -> Type
  def MSlang.natType position = mkBase (makeId "Nat" "Nat", [], position)
  def MSlang.boolType position = ([], Boolean position)
  def MSlang.stringType position = mkBase (makeId "String" "String", [], position)

  % op Term.pp : Term -> Doc
  def Term.pp term = pp (printTerm term)

  % op noTypeVars : TypeVars
  def MSlang.noTypeVars = []

  % op Term.show : Term -> String
  def Term.show term = printTerm term

  % op Type.pp : Type -> Doc
  def Type.pp typ = pp (printTypeScheme typ)

  % op Type.show : Type -> String
  def Type.show typ = printTypeScheme typ

  % op MSlangEnv.mkApply : Term * Term * Position -> Env Term
  def MSlangEnv.mkApply (t1,t2,position) = return (Apply (t1,t2,position))
  def MSlang.mkApply (t1,t2,position) = (Apply (t1,t2,position))

  % op mkApplyN : Term * Term * Position -> Term
  def MSlang.mkApplyN (t1, t2, position) = ApplyN ([t1,t2],position)

  % op mkTuple : (List Term) * Position -> Term
  def MSlang.mkTuple (terms, position) =
    let def loop (n, terms) = 
       case terms  of
          | [] -> []
          | term::terms -> cons ((makeId (Nat.show n), term), loop(n + 1, terms))
  in
    case terms of
      | [term] -> term
      | _ -> MSlang.mkRecord (loop (1,terms), position)

  op idToFieldName : Id.Id -> String
  def idToFieldName (Qualified (qual,id)) = id

  % op mkRecord : List (Id * Term) -> Position -> Term
  def MSlang.mkRecord (fields, position) =
    Record (map (fn (id,term) -> (idToFieldName id,term)) fields,position)

  def MSlang.mkProduct (types,position) =
    let def loop (n, types) = 
      case types  of
        | []  -> []
        | (_,srt)::types -> cons ((Nat.show n, srt), loop (n + 1, types))
    in
      case types of
        | [typ] -> typ
        | _ -> ([], Product (loop(1,types), position))

  % op mkBase : Id.Id * List Type * Position -> Type
  def MSlang.mkBase (id, types, position) = ([], Base (id, map (fn (_,srt) -> srt) types, position))

  % op mkArrow : Type * Type * Position -> Type
  def MSlang.mkArrow ((_,srt1),(_,srt2),position) = ([], Arrow (srt1,srt2,position))

  % op mkEquals : Type * Position -> Term
  def MSlang.mkEquals (typ, position) = MSlang.mkFun (Equals, typ, position)
   
  (*
   * This differs from the usual in that we don't give the type for equality
   * It must be inferred. 
   *)
  % op mkEquality : Term * Term * Position -> Term
  def MSlang.mkEquality (t0,t1,position) = 
    let mtv = freshMetaTyVar ("mkEquality", position) in
    mkApplyN (mkEquals (mtv,position), mkTuple ([t0,t1], position),position)

  % op mkTrue : Position -> Term
  def MSlang.mkTrue position = mkFun (Bool true, boolType position, position)
  def MSlang.mkFalse position = mkFun (Bool false, boolType position, position)

  % op MSPosEnv.mkTrue : Position -> Env Term
  
  % op mkNot : Term -> Position -> Term
  def MSlang.mkNot (trm, position) = mkApplyN (Fun (Not, unaryBoolType, noPos),
					       trm, 
					       position)
  
  op MSlang.charType : Position -> Type
  def MSlang.charType position = mkBase (makeId "Char" "Char", [], position)

  op unaryBoolType : Position -> Type
  def unaryBoolType position  = mkArrow (boolType position, boolType position, position)

  op binaryBoolType : Position -> Type
  def binaryBoolType position =
    mkArrow (mkProduct ([boolType position, boolType position], position), boolType position, position)

  op notOp : Position -> MSlang.Term
  op orOp  : Position -> MSlang.Term
  op andOp : Position -> MSlang.Term

  def notOp position = mkFun (Not, unaryBoolType  position, position)
  def orOp  position = mkFun (Or,  binaryBoolType position, position)
  def andOp position = mkFun (And, binaryBoolType position, position)

  op mkNameRef : List String -> MSlang.Fun
  def mkNameRef names =
    case names of
      | [] -> fail "makeNameRef: given empty list"
      | [name] -> OneName (name,Nonfix)
      | [name1,name2] -> TwoNames (name1,name2,Nonfix)
      | _ -> fail "makeNameRef: given more than two names"

  % op mkFun : Fun * Type * Position -> Term
  def MSlang.mkFun (fun, (_,srt), position) = Fun (fun, srt, position) 

  % op mkOp : Id * Type * Position -> Term
  % op mkOr : Term * Term * Position -> Term
  def MSlang.mkOr (term1, term2, position) = mkApplyN (orOp position, mkTuple ([term1,term2],position), position)

  % op disjList : List Term * Position -> Term
  def MSlang.disjList (terms, position) =
    case terms of
      | []  -> MSlang.mkTrue position
      | [term]  -> term
      | term::terms -> mkOr (term, disjList (terms, position), position)

  % op mkNat : Nat -> Term
  def MSlang.mkNat (n, position) = mkFun (Nat n, natType position, position)

  def MSlang.mkString (str, position) = mkFun (String str, stringType position, position)

  % op freshMetaTyVar : String * Position -> Type
  def MSlang.freshMetaTyVar (prefix, position) = ([],Utilities.freshMetaTyVar (prefix, position))

  % op idToNameRef : Id.Id -> MSlang.Fun
  def MSlang.idToNameRef (Qualified (qual,id)) =
    if qual = UnQualified then
      OneName (id,Nonfix)
    else
      TwoNames (qual,id,Nonfix)
endspec
\end{spec}
