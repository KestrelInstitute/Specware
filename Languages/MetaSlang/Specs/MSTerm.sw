MS qualifying spec
 import ../AbstractSyntax/AnnTerm
 import /Library/Legacy/DataStructures/ListUtilities % for listUnion
 import Position
 import /Library/Legacy/DataStructures/MergeSort

 type StandardAnnotation = Position

 type MSTypes    = List MSType
 type MSType     = AType Position

 type MSTerms    = List MSTerm
 type MSTerm     = ATerm Position

 type MSPatterns = List MSPattern
 type MSPattern  = APattern Position

 type Var          = AVar            StandardAnnotation
 type Match        = AMatch          StandardAnnotation
 type Fun          = AFun            StandardAnnotation

 type Fields       = AFields         StandardAnnotation
 type Field        = AField          StandardAnnotation

 type MetaTyVar    = AMetaTyVar      StandardAnnotation
 type MetaTyVars   = AMetaTyVars     StandardAnnotation


 op mkTyVar        : String                        -> MSType
 op mkBase         : QualifiedId * MSTypes         -> MSType
 op mkArrow        : MSType * MSType               -> MSType
 op mkSubtype      : MSType * MSTerm               -> MSType
 op mkQuotientType : MSType * MSTerm               -> MSType
 op mkProduct      : List MSType                   -> MSType
 op mkRecordType (fields: List(Id * MSType)): MSType =
   Product(fields, noPos)
 op mkCanonRecordType(fields: List(Id * MSType)): MSType =
   mkRecordType(sortGT (fn ((fld1,_), (fld2,_)) -> fld1 > fld2) fields)

 op mkCoProduct    : List (String * Option MSType) -> MSType

 def mkTyVar        name        = TyVar    (name,       noPos)
 def mkBase         (qid, srts) = Base     (qid, srts,  noPos)
 def mkArrow        (s1, s2)    = Arrow    (s1, s2,     noPos)
 def mkSubtype      (srt, pred) = Subtype  (srt, pred,  noPos)
 def mkQuotientType (srt, rel)  = Quotient (srt, rel,   noPos)

 def mkProduct types =
  case types of
    | [s] -> s
    | _ ->
      let def loop (n, types) = 
	   case types  of
	      | []         -> []
	      | srt::types -> Cons((show n, srt), loop(n + 1, types))
      in
	Product(loop(1,types), noPos)

 def mkCoProduct fields = CoProduct (fields, noPos)

 op mkCanonCoProduct(flds: List(String * Option MSType)): MSType =
   mkCoProduct (sortGT (fn ((fld1,_), (fld2,_)) -> fld1 > fld2) flds)

 %% Type terms for constant types:

 op boolType   : MSType
 op intType    : MSType
 op natType    : MSType
 op charType   : MSType
 op stringType : MSType

 def boolType    = Boolean noPos
 def intType     = mkBase (Qualified("Integer", "Int"),    []) 
 def natType     = mkBase (Qualified("Nat",     "Nat"),    []) 
 def charType    = mkBase (Qualified("Char",    "Char"),   [])
 def stringType  = mkBase (Qualified("String",  "String"), [])
 op voidType : MSType = mkProduct[]

 op mkListType  (ty: MSType): MSType = mkBase(Qualified("List",  "List"),   [ty])
 op mkOptionType(ty: MSType): MSType = mkBase(Qualified("Option","Option"), [ty])

 op listCharType     : MSType = mkListType charType
 op optionStringType : MSType = mkOptionType stringType


 def unaryBoolType  = mkArrow (boolType, boolType)
 def binaryBoolType = mkArrow (mkProduct [boolType, boolType], boolType)

 def unaryBoolSort  = unaryBoolType % TODO -- temp, remove when parser no longer uses this

 %% Primitive term constructors:

 op mkRecord      : List (Id * MSTerm)                 -> MSTerm
 op mkLetRec      : List (Var       * MSTerm) * MSTerm -> MSTerm
 op mkLambda      : MSPattern * MSTerm                 -> MSTerm
 op mkThe         : Var * MSTerm                       -> MSTerm
 op mkBind        : Binder * List Var * MSTerm         -> MSTerm
 op mkVar         : Var                                -> MSTerm
 op mkFun         : Fun * MSType                       -> MSTerm
 op mkApply       : MSTerm * MSTerm                    -> MSTerm
 op mkAppl        : MSTerm * MSTerms                   -> MSTerm
 op mkApplication : MSTerm * MSTerms                   -> MSTerm
 op mkIfThenElse  : MSTerm * MSTerm * MSTerm           -> MSTerm

 def mkRecord     fields          = Record     (fields,                  noPos)
 op mkCanonRecord(fields: List(Id * MSTerm)): MSTerm =
   mkRecord(sortGT (fn ((fld1,_), (fld2,_)) -> fld1 > fld2) fields)

 op mkLet1 (pat : MSPattern, val : MSTerm, body : MSTerm) : MSTerm = 
  Let ([(pat,val)], body, termAnn body)

 op mkLet  (bindings : List (MSPattern * MSTerm), body : MSTerm) : MSTerm =
  case bindings of
    | [] -> body
    | (pat, val) :: bindings -> mkLet1 (pat, val, mkLet (bindings, body))
   
 def mkLetRec     (decls, term)   = LetRec     (decls,  term,            termAnn(term))
 def mkLambda     (pat,   term)   = Lambda     ([(pat, mkTrue(), term)], termAnn(term))
 def mkThe        (var, term)     = The        (var, term,               termAnn(term))
 def mkBind       (b, vars, term) = Bind       (b, vars, term,           termAnn(term))
 op mkCaseExpr(c_tm: MSTerm, cases: List(MSPattern * MSTerm)): MSTerm =
    let trp_cases = map (fn (p, b) -> (p, trueTerm, b)) cases in
    mkApply(Lambda(trp_cases, noPos), c_tm)


 def mkVar        v               = Var        (v,                       noPos)
 def mkFun        (constant, srt) = Fun        (constant, srt,           noPos) 
 def mkApply      (t1, t2)        = Apply      (t1, t2,                  termAnn(t2))
 op mkCurriedApply(f: MSTerm, terms: MSTerms): MSTerm =
   foldl mkApply f terms

 def mkAppl       (t1, tms)       = Apply      (t1, mkTuple tms,         termAnn(t1))  
 def mkApplication(t1, tms)       = 
   let pos = termAnn(t1) in
   case tms of
     | [] -> mkApply(t1,Record([],pos))
     | [t2] -> mkApply(t1, t2)
     | trm::rest -> mkAppl(t1, tms)
 def mkIfThenElse (t1, t2, t3)    = IfThenElse (t1, t2, t3,              termAnn(t1))
 op mkSeq(tms: MSTerms): MSTerm =
   case tms of
     | [tm] -> tm
     | _ -> Seq(tms, noPos)
 op mkTypedTerm(tm: MSTerm, ty: MSType): MSTerm = TypedTerm(tm, ty, termAnn tm)

 %% Fun's

 op mkTrue   : ()     -> MSTerm
 op mkFalse  : ()     -> MSTerm
 op mkInt    : Int    -> MSTerm
 op mkNat    : Nat    -> MSTerm
 op mkChar   : Char   -> MSTerm
 op mkBool   : Bool   -> MSTerm
 op mkString : String -> MSTerm

 op mkRelax    : MSType        * MSTerm -> MSTerm
 op mkEmbed0   : FieldName   * MSType -> MSTerm
 op mkEmbed1   : FieldName   * MSType -> MSTerm
 op mkEmbedded : FieldName   * MSType -> MSTerm
 op mkOp       : QualifiedId * MSType -> MSTerm
 op mkInfixOp  : QualifiedId * Fixity * MSType -> MSTerm

 def mkTrue  () = mkFun (Bool true,  boolType)
 def mkFalse () = mkFun (Bool false, boolType)

 op trueTerm : MSTerm = mkTrue()
 op falseTerm: MSTerm = mkFalse()

 op  trueTerm?: [a] ATerm a -> Bool
 def trueTerm? t =
   case t of
     | Fun(Bool true,_,_)  -> true
     | _ -> false

 op  falseTerm?: [a] ATerm a -> Bool
 def falseTerm? t =
   case t of
     | Fun(Bool false,_,_)  -> true
     | _ -> false

 def mkInt i = if i >= 0
		 then mkNat(i)
	       else mkApply (mkOp(mkQualifiedId("Integer", "-"), mkArrow(intType, natType)), mkNat(-i))
 def mkNat n = mkFun (Nat n, natType)
 def mkChar char = mkFun (Char char, charType)
 def mkBool bool = mkFun (Bool bool, boolType)
 def mkString str = mkFun (String str, stringType)

 def mkRelax    (srt, pred)   = mkFun (Relax, mkArrow (mkSubtype (srt, pred), srt))
 def mkRestrict (srt, pred)   = mkFun (Restrict, mkArrow (srt, mkSubtype (srt, pred)))
% def mkChoose   (srt, equiv) = let q = mkQuotientType (srt, equiv) in mkFun (Choose q, mkArrow (q, srt))
 def mkQuotient (a,qid,ty) =
   let ty_args = case ty of
                   | Base(_, ty_args, _) -> ty_args
                   | _ -> []
   in
   %% Could well need a better way of getting ty_args
   mkApply(mkFun (Quotient qid, mkArrow(ty,Base(qid,ty_args,noPos))), a)

 def mkEmbed0 (id, srt) = mkFun (Embed (id, false), srt) % no arg
 def mkEmbed1 (id, srt) = mkFun (Embed (id, true), srt) % arg
 def mkEmbedded (id, srt) = mkFun (Embedded id, mkArrow (srt, boolType))
 def mkProject (id, super, sub) = mkFun (Project id, mkArrow (super, sub))
 def mkSelect (id, super, field) = mkFun (Project id, mkArrow (super, field))
 def mkEquals (srt) = mkFun (Equals, srt)
 def mkNotEquals (srt) = mkFun (NotEquals, srt)

 % Is the Nonfix here always correct?
 def mkOp (qid, srt) = mkFun (Op (qid, Nonfix), srt)
 def mkInfixOp (qid, fixity, srt) = mkFun (Op (qid, fixity), srt)

 %% Op's (particular Fun's)

 %% Record's

 op mkTuple : List MSTerm -> MSTerm

 op tagTuple : [A] List A -> List (Id * A)

 def tagTuple (labels) = 
  let def loop (i,labels) = 
       case labels of
          | []          -> []
          | label::tail -> Cons((show i,label),loop(i + 1,tail))
  in
  loop(1,labels)

 def mkTuple terms = 
  case terms of
     | [x] -> x
     | _   -> mkRecord (tagTuple terms)

 op voidTerm: MSTerm = mkTuple []

 op  termToList: [a] ATerm a -> List(ATerm a)
 def termToList t =
    case t of
      | Record (fields,_) ->
        if tupleFields? fields
	  then map (fn (_,x) -> x) fields
	 else [t]
      | _ -> [t]

 op  tupleFields?: [a] List (Id * a) -> Bool
 def tupleFields? fields =
   (foldl (fn (i,(id,_)) ->
	   if i < 0 then i
	     else if id = show i then i + 1 else -1)
      1 fields)
   > 0

 op [a] sameFieldNames?(flds1: List (Id * a), flds2: List (Id * a)): Bool =
   length flds1 = length flds2
     && forall? (fn ((f1, _), (f2, _)) -> f1 = f2) (zip(flds1, flds2))

 op  findField: [a] Id * List(Id * a) -> a
 def findField(id,fields) = 
   case fields
     of [] -> System.fail ("Field identifier "^id^" was not found")
      | (id2,tm)::fields -> 
	if id = id2 then tm else findField(id,fields)

 %% Applications...

 op mkNot         : MSTerm                         -> MSTerm
 op mkAnd         : MSTerm * MSTerm                -> MSTerm
 op mkOr          : MSTerm * MSTerm                -> MSTerm
 op mkImplies     : MSTerm * MSTerm                -> MSTerm
 op mkIff         : MSTerm * MSTerm                -> MSTerm
 op mkConj        : MSTerms                        -> MSTerm
 op mkOrs         : MSTerms                        -> MSTerm
 op mkEquality    : MSType * MSTerm * MSTerm       -> MSTerm
 op mkRestriction : {pred : MSTerm, term : MSTerm} -> MSTerm
 op mkChoice      : MSTerm * MSTerm * MSType       -> MSTerm
 op mkProjection  : Id * MSTerm                    -> MSTerm
 op mkSelection   : Id * MSTerm                    -> MSTerm

 def mkNot     trm      = mkApply (Fun (Not,     unaryBoolType,  noPos), trm)
 def mkAnd     (t1, t2) = mkApply (Fun (And,     binaryBoolType, noPos), mkTuple [t1,t2])
 def mkOr      (t1, t2) = mkApply (Fun (Or,      binaryBoolType, noPos), mkTuple [t1,t2])
 def mkImplies (t1, t2) = mkApply (Fun (Implies, binaryBoolType, noPos), mkTuple [t1,t2])
 def mkIff     (t1, t2) = mkApply (Fun (Iff,     binaryBoolType, noPos), mkTuple [t1,t2])

 op mkRecordMerge(t1: MSTerm, t2: MSTerm): MSTerm =
   let arg = mkTuple [t1,t2] in
   let rec_ty = termType t1 in
   mkApply(mkFun(RecordMerge, mkArrow(mkProduct[rec_ty, termType t2], rec_ty)), mkTuple [t1,t2])

 def mkConj(cjs) =
  case cjs
    of []     -> mkTrue()
     | [x]    -> x
     | x::rcs -> mkAnd (x, mkConj rcs)

 def mkOrs(cjs) =
  case cjs
    of []     -> mkTrue()
     | [x]    -> x
     | x::rcs -> mkOr (x, mkOrs rcs)

 def mkEquality (dom_type, t1, t2) = 
     let srt = mkArrow(mkProduct [dom_type,dom_type],boolType) in
     mkApply(mkEquals srt, mkTuple [t1,t2])

 op mkNotEquality (dom_type: MSType, t1: MSTerm, t2: MSTerm): MSTerm = 
     let srt = mkArrow(mkProduct [dom_type,dom_type],boolType) in
     mkApply(mkNotEquals srt, mkTuple [t1,t2])

 def mkRestriction {pred, term} = 
   let srt = termType term in
   mkApply (mkRestrict(srt, pred), term)
    
 % This definition of choose is not correct according to David's
 % requirements.
% def mkChoice (term, equiv, srt) =   mkApply (mkChoose(srt, equiv), term)

 def mkChooseFun (q as Base(qid,_,_), srt1, srt2, f) = % used by matchSubType
   let chSrt = mkArrow(mkArrow(srt1,srt2), mkArrow (q, srt2)) in
   let ch = mkFun(Choose qid, chSrt) in
   mkApply (ch, f)

 def mkProjection (id, term) = 
   let super_type = termType(term) in
   case super_type of
    | Product (fields, _) -> 
      (case findLeftmost (fn (id2, _) -> id = id2) fields of
        | Some (_,sub_type) -> 
          mkApply (mkProject (id, super_type, sub_type),term)
        | _ -> System.fail ("Projection index " ^ id ^ " not found in product " ^ printType super_type))
    | _ -> System.fail ("Product type expected for mkProjection: " ^ printType super_type)


 def mkSelection (id, term) = 
   let srt = termType term in
   case srt
     of CoProduct(fields,_) -> 
        (case findLeftmost (fn (id2,_) -> id = id2) fields
           of Some (_,Some fieldType) ->
              mkApply(mkSelect (id, srt, fieldType), term)
            | _ -> System.fail "Selection index not found in product")
      | _ -> System.fail ("CoProduct type expected for mkSelection: " ^ printType srt)

 op negateTerm: MSTerm -> MSTerm
 %% Gets the negated version of term. 
 def negateTerm tm =
   case tm of
     | Apply(Fun(Not,_,_),negTm,_) -> negTm
     | Apply(Fun(NotEquals,ty,a1),args,a2) ->
       Apply(Fun(Equals,ty,a1),args,a2)
     | _ -> mkNot tm

 %% Patterns ...

 op mkAliasPat      : MSPattern * MSPattern          -> MSPattern
 op mkVarPat        : Var                            -> MSPattern
 op mkEmbedPat      : Id * Option MSPattern * MSType -> MSPattern
 op mkRecordPat     : List(Id * MSPattern)           -> MSPattern
 op mkTuplePat      : MSPatterns                     -> MSPattern
 op mkWildPat       : MSType                         -> MSPattern
 op mkBoolPat       : Bool                           -> MSPattern
 op mkNatPat        : Nat                            -> MSPattern
 op mkStringPat     : String                         -> MSPattern
 op mkCharPat       : Char                           -> MSPattern
 op mkQuotientPat   : MSPattern * TypeName           -> MSPattern
 op mkRestrictedPat : MSPattern * MSTerm             -> MSPattern
 op mkTypedPat      : MSPattern * MSType             -> MSPattern

 op patternToList: [a] APattern a -> List(APattern a)

 def mkAliasPat      (p1, p2)     = AliasPat      (p1, p2,        noPos)
 def mkVarPat        v            = VarPat        (v,             noPos)
 def mkEmbedPat      (id, pat, s) = EmbedPat      (id, pat, s,    noPos) 

 def mkRecordPat     pats         = RecordPat     (pats,          noPos)
 def mkTuplePat      pats     = case pats of
                                  | [p] -> p
                                  | _ -> 
                                    RecordPat     (tagTuple pats, noPos)

 def mkWildPat       s            = WildPat       (s,             noPos)
 def mkBoolPat       b            = BoolPat       (b,             noPos)
 def mkNatPat        n            = NatPat        (n,             noPos)
 def mkStringPat     s            = StringPat     (s,             noPos)
 def mkCharPat       c            = CharPat       (c,             noPos)
 def mkQuotientPat   (p, qid)     = QuotientPat   (p, qid,        noPos)
 def mkRestrictedPat (p, tm)      = RestrictedPat (p, tm,         noPos)
 def mkTypedPat      (p, typ)     = TypedPat      (p, typ,        noPos)

 op mkConsPat(p1: MSPattern, p2: MSPattern): MSPattern = mkEmbedPat("Cons", Some(mkTuplePat[p1, p2]), patternType p2)
 op mkNilPat(ty: MSType): MSPattern = mkEmbedPat("Nil", None, ty)
 op mkListPat(pats: MSPatterns | pats ~= []): MSPattern =
   let el_ty = patternType(pats@0) in
   foldr mkConsPat (mkNilPat(mkListType el_ty)) pats

 def patternToList t =
    case t of
      | RecordPat (fields,_) ->
        if tupleFields? fields
	  then map (fn (_,x) -> x) fields
	 else [t]
      | _ -> [t]

  op mkUnaryBooleanFn : Fun * Position -> MSTerm
 def mkUnaryBooleanFn (f,pos) =
   %let pos = Internal "mkUnaryBooleanFn" in
   let pattern = VarPat (("xb", Boolean pos), pos) in
   let f       = Fun (f, unaryBoolType, pos) in
   let arg     = Var (("xb", Boolean pos), pos) in
   let branch  = (pattern, mkTrue(), Apply(f,arg,pos)) in
   Lambda ([branch], pos)

 op  mkBinaryFn : Fun * MSType * MSType * MSType * Position -> MSTerm
 def mkBinaryFn (f,t1,t2,t3,pos) =
   %let pos = Internal "mkBinaryFn" in
   let pattern = RecordPat ([("1", VarPat(("xxx", t1), pos)),
			     ("2", VarPat(("yyy", t2), pos))],
			    pos)
   in
   let f       = Fun (f, Arrow(mkProduct[t1,t2],t3,pos), pos) in
   let arg     = Record ([("1", Var(("xxx", t1), pos)),
			  ("2", Var(("yyy", t2), pos))],
			 pos)
   in
   let branch  = (pattern, mkTrue(), ApplyN([f,arg],pos)) in
   Lambda ([branch], pos)

  op  termList: MSTerm -> MSTerms
  def termList t =
    case t of
      | Record(fields as ("1", _) :: _, _ ) -> foldr (fn ((_, st), r) -> st::r) [] fields
      | _ -> [t]

endspec
