% derived from SW4/Languages/MetaSlang/ADT/Specs/StandardSpec.sl, v1.5
% derived from SW4/Languages/MetaSlang/ADT/Specs/StandardSpecSig.sl, v1.1.1.1

StandardSpec qualifying spec {
 import AnnSpec
 import /Library/Legacy/DataStructures/ListUtilities % for listUnion

 % sort SpecName = String % Repeated so MetaSlang4.SpecName exists

 %% -- See ../AbstractSyntax/AnnTerm
 sort Term         = ATerm           StandardAnnotation
 sort Var          = AVar            StandardAnnotation
 sort Match        = AMatch          StandardAnnotation
 sort Sort         = ASort           StandardAnnotation
 sort Pattern      = APattern        StandardAnnotation
 sort Fun          = AFun            StandardAnnotation

 % sort MetaTyVar       = AMetaTyVar      StandardAnnotation
 % sort MetaTyVars      = AMetaTyVars     StandardAnnotation
 % sort MetaSortScheme  = AMetaSortScheme StandardAnnotation

 sort Fields       = AFields         StandardAnnotation
 sort Field        = AField          StandardAnnotation

 %% -- See AnnSpec

 % already defined in AnnSpec
 % sort Spec         = ASpec           StandardAnnotation

 sort SortMap      = ASortMap        StandardAnnotation
 sort OpMap        = AOpMap          StandardAnnotation

 sort SortInfo     = ASortInfo       StandardAnnotation 
 sort OpInfo       = AOpInfo         StandardAnnotation

 sort Properties   = AProperties     StandardAnnotation
 sort Property     = AProperty       StandardAnnotation

 sort Specs        = ASpecs          StandardAnnotation
 % sort Sorts        = ASorts          StandardAnnotation
 % sort Ops          = AOps            StandardAnnotation

 sort OpSignature  = AOpSignature    StandardAnnotation
 sort SortScheme   = ASortScheme     StandardAnnotation
 sort TermScheme   = ATermScheme     StandardAnnotation

 % sort QualifierMap = AQualifierMap   StandardAnnotation

 % ========================================================================

 op emptySortMap    : SortMap    
 op emptyOpMap      : OpMap      
 op emptyProperties : Properties 

 def emptySortMap    = emptyASortMap
 def emptyOpMap      = emptyASortMap
 def emptyProperties = emptyAProperties

 % ========================================================================

 %% Sort term constructors:

 op mkTyVar        : String                       -> Sort
 op mkBase         : QualifiedId * List Sort      -> Sort
 op mkArrow        : Sort * Sort                  -> Sort
 op mkSubsort      : Sort * Term                  -> Sort
 op mkQuotientSort : Sort * Term                  -> Sort
 op mkProduct      : List Sort                    -> Sort
 op mkCoProduct    : List (String * Option Sort)  -> Sort

 def mkTyVar        name        = TyVar    (name,       noPos)
 def mkBase         (qid, srts) = Base     (qid, srts,  noPos)
 def mkArrow        (s1, s2)    = Arrow    (s1, s2,     noPos)
 def mkSubsort      (srt, pred) = Subsort  (srt, pred,  noPos)
 def mkQuotientSort (srt, rel)  = Quotient (srt, rel,   noPos)

 def mkProduct sorts =
  let def loop (n, sorts) = 
       case sorts  of
          | []         -> []
          | srt::sorts -> cons((Nat.toString n, srt), loop(n + 1, sorts))
  in
    Product(loop(1,sorts), noPos)

 def mkCoProduct fields = CoProduct (fields, noPos)

 %% Sort terms for constant sorts:

 op natSort         : Sort
 op boolSort        : Sort
 op charSort        : Sort
 op stringSort      : Sort
 op unary_boolean   : Sort
 op binary_boolean  : Sort

 def natSort        = mkBase  (Qualified("Nat",     "Nat"),     []) 
 def charSort       = mkBase  (Qualified("Char",    "Char"),    [])
 def stringSort     = mkBase  (Qualified("String",  "String"),  [])
 def boolSort       = mkBase  (Qualified("Boolean", "Boolean"), [])

 def unaryBoolSort  = mkArrow (boolSort,                       boolSort)
 def binaryBoolSort = mkArrow (mkProduct [boolSort, boolSort], boolSort)

 %% Primitive term constructors:

 op mkRecord      : List (Id * Term)              -> Term
 op mkLet         : List (Pattern * Term) * Term  -> Term
 op mkLetRec      : List (Var     * Term) * Term  -> Term
 op mkLambda      : Pattern * Term                -> Term
 op mkBind        : Binder * List Var * Term      -> Term
 op mkVar         : Var                           -> Term
 op mkFun         : Fun * Sort                    -> Term
 op mkApply       : Term * Term                   -> Term
 op mkAppl        : Term * List Term              -> Term
 op mkIfThenElse  : Term * Term * Term            -> Term

 def mkRecord     fields          = Record     (fields,                  noPos)
 def mkLet        (decls, term)   = Let        (decls, term,             noPos)
 def mkLetRec     (decls, term)   = LetRec     (decls, term,             noPos)
 def mkLambda     (pat,   term)   = Lambda     ([(pat, mkTrue(), term)], noPos)
 def mkBind       (b, vars, term) = Bind       (b, vars, term,           noPos)

 def mkVar        v               = Var        (v,                       noPos)
 def mkFun        (constant, srt) = Fun        (constant, srt,           noPos) 
 def mkApply      (t1, t2)        = Apply      (t1, t2,                  noPos)
 def mkAppl       (t1, tms)       = Apply      (t1, mkTuple tms,         noPos)  
 def mkIfThenElse (t1, t2, t3)    = IfThenElse (t1, t2, t3,              noPos)

 %% Fun's

 op mkTrue : () -> Term
 op mkFalse : () -> Term

 op mkNat : Nat -> Term
 op mkChar : Char -> Term
 op mkBool : Boolean -> Term
 op mkString : String -> Term

 op mkRelax : Sort * Term -> Term
 op mkEmbed0 : FieldName * Sort -> Term
 op mkEmbed1 : FieldName * Sort -> Term
 op mkEmbedded : FieldName * Sort -> Term
 op mkOp : QualifiedId * Sort -> Term
 op mkInfixOp : QualifiedId * Fixity * Sort -> Term

 def mkTrue () = mkFun (Bool true, boolSort)
 def mkFalse () = mkFun (Bool false, boolSort)

 def mkNat n = mkFun (Nat n, natSort)
 def mkChar char = mkFun (Char char, charSort)
 def mkBool bool = mkFun (Bool bool, boolSort)
 def mkString str = mkFun (String str, stringSort)

 def mkRelax (srt, pred) = mkFun (Relax, mkArrow (mkSubsort (srt, pred), srt))
 def mkRestrict (srt, pred) = mkFun (Restrict, mkArrow (srt, mkSubsort (srt, pred)))
 def mkChoose (srt, equiv) = mkFun (Choose, mkArrow (mkQuotientSort (srt, equiv), srt))

 def mkEmbed0 (id, srt) = mkFun (Embed (id, false), srt) % no arg
 def mkEmbed1 (id, srt) = mkFun (Embed (id, true), srt) % arg
 def mkEmbedded (id, srt) = mkFun (Embedded id, mkArrow (srt, boolSort))
 def mkProject (id, super, sub) = mkFun (Project id, mkArrow (super, sub))
 def mkSelect (id, super, field) = mkFun (Project id, mkArrow (super, field))
 def mkEquals (srt) = mkFun (Equals, srt)

 def mkOp (qid, srt) = mkFun (Op (qid, Nonfix), srt)
 def mkInfixOp (qid, fixity, srt) = mkFun (Op (qid, fixity), srt)

 %% Op's (particular Fun's)

 op notOp : Term 
 op andOp : Term 
 op orOp : Term 
 op impliesOp : Term 
 op iffOp : Term 

 def notOp = mkOp (Qualified("Boolean", "~" ), unaryBoolSort)
 def andOp = mkInfixOp (Qualified("Boolean", "&" ), Infix(Right,15), binaryBoolSort)
 def orOp = mkInfixOp (Qualified("Boolean", "or"), Infix(Right,14), binaryBoolSort)
 def impliesOp = mkInfixOp (Qualified("Boolean", "=>"), Infix(Right,13), binaryBoolSort)
 def iffOp = mkInfixOp (Qualified("Boolean","<=>"), Infix(Right,12), binaryBoolSort)

 %% Record's

 op mkTuple : List Term -> Term

 op tagTuple : fa(A) List A -> List (Id * A)

 def tagTuple (labels) = 
  let def loop (i,labels) = 
       case labels of
          | []          -> []
          | label::tail -> cons((Nat.toString i,label),loop(i + 1,tail))
  in
  loop(1,labels)

 def mkTuple terms = 
  case terms of
     | [x] -> x
     | _   -> mkRecord (tagTuple terms)

 %% Applications...

 op mkNot         : Term                        -> Term
 op mkAnd         : Term * Term                 -> Term
 op mkOr          : Term * Term                 -> Term
 op mkImplies     : Term * Term                 -> Term
 op mkIff         : Term * Term                 -> Term
 op mkConj        : List Term                   -> Term
 op mkOrs         : List Term                   -> Term
 op mkEquality    : Sort * Term * Term          -> Term
 op mkRestriction : {pred : Term, term : Term}  -> Term
 op mkChoice      : Term * Term * Sort          -> Term
 op mkProjection  : Id * Term                   -> Term
 op mkSelection   : Id * Term                   -> Term

 def mkNot     trm      = mkApply (notOp,     trm)
 def mkAnd     (t1, t2) = mkApply (andOp,     mkTuple [t1,t2])
 def mkOr      (t1, t2) = mkApply (orOp,      mkTuple [t1,t2])
 def mkImplies (t1, t2) = mkApply (impliesOp, mkTuple [t1,t2])
 def mkIff     (t1, t2) = mkApply (iffOp,     mkTuple [t1,t2])

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

 def mkEquality (dom_sort, t1, t2) = 
     let srt = mkArrow(mkProduct [dom_sort,dom_sort],boolSort) in
     mkApply(mkEquals srt, mkTuple [t1,t2])

 def mkRestriction {pred, term} = 
   let srt = termSort term in
   mkApply (mkRestrict(srt, pred), term)
    
 % This definition of choose is not correct according to David's
 % requirements.
 def mkChoice (term, equiv, srt) =
   mkApply (mkChoose(srt, equiv), term)

 def mkChooseFun (equiv, srt1, srt2, f) = % used by matchSubSort
   let chSrt = mkArrow(mkArrow(srt1,srt2), mkArrow (mkQuotientSort (srt1,equiv), srt2)) in
   let ch = mkFun(Choose,chSrt) in
   mkApply (ch, f)

 def mkProjection (id, term) = 
   let super_sort = termSort(term) in
   case super_sort of
    | Product (fields, _) -> 
      (case find (fn (id2, _) -> id = id2) fields of
        | Some (_,sub_sort) -> 
          mkApply (mkProject (id, super_sort, sub_sort),term)
        | _ -> System.fail "Projection index not found in product")
    | _ -> System.fail "Product sort expected for mkProjectTerm"    


 def mkSelection (id, term) = 
   let srt = termSort term in
   case srt
     of CoProduct(fields,_) -> 
        (case find (fn (id2,_) -> id = id2) fields
           of Some (_,Some fieldSort) ->
              mkApply(mkSelect (id, srt, fieldSort), term)
            | _ -> System.fail "Selection index not found in product")
      | _ -> System.fail ("CoProduct sort expected for mkSelectTerm "^
                           System.toString  srt)

 %% Patterns ...

 op mkVarPat    : Var           -> Pattern
 op mkNatPat    : Nat           -> Pattern
 op mkCharPat   : Char          -> Pattern
 op mkBoolPat   : Boolean       -> Pattern
 op mkStringPat : String        -> Pattern
 op mkTuplePat  : List Pattern  -> Pattern
 op mkWildPat   : Sort          -> Pattern

 def mkNatPat    n    = NatPat    (n,              noPos)
 def mkBoolPat   b    = BoolPat   (b,              noPos)
 def mkCharPat   c    = CharPat   (c,              noPos)
 def mkStringPat s    = StringPat (s,              noPos)
 def mkVarPat    v    = VarPat    (v,              noPos)
 def mkWildPat   s    = WildPat   (s,              noPos)
 def mkTuplePat  pats = RecordPat (tagTuple(pats), noPos)

 op negateTerm: Term -> Term
 %% Gets the negated version of term. 
 def negateTerm tm =
   case tm of
     | Apply(Fun(Op(Qualified("Boolean","~"),_),_,_),negTm,_) -> negTm
     | _ -> mkApply(notOp,tm)

 %% ---

 op findTheSort  : fa(a) ASpec a * QualifiedId    -> Option (ASortInfo a)  
 op findTheOp    : fa(a) ASpec a * QualifiedId    -> Option (AOpInfo   a)

 op findAllSorts : fa(a) ASpec a * QualifiedId -> List (ASortInfo a)
 op findAllOps   : fa(a) ASpec a * QualifiedId -> List (AOpInfo   a)

 def findTheSort (spc, Qualified (qualifier,id)) =
  %% We're looking for precisely one sort,
  %% which we might have specified as being unqualified.
  %% (I.e., unqualified is not a wildcard here.)
  findAQualifierMap (spc.sorts, qualifier, id)

 def findTheOp (spc, Qualified (qualifier,id)) =
  %% We're looking for precisely one op,
  %% which we might have specified as being unqualified.
  %% (I.e., unqualified is not a wildcard here.)
  findAQualifierMap (spc.ops, qualifier, id)


  %% Overloading is not particularly meaningful for sorts. 
 %% (Would we ever want both  FOO.FOO x and FOO.FOO x y  as distinct sorts?)
 %% but we might have two or more sorts X.S, Y.S, etc.
 %% If the qualifier is UnQualified then we return unqualified answer first so as to
 %% give preference to it because there is no other way to refer to this entry.
 %% Note that checkSort depends on this behavior.
 def findAllSorts (spc, Qualified (qualifier,id)) =
  let found = (case findAQualifierMap (spc.sorts, qualifier, id) of
                | Some sort_info -> [sort_info]
		| None           -> [])
  in
  if qualifier = UnQualified
    then found
       ++ filter (fn op_info -> ~(member(op_info,found)))
             (wildFindUnQualified (spc.sorts, id))
    else found
 
 def findAllOps (spc, Qualified (qualifier,id)) =
  if qualifier = UnQualified then
    wildFindUnQualified (spc.ops, id)
  else
    case findAQualifierMap (spc.ops, qualifier, id) of
     | Some op_info -> [op_info]
     | None         -> []
		
 %%  find all the matches to id in every second level map
 op wildFindUnQualified : fa (a) AQualifierMap a * Id -> List a
 def wildFindUnQualified (qualifier_map, id) =
  StringMap.foldri (fn (qualifier, qmap, results) ->
                     case StringMap.find (qmap, id) of
                      | Some result -> results ++ [result]
                      | None        -> results)
                   []
                   qualifier_map
}
