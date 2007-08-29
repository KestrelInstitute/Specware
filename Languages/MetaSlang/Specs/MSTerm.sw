MS qualifying spec
 import ../AbstractSyntax/AnnTerm
 import /Library/Legacy/DataStructures/ListUtilities % for listUnion
 import Position

 op AnnSpecPrinter.printSort : [a] ASort a -> String  % see Printer.sw for def

 sort StandardAnnotation = Position

 sort Term         = ATerm           StandardAnnotation
 sort Var          = AVar            StandardAnnotation
 sort Match        = AMatch          StandardAnnotation
 sort Sort         = ASort           StandardAnnotation
 sort Pattern      = APattern        StandardAnnotation
 sort Fun          = AFun            StandardAnnotation

 sort Fields       = AFields         StandardAnnotation
 sort Field        = AField          StandardAnnotation

 sort MetaTyVar       = AMetaTyVar      StandardAnnotation
 sort MetaTyVars      = AMetaTyVars     StandardAnnotation


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
  case sorts of
    | [s] -> s
    | _ ->
      let def loop (n, sorts) = 
	   case sorts  of
	      | []         -> []
	      | srt::sorts -> cons((Nat.toString n, srt), loop(n + 1, sorts))
      in
	Product(loop(1,sorts), noPos)

 def mkCoProduct fields = CoProduct (fields, noPos)

 %% Sort terms for constant sorts:

 op boolSort        : Sort
 op natSort         : Sort
 op charSort        : Sort
 op stringSort      : Sort

 def boolSort       = Boolean noPos
 def integerSort    = mkBase  (Qualified("Integer", "Integer"), []) 
 def natSort        = mkBase  (Qualified("Nat",     "Nat"),     []) 
 def charSort       = mkBase  (Qualified("Char",    "Char"),    [])
 def stringSort     = mkBase  (Qualified("String",  "String"),  [])

 def unaryBoolSort  = mkArrow (boolSort, boolSort)
 def binaryBoolSort = mkArrow (mkProduct [boolSort, boolSort], boolSort)

 %% Primitive term constructors:

 op mkRecord      : List (Id * Term)              -> Term
 op mkLet         : List (Pattern * Term) * Term  -> Term
 op mkLetRec      : List (Var     * Term) * Term  -> Term
 op mkLambda      : Pattern * Term                -> Term
 op mkThe         : Var * Term                    -> Term
 op mkBind        : Binder * List Var * Term      -> Term
 op mkVar         : Var                           -> Term
 op mkFun         : Fun * Sort                    -> Term
 op mkApply       : Term * Term                   -> Term
 op mkAppl        : Term * List Term              -> Term
 op mkApplication : Term * List Term              -> Term
 op mkIfThenElse  : Term * Term * Term            -> Term

 def mkRecord     fields          = Record     (fields,                  noPos)
 def mkLet        (decls, term)   = Let        (decls, term,             termAnn(term))
 def mkLetRec     (decls, term)   = LetRec     (decls, term,             termAnn(term))
 def mkLambda     (pat,   term)   = Lambda     ([(pat, mkTrue(), term)], termAnn(term))
 def mkThe        (var, term)     = The        (var, term,              termAnn(term))
 def mkBind       (b, vars, term) = Bind       (b, vars, term,           termAnn(term))

 def mkVar        v               = Var        (v,                       noPos)
 def mkFun        (constant, srt) = Fun        (constant, srt,           noPos) 
 def mkApply      (t1, t2)        = Apply      (t1, t2,                  termAnn(t2))
 def mkAppl       (t1, tms)       = Apply      (t1, mkTuple tms,         termAnn(t1))  
 def mkApplication(t1, tms)       = 
   let pos = termAnn(t1) in
   case tms of
     | [] -> mkApply(t1,Record([],pos))
     | [t2] -> mkApply(t1, t2)
     | trm::rest -> mkAppl(t1, tms)
 def mkIfThenElse (t1, t2, t3)    = IfThenElse (t1, t2, t3,              termAnn(t1))

 %% Fun's

 op mkTrue : () -> Term
 op mkFalse : () -> Term

 op mkInt : Integer -> Term
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

 def mkTrue  () = mkFun (Bool true,  boolSort)
 def mkFalse () = mkFun (Bool false, boolSort)

 op trueTerm : Term = mkTrue()
 op falseTerm: Term = mkFalse()

 op  trueTerm?: [a] ATerm a -> Boolean
 def trueTerm? t =
   case t of
     | Fun(Bool true,_,_)  -> true
     | _ -> false

 op  falseTerm?: [a] ATerm a -> Boolean
 def falseTerm? t =
   case t of
     | Fun(Bool false,_,_)  -> true
     | _ -> false

 def mkInt i = if i >= 0
		 then mkNat(i)
	       else mkApply (mkOp(mkQualifiedId("Integer", "-"), mkArrow(integerSort, natSort)), mkNat(-i))
 def mkNat n = mkFun (Nat n, natSort)
 def mkChar char = mkFun (Char char, charSort)
 def mkBool bool = mkFun (Bool bool, boolSort)
 def mkString str = mkFun (String str, stringSort)

 def mkRelax    (srt, pred)   = mkFun (Relax, mkArrow (mkSubsort (srt, pred), srt))
 def mkRestrict (srt, pred)   = mkFun (Restrict, mkArrow (srt, mkSubsort (srt, pred)))
% def mkChoose   (srt, equiv) = let q = mkQuotientSort (srt, equiv) in mkFun (Choose q, mkArrow (q, srt))
 def mkQuotient (a,qid,srt)   = mkApply(mkFun (Quotient qid, mkArrow(srt,Base(qid,[],noPos))), a)

 def mkEmbed0 (id, srt) = mkFun (Embed (id, false), srt) % no arg
 def mkEmbed1 (id, srt) = mkFun (Embed (id, true), srt) % arg
 def mkEmbedded (id, srt) = mkFun (Embedded id, mkArrow (srt, boolSort))
 def mkProject (id, super, sub) = mkFun (Project id, mkArrow (super, sub))
 def mkSelect (id, super, field) = mkFun (Project id, mkArrow (super, field))
 def mkEquals (srt) = mkFun (Equals, srt)

 def mkOp (qid, srt) = mkFun (Op (qid, Nonfix), srt)
 def mkInfixOp (qid, fixity, srt) = mkFun (Op (qid, fixity), srt)

 %% Op's (particular Fun's)

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

 op  termToList: fa(a) ATerm a -> List(ATerm a)
 def termToList t =
    case t of
      | Record (fields,_) ->
        if tupleFields? fields
	  then map (fn (_,x) -> x) fields
	 else [t]
      | _ -> [t]

 op  tupleFields?: fa(a) List (Id * a) -> Boolean
 def tupleFields? fields =
   (foldl (fn ((id,_),i) ->
	   if i < 0 then i
	     else if id = Nat.toString i then i + 1 else -1)
      1 fields)
   > 0

 op  findField: fa(a) Id * List(Id * a) -> a
 def findField(id,fields) = 
   case fields
     of [] -> System.fail ("Field identifier "^id^" was not found")
      | (id2,tm)::fields -> 
	if id = id2 then tm else findField(id,fields)

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

 def mkNot     trm      = mkApply (Fun (Not,     unaryBoolSort,  noPos), trm)
 def mkAnd     (t1, t2) = mkApply (Fun (And,     binaryBoolSort, noPos), mkTuple [t1,t2])
 def mkOr      (t1, t2) = mkApply (Fun (Or,      binaryBoolSort, noPos), mkTuple [t1,t2])
 def mkImplies (t1, t2) = mkApply (Fun (Implies, binaryBoolSort, noPos), mkTuple [t1,t2])
 def mkIff     (t1, t2) = mkApply (Fun (Iff,     binaryBoolSort, noPos), mkTuple [t1,t2])

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
% def mkChoice (term, equiv, srt) =   mkApply (mkChoose(srt, equiv), term)

 def mkChooseFun (q as Base(qid,_,_), srt1, srt2, f) = % used by matchSubSort
   let chSrt = mkArrow(mkArrow(srt1,srt2), mkArrow (q, srt2)) in
   let ch = mkFun(Choose qid, chSrt) in
   mkApply (ch, f)

 def mkProjection (id, term) = 
   let super_sort = termSort(term) in
   case super_sort of
    | Product (fields, _) -> 
      (case find (fn (id2, _) -> id = id2) fields of
        | Some (_,sub_sort) -> 
          mkApply (mkProject (id, super_sort, sub_sort),term)
        | _ -> System.fail ("Projection index " ^ id ^ " not found in product " ^ printSort super_sort))
    | _ -> System.fail ("Product sort expected for mkProjection: " ^ printSort super_sort)


 def mkSelection (id, term) = 
   let srt = termSort term in
   case srt
     of CoProduct(fields,_) -> 
        (case find (fn (id2,_) -> id = id2) fields
           of Some (_,Some fieldSort) ->
              mkApply(mkSelect (id, srt, fieldSort), term)
            | _ -> System.fail "Selection index not found in product")
      | _ -> System.fail ("CoProduct sort expected for mkSelection: " ^ printSort srt)

 op negateTerm: Term -> Term
 %% Gets the negated version of term. 
 def negateTerm tm =
   case tm of
     | Apply(Fun(Not,_,_),negTm,_) -> negTm
     | Apply(Fun(NotEquals,ty,a1),args,a2) ->
       Apply(Fun(Equals,ty,a1),args,a2)
     | _ -> mkNot tm

 %% Patterns ...

 op mkAliasPat      : Pattern * Pattern          -> Pattern
 op mkVarPat        : Var                        -> Pattern
 op mkEmbedPat      : Id * Option Pattern * Sort -> Pattern
 op mkRecordPat     : List(Id * Pattern)         -> Pattern
 op mkTuplePat      : List Pattern               -> Pattern
 op mkWildPat       : Sort                       -> Pattern
 op mkBoolPat       : Boolean                    -> Pattern
 op mkNatPat        : Nat                        -> Pattern
 op mkStringPat     : String                     -> Pattern
 op mkCharPat       : Char                       -> Pattern
 op mkQuotientPat   : Pattern * SortName         -> Pattern
 op mkRestrictedPat : Pattern * Term             -> Pattern
 op mkSortedPat     : Pattern * Sort             -> Pattern

 op patternToList: fa(a) APattern a -> List(APattern a)

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
 def mkSortedPat     (p, typ)     = SortedPat     (p, typ,        noPos)

 def patternToList t =
    case t of
      | RecordPat (fields,_) ->
        if tupleFields? fields
	  then map (fn (_,x) -> x) fields
	 else [t]
      | _ -> [t]

  op mkUnaryBooleanFn : Fun * Position -> Term
 def mkUnaryBooleanFn (f,pos) =
   %let pos = Internal "mkUnaryBooleanFn" in
   let pattern = VarPat (("x", Boolean pos), pos) in
   let f       = Fun (f, unaryBoolSort, pos) in
   let arg     = Var (("x", Boolean pos), pos) in
   let branch  = (pattern, mkTrue(), Apply(f,arg,pos)) in
   Lambda ([branch], pos)

 op  mkBinaryFn : Fun * Sort * Sort * Sort * Position -> Term
 def mkBinaryFn (f,t1,t2,t3,pos) =
   %let pos = Internal "mkBinaryFn" in
   let pattern = RecordPat ([("1", VarPat(("x", t1), pos)),
			     ("2", VarPat(("y", t2), pos))],
			    pos)
   in
   let f       = Fun (f, Arrow(mkProduct[t1,t2],t3,pos), pos) in
   let arg     = Record ([("1", Var(("x", t1), pos)),
			  ("2", Var(("y", t2), pos))],
			 pos)
   in
   let branch  = (pattern, mkTrue(), ApplyN([f,arg],pos)) in
   Lambda ([branch], pos)


endspec
