(* Copyright 2015 Kestrel Institute. See file LICENSE for license details *)

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

type MSBindings = List MSBinding
type MSBinding  = MSPattern * MSTerm 

type MSRules    = List MSRule  % same as Match
type MSRule     = MSPattern * MSTerm * MSTerm 

type MSVars       = List MSVar
type MSVar        = AVar            Position

type MSVarSubst   = List (MSVar * MSTerm)
% FIXME: rename this to MSTyVarSubst, for conssitency
type TyVarSubst = List(TyVar * MSType)

type MSMatch      = AMatch          Position
type MSFun        = AFun            Position
type MSFuns       = List(AFun       Position)

type MetaTyVar    = AMetaTyVar      Position
type MetaTyVars   = AMetaTyVars     Position

type MSFieldName    = Id

type MSRecordFields = List MSRecordField
type MSRecordField  = MSFieldName * MSTerm

type MSProductFields = List MSProductField
type MSProductField  = MSFieldName * MSType

type MSCoProductFields = List MSCoProductField
type MSCoProductField  = QualifiedId * Option MSType

op mkTyVar        (name : String)                       : MSType = TyVar     (name,       noPos)
op mkBase         (qid  : QualifiedId, types : MSTypes) : MSType = Base      (qid, types, noPos)
op mkArrow        (dom  : MSType,      rng   : MSType)  : MSType = Arrow     (dom, rng,   noPos)
op mkArrows       (doms : MSTypes,     rng   : MSType)  : MSType = foldr mkArrow rng doms
op mkSubtype      (typ  : MSType,      pred  : MSTerm)  : MSType = Subtype   (typ, pred,  noPos)
op mkQuotientType (typ  : MSType,      rel   : MSTerm)  : MSType = Quotient  (typ, rel,   noPos)

op mkRecordType   (fields : MSProductFields)            : MSType = Product   (fields,     noPos)
op mkCoProduct    (alts   : MSCoProductFields)          : MSType = CoProduct (alts,       noPos)

op mkProduct (types : MSTypes) : MSType =
 case types of
   | [s] -> s
   | _ ->
     let def loop (n, types) = 
          case types  of
            | []         -> []
            | typ::types -> Cons((show n, typ), loop(n + 1, types))
     in
     Product (loop (1, types), noPos)

op mkCanonRecordType (fields : MSProductFields) : MSType =
  mkRecordType (sortGT (fn ((id1,_), (id2,_)) -> id1 > id2) fields)

op sortFields(qids: QualifiedIds): QualifiedIds =
  sortGT(fn (Qualified(_,id1), Qualified(_,id2)) -> id1 > id2) qids

op mkCanonCoProduct (alts: MSCoProductFields) : MSType =
 mkCoProduct  (sortGT (fn ((Qualified(_,id1),_), (Qualified(_,id2),_)) -> id1 > id2) alts)

%% Type terms for constant types:

op voidType         : MSType = mkProduct []
op boolType         : MSType = Boolean noPos
op intType          : MSType = mkBase (Qualified("Integer", "Int"),    []) 
op natType          : MSType = mkBase (Qualified("Nat",     "Nat"),    []) 
op charType         : MSType = mkBase (Qualified("Char",    "Char"),   [])
op stringType       : MSType = mkBase (Qualified("String",  "String"), [])
op listCharType     : MSType = mkListType   charType
op optionStringType : MSType = mkOptionType stringType

op mkListType   (typ : MSType) : MSType = mkBase (Qualified ("List",  "List"),   [typ])
op mkOptionType (typ : MSType) : MSType = mkBase (Qualified ("Option","Option"), [typ])

op unaryBoolType    : MSType = mkArrow (boolType, boolType)
op binaryBoolType   : MSType = mkArrow (mkProduct [boolType, boolType], boolType)

%% Primitive term constructors:

op mkRecord      (fields : MSRecordFields) : MSTerm = Record (fields, noPos)

op mkCanonRecord (fields : MSRecordFields) : MSTerm = 
 mkRecord (sortGT (fn ((id1,_), (id2,_)) -> id1 > id2) fields)

op mkTypedTerm   (term     : MSTerm, typ : MSType)                   : MSTerm = TypedTerm  (term, typ,               noPos)
op mkLetRec      (decls    : List (MSVar * MSTerm),   body : MSTerm) : MSTerm = LetRec     (decls,  body,            noPos)
op mkLambda      (pat      : MSPattern,               body : MSTerm) : MSTerm = Lambda     ([(pat, mkTrue(), body)], noPos)
op mkThe         (var      : MSVar,                   body : MSTerm) : MSTerm = The        (var, body,               noPos)
op mkBind        (binder   : Binder, vars : MSVars,   body : MSTerm) : MSTerm = Bind       (binder, vars, body,      noPos)
op mkVar         (v        : MSVar)                                  : MSTerm = Var        (v,                       noPos)
op mkFun         (constant : MSFun, typ : MSType)                    : MSTerm = Fun        (constant, typ,           noPos)
op mkIfThenElse  (t1       : MSTerm,  t2 : MSTerm,  t3 : MSTerm)     : MSTerm = IfThenElse (t1, t2, t3,              noPos)

op mkForall(vars : MSVars, body : MSTerm) : MSTerm = mkBind(Forall, vars, body)
op mkExists(vars : MSVars, body : MSTerm) : MSTerm = mkBind(Exists, vars, body)
op mkExists1(vars : MSVars, body : MSTerm): MSTerm = mkBind(Exists1,vars, body)

op mkApply       (f : MSTerm, arg  : MSTerm)  : MSTerm = Apply (f, arg,          noPos)
op mkAppl        (f : MSTerm, args : MSTerms) : MSTerm = Apply (f, mkTuple args, noPos)
op mkApplication (f : MSTerm, args : MSTerms) : MSTerm = Apply (f, mkTuple args, noPos)

op mkLet1 (pat : MSPattern, val : MSTerm, body : MSTerm) : MSTerm = Let ([(pat,val)], body, noPos)

op mkLet  (bindings : MSBindings, body : MSTerm) : MSTerm =
 case bindings of
   | [] -> body
   | (pat, val) :: bindings -> mkLet1 (pat, val, mkLet (bindings, body))
  
op mkCaseExpr (c_tm: MSTerm, cases: List (MSPattern * MSTerm)) : MSTerm =
 let trp_cases = map (fn (p, b) -> (p, trueTerm, b)) cases in
 mkApply (Lambda (trp_cases, noPos), c_tm)

op mkCurriedApply (f : MSTerm, terms : MSTerms): MSTerm =
 foldl mkApply f terms

op mkApplC(f : MSTerm, args : MSTerms, curried? : Bool) : MSTerm =
  if curried? then mkCurriedApply(f, args)
    else mkAppl(f, args)

op mkSeq (tms: MSTerms) : MSTerm =
 case tms of
   | [tm] -> tm
   | _ -> Seq(tms, noPos)

%% Fun's

op mkTrue  () : MSTerm = mkFun (Bool true,  boolType)
op mkFalse () : MSTerm = mkFun (Bool false, boolType)
op mkInt   (i : Int) : MSTerm =
 if i >= 0 then
   mkNat i
 else 
   mkApply (mkOp(mkQualifiedId("IntegerAux", "-"), mkArrow(natType, intType)), mkNat(-i))

op mkNat    (n : Nat)    : MSTerm = mkFun (Nat  n,   natType)
op mkChar   (c : Char)   : MSTerm = mkFun (Char c,   charType)
op mkBool   (b : Bool)   : MSTerm = mkFun (Bool b,   boolType)
op mkString (s : String) : MSTerm = mkFun (String s, stringType)

op mkRelax    (typ : MSType,      pred : MSTerm) : MSTerm = mkFun (Relax,    mkArrow (mkSubtype (typ, pred), typ))
op mkRestrict (typ : MSType,      pred : MSTerm) : MSTerm = mkFun (Restrict, mkArrow (typ, mkSubtype (typ, pred)))
op mkEmbed0   (qid  : QualifiedId, typ  : MSType) : MSTerm = mkFun (Embed (qid, false), typ) % no arg
op mkEmbed1   (qid  : QualifiedId, typ  : MSType) : MSTerm = mkFun (Embed (qid, true),  typ) % arg

% def mkChoose   (typ, equiv) = let q = mkQuotientType (typ, equiv) in mkFun (Choose q, mkArrow (q, typ))
% This definition of choose is not correct according to David's requirements.
% def mkChoice (term, equiv, typ) =   mkApply (mkChoose(typ, equiv), term)

op mkChooseFun (quotient_type as Base (qid,_,_) : MSType,
                typ1                            : MSType, 
                typ2                            : MSType, 
                f                               : MSTerm) 
 : MSTerm =
 % used by matchSubType
 let chooser_type = mkArrow (mkArrow (typ1,          typ2), 
                             mkArrow (quotient_type, typ2)) 
 in
 let chooser = mkFun (Choose qid, chooser_type) in
 mkApply (chooser, f)

op mkQuotient (a : MSTerm, qid : QualifiedId, typ : MSType) : MSTerm =
 let type_args = case typ of
                   | Base(_, type_args, _) -> type_args
                   | _ -> []
 in
 %% Could well need a better way of getting type_args
 mkApply (mkFun (Quotient qid, 
                 mkArrow (typ, 
                          Base (qid, type_args, noPos))), 
          a)

op mkEmbedded (qid : QualifiedId, typ : MSType) : MSTerm = mkFun (Embedded qid, mkArrow (typ, boolType))

 % Is the Nonfix here always correct?
op mkOp       (qid : QualifiedId,                  typ : MSType) : MSTerm = mkFun (Op (qid, Nonfix), typ)
op mkInfixOp  (qid : QualifiedId, fixity : Fixity, typ : MSType) : MSTerm = mkFun (Op (qid, fixity), typ)

op voidTerm   : MSTerm = mkTuple []
op trueTerm   : MSTerm = mkTrue  ()
op falseTerm  : MSTerm = mkFalse ()

op [a] trueTerm? (term : ATerm a) : Bool =
 case term of
   | Fun (Bool true,_,_)  -> true
   | _ -> false

op [a] falseTerm? (term : ATerm a) : Bool =
 case term of
   | Fun (Bool false,_,_)  -> true
   | _ -> false

op [a] existsTerm? (term: ATerm a) : Bool =
 case term of
   | Bind(Exists, _, _, _) -> true
   | _ -> false

op [a] forallTerm? (term : ATerm a) : Bool =
 case term of
   | Bind (Forall, _, _, _) -> true
   | _ -> false

op [a] voidTerm? (term : ATerm a) : Bool =
 case term of
   | Record([], _) -> true
   | _ -> false

op [a] voidType? (ty : AType a) : Bool =
 case ty of
   | Product([], _) -> true
   | _ -> false


%% Op's (particular Fun's)

op mkProject   (id : Id, super : MSType, sub   : MSType) : MSTerm = mkFun (Project id, mkArrow (super, sub))
op mkSelect    (qid : QualifiedId, super : MSType, field : MSType) : MSTerm = mkFun (Select qid, mkArrow (super, field))
op mkEquals    (typ : MSType)                            : MSTerm = mkFun (Equals,    typ)
op mkNotEquals (typ : MSType)                            : MSTerm = mkFun (NotEquals, typ)

%% Record's

op mkTuple (terms : MSTerms) : MSTerm =
 case terms of
   | [x] -> x
   | _   -> mkRecord (tagTuple terms)

op [a] tagTuple (terms : List a) : List (Id * a) =
 let 
   def aux (index, terms) = 
     case terms of
       | []           -> []
       | term :: tail -> (show index, term) :: aux (index + 1, tail)
 in
 aux (1, terms)

op [a] termToList (term : ATerm a) : List (ATerm a) =
 case term of
   | Record (fields,_) ->
     if tupleFields? fields then
       map (fn (_,x) -> x) fields
     else 
       [term]
   | _ -> [term]

op [a] tupleFields? (fields : List (Id * a)) : Bool =
 let last_index = 
     foldl (fn (i,(id,_)) ->
              if i < 0 then 
                i
              else if id = show i then 
                i + 1 
              else -1)
           1 
           fields
 in
 last_index > 0

op [a] sameFieldNames? (flds1: List (Id * a), 
                        flds2: List (Id * a))
 : Bool =
 length flds1 = length flds2
 && 
 forall? (fn ((f1, _), (f2, _)) -> f1 = f2) (zip(flds1, flds2))

op [a] findField (id : Id, fields : List (Id * a)) : a =
 case fields of
   | [] -> System.fail ("Field identifier "^id^" was not found")
   | (id2, tm) :: fields -> 
     if id = id2 then
       tm 
     else 
       findField (id, fields)

%% Applications...

op mkNot     (term : MSTerm)            : MSTerm = mkApply (Fun (Not,     unaryBoolType,  noPos), term)
op mkAnd     (t1 : MSTerm, t2 : MSTerm) : MSTerm = mkApply (Fun (And,     binaryBoolType, noPos), mkTuple [t1,t2])
op mkOr      (t1 : MSTerm, t2 : MSTerm) : MSTerm = mkApply (Fun (Or,      binaryBoolType, noPos), mkTuple [t1,t2])
op mkImplies (t1 : MSTerm, t2 : MSTerm) : MSTerm = mkApply (Fun (Implies, binaryBoolType, noPos), mkTuple [t1,t2])
op mkIff     (t1 : MSTerm, t2 : MSTerm) : MSTerm = mkApply (Fun (Iff,     binaryBoolType, noPos), mkTuple [t1,t2])

op mkConj (conjuncts : MSTerms) : MSTerm =
 case conjuncts of
   | []     -> mkTrue ()
   | [x]    -> x
   | x::rcs -> mkAnd (x, mkConj rcs)


op mkOrs (disjuncts : MSTerms) : MSTerm =
 case disjuncts of
   | []     -> mkTrue()
   | [x]    -> x
   | x::rcs -> mkOr (x, mkOrs rcs)


op mkRestriction (pred : MSTerm, term : MSTerm) : MSTerm =
 let typ = termType term in
 mkApply (mkRestrict (typ, pred), term)


op mkChoice      : MSTerm * MSTerm * MSType       -> MSTerm

op mkProjection  (id : Id, term : MSTerm) : MSTerm =
 let super_type = termType term in
 case super_type of
   | Product (fields, _) -> 
     (case findLeftmost (fn (id2, _) -> id = id2) fields of
        | Some (_, sub_type) -> 
          mkApply (mkProject (id, super_type, sub_type),
                   term)
        | _ -> 
          System.fail ("Projection index " ^ id ^ " not found in product " ^ printType super_type))
   | _ -> 
     System.fail ("Product type expected for mkProjection: " ^ printType super_type)

op mkSelection (id : QualifiedId, term : MSTerm) : MSTerm =
 let typ = termType term in
 case typ of
   | CoProduct(fields,_) -> 
     (case findLeftmost (fn (id2,_) -> id = id2) fields of
        | Some (_, Some fieldType) ->
          mkApply(mkSelect (id, typ, fieldType), term)
        | _ -> 
          System.fail "Selection index not found in product")
   | _ -> 
     System.fail ("CoProduct type expected for mkSelection: " ^ printType typ)

op mkRecordMerge (t1 : MSTerm, t2 : MSTerm) : MSTerm =
 let arg = mkTuple [t1,t2] in
 let record_type = termType t1 in
 mkApply (mkFun (RecordMerge, 
                 mkArrow (mkProduct [record_type, termType t2], 
                          record_type)), 
          mkTuple [t1, t2])

% TODO: Is it the case that dom_type should never be a Pi type?  I made that mistake once.
op mkEquality (dom_type : MSType, t1 : MSTerm, t2 : MSTerm) : MSTerm = 
 let typ = mkArrow(mkProduct [dom_type, dom_type], boolType) in
 mkApply(mkEquals typ, mkTuple [t1,t2])

op mkNotEquality (dom_type: MSType, t1 : MSTerm, t2 : MSTerm) : MSTerm = 
 let typ = mkArrow (mkProduct [dom_type, dom_type], boolType) in
 mkApply(mkNotEquals typ, mkTuple [t1,t2])

% Test if a term is an equality
op matchEquality (t : MSTerm) : Option (MSType * MSTerm * MSTerm) =
  case t of
    | Apply(Fun(Equals, typ, _), Record([("1", lhs), ("2", rhs)], _), _) ->
      (case typ of
         | Arrow (_, range, _) -> Some (range, lhs, rhs)
         | _ -> fail ("Unexpected type for =: " ^ printType typ))
    | _ -> None

% Test if a term is an implication
op matchImplication (t : MSTerm) : Option (MSTerm * MSTerm) =
  case t of
    | Apply(Fun(Implies, _, _), Record([("1", lhs), ("2", rhs)], _), _) ->
      Some (lhs, rhs)
    | _ -> None

% Test if a term is a forall; "1" means match just the first variable
op matchForall1 (t : MSTerm) : Option (Id * MSType * MSTerm) =
  case t of
    | Bind (Forall, [(var, typ)], body, pos) ->
      Some (var, typ, body)
    | Bind (Forall, (var, typ) :: vars, body, pos) ->
      Some (var, typ, Bind (Forall, vars, body, pos))
    | _ -> None

op negateTerm (term : MSTerm) : MSTerm =
 %% Gets the negated version of term. 
 case term of
   | Apply (Fun (Not,_,_), trm, _) -> trm
   | Apply (Fun (NotEquals, typ, a1), args, a2) ->
     Apply (Fun (Equals,    typ, a1), args, a2)
   | _ -> mkNot term

%% Misc Terms

 % lambda-abstract a list of variables
 op mkMultiLambda (vars : MSVars, body : MSTerm) : MSTerm =
   foldr (fn (var, tm) -> mkLambda (VarPat (var, noPos), tm)) body vars


%% Patterns ...

op mkAliasPat   (p1   : MSPattern, p2 : MSPattern)                : MSPattern = AliasPat  (p1, p2,       noPos)
op mkVarPat     (v    : MSVar)                                    : MSPattern = VarPat    (v,            noPos)
op mkEmbedPat   (qid  : QualifiedId, pat : Option MSPattern, typ : MSType) : MSPattern = EmbedPat  (qid, pat, typ, noPos) 
op mkRecordPat  (pats : List (Id * MSPattern))                    : MSPattern = RecordPat (pats,         noPos)

op mkTuplePat   (pats : MSPatterns) : MSPattern =
 case pats of
   | [p] -> p
   | _ -> 
     RecordPat (tagTuple pats, noPos)

op mkVarsPat(vs: MSVars): MSPattern = mkTuplePat(map mkVarPat vs)

op mkWildPat       (typ : MSType) : MSPattern = WildPat   (typ, noPos)
op mkBoolPat       (b   : Bool)   : MSPattern = BoolPat   (b,   noPos)
op mkNatPat        (n   : Nat)    : MSPattern = NatPat    (n,   noPos)
op mkStringPat     (s   : String) : MSPattern = StringPat (s,   noPos)
op mkCharPat       (c   : Char)   : MSPattern = CharPat   (c,   noPos)

op mkQuotientPat   (pat : MSPattern, qid  : TypeName, params: MSTypes) : MSPattern =
  QuotientPat   (pat, qid,  params, noPos)
op mkRestrictedPat (pat : MSPattern, term : MSTerm)   : MSPattern = RestrictedPat (pat, term, noPos)
op mkTypedPat      (pat : MSPattern, typ  : MSType)   : MSPattern = TypedPat      (pat, typ,  noPos)
op [a] patternToList (pat : APattern a) : List (APattern a) =
 case pat of
   | RecordPat (fields,_) ->
     if tupleFields? fields then
       map (fn (_, x) -> x) fields
     else 
       [pat]
   | _ -> 
     [pat]

op mkConsPat (p1   : MSPattern, p2 : MSPattern) : MSPattern = mkEmbedPat (Qualified("List", "Cons"), Some (mkTuplePat [p1, p2]), patternType p2)
op mkNilPat  (typ  : MSType)                    : MSPattern = mkEmbedPat (Qualified("List", "Nil"),  None,                       typ)
op mkListPat (pats : MSPatterns | pats ~= []): MSPattern =
 let elt_type = patternType (pats @ 0) in
 foldr mkConsPat (mkNilPat (mkListType elt_type)) pats

op mkUnaryBooleanFn (f : MSFun, pos : Position) : MSTerm =
 %let pos = Internal "mkUnaryBooleanFn" in
 let pattern = VarPat (("xb", Boolean pos), pos) in
 let f       = Fun (f, unaryBoolType, pos) in
 let arg     = Var (("xb", Boolean pos), pos) in
 let branch  = (pattern, mkTrue(), Apply(f,arg,pos)) in
 Lambda ([branch], pos)

op mkBinaryFn (f   : MSFun, 
               t1  : MSType, 
               t2  : MSType, 
               t3  : MSType, 
               pos : Position)
 : MSTerm =
 %let pos = Internal "mkBinaryFn" in
 let pattern = RecordPat ([("1", VarPat(("xxx", t1), pos)),
                           ("2", VarPat(("yyy", t2), pos))],
                          pos)
 in
 let f      = Fun (f, Arrow (mkProduct [t1, t2], t3, pos), pos) in
 let arg    = Record ([("1", Var(("xxx", t1), pos)),
                       ("2", Var(("yyy", t2), pos))],
                      pos)
 in
 let branch = (pattern, mkTrue(), ApplyN ([f, arg], pos)) in
 Lambda ([branch], pos)

op termList (term : MSTerm) : MSTerms =
 case term of
   | Record (fields as ("1", _) :: _, _ ) -> 
     foldr (fn ((_, tm), terms) -> tm :: terms)
           [] 
           fields
   | _ -> 
     [term]

op filePositionOfTerm (tm: MSTerm): Option Position =
  foldSubTerms (fn (t,val) ->
		  case val of
		    | Some _ -> val
		    | None ->
                      case termAnn t of
                        | pos as File _ -> Some pos
                        | _ -> None)
    None tm

op fileNameOfTerm (tm: MSTerm): Option String =
  mapOption (fn File(nm,_,_) -> nm) (filePositionOfTerm tm)

op filePositionOfType (ty: MSType): Option Position =
  foldTypesInType (fn (val,t) ->
                     case typeAnn t of
                       | pos as File _ -> Some pos
                       | _ -> val)
    None ty
    
end-spec
