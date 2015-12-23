(* Copyright 2015 Kestrel Institute. See file LICENSE for license details *)

MetaSlang qualifying spec
 import QualifiedId                                    % QualifiedId
 import /Library/Legacy/Utilities/State                % MetaTyVar
 import /Library/Legacy/Utilities/System               % fail
 import /Library/Legacy/DataStructures/ListPair        % misc operations on pairs of lists
 import PrinterSig                                     % printTerm, printType, printPattern
 import /Languages/SpecCalculus/AbstractSyntax/SCTerm  % SCTerm

 %%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%

 type TypeNames      = List TypeName
 type OpNames        = List OpName
 type PropertyNames  = List PropertyName

 type TypeName       = QualifiedId
 type OpName         = QualifiedId
 type PropertyName   = QualifiedId

 %%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%
 %%%                Type Variables
 %%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%

 type TyVar   = Id
 type TyVars  = List TyVar

 %%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%
 %%%                Terms
 %%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%
 %%% ATerm, AType, APattern, AFun, AVar, AMatch, and MetaTyVar
 %%%  are all mutually recursive types.  FIXME: Are they really?

 %% Terms are tagged with auxiliary information such as
 %% location information and free variables for use in
 %% various transformation steps.

 type ATerm b =
  | Apply        ATerm b * ATerm b                       * b
  | ApplyN       List (ATerm b)                          * b % Before elaborateSpec  %Remove
  | Record       List (Id * ATerm b)                     * b
  | Bind         Binder * List (AVar b)      * ATerm b   * b
  | The          AVar b * ATerm b                        * b
  | Let          List (APattern b * ATerm b) * ATerm b   * b
  | LetRec       List (AVar b     * ATerm b) * ATerm b   * b
  | Var          AVar b                                  * b
  | Fun          AFun b * AType b                        * b
  % Add: |  Lit ALiteral b and add ALiteral
  | Lambda       AMatch b                                * b  %Remove
  % Add: | Lambda AVar b * ATerm b
  % Add: | Case ATerm * AMatch
  | IfThenElse   ATerm b * ATerm b * ATerm b             * b
  | Seq          List (ATerm b)                          * b  %drop? parser could turn this into let?
  | TypedTerm    ATerm b * AType b                       * b
  | Transform    ATransformExpr b                        * b  % For specifying refinement by script.  Move to Spec?
  | Pi           TyVars * ATerm b                        * b  % for now, used only at top level of defn's
                                                              % Remove
  | And          List (ATerm b)                          * b  % for now, used only by colimit and friends -- meet (or join) not be confused with boolean AFun And 
                                                              % We might want to record a quotient of consistent terms plus a list of inconsistent pairs,
                                                              % but then the various mapping functions become much trickier.
                                                              %Remove
  | Any                                                    b  % e.g. "op f : Nat -> Nat"  has defn:  TypedTerm (Any noPos, Arrow (Nat, Nat, p1), noPos)
                                                              %Remove
 type Binder =
  | Forall
  | Exists
  | Exists1

 type AVar b = Id * AType b
 type AVars b = List (AVar b)

 op [a] varType((_,ty): AVar a): AType a = ty
 op [b] varName((nm, _): AVar b): Id = nm

  %% Maybe AMatch should be a single thing, and then we use List AMatch in Case above.
 type AMatch b = List (APattern b * ATerm b * ATerm b) % Match is a pattern, a guard, and a body.

 type AType b =
  | Arrow        AType b * AType b                   * b
  | Product      List (Id * AType b)                 * b
  | CoProduct    List (QualifiedId * Option (AType b)) * b
  | Quotient     AType b * ATerm b                   * b
  | Subtype      AType b * ATerm b                   * b
  | Base         QualifiedId * List (AType b)        * b  % Typechecker verifies that QualifiedId refers to some typeInfo.  The items in the list are the actuals of this type instantiation (if any).
  | Boolean                                            b
  | TyVar        TyVar                               * b
  | MetaTyVar    AMetaTyVar b                        * b  % Before elaborateSpec
  | Pi           TyVars * AType b                    * b  % for now, used only at top level of defn's
%% GK says:  | Pi List (AVar b * AType b)
  | And          List (AType b)                      * b  % for now, used only by colimit and friends -- meet (or join)
                                                          % We might want to record a quotient of consistent types plus a list of inconsistent pairs,
                                                          % but then the various mapping functions become much trickier.
                                                          % Remove
  | Any                                                b  % e.g. "type S a b c "  has defn:  Pi ([a,b,c], Any p1, p2)
                                                          % Remove

 type APattern b =
  | AliasPat      APattern b * APattern b             * b
%GK says:  | AliasPat      AVar b * APattern b             * b
  | VarPat        AVar b                              * b
  | EmbedPat      QualifiedId * Option (APattern b) * AType b  * b
  | RecordPat     List(Id * APattern b)               * b
  | WildPat       AType b                             * b
  %% Add a LiteralPat for these (takes an ALiteral <-- also new):
  | BoolPat       Bool                                * b
  | NatPat        Nat                                 * b
  | StringPat     String                              * b
  | CharPat       Char                                * b
  %% Broken for Isabelle:
  | QuotientPat   APattern b * TypeName * List(AType b) * b
  %% Remove and include in AMatch:
  | RestrictedPat APattern b * ATerm b                * b
  | TypedPat      APattern b * AType b                * b  % Before elaborateSpec

 type AFun b =

  % Move into Op:
  | Not
  | And
  | Or
  | Implies
  | Iff
  | Equals
  | NotEquals

  | Quotient       TypeName
  | Choose         TypeName
  | Restrict  % deprecate and eliminate
  | Relax     % deprecate and eliminate

  | PQuotient      TypeName % Before elaborateSpec
  | PChoose        TypeName % Before elaborateSpec

  | Op             QualifiedId * Fixity
  | Project        Id
  | RecordMerge             % <<
  | Embed          QualifiedId * Bool  % represents a call of a co-product constructor (the bool indicates whether the constructor takes arguments)
  | Embedded       QualifiedId         % represents a call to embed?, takes a constructor
  | Select         QualifiedId         % specific case extraction -- generated only by pattern match compiler and type obligation generator (deprecate?)
  %% Factor out literals as new ALiteral construct:
  | Nat            Nat
  | Char           Char
  | String         String
  | Bool           Bool
  % hacks to avoid ambiguity during parse of A.B.C, etc.
  | OneName        Id * Fixity         % Before elaborateSpec
  | TwoNames       Id * Id * Fixity    % Before elaborateSpec

 type Fixity        = | Nonfix 
                      | Constructor0   % Nullary constructor
                      | Constructor1   % Constructor that takes argument
                      | Infix Associativity * Precedence 
                      | Unspecified 
                      %% The following is used only when combining specs,
                      %% as within colimit, to allow us to delay the
                      %% raising of errors at inopportune times.
                      | Error (List Fixity) 

 %% Currently Specware doesn't allow "NotAssoc" but is there for Haskell translation compatibility
 type Associativity = | Left | Right | NotAssoc
 type Precedence    = Nat

 type AMetaTyVar      b = Ref ({link     : Option (AType b),
                                uniqueId : Nat,
                                name     : String })

 type AMetaTyVars     b = List (AMetaTyVar b)
 type AMetaTypeScheme b = AMetaTyVars b * AType b

 type ATransformExpr a =
    | Name      String                           * a
    | Number    Nat                              * a
    | Str       String                           * a
    | Qual      String * String                  * a
    | SCTerm    SCTerm                           * a
    | QuotedTerm (ATerm a)                       * a
    | Item      String * ATransformExpr a        * a  % e.g. unfold map

    | Slice     OpNames * TypeNames * (OpName -> Bool) * (TypeName -> Bool) * a  

    | Repeat    Nat * ATransformExpr a           * a
    | Tuple     List (ATransformExpr a)          * a    % (..., ...)
    | Record    List (String * ATransformExpr a) * a    % {..., attr: val, ...}
    | Options   List (ATransformExpr a)          * a    % [..., ...]
    | Block     List (ATransformExpr a)          * a
    | At        QualifiedIds * ATransformExpr a * a
    | Command   String * List (ATransformExpr a) * a

 op [a] posOf(tr: ATransformExpr a): a =
   case tr of
     | Name(_, a) -> a
     | Number(_, a) -> a
     | Str(_, a) -> a
     | Qual(_, _, a) -> a
     | SCTerm(_, a) -> a
     | Item( _, _, a) -> a
     | Slice(_, _, _, _, a) -> a
     | Repeat(_, _, a) -> a
     | Tuple(_, a) -> a
     | Record(_, a) -> a
     | Options(_, a) -> a
     | Block(_, a) -> a
     | At(_, _, a) -> a
     | Command(_, _, a) -> a


 %%% Predicates
 op [a] product? (s : AType a) : Bool =
   case s of
     | Product _ -> true
     | _         -> false

 op [b] maybePiType (tvs : TyVars, ty : AType b) : AType b =
   case tvs of
     | [] -> ty
     | _ -> Pi (tvs, ty, typeAnn ty)

 %% Wraps a Pi around tm if there are any type variables:
 op [b] maybePiTerm (tvs : TyVars, tm : ATerm b) : ATerm b =
   case tvs of
     | [] -> tm
     | _ -> Pi (tvs, tm, termAnn tm)

op [a] maybePiTypedTerm(tvs: TyVars, o_ty: Option(AType a), tm: ATerm a): ATerm a =
  let s_tm = case o_ty of
               | Some ty -> TypedTerm(tm, ty, termAnn tm)
               | None -> tm
  in
  maybePiTerm(tvs, s_tm)

op [a] piTypeAndTerm(tvs: TyVars, ty: AType a, tms: List(ATerm a)): ATerm a =
  let (main_tm, pos) = case tms of
                         | [] -> (And(tms, typeAnn ty), typeAnn ty)
                         | [tm] -> (tm, termAnn tm)
                         | tms -> (And(tms, termAnn(head tms)), termAnn (head tms))
  in
  maybePiTerm(tvs, TypedTerm(main_tm, ty, pos))

op [a] maybePiAndTypedTerm (triples : List(TyVars * AType a * ATerm a)): ATerm a =
  case triples of
    | [(tvs, ty, tm)] -> maybePiTerm (tvs, TypedTerm (tm, ty, termAnn tm))
    | (_, _, tm) :: _ -> And (map (fn (tvs, ty, tm) -> maybePiTerm (tvs, TypedTerm (tm, ty, typeAnn ty)))
                                  triples,
                              termAnn tm)

 %%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%
 %%%                Fields
 %%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%

 %% A fundamental assumption for
 %%
 %% . Records
 %% . Product types
 %% . CoProduct types
 %%
 %% is that the fields are always sorted in alphabetical order
 %% according to their labels (Id).
 %% For example, a tuple with 10 fields is sorted internally:
 %% {1,10,2,3,4,5,6,7,8,9}
 %%
 %% This invariant is established by the parser and must be
 %% maintained by all transformations.

 %% type AFields b = List (AField b)
 %% type AField  b = FieldName * AType b  % used by products and co-products
 %% type FieldName = String

 op [a] getField (m : List (Id * ATerm a), id : Id) : Option(ATerm a) =
   case findLeftmost (fn (id1,_) -> id = id1) m of
     | None      -> None
     | Some(_,t) -> Some t

 op [a] getTermField(l:  List (Id * AType a), id: Id): Option(AType a) =
   case findLeftmost (fn (id1,_) -> id = id1) l of
     | None      -> None
     | Some(_,s) -> Some s

 %%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%
 %%%                Term Annotations
 %%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%

 op [a] termAnn (tm : ATerm a) : a =
   case tm of
     | Apply      (_,_,   a) -> a
     | ApplyN     (_,     a) -> a
     | Record     (_,     a) -> a
     | Bind       (_,_,_, a) -> a
     | Let        (_,_,   a) -> a
     | LetRec     (_,_,   a) -> a
     | Var        (_,     a) -> a
     | Fun        (_,_,   a) -> a
     | Lambda     (_,     a) -> a
     | The        (_,_,   a) -> a
     | IfThenElse (_,_,_, a) -> a
     | Seq        (_,     a) -> a
     | TypedTerm  (_,_,   a) -> a
     | Transform  (_,     a) -> a
     | Pi         (_,_,   a) -> a
     | And        (_,     a) -> a
     | Any                a  -> a

 op [a] withAnnT (tm : ATerm a, a : a) : ATerm a =
   case tm of
     | Apply      (t1, t2,   b) -> if a = b then tm else Apply      (t1, t2,     a)
     | ApplyN     (l,        b) -> if a = b then tm else ApplyN     (l,          a)
     | Record     (l,        b) -> if a = b then tm else Record     (l,          a)
     | Bind       (x, l, t,  b) -> if a = b then tm else Bind       (x, l, t,    a)
     | The        (v, t,     b) -> if a = b then tm else The        (v, t,       a)
     | Let        (l,t,      b) -> if a = b then tm else Let        (l, t,       a)
     | LetRec     (l,t,      b) -> if a = b then tm else LetRec     (l, t,       a)
     | Var        (v,        b) -> if a = b then tm else Var        (v,          a)
     | Fun        (f,s,      b) -> if a = b then tm else Fun        (f, s,       a)
     | Lambda     (m,        b) -> if a = b then tm else Lambda     (m,          a)
     | IfThenElse (t1,t2,t3, b) -> if a = b then tm else IfThenElse (t1, t2, t3, a)
     | Seq        (l,        b) -> if a = b then tm else Seq        (l,          a)
     | TypedTerm  (t,s,      b) -> if a = b then tm else TypedTerm (t, s,       a)
     | Transform  (t,        b) -> if a = b then tm else Transform  (t,          a)
     | Pi         (tvs, t,   b) -> if a = b then tm else Pi         (tvs, t,     a)
     | And        (l,        b) -> if a = b then tm else And        (l,          a)
     | Any                   b  -> if a = b then tm else Any                     a

 op [a] typeAnn (ty : AType a) : a =
   case ty of
     | Arrow     (_,_, a) -> a
     | Product   (_,   a) -> a
     | CoProduct (_,   a) -> a
     | Quotient  (_,_, a) -> a
     | Subtype   (_,_, a) -> a
     | Base      (_,_, a) -> a
     | Boolean         a  -> a
     | TyVar     (_,   a) -> a
     | MetaTyVar (_,   a) -> a
     | Pi        (_,_, a) -> a
     | And       (_,   a) -> a
     | Any             a  -> a

 op [a] patAnn (pat : APattern a) : a =
   case pat of
     | AliasPat     (_,_,   a) -> a
     | VarPat       (_,     a) -> a
     | EmbedPat     (_,_,_, a) -> a
     | RecordPat    (_,     a) -> a
     | WildPat      (_,     a) -> a
     | BoolPat      (_,     a) -> a
     | NatPat       (_,     a) -> a
     | StringPat    (_,     a) -> a
     | CharPat      (_,     a) -> a
     | QuotientPat  (_,_,_, a) -> a
     | RestrictedPat(_,_,   a) -> a
     | TypedPat     (_,_,   a) -> a

 op [a] withAnnP (pat : APattern a, b : a) : APattern a =
   case pat of
     | AliasPat      (p1,p2,   a) -> if b = a then pat else AliasPat     (p1,p2,   b)
     | VarPat        (v,       a) -> if b = a then pat else VarPat       (v,       b)
     | EmbedPat      (i,p,s,   a) -> if b = a then pat else EmbedPat     (i,p,s,   b)
     | RecordPat     (f,       a) -> if b = a then pat else RecordPat    (f,       b)
     | WildPat       (s,       a) -> if b = a then pat else WildPat      (s,       b)
     | BoolPat       (bp,      a) -> if b = a then pat else BoolPat      (bp,      b)
     | NatPat        (n,       a) -> if b = a then pat else NatPat       (n,       b)
     | StringPat     (s,       a) -> if b = a then pat else StringPat    (s,       b)
     | CharPat       (c,       a) -> if b = a then pat else CharPat      (c,       b)
     | QuotientPat   (p,t,tys, a) -> if b = a then pat else QuotientPat  (p,t,tys,  b)
     | RestrictedPat (p,t,     a) -> if b = a then pat else RestrictedPat(p,t,     b)
     | TypedPat      (p,s,     a) -> if b = a then pat else TypedPat     (p,s,     b)

 op [a] withAnnS (ty : AType a, a : a) : AType a =
  % Avoid creating new structure if possible
   case ty of
     | Arrow     (s1,s2,    b) -> if a = b then ty else Arrow     (s1,s2,    a)
     | Product   (fields,   b) -> if a = b then ty else Product   (fields,   a)
     | CoProduct (fields,   b) -> if a = b then ty else CoProduct (fields,   a)
     | Quotient  (ss,t,     b) -> if a = b then ty else Quotient  (ss,t,     a)
     | Subtype   (ss,t,     b) -> if a = b then ty else Subtype   (ss,t,     a)
     | Base      (qid,tys, b)  -> if a = b then ty else Base      (qid,tys, a)
     | Boolean              b  -> if a = b then ty else Boolean a
     | TyVar     (tv,       b) -> if a = b then ty else TyVar     (tv,       a)
     | MetaTyVar (mtv,      b) -> if a = b then ty else MetaTyVar (mtv,      a)
     | Pi        (tvs, t,   b) -> if a = b then ty else Pi        (tvs, t,   a)
     | And       (types,    b) -> if a = b then ty else And       (types,    a)
     | Any                  b  -> if a = b then ty else Any       a

 %%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%
 %%%                Type components
 %%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%

 op [b] unpackType (s : AType b) : TyVars * AType b =
   case s of
     | Pi (tvs, ty, _) -> (tvs, ty)
     | And (tys, _) ->
       (case filter (fn ty -> ~(anyType? ty)) tys of
          | [] -> ([], s)
          | ty1 :: _ -> unpackType ty1)
     | _ -> ([], s)

 op [b] typeTyVars (ty : AType b) : TyVars =
   case ty of
     | Pi (tvs, _, _) -> tvs
     | And (tys, _) ->
       (case filter (fn ty -> ~(anyType? ty)) tys of
          | [] -> []
          | ty1 :: _ -> typeTyVars ty1)
     | _ -> []

 op [b] typeInnerType (ty : AType b) : AType b =
   case ty of
     | Pi (_, ty, _) -> ty
     | And _ -> ty % fail ("typeInnerType: Trying to extract inner type from an And of types.")
     | _ -> ty

 op [a] anyType?(t: AType a): Bool =
   case t of
     | Any _        -> true
     | Pi(_, ty, _) -> anyType? ty
     | And(tys, _)  -> forall? anyType? tys
     | _ -> false

 %%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%
 %%%                Term components
 %%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%

 op maybeAndType  : [b] List (AType b) * b -> AType b % Defined in Equalities.sw

 op [b] maybeMkAndTerm(tms : List (ATerm b), a : b) : ATerm b =
   case tms of
     | [tm] -> tm
     | _ -> And(tms, a)

 op [a] anyTerm?(t: ATerm a): Bool =
   case t of
     | Any _                 -> true
     | Pi(_, tm, _)          -> anyTerm? tm
     | TypedTerm(tm, _, _)   -> anyTerm? tm
     | And(tms, _)           -> forall? anyTerm? tms
     | Lambda([(_,_,tm)], _) -> anyTerm? tm     % Arguments given but no body
     | Apply(f, _, _)        -> anyTerm? f
     | _ -> false

 op [a] transformSteps?(t: ATerm a): Option(ATransformExpr a) =
   case t of
     | Transform(transfm_stmt, _) -> Some transfm_stmt
     | Any _                 -> None
     | Pi(_, tm, _)          -> transformSteps? tm
     | TypedTerm(tm, _, _)   -> transformSteps? tm
     | And(tms, _)           -> None
     | Lambda([(_,_,tm)], _) -> transformSteps? tm     % Arguments given but no body
     | _ -> None

 op [a] unpackTerm (t : ATerm a) : TyVars * AType a * ATerm a =
   let def unpack(t: (ATerm a), tvs: TyVars, o_ty: Option(AType a)): TyVars * (AType a) * (ATerm a) =
        case t of
	 | Pi (tvs, tm, _) -> unpack(tm, tvs, o_ty)
         | TypedTerm(tm, ty, _) -> (case ty of
                                       | Pi(tvs, s_ty, _) -> unpack(tm, tvs, Some s_ty)
                                       | _ -> unpack(tm, tvs, Some ty))
         | And ([tm], _)   -> unpack(tm, tvs, o_ty)
	 | And (tms, a) ->
           (let real_tms = filter (fn tm -> ~(anyTerm? tm)) tms in
              case if real_tms = [] then tms else real_tms of
                | [] -> (case o_ty of
                           | Some ty -> (tvs, ty, And (real_tms, a))
                           | None -> fail("Untyped term: "^printTerm t))
                | [tm]  -> unpack(tm, tvs, o_ty)
                | tm :: r_tms ->
                  case o_ty of
                    | Some ty -> (tvs, ty, And (real_tms, a))
                    | None ->
                  let (tvs, ty, u_tm) = unpack(tm, tvs, o_ty) in
                  (tvs, ty,
                   And (tm :: map termInnerTerm r_tms, a)))
	 | _ -> (tvs,
                 case o_ty of
                   | Some ty -> ty
                   | None -> termType t,
                 t)
   in
   let (tvs, ty, tm) = unpack(t, [], None) in
   % let _ = if embed? And tm then writeLine("unpack:\n"^printTerm t^"\n"^printTerm tm) else () in
   (tvs, ty, tm)

 op [b] termTyVars (tm : ATerm b) : TyVars  =
   case tm of
     | Pi (tvs, _, _) -> tvs
     | And _ -> fail ("termTyVars: Trying to extract type vars from an And of terms.")
     | _ -> []

 % FIXME: termType should never be used: it will fail if an applied
 % function has a defined type (like Bijection) that cannot be
 % understood in an application without looking at the type definition
 op [b] termType (term : ATerm b) : AType b =
   case term of
     | Apply      (t1,t2,   _) -> (case termType t1 of
				     | Arrow(dom,rng,_) -> rng
                                     | Subtype(Arrow(dom,rng,_),_,_) -> rng
				     | _ -> System.fail ("Cannot extract type of application:\n"
							 ^ printTerm term))
     | ApplyN     ([t1,t2], _) -> (case termType t1 of
				     | Arrow(dom,rng,_) -> rng
				     | _ -> System.fail ("Cannot extract type of application "
							 ^ printTerm term))

     | Record     (fields,  a)              -> Product (map (fn (id, t) -> (id, termType t)) fields, a)
     | Bind       (_,_,_,   a)              -> Boolean a
     | Let        (_,term,  _)              -> termType term
     | LetRec     (_,term,  _)              -> termType term
     | Var        ((_,ty), _)               -> ty
     | Fun        (_,ty,   _)               -> ty
     | The        ((_,ty),_,_)              -> ty
     | Lambda     ([(pat,_,body)], a)       -> Arrow(patternType pat, termType body, a)
     | Lambda     (Cons((pat,_,body),_), a) ->
       let dom = case pat of
                   | RestrictedPat(p, t, a) -> patternType p
                   | _ -> patternType pat
       in Arrow(dom, termType body, a)
     | Lambda     ([],                   _) -> System.fail "termType: Ill formed lambda abstraction"
     | IfThenElse (_,t2,t3, _)              -> termType t2
     | Seq        (tms,     a)              -> if tms = []
                                                then Product([],a)
                                                else termType(last tms)
     | TypedTerm  (_,   s,  _)              -> s
     | Pi         (tvs, t,  a)              -> Pi (tvs, termType t, a) 
     | And        (tms,     a)              -> maybeAndType (map termType tms,  a)
     | Any                  a               -> Any a
     | mystery -> fail ("\n No match in termType with: " ^ (anyToString mystery) ^ "\n")

 op [a] maybeTermType(term: ATerm a): Option(AType a) =
   case term of
     | Apply      (t1,t2,   _)  -> (case maybeTermType t1 of
				     | Some(Arrow(dom,rng,_)) ->
                                       (case rng of
                                         | MetaTyVar(tv,_) -> 
                                           let {name=_,uniqueId=_,link} = ! tv in
                                           (case link
                                              of None -> (
                                                          Some rng)
                                               | _ -> Some rng)
                                         | _ -> Some rng)
                                     | Some(Subtype(Arrow(dom,rng,_),_,_)) -> Some rng
				     | _ -> None)
     | ApplyN     ([t1,t2], _)  -> (case maybeTermType t1 of
				     | Some(Arrow(dom,rng,_)) ->
                                       % let _ = writeLine("tt2*: "^printTerm term^"\n"^anyToString t1) in
                                       (case rng of
                                         | MetaTyVar(tv,_) -> 
                                           let {name=_,uniqueId=_,link} = ! tv in
                                           (case link
                                              of None -> (writeLine("tt*: "^printTerm term^"\n"^anyToString t2);
                                                          Some rng)
                                               | _ -> Some rng)
                                         | _ -> Some rng)
				     | _ -> None)

     | Record     (fields,  a)  ->
       (case foldr (fn ((id, t), result) ->
                     case result of
                       | None -> None
                       | Some fld_prs ->
                     case maybeTermType t of
                       | None -> None
                       | Some ty -> Some((id, ty) :: fld_prs))
              (Some []) fields of
         | None -> None
         | Some fld_prs -> Some(Product (fld_prs, a)))
     | Bind       (_,_,_,   a) -> Some(Boolean a)
     | Let        (_,term,  _) -> maybeTermType term
     | LetRec     (_,term,  _) -> maybeTermType term
     | Var        ((_,ty), _)  -> Some ty
     | Fun        (_,ty,   _)  -> Some ty
     | The        ((_,ty),_,_) -> Some ty
     | Lambda([(pat,_,body)], a) ->
       (case maybeTermType body of
          | None -> None
          | Some body_ty -> Some(Arrow(patternType pat, body_ty, a)))
     | Lambda((pat,_,body) :: _, a) ->
       let dom = case pat of
                   | RestrictedPat(p, t, a) -> patternType p
                   | _ -> patternType pat
       in
       (case maybeTermType body of
          | None -> None
          | Some body_ty -> Some(Arrow(dom, body_ty, a)))
     | Lambda     ([],_) -> None
     | IfThenElse (_,t2,t3, _) -> maybeTermType t2
     | Seq        ([],      a) -> Some (Product ([], a))
     | Seq        (tms,     _) -> maybeTermType(last tms)
     | TypedTerm  (_,   s,  _) -> Some s
     | Pi         (tvs, t,  a) ->
       (case maybeTermType t of
          | None -> None
          | Some t_ty -> Some(Pi (tvs, t_ty, a))) 
     | And        (tms,     a) ->
       let tys = mapPartial maybeTermType tms in
       if tys = [] then None
         else Some(maybeAndType (tys,  a))
     | _ -> None

 op [b] termInnerTerm (tm : ATerm b) : ATerm b =
   case tm of
     | Pi (_, tm, _) -> termInnerTerm tm
     | And (tm::r,pos) ->
       if embed? Transform tm
         then termInnerTerm(And(r, pos))
         else termInnerTerm tm
     | TypedTerm (tm, _, _) -> termInnerTerm tm
     | _                     -> tm

 op [a] innerTerms(tm: ATerm a): List (ATerm a) =
   case tm of
     | Pi         (_, tm, _) -> innerTerms tm
     | And        (tms,_)    -> foldl (fn (rtms,tm) -> rtms ++ innerTerms tm) [] tms
     | TypedTerm (tm, _, _)  -> innerTerms tm
    %| Any        _          -> []
     | _                     -> [tm]

 op [a] numTerms(tm: ATerm a): Nat = length (unpackTypedTerms tm)

 % Given a term, extract a three tuple of
 %  1. A list of the quantified type variables.
 %  2. The type of the term.
 %  3. The body of the term.
 % In the case where the term is the conjunction (with And) of a number
 % of terms -- which can happen in the case where a refine def is used,
 % then this will return just the first triple of type variables * type * body,
 % as returned by `unpackTypedTerms`.
 op [a] unpackFirstTerm(t: ATerm a): TyVars * AType a * ATerm a =
   %let (tvs, ty, tm) = unpackTerm t in
   let ((tvs, ty, tm) :: _) = unpackTypedTerms t in
   (tvs, ty, tm)

 op [a] unpackFirstRealTerm(t: ATerm a): TyVars * AType a * ATerm a =
   %let (tvs, ty, tm) = unpackTerm t in
   let Some(tvs, ty, tm) = List.findLeftmost (fn (_, _, tm) -> ~(embed? Transform tm)) (unpackTypedTerms t) in
   (tvs, ty, tm)

 op [a] refinedTerm(tm: ATerm a, i: Nat): ATerm a =
   let tms = innerTerms tm in
   let len = length tms in
   if len = 0 then tm
     else tms@(max(len - i - 1, 0))            % Do best guess in case previous versions replaced
(*
   if i >= 0 && i < len then tms@(len - i - 1)
     else if len <= 1 then tm
     else fail("Less than "^show (i+1)^" refined terms in\n"^printTerm tm)
*)

 % Given a term, extract a list of three-tuples, each element of which represents
 %  1. A list of the quantified type variables.
 %  2. The type of the term.
 %  3. The body of the term.
 % In the case where the term is the conjunction (with And) of a number
 % of terms -- which can happen in the case where a refine def is used,
 % then the various elements of the list will correspond to the arguments to the And(s).
 op [a] unpackTypedTerms (tm : ATerm a) : List (TyVars * AType a * ATerm a) =
   let 
     def unpackTm (tm: ATerm a, ty: AType a) : List (TyVars * AType a * ATerm a) =
       case tm of
         | Pi (pi_tvs, stm, _) -> 
           foldl (fn (result, (tvs, typ, sstm)) -> result ++ [(pi_tvs ++ tvs, typ, sstm)])
             [] 
             (unpackTm(stm, ty))
         | And ([], pos) -> [([], ty, Any pos)]
         | And (tms, _) -> foldl (fn (result, stm) -> result ++ unpackTm(stm, ty)) [] tms
         | TypedTerm (stm, ty, _) -> unpackTm(stm, ty)
         | _ -> [([], ty, tm)]
   in   
   case tm of
     | Pi (pi_tvs, stm, _) -> 
       foldl (fn (result, (tvs, typ, sstm)) -> result ++ [(pi_tvs ++ tvs, typ, sstm)])
         [] 
         (unpackTypedTerms stm)

     | And (tms, _) ->
       foldl (fn (result, tm) -> result ++ (unpackTypedTerms tm)) [] tms

     | TypedTerm (stm, Pi(pi_tvs, ty, _), _)  ->
       foldl (fn (result, (tvs, typ, sstm)) -> result ++ [(pi_tvs ++ tvs, typ, sstm)])
         [] 
         (unpackTm(stm, ty))

     | TypedTerm (stm, ty, _)  -> unpackTm(stm, ty)

     | _                       -> [([], termType tm, tm)]  %% TODO: Print an error here?  The call to termType can crash, since it doesn't have access to the spec.

 op [a] unpackBasicTerm(tm: ATerm a): TyVars * AType a * ATerm a =
   case tm of
     | Pi (tvs, TypedTerm (tm, ty, _), _) -> (tvs, ty, tm)
     | TypedTerm (tm, ty, _) -> ([], ty, tm)
     | _                      -> ([], Any(termAnn tm), tm)

 op [a] nthRefinement(l: List a, n: Nat | l ~= []): a =
   let len = length l in
   l @ (max (len - n - 1, 0))

 op [a] replaceNthRefinement(l: List a, n: Nat, el: a | l ~= []): List a =
   let len = length l in
   let j   = min (n, len - 1) in  % silently restrict to latest value if index would exceed available entries
   let (pref, _, post) = splitAt(l, len - j - 1) in
   pref ++ (el :: post)

 op [a] unpackNthTerm (tm : ATerm a, n: Nat): TyVars * AType a * ATerm a =
   % let _ = writeLine(printTerm tm) in
   let ty_tms = unpackTypedTerms tm in
   let len = length ty_tms in
   if len = 0 then 
     ([], Any(termAnn tm), tm)
   else 
     let (tvs, ty, tm) = ty_tms @ (max (len - n - 1, 0)) in
     % let _ = writeLine("unpackNthTerm: "^show n^"\n"^printTerm(TypedTerm(tm, ty, termAnn t))^"\n"^printTerm t) in
     (tvs, ty, tm)

 op [a] replaceNthTerm(full_tm: ATerm a, i: Nat, new_tm: ATerm a): ATerm a =
   let tms = innerTerms full_tm in
   maybeMkAndTerm (replaceNthRefinement(tms, i, new_tm), termAnn full_tm)

 op [a] andTerms (tms: List(ATerm a)): List(ATerm a) =
   foldr (fn (tm, result) ->
            case tm of
              | And(s_tms, _) -> andTerms s_tms ++ result
              | _ -> tm :: result)
     [] tms

 op [a] mkAnd(tms: List(ATerm a) | tms ~= []): ATerm a =
   case tms of
     | [t] -> t
     | t::_ -> And(tms, termAnn t)

% op equalTerm?          : [a,b] ATerm    a * ATerm    b -> Bool

 op [a] flattenAnds(tm: ATerm a): ATerm a =
   let result =
       case tm of
         | And(tms, a) -> And(andTerms (map flattenAnds tms), a)
         | Pi(tvs, tm, a) -> Pi(tvs, flattenAnds tm, a)
         | TypedTerm(tm, ty, a) -> TypedTerm(flattenAnds tm, ty, a)
         | _ -> tm
   in
   % let _ = writeLine("fla:\n"^printTerm tm^"\n -->"^printTerm result) in
   result

 % Return true iff tm is a variable
 op [a] isVar? (tm: ATerm a) : Bool =
   case tm of | Var _ -> true | _ -> false


 % Return the (head, args) of a curried application head arg1 ... argn
 op [a] unpackApplication (tm: ATerm a) : ATerm a * List (ATerm a) =
   case tm of
     | Apply (t1, t2, _) ->
       let (head, args) = unpackApplication t1 in
       (head, args ++ [t2])
     | _ -> (tm, [])


 %%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%
 %%%                Pattern components
 %%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%

 op [b] patternType (pat : APattern b) : AType b =
   case pat of
     | AliasPat     (p1,_,    _) -> patternType p1
     | VarPat       ((_,s),   _) -> s
     | EmbedPat     (_,_,s,   _) -> s
     | RecordPat    (fields,  a) -> Product (map (fn (id, p) -> (id, patternType p)) fields, a)
     | WildPat      (ty,     _) -> ty
     | BoolPat      (_,       a) -> Boolean a
     | NatPat       (n,       a) -> mkABase  (Qualified ("Nat",     "Nat"),     [], a)
     | StringPat    (_,       a) -> mkABase  (Qualified ("String",  "String"),  [], a)
     | CharPat      (_,       a) -> mkABase  (Qualified ("Char",    "Char"),    [], a)
     | QuotientPat  (_, qid, tys, a) -> mkABase (qid, tys, a)
     | RestrictedPat(p, t,    a) ->
       Subtype(patternType p,Lambda([(p,mkTrueA a,t)],a),a)
     | TypedPat     (_, ty,  _) -> ty

 op [a] tyVarsInPattern (pattern : APattern a) : TyVars =
  let
    def tvsInTerm    tvs trm = (trm, tvs)
    def tvsInPattern tvs pat = (pat, tvs)
    def tvsInType    tvs typ =
      (typ,
       case typ of 
         | TyVar(tv, _) -> 
           if tv in? tvs then
             tvs
           else
             tvs ++ [tv] 
         | _ -> tvs)
  in
  let tsp = (tvsInTerm, tvsInType, tvsInPattern) in
  let (_, tvs) = mapAccumPattern tsp [] pattern in
  tvs

 op [a] deRestrict (p: APattern a): APattern a =
   case p of
     | RestrictedPat(p,_,_) -> deRestrict p
     | _ -> p

 % Find all the RestrictedPat terms in a pattern
 op [a] getAllPatternGuards (patt: APattern a) : List (ATerm a) =
   let
     def do_term gds trm = (trm, gds)
     def do_type gds typ = (typ, gds)
     def do_pat  gds pat =
       (pat,
        case pat of
          | RestrictedPat (_, trm, _) -> trm::gds
          | _ -> gds)
   in
   let (_, rev_gds) = mapAccumPattern (do_term, do_type, do_pat) [] patt in
   reverse rev_gds
   
 % mapAccum is like map, but threads an accumulator through. 
 op [acc,a,b] mapAccum(f: acc -> a ->  (b*acc))(accum:acc)(xs: List a):(List b * acc) =
    case xs of
      | [] -> ([],accum)
      | y::ys -> let (y',acc') = f accum y in
                 let (ys',acc'') = mapAccum f acc'  ys
                 in (y' :: ys', acc'')

 %% "TSP" stands for "term, sort, pattern"  (Now "sort" has been changed to "type".)
 type TSP_MapAccums (accum,b) = (accum -> ATerm    b -> (ATerm    b * accum)) *
                                (accum -> AType    b -> (AType    b * accum)) *
                                (accum -> APattern b -> (APattern b * accum))

 op mapAccumTerm    : [accum,b] TSP_MapAccums (accum,b) -> accum -> ATerm    b -> (ATerm    b * accum)
 op mapAccumType    : [accum,b] TSP_MapAccums (accum,b) -> accum -> AType    b -> (AType    b * accum)
 op mapAccumPattern : [accum,b] TSP_MapAccums (accum, b) -> accum -> APattern b -> (APattern b * accum)
 op [accum,b] mapAccumSLst (accum: accum)
                           (tsp: TSP_MapAccums (accum,b))
                           (tys: List(AType b))
                : (List(AType b) * accum) =
   case tys of
     | [] -> ([],accum)
     | sty::rtys ->
       let (sty',  accum')  = mapAccumType tsp accum sty in
       let (rtys', accum'') = mapAccumSLst accum' tsp rtys in
       (sty'::rtys', accum'')

 def mapAccumTerm  (tsp as (term_map,_,_)) accum term =
   %%
   %% traversal of term with post-order applications of term_map
   %%
   %% i.e. recursively apply term_map to result of mapping over term
   %%
   %% i.e. term will be revised using term_map on its components,
   %% then term_map will be applied to the revised term.
   %%
   let

     def mapT accum (tsp, term) =
       case term of

	 | Apply (t1, t2, a) ->
	   let (newT1, accum')  = mapAccumRec accum  t1 in
	   let (newT2, accum'') = mapAccumRec accum' t2 in
             (Apply (newT1, newT2, a),accum'')

	 | ApplyN (terms, a) ->
	   let (newTerms,accum') = mapAccum mapAccumRec accum terms in
	     (ApplyN (newTerms, a),accum')

	 | Record (row, a) ->
	   let (newRow,accum') = mapAccum 
              (fn acc -> fn (id,trm) ->
                let (trm',acc') = mapAccumRec acc trm in  ((id, trm'),acc')) 
             accum row 
           in (Record (newRow, a),accum')

	 | Bind (bnd, vars, trm, a) ->
	   let (newVars,accum') = 
               mapAccum (fn accum -> fn (id, ty) ->
                           let (ty',accum') = mapAccumType tsp accum ty
                           in ((id, ty'), accum')) 
                        accum vars
           in
	   let (newTrm,accum'') = mapAccumRec accum' trm 
           in (Bind (bnd, newVars, newTrm, a),accum'')


	 | The (var as (id,ty), trm, a) ->
           let (ty',accum') = mapAccumType tsp accum ty in
	   let newVar = (id, ty') in
	   let (newTrm,accum'') = mapAccumRec accum' trm in
	      (The (newVar, newTrm, a),accum'')

	 | Let (decls, bdy, a) ->
	   let (newDecls,accum') =
                  mapAccum (fn accum -> fn (pat, trm) ->
                              let (pat',accum') = mapAccumPattern tsp accum pat in
                              let (trm',accum'') = mapAccumRec accum' trm in
                              ((pat',trm'),accum''))
                  accum decls
	   in
	   let (newBdy,accum'') = mapAccumRec accum' bdy in
	     (Let (newDecls, newBdy, a),accum'')

	 | LetRec (decls, bdy, a) ->
	   let (newDecls,accum') = 
                 mapAccum (fn accum -> fn ((id, ty), trm) ->
                             let (ty',accum') = mapAccumType tsp accum ty in
                             let (trm',accum'') = mapAccumRec accum' trm in
                                 (((id,ty'),trm'),accum''))
                          accum decls
	   in
	   let (newBdy,accum'') = mapAccumRec accum' bdy in
	     (LetRec (newDecls, newBdy, a),accum'')

	 | Var ((id, ty), a) ->
	   let (newTy,accum') = mapAccumType tsp accum ty in
	     (Var ((id, newTy), a),accum')

	 | Fun (f, ty, a) ->
	   let (newTy,accum') = mapAccumType tsp accum ty in
	     (Fun (f, newTy, a),accum')

	 | Lambda (match, a) ->
	   let (newMatch,accum') = mapAccum 
                 (fn accum -> fn (pat, cond, trm)->
                    let (pat',accum') = mapAccumPattern tsp accum pat in
                    let (cond',accum'') = mapAccumRec  accum' cond in
                    let (trm',accum''') = mapAccumRec accum'' trm in
                    ((pat',cond',trm'),accum'''))
                 accum match
	   in (Lambda (newMatch, a),accum')

	 | IfThenElse (t1, t2, t3, a) ->
	   let (newT1,accum') = mapAccumRec accum t1 in
	   let (newT2,accum'') = mapAccumRec accum' t2  in
	   let (newT3,accum''') = mapAccumRec accum'' t3 in
	     (IfThenElse (newT1, newT2, newT3, a),accum''')

	 | Seq (terms, a) ->
	   let (newTerms,accum') = mapAccum mapAccumRec accum terms in
	     (Seq (newTerms, a),accum')

	 | TypedTerm (trm, ty, a) ->
	   let (newTrm,accum') = mapAccumRec accum trm in
	   let (newTy,accum'') = mapAccumType tsp accum' ty in
	     (TypedTerm (newTrm, newTy, a),accum'')

         | Pi  (tvs, t, a) -> 
           let (t',accum') = mapAccumRec accum t in
             (Pi (tvs, t',   a),accum') % TODO: what if map alters vars??

         | And (tms, a)    -> 
           let (tms',accum') = mapAccum mapAccumRec accum tms
           in (maybeMkAndTerm (tms', a),accum')
         | _           -> (term,accum)

     def mapAccumRec accum term =
       %% apply map to leaves, then apply map to result
       let (term', accum') = mapT accum (tsp, term) in % Recursively apply map to subterms
       let (term'',accum'') = term_map accum' term' in % Apply map to top-level term
       % We do the equality check to reduce space.
       if (term'' = term) then (term,accum'') else (term'',accum'') % term_map accum' term'

   in
     mapAccumRec accum term

 op [accum,b] mapAccumType ((tsp as (_, type_map, _)) : TSP_MapAccums (accum,b))
                           (accum : accum)
                           (ty : AType b) : (AType b * accum) =
   let

     %% Written with explicit parameter passing to avoid closure creation
     def mapS accum (tsp, type_map, ty) =
       case ty of

	 | Arrow (s1, s2, a) ->
	   let (newS1,accum') = mapAccumRec accum (tsp, type_map, s1) in
	   let (newS2,accum'') = mapAccumRec accum' (tsp, type_map, s2) in
	     (Arrow (newS1, newS2, a),accum'')
	   
	 | Product (row, a) ->
	   let (newRow,accum') = mapAccumSRow accum (tsp, type_map, row) in
	     (Product (newRow, a),accum')
	     
	 | CoProduct (row, a) ->
	   let (newRow,accum') = mapAccumSRowOpt accum (tsp, type_map, row) in
	     (CoProduct (newRow, a),accum')
	       
	 | Quotient (super_type, trm, a) ->
	   let (newSty,accum') = mapAccumRec accum (tsp, type_map, super_type) in
	   let (newTrm,accum'') =  mapAccumTerm tsp accum' trm in
	     (Quotient (newSty, newTrm, a),accum'')
		 
	 | Subtype (sub_type, trm, a) ->
	   let (newSty,accum') = mapAccumRec accum (tsp, type_map, sub_type) in
	   let (newTrm,accum'') =  mapAccumTerm tsp accum' trm in
	     (Subtype (newSty, newTrm, a),accum'')
		   
	 | Base (qid, tys, a) ->
	   let (newTys,accum') = mapAccumSLst accum tsp tys in
	     (Base (qid, newTys, a),accum')
		     
	 | Boolean _ -> (ty,accum)
		     
       % | TyVar ??
		     
	 | MetaTyVar (mtv, pos) ->
	   let {name,uniqueId,link} = ! mtv in
	   (case link of
	      | None -> (ty,accum)
	      | Some sty ->
	        let (newsty,accum') = mapAccumRec accum (tsp, type_map, sty) in
	          (MetaTyVar(Ref {name     = name,
	        		 uniqueId = uniqueId,
	        		 link     = Some newsty},
	        	    pos), accum'))

         | Pi  (tvs, ty, a) -> 
              let (ty',accum') = mapAccumRec accum (tsp, type_map, ty)
              in (Pi (tvs,ty' , a), accum')  % TODO: what if map alters vars?

         | And (tys,     a) -> 
             let (tys',accum') = 
               mapAccum (fn accum -> fn ty -> mapAccumRec accum (tsp, type_map, ty)) accum tys
             in (maybeAndType(tys', a), accum')
         | Any  _            -> (ty,accum)

	 | _ -> (ty,accum)

     def mapAccumSRowOpt accum (tsp, type_map, row) =
       case row of
	 | [] -> ([],accum)
	 | (id,optty)::rrow -> 
           let (optty',accum') = mapAccumRecOpt accum (tsp, type_map, optty) in
           let (rrow',accum'') = mapAccumSRowOpt accum' (tsp, type_map, rrow) in
           (Cons ((id, optty'),rrow'),accum'')

     def mapAccumSRow accum (tsp, type_map, row) =
       case row of
	 | [] -> ([],accum)
	 | (id,sty)::rrow -> 
           let (sty',accum') =  mapAccumRec accum (tsp, type_map, sty) in
           let (rrow',accum'') = mapAccumSRow accum (tsp, type_map, rrow) in
           (Cons ((id, sty'),rrow'),accum'')

     def mapAccumRecOpt accum (tsp, type_map, opt_type) =
       case opt_type of
	 | None      -> (None,accum)
	 | Some sty -> 
           let (sty',accum') = mapAccumRec accum (tsp, type_map, sty) in
           (Some sty',accum')
           

     def mapAccumRec accum (tsp, type_map, ty) =
       %% apply map to leaves, then apply map to result
       let (ty',accum') = (mapS accum (tsp, type_map, ty)) in
       let (ty'',accum'') = type_map accum' ty' 
       % We do the equality check to reduce space.
       in if ty'' = ty then (ty,accum'') else (ty'',accum'')
   in
     mapAccumRec accum (tsp, type_map, ty)

 op [accum,b] mapAccumPattern ((tsp as (_, _, pattern_map)) : TSP_MapAccums (accum, b))
                              (accum : accum)
                              (pattern : APattern b) : (APattern b * accum) =
   let

     def mapP accum (tsp, pattern) =
       case pattern of

	 | AliasPat (p1, p2, a) ->
           let (newP1,accum') = mapAccumRec accum p1 in
	   let (newP2,accum'') = mapAccumRec accum' p2 in
	     (AliasPat (newP1, newP2, a),accum'')
	   
	 | VarPat ((v, ty), a) ->
	   let (newTy,accum') = mapAccumType tsp accum ty in
	     (VarPat ((v, newTy), a),accum')
	     
	 | EmbedPat (id, Some pat, ty, a) ->
	   let (newPat,accum') = mapAccumRec accum pat in
	   let (newTy,accum'') = mapAccumType tsp accum' ty in
	     (EmbedPat (id, Some newPat, newTy, a),accum'')
	       
	 | EmbedPat (id, None, ty, a) ->
	   let (newTy,accum') = mapAccumType tsp accum ty in
	     (EmbedPat (id, None, newTy, a),accum')
		 
	 | RecordPat (fields, a) ->
	   let (newFields,accum') = mapAccum 
               (fn accum -> fn (id, p) -> 
                  let (p',accum') = mapAccumRec accum p in ((id, p'),accum')) accum fields in
	     (RecordPat (newFields, a),accum')
		   
	 | WildPat (ty, a) ->
	   let (newTy,accum') = mapAccumType tsp accum ty in
	     (WildPat (newTy, a),accum')
		     
	 | QuotientPat (pat, qid, tys, a) ->
	   let (newPat,accum') = mapAccumRec accum pat in
           let (newTys,accum') = mapAccumSLst accum' tsp tys in
	     (QuotientPat (newPat, qid, newTys, a),accum')
			 
	 | RestrictedPat (pat, trm, a) ->
	   let (newPat,accum') = mapAccumRec accum pat in
	   let (newTrm,accum'') = mapAccumTerm tsp accum' trm in
	     (RestrictedPat (newPat, newTrm, a),accum'')
			 
	 | TypedPat (pat, ty, a) ->
	   let (newPat,accum') = mapAccumRec accum pat in
	   let (newTy,accum'') = mapAccumType tsp accum' ty in
	     (TypedPat (newPat, newTy, a),accum'')
			   
       % | BoolPat   ??
       % | NatPat    ??
       % | StringPat ??
       % | CharPat   ??
	     
	 | _ -> (pattern,accum)

     def mapAccumRec accum pat =
       %% apply map to leaves, then apply map to result
       let (pat',accum') = mapP accum (tsp, pat) in
       let (pat'',accum'') =  pattern_map accum' pat' 
       % We do the equality check to reduce space.
       in if (pat'' = pat) then (pat,accum'') else (pat'',accum'')

   in
     mapAccumRec accum pattern

 %%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%
 %%%                Recursive TSP Mappings
 %%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%
 %%% "TSP" means "Term, Type, Pattern" (Used to be "Term, Sort, Pattern".)

 type TSP_Maps b = (ATerm    b -> ATerm    b) *
                   (AType    b -> AType    b) *
                   (APattern b -> APattern b)


(*
   % GMK: The map* functions can be defined in terms of mapAccum*, as shown below. 
   % However, it appears that there is a small performance cost (empirically observed 
   % to be about 5%, when building specware itself with this definition) so we instead
   % use the direct definition.


 op [a,b,atype] add_acc(f:a->b)(acc:atype)(x:a):(b*atype) = (f x, acc)

 
 op [b] mapTerm (tsp as (term_map,type_map,pat_map))(t:ATerm b):(ATerm b) =
    let (val,_) = mapAccumTerm (add_acc term_map, add_acc type_map, add_acc pat_map) () t
   in val

 op [b] mapType (tsp as (term_map,type_map,pat_map))(t:AType b):(AType b) =
    let (val,_) = mapAccumType (add_acc term_map, add_acc type_map, add_acc pat_map) () t
   in val

 op [b] mapPattern (tsp as (term_map,type_map,pat_map))(t:APattern b):(APattern b) =
    let (val,_) = mapAccumPattern (add_acc term_map, add_acc type_map, add_acc pat_map) () t
   in val
*)

 op [b] mapTerm ((tsp as (term_map,_,_)) : TSP_Maps b) (term : ATerm b) : ATerm b =
   %%
   %% traversal of term with post-order applications of term_map
   %%
   %% i.e. recursively apply term_map to result of mapping over term
   %%
   %% i.e. term will be revised using term_map on its components,
   %% then term_map will be applied to the revised term.
   %%
   let

     def mapT (tsp, term) =
       case term of

         | Apply (t1, t2, a) ->
           let newT1 = mapRec t1 in
           let newT2 = mapRec t2 in
           if newT1 = t1 && newT2 = t2 then
             term
           else
             Apply (newT1, newT2, a)

         | ApplyN (terms, a) ->
           let newTerms = map mapRec terms in
           if newTerms = terms then
             term
           else
             ApplyN (newTerms, a)

         | Record (row, a) ->
           let newRow = map (fn (id,trm) -> (id, mapRec trm)) row in
           if newRow = row then
             term
           else
             Record (newRow, a)

         | Bind (bnd, vars, trm, a) ->
           let newVars = mapVars tsp vars in
           let newTrm = mapRec trm in
           if newVars = vars && newTrm = trm then
             term
           else
             Bind (bnd, newVars, newTrm, a)

         | The (var as (id,ty), trm, a) ->
           let newVar = (id, mapType tsp ty) in
           let newTrm = mapRec trm in
           if newVar = var && newTrm = trm then
             term
           else
             The (newVar, newTrm, a)

         | Let (decls, bdy, a) ->
           let newDecls = map (fn (pat, trm) ->
        		       (mapPattern tsp pat,
        			mapRec trm))
                              decls
           in
           let newBdy = mapRec bdy in
           if newDecls = decls && newBdy = bdy then
             term
           else
             Let (newDecls, newBdy, a)

         | LetRec (decls, bdy, a) ->
           let newDecls = map (fn ((id, ty), trm) ->
        		       ((id, mapType tsp ty),
        			mapRec trm))
                              decls
           in
           let newBdy = mapRec bdy in
           if newDecls = decls && newBdy = bdy then
             term
           else
             LetRec (newDecls, newBdy, a)

         | Var ((id, ty), a) ->
           let newTy = mapType tsp ty in
           if newTy = ty then
             term
           else
             Var ((id, newTy), a)

         | Fun (f, ty, a) ->
           let newTy = mapType tsp ty in
           if newTy = ty then
             term
           else
             Fun (f, newTy, a)

         | Lambda (match, a) ->
           let newMatch = map (fn (pat, cond, trm)->
        		       (mapPattern tsp pat,
        			mapRec cond,
        			mapRec trm))
                              match
           in
           if newMatch = match then
             term
           else
             Lambda (newMatch, a)

         | IfThenElse (t1, t2, t3, a) ->
           let newT1 = mapRec t1 in
           let newT2 = mapRec t2 in
           let newT3 = mapRec t3 in
           if newT1 = t1 && newT2 = t2 && newT3 = t3 then
             term
           else
             IfThenElse (newT1, newT2, newT3, a)

         | Seq (terms, a) ->
           let newTerms = map mapRec terms in
           if newTerms = terms then
             term
           else
             Seq (newTerms, a)

         | TypedTerm (trm, ty, a) ->
           let newTrm = mapRec trm in
           let newTy = mapType tsp ty in
           if newTrm = trm && newTy = ty then
             term
           else
             TypedTerm (newTrm, newTy, a)

         | Pi  (tvs, t, a) -> Pi (tvs, mapRec t,   a) % TODO: what if map alters vars??

         | And (tms, a)    -> maybeMkAndTerm (map mapRec tms, a)

         | _           -> term

     def mapRec term =
       %% apply map to leaves, then apply map to result
       term_map (mapT (tsp, term))

   in
     mapRec term

 op [b] mapVar (tsp: TSP_Maps b) ((id, ty) : AVar b): AVar b =
   (id, mapType tsp ty)

 op [b] mapVars (tsp: TSP_Maps b) (vars : List (AVar b)): List (AVar b) =
   map (mapVar tsp) vars

 op [b] mapSLst (tsp: TSP_Maps b) (tys: List(AType b)): List(AType b) =
   case tys of
     | [] -> []
     | sty :: rtys -> (mapType tsp sty) :: (mapSLst tsp rtys)


 def mapType (tsp as (_, type_map, _)) ty =
   let
     %% Written with explicit parameter passing to avoid closure creation
     def mapS (tsp, type_map, ty) =
       case ty of

         | Arrow (s1, s2, a) ->
           let newS1 = mapRec (tsp, type_map, s1) in
           let newS2 = mapRec (tsp, type_map, s2) in
           if newS1 = s1 && newS2 = s2 then
             ty
           else
             Arrow (newS1, newS2, a)
	   
         | Product (row, a) ->
           let newRow = mapSRow (tsp, type_map, row) in
           if newRow = row then
             ty
           else
             Product (newRow, a)
	     
         | CoProduct (row, a) ->
           let newRow = mapSRowOpt (tsp, type_map, row) in
           if newRow = row then
             ty
           else
             CoProduct (newRow, a)
	       
         | Quotient (super_type, trm, a) ->
           let newSty = mapRec (tsp, type_map, super_type) in
           let newTrm =  mapTerm tsp trm in
           if newSty = super_type && newTrm = trm then
             ty
           else
             Quotient (newSty, newTrm, a)
		 
         | Subtype (sub_type, trm, a) ->
           let newSty = mapRec (tsp, type_map, sub_type) in
           let newTrm =  mapTerm tsp trm in
           if newSty = sub_type && newTrm = trm then
             ty
           else
             Subtype (newSty, newTrm, a)
		   
         | Base (qid, tys, a) ->
           let newTys = mapSLst tsp tys in
           if newTys = tys then
             ty
           else
             Base (qid, newTys, a)
		     
         | Boolean _ -> ty
		     
       % | TyVar ??
		     
         | MetaTyVar (mtv, pos) ->
           let {name,uniqueId,link} = ! mtv in
           (case link of
              | None -> ty
              | Some sty ->
                let newsty = mapRec (tsp, type_map, sty) in
        	if newsty = sty % || equalType?(newsty, sty)
                  then ty
        	else
        	   MetaTyVar(Ref {name     = name,
        	         	 uniqueId = uniqueId,
        	         	 link     = Some newsty},
        	             pos))

         | Pi  (tvs, ty, a) -> Pi (tvs, mapRec (tsp, type_map, ty), a)  % TODO: what if map alters vars?

         | And (tys,     a) -> maybeAndType (map (fn ty -> mapRec (tsp, type_map, ty)) tys, a)

         | Any  _            -> ty

         | _ -> ty

     def mapSRowOpt (tsp, type_map, row) =
       case row of
         | [] -> []
         | (id,optty)::rrow -> Cons ((id, mapRecOpt (tsp, type_map, optty)),
        			      mapSRowOpt (tsp, type_map, rrow))

     def mapSRow (tsp, type_map, row) =
       case row of
         | [] -> []
         | (id,sty)::rrow -> Cons ((id, mapRec (tsp, type_map, sty)),
        			    mapSRow (tsp, type_map, rrow))

     def mapRecOpt (tsp, type_map, opt_type) =
       case opt_type of
         | None      -> None
         | Some sty -> Some (mapRec (tsp, type_map, sty))

     def mapRec (tsp, type_map, ty) =
       %% apply map to leaves, then apply map to result
       type_map (mapS (tsp, type_map, ty))

   in
     mapRec (tsp, type_map, ty)

 op [b] mapPattern ((tsp as (_, _, pattern_map)) : TSP_Maps b) (pattern : APattern b) : APattern b =
   let

     def mapP (tsp, pattern) =
       case pattern of

         | AliasPat (p1, p2, a) ->
           let newP1 = mapRec p1 in
           let newP2 = mapRec p2 in
           if newP1 = p1 && newP2 = p2 then
             pattern
           else
             AliasPat (newP1, newP2, a)
	   
         | VarPat ((v, ty), a) ->
           let newTy = mapType tsp ty in
           if newTy = ty then
             pattern
           else
             VarPat ((v, newTy), a)
	     
         | EmbedPat (id, Some pat, ty, a) ->
           let newPat = mapRec pat in
           let newTy = mapType tsp ty in
           if newPat = pat && newTy = ty then
             pattern
           else
             EmbedPat (id, Some newPat, newTy, a)
	       
         | EmbedPat (id, None, ty, a) ->
           let newTy = mapType tsp ty in
           if newTy = ty then
             pattern
           else
             EmbedPat (id, None, newTy, a)
		 
         | RecordPat (fields, a) ->
           let newFields = map (fn (id, p) -> (id, mapRec p)) fields in
           if newFields = fields then
             pattern
           else
             RecordPat (newFields, a)
		   
         | WildPat (ty, a) ->
           let newTy = mapType tsp ty in
           if newTy = ty then
             pattern
           else
             WildPat (newTy, a)
		     
         | QuotientPat (pat, qid, tys, a) ->
           let newPat = mapRec pat in
           let newTys = mapSLst tsp tys in
           if newPat = pat && tys = newTys then
             pattern
           else
             QuotientPat (newPat, qid, newTys, a)
			 
         | RestrictedPat (pat, trm, a) ->
           let newPat = mapRec pat in
           let newTrm = mapTerm tsp trm in
           if newPat = pat && newTrm = trm then
             pattern
           else
             RestrictedPat (newPat, newTrm, a)
			 
         | TypedPat (pat, ty, a) ->
           let newPat = mapRec pat in
           let newTy = mapType tsp ty in
           if newPat = pat && newTy = ty then
             pattern
           else
             TypedPat (newPat, newTy, a)
			   
       % | BoolPat   ??
       % | NatPat    ??
       % | StringPat ??
       % | CharPat   ??
	     
         | _ -> pattern

     def mapRec pat =
       %% apply map to leaves, then apply map to result
       pattern_map (mapP (tsp, pat))

   in
     mapRec pattern

 %% Like mapTerm but ignores types
 op [a] mapSubTerms (f : (ATerm a -> ATerm a)) (term : ATerm a) : ATerm a =
   let

     def mapT term =
       case term of

	 | Apply (t1, t2, a) ->
	   let newT1 = mapRec t1 in
	   let newT2 = mapRec t2 in
	   if newT1 = t1 && newT2 = t2 then
	     term
	   else
	     Apply (newT1, newT2, a)
	   
	 | ApplyN (terms, a) ->
	   let newTerms = map mapRec terms in
	   if newTerms = terms then
	     term
	   else
	     ApplyN (newTerms, a)
	     
	 | Record (row, a) ->
	   let newRow = map (fn (id,trm) -> (id, mapRec trm)) row in
	   if newRow = row then
	     term
	   else
	     Record(newRow,a)
	       
	 | Bind (bnd, vars, trm, a) ->
	   let newTrm = mapRec trm in
	   if newTrm = trm then
	     term
	   else
	     Bind (bnd, vars, newTrm, a)
		 
	 | The (var, trm, a) ->
	   let newTrm = mapRec trm in
	   if newTrm = trm then
	     term
	   else
	     The (var, newTrm, a)
		 
	 | Let (decls, bdy, a) ->
	   let newDecls = map (fn (pat, trm) -> (mapPat1 pat, mapRec trm)) decls in
	   let newBdy = mapRec bdy in
	   if newDecls = decls && newBdy = bdy then
	     term
	   else
	     Let (newDecls, newBdy, a)
		   
	 | LetRec (decls, bdy, a) ->
	   let newDecls = map (fn ((id, ty), trm) -> ((id, ty), mapRec trm)) decls in
	   let newBdy = mapRec bdy in
	   if newDecls = decls && newBdy = bdy then
	     term
	   else
	     LetRec(newDecls, newBdy, a)
		     
	 | Var _ -> term
	     
	 | Fun _ -> term
		     
	 | Lambda (match, a) ->
	   let newMatch = map (fn (pat, cond, trm)->
			       (mapPat1 pat, mapRec cond, mapRec trm))
	                      match 
	   in
	     if newMatch = match then
	       term
	     else
	       Lambda (newMatch, a)
		       
	 | IfThenElse (t1, t2, t3, a) ->
	   let newT1 = mapRec t1 in
	   let newT2 = mapRec t2 in
	   let newT3 = mapRec t3 in
	   if newT1 = t1 && newT2 = t2 && newT3 = t3 then
	     term
	   else
	     IfThenElse (newT1, newT2, newT3, a)
			 
	 | Seq (terms, a) ->
	   let newTerms = map mapRec terms in
	   if newTerms = terms then
	     term
	   else
	     Seq (newTerms, a)
			   
	 | TypedTerm (trm, ty, a) ->
	   let newTrm = mapRec trm in
	   if newTrm = trm then
	     term
	   else
	     TypedTerm (newTrm, ty, a)
			     
         | Pi  (tvs, t, a) -> Pi (tvs, mapRec t, a)  % TODO: what if map alters vars?

         | And (tms, a)    -> maybeMkAndTerm (map mapT tms, a)

         | _ -> term
			     
     def mapRec term =
       %% apply map to leaves, then apply map to result
       f (mapT term)

     def mapPat1 pat =
       case pat of
	 %% RestrictedPats can only occur at top level
	 | RestrictedPat(spat,tm,a) -> RestrictedPat(spat,mapRec tm,a)
	 | _ -> pat

   in
     mapRec term

  %% Like mapAccumTerm but ignores types
  op [a,b] mapAccumSubTerms (f     : b -> ATerm a -> (ATerm a) * b)
                            (accum : b) 
                            (term  : ATerm a) 
   : (ATerm a) * b =
   let

     def mapT accum term =
       case term of

	 | Apply (t1, t2, a) ->
	   let (newT1, accum) = mapAccumRec accum t1 in
	   let (newT2, accum) = mapAccumRec accum t2 in
           let new_term =
	       if newT1 = t1 && newT2 = t2 then
                 term
               else
                 Apply (newT1, newT2, a)
           in
           (new_term, accum)
	   
	 | ApplyN (terms, a) ->
	   let (new_terms, accum) = 
               foldl (fn ((new_terms, accum), tm) ->
                        let (new_tm, accum) = mapAccumRec accum tm in
                        (new_terms ++ [new_tm], accum))
                     ([], accum)
                     terms
           in
           let new_term =
	       if new_terms = terms then
                 term
               else
                 ApplyN (new_terms, a)
           in
           (new_term, accum)

	 | Record (row, a) ->
	   let (new_row, accum) = 
               foldl (fn ((new_row, accum), (id, tm)) -> 
                        let (new_tm, accum) = mapAccumRec accum tm in
                        (new_row ++ [(id, new_tm)], accum))
                     ([], accum)
                     row 
           in
           let new_term =
	       if new_row = row then
                 term
               else
                 Record (new_row, a)
           in
           (new_term, accum)
	       
	 | Bind (bnd, vars, trm, a) ->
	   let (newTrm, accum) = mapAccumRec accum trm in
           let new_term =
  	       if newTrm = trm then
                 term
               else
                 Bind (bnd, vars, newTrm, a)
           in
           (new_term, accum)

	 | The (var, trm, a) ->
	   let (newTrm, accum) = mapAccumRec accum trm in
           let new_term =
	       if newTrm = trm then
                 term
               else
                 The (var, newTrm, a)
           in
           (new_term, accum)
		 
	 | Let (decls, body, a) ->
	   let (new_decls, accum) = 
               foldl (fn ((new_decls, accum), (pat, tm)) -> 
                        let (new_tm, accum) = mapAccumRec accum tm in
                        (new_decls ++ [(pat, new_tm)], accum))
                     ([], accum)
                     decls 
           in
	   let (new_body, accum) = mapAccumRec accum body in
           let new_term =
	       if new_decls = decls && new_body = body then
                 term
               else
                 Let (new_decls, new_body, a)
           in
           (new_term, accum)

	 | LetRec (decls, body, a) ->
	   let (new_decls, accum) = 
               foldl (fn ((new_decls, accum), (pat, tm)) -> 
                        let (new_tm, accum) = mapAccumRec accum tm in
                        (new_decls ++ [(pat, new_tm)], accum))
                     ([], accum)
                     decls 
           in
	   let (new_body, accum) = mapAccumRec accum body in
           let new_term =
	       if new_decls = decls && new_body = body then
                 term
               else
                 LetRec (new_decls, new_body, a)
           in
           (new_term, accum)
		     
	 | Var _ -> (term, accum)
	     
	 | Fun _ -> (term, accum)
		     
	 | Lambda (match, a) ->
	   let (new_match, accum) = 
               foldl (fn ((new_match, accum), (pat, cond, trm)) ->
                        let (pat,  accum) = mapAccumPat accum pat  in
                        let (cond, accum) = mapAccumRec accum cond in
                        let (body, accum) = mapAccumRec accum trm  in
                        (new_match ++ [(pat, cond, body)],
                         accum))
                     ([], accum)
                     match 
	   in
           let new_term =
               if new_match = match then
                 term
               else
                 Lambda (new_match, a)
           in
           (new_term, accum)
		       
	 | IfThenElse (t1, t2, t3, a) ->
	   let (new_t1, accum) = mapAccumRec accum t1 in
	   let (new_t2, accum) = mapAccumRec accum t2 in
	   let (new_t3, accum) = mapAccumRec accum t3 in
           let new_term =
	       if new_t1 = t1 && new_t2 = t2 && new_t3 = t3 then
                 term
               else
                 IfThenElse (new_t1, new_t2, new_t3, a)
           in
           (new_term, accum)
			 
	 | Seq (terms, a) ->
	   let (new_terms, accum) = 
               foldl (fn ((new_tms, accum), tm) ->
                        let (new_tm, accum) = mapAccumRec accum tm in
                        (new_tms ++ [new_tm], accum))
                     ([], accum) 
                     terms
           in
           let new_term =
	       if new_terms = terms then
                 term
               else
                 Seq (new_terms, a)
           in
           (new_term, accum)
			   
	 | TypedTerm (trm, ty, a) ->
	   let (newTrm, accum) = mapAccumRec accum trm in
           let new_term =
	       if newTrm = trm then
                 term
               else
                 TypedTerm (newTrm, ty, a)
           in
           (new_term, accum)
			     
         | Pi  (tvs, tm, a) -> 
           let (new_tm, accum) = mapAccumRec accum tm in
           (Pi (tvs, new_tm, a), accum)  % TODO: what if map alters vars?

         | And (tms, a) -> 
           let (new_tms, accum) =
               foldl (fn ((new_tms, accum), tm) ->
                        let (new_tm, accum) = mapAccumRec accum tm in
                        (new_tms ++ [new_tm], accum))
                     ([], accum)
                     tms
           in
           (maybeMkAndTerm (new_tms, a), accum)

         | _ -> (term, accum)
			     
     def mapAccumRec accum term =
       %% apply map to leaves, then apply map to result
       let (tm, accum) = mapT accum term in
       f accum tm

     def mapAccumPat accum pat =
       case pat of
	 %% RestrictedPats can only occur at top level
	 | RestrictedPat (spat, tm, a) -> 
           let (new_tm, accum) = mapAccumRec accum tm in
           (RestrictedPat (spat, new_tm, a), accum)
	 | _ ->
           (pat, accum)

   in
     mapAccumRec accum term


op [a] mapType1 (f: AType a -> AType a) (ty: AType a): AType a =
  let rec_ty =
      case ty of
        | Arrow (s1, s2, a) ->
          let newS1 = mapType1 f s1 in
          let newS2 = mapType1 f s2 in
          if newS1 = s1 && newS2 = s2 then ty
          else Arrow (newS1, newS2, a)
        | Product (row, a) ->
          let newRow = map (fn (id, sty) -> (id, mapType1 f sty)) row in
          if newRow = row then ty
          else Product (newRow, a)
        | CoProduct (row, a) ->
          let newRow = map (fn (id, o_sty) -> (id, mapOption (mapType1 f) o_sty)) row in
          if newRow = row then ty
          else CoProduct (newRow, a)
        | Quotient (super_type, trm, a) ->
          let newSty = mapType1 f super_type in
          if newSty = super_type then ty
          else Quotient (newSty, trm, a)
        | Subtype (sub_type, trm, a) ->
          let newSty = mapType1 f sub_type in
          if newSty = sub_type then ty
          else Subtype (newSty, trm, a)
        | Base (qid, tys, a) ->
          let newTys = map (mapType1 f) tys in
          if newTys = tys then ty
          else Base (qid, newTys, a)
        | MetaTyVar (mtv, pos) ->
          let {name,uniqueId,link} = ! mtv in
          (case link of
             | None -> ty
             | Some sty ->
               let newsty = mapType1 f sty in
               if newsty = sty % || equalType?(newsty, sty)
                 then ty
               else
                  MetaTyVar(Ref {name     = name,
                                 uniqueId = uniqueId,
                                 link     = Some newsty},
                            pos))
        | Pi  (tvs, ty, a) -> Pi (tvs, mapType1 f ty, a)  % TODO: what if map alters vars?
        | And (tys,     a) -> maybeAndType (map (fn ty -> mapType1 f ty) tys, a)
        | _ -> ty
  in
  f rec_ty

op[a] mapPattern1 (f: APattern a -> APattern a) (pattern: APattern a): APattern a =
  let rec_pat =
      case pattern of
         | AliasPat (p1, p2, a) ->
           let newP1 = mapPattern1 f p1 in
           let newP2 = mapPattern1 f p2 in
           if newP1 = p1 && newP2 = p2 then pattern
           else AliasPat (newP1, newP2, a)
         | EmbedPat (id, Some pat, ty, a) ->
           let newPat = mapPattern1 f pat in
           if newPat = pat then pattern
           else EmbedPat (id, Some newPat, ty, a)
         | RecordPat (fields, a) ->
           let newFields = map (fn (id, p) -> (id, mapPattern1 f p)) fields in
           if newFields = fields then pattern
           else RecordPat (newFields, a)
         | QuotientPat (pat, qid, tys, a) ->
           let newPat = mapPattern1 f pat in
           if newPat = pat then pattern
           else QuotientPat (newPat, qid, tys, a)
         | RestrictedPat (pat, trm, a) ->
           let newPat = mapPattern1 f pat in
           if newPat = pat then pattern
           else RestrictedPat (newPat, trm, a)
         | TypedPat (pat, ty, a) ->
           let newPat = mapPattern1 f pat in
           if newPat = pat then pattern
           else TypedPat (newPat, ty, a)
         | _ -> pattern
  in
  f rec_pat

 %%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%
 %%%                Recursive Term Search
 %%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%

  op [b] existsSubTerm (pred?:ATerm b -> Bool) (term:ATerm b): Bool
    = existsSubTerm2 true pred? term

  op [b] existsSubTerm2 (descendIntoSubtypes? : Bool) (pred? : ATerm b -> Bool) (term : ATerm b) : Bool =
   pred? term ||
   (case term of

      | Apply       (M, N,     _) -> existsSubTerm2 descendIntoSubtypes? pred? M ||
                                     existsSubTerm2 descendIntoSubtypes? pred? N

      | ApplyN      (Ms,       _) -> exists? (existsSubTerm2 descendIntoSubtypes? pred?) Ms

      | Record      (fields,   _) -> exists? (fn (_,M) ->
                                              existsSubTerm2 descendIntoSubtypes? pred? M) fields

      | Bind        (_,_,M,    _) -> existsSubTerm2 descendIntoSubtypes? pred? M

      | The         (_,M,      _) -> existsSubTerm2 descendIntoSubtypes? pred? M

      | Let         (decls, M, _) -> existsSubTerm2 descendIntoSubtypes? pred? M ||
                                     exists? (fn (p,M) ->
                                              (descendIntoSubtypes?
                                                   && existsSubTermPat pred? p)
                                              || existsSubTerm2 descendIntoSubtypes? pred? M) decls

      | LetRec      (decls, M, _) -> existsSubTerm2 descendIntoSubtypes? pred? M ||
				     exists? (fn (_,M) ->
                                              existsSubTerm2 descendIntoSubtypes? pred? M) decls

      | Var         _             -> false
				     
      | Fun         _             -> false

      | Lambda      (rules,    _) -> exists? (fn (p, c, M) ->
                                                (descendIntoSubtypes?
                                                   && existsSubTermPat pred? p) ||
                                                existsSubTerm2 descendIntoSubtypes? pred? c ||
                                                existsSubTerm2 descendIntoSubtypes? pred? M)
                                            rules

      | IfThenElse  (M, N, P,  _) -> existsSubTerm2 descendIntoSubtypes? pred? M ||
			  	     existsSubTerm2 descendIntoSubtypes? pred? N ||
				     existsSubTerm2 descendIntoSubtypes? pred? P

      | Seq         (Ms,       _) -> exists? (existsSubTerm2 descendIntoSubtypes? pred?) Ms

      | TypedTerm   (M, ty,   _) -> existsSubTerm2 descendIntoSubtypes? pred? M

      %% TODO: What about transform?

      | Pi          (tvs, t,   _) -> descendIntoSubtypes? &&
                                     existsSubTerm2 descendIntoSubtypes? pred? t

      | And         (tms,      _) -> exists? (existsSubTerm2 descendIntoSubtypes? pred?) tms

      %% TODO: What about Any?

      | _  -> false
      )				    

 op [b] existsSubTermPat (pred? : (ATerm b -> Bool)) (pat : APattern b) : Bool =
   case pat of
     | RestrictedPat(_,t,_) -> existsSubTerm pred? t
     | _ -> false

 op [b] existsPattern? (pred? : (APattern b -> Bool)) (pattern : APattern b) : Bool =
   pred? pattern ||
   (case pattern of
     | AliasPat(p1, p2,_) ->
       existsPattern? pred? p1 || existsPattern? pred? p2
     | EmbedPat(id, Some pat,_,_) -> existsPattern? pred? pat
     | RecordPat(fields,_) ->
       exists? (fn (_,p)-> existsPattern? pred? p) fields
     | QuotientPat  (pat,_,_,_) -> existsPattern? pred? pat
     | RestrictedPat(pat,_,_) -> existsPattern? pred? pat
     | TypedPat     (pat,_,_) -> existsPattern? pred? pat
     | _ -> false)

 op [a] existsInType? (pred?: AType a -> Bool) (ty: AType a): Bool =
   pred? ty ||
   (case ty of
      | Base(_, ty_args, _) -> exists? (existsInType? pred?) ty_args
      | Arrow(x,y,_) -> existsInType? pred? x || existsInType? pred? y
      | Product(prs,_) -> exists? (fn (_,f_ty) -> existsInType? pred? f_ty) prs
      | CoProduct(prs,_)  -> exists? (fn (_,o_f_ty) ->
                                       case o_f_ty of
                                         | Some f_ty -> existsInType? pred? f_ty
                                         | None -> false)
                               prs
      | Quotient(x,_,_) -> existsInType? pred? x
      | Subtype(x,_,_) -> existsInType? pred? x
      | MetaTyVar(Ref{link = Some x, name, uniqueId}, _) -> existsInType? pred? x
      | And(tys,_) -> exists? (existsInType? pred?) tys
      | _ -> false)

op [a] existsTypeInPattern? (pred?: AType a -> Bool) (pat: APattern a): Bool =
  existsPattern? (fn p ->
                  case p of
                    | VarPat ((_, ty), _)    -> existsInType? pred? ty
                    | WildPat(ty, _)         -> existsInType? pred? ty
                    | EmbedPat (_, _, ty, _) -> existsInType? pred? ty
                    | TypedPat (_, ty, _)    -> existsInType? pred? ty
                    | _ -> false)
    pat

op [a] existsTypeInTerm? (pred?: AType a -> Bool) (tm: ATerm a): Bool =
  existsSubTerm (fn t ->
                 case t of
                   | Var((_, ty), _) -> existsInType? pred? ty
                   | Fun(_, ty, _)   -> existsInType? pred? ty
                   | Bind (_, vars, _, _) ->
                     exists? (fn (_, ty) -> existsInType? pred? ty) vars
                   | The ((_,ty), _, _) -> existsInType? pred? ty
                   | Let (decls, bdy, a) ->
                     exists? (fn (pat, _) -> existsTypeInPattern? pred? pat) decls
                   | LetRec (decls, bdy, a) ->
                     exists? (fn ((_, ty), _) -> existsInType? pred? ty) decls
                   | Lambda (match, a) ->
                     exists? (fn (pat, _, _) -> existsTypeInPattern? pred? pat) match
                   | TypedTerm(_, ty, _) -> existsInType? pred? ty
                   | _ -> false)
    tm

 op defensive_execution? : Bool = false  % todo: make arg to foldSubTerms ?

 %% folds function over all the subterms in top-down order
 op [b,r] foldSubTerms (f : ATerm b * r -> r) (val : r) (term : ATerm b) : r =
   let newVal = f (term, val) in
   case term of

     | Apply     (M, N, _)     -> foldSubTerms f (foldSubTerms f newVal M) N

     | ApplyN    (Ms,       _) -> foldl (fn (val,M)     -> foldSubTerms f val M) newVal Ms

     | Record    (fields, _)   -> foldl (fn (val,(_,M)) -> foldSubTerms f val M) newVal fields

     | Bind      (_,_,M,    _) -> foldSubTerms f newVal M

     | The       (_,M,      _) -> foldSubTerms f newVal M

     | Let       (decls, N, _) -> foldl (fn (val,(_,M)) -> foldSubTerms f val M)
                                        (foldSubTerms f newVal N) 
					decls

     | LetRec    (decls, N, _) -> foldl (fn (val,(_,M)) -> (foldSubTerms f val M))
				        (foldSubTerms f newVal N) 
					decls

     | Var _                   -> newVal

     | Fun _                   -> newVal

     | Lambda    (rules,    _) -> let first_cases              = butLast rules in       
                                  let (last_p, last_c, last_M) = last    rules in
                                  let val =
                                      foldl (fn (val,(p, c, M)) ->
                                               foldSubTerms f (foldSubTerms f (foldSubTermsPat f val p) c) M)
                                            newVal 
                                            first_cases
                                  in
                                  %% todo: this is used by slicing, verify that it is coordinated with code generation
                                  let val = 
                                      if defensive_execution? then
                                        %% We could ignore restriction functions here, but choose not to.
                                        %% An execution slice, for example, will include the restriction function.
                                        %% If the restriction here should fail, this will cause a fall-through
                                        %% to the end of a case statement or lambda dispatch.
                                        foldSubTermsPat f val last_p
                                      else
                                        %% Ignore any restriction function in the pattern of the last case,
                                        %% since we presumably cannot fail to take the last case.
                                        %% An execution slice, for example, will not include the restriction function.
                                        %% If the restriction here would have failed if present, this omission
                                        %% would cause the last case to (incorrectly) be executed anyway.
                                        % let _ = 
                                        %     case last_p of
                                        %       | RestrictedPat(_,t,_) -> writeLine ("Ignoring final restriction: " ^ printTerm t)
                                        %       |  _ -> ()
                                        % in
                                        val
                                  in
                                  foldSubTerms f (foldSubTerms f val last_c) last_M

     | IfThenElse(M, N, P,  _) -> foldSubTerms f
					       (foldSubTerms f 
						             (foldSubTerms f newVal M) 
						             N)
					       P

     | Seq       (Ms,       _) -> foldl (fn (val,M) -> foldSubTerms f val M) newVal Ms

     | TypedTerm (M,   _,   _) -> foldSubTerms f newVal M

     %% TODO: What about transform?

     | Pi        (_,   M,   _) -> foldSubTerms f newVal M

     | And       (tm1::tms, _) -> foldSubTerms f newVal tm1

     %% TODO: What about Any?

     | _  -> newVal

 op [b,r] foldSubTermsPat (f : ATerm b * r -> r) (val : r) (pat : APattern b) : r =
   case pat of
     | RestrictedPat(_,t,_) -> foldSubTerms f val t
     | _ -> val

 op [b,r] foldSubTermsEvalOrder (f : ATerm b * r -> r) ( val : r) (term : ATerm b) : r =
   let recVal =
       case term of

	 | Apply     (M as Lambda (rules,  _), N, _) ->	% case statement
	   let val = (foldSubTermsEvalOrder f val N) in
	   foldl (fn (val,(_,c,M)) ->
		  foldSubTermsEvalOrder f (foldSubTermsEvalOrder f val c) M)
	         val rules

	 | Apply     (M,N,    _) -> foldSubTermsEvalOrder f
	                                                  (foldSubTermsEvalOrder f val M)
							  N

	 | ApplyN    (Ms,     _) -> foldl (fn (val,M) -> 
					   foldSubTermsEvalOrder f val M)
		                          val Ms

	 | Record    (fields, _) -> foldl (fn (val,(_,M)) -> 
					    foldSubTermsEvalOrder f val M)
					  val fields

	 | Bind      (_,_,M,  _) -> foldSubTermsEvalOrder f val M

	 | The       (_,M,    _) -> foldSubTermsEvalOrder f val M

	 | Let       (decls,N,_) -> let dval = foldl (fn (val,(_, M)) ->
						      foldSubTermsEvalOrder f val M)
						     val decls
				    in 
				      foldSubTermsEvalOrder f dval N

	 | LetRec    (decls,N,_) -> foldl (fn (val,(_, M)) -> 
					   foldSubTermsEvalOrder f val M)
				          (foldSubTermsEvalOrder f val N) 
					  decls

	 | Var _                 -> val

	 | Fun _                 -> val

	 | Lambda    (rules,  _) -> let val = f (term, val) in
				    %% lambda is evaluated before its contents
				    %% this is an approximation as we don't know when
				    %% contents will be evaluated
				    foldl (fn (val,(p, c, M)) ->
					   foldSubTermsEvalOrder f
					     (foldSubTermsEvalOrder f
					        (foldSubTermsEvalOrderPat f val p) c) 
					     M)
					val rules

         | IfThenElse(M,N,P,  _) -> foldSubTermsEvalOrder f
				      (foldSubTermsEvalOrder f
				        (foldSubTermsEvalOrder f val M) 
					N)
				      P

	 | Seq       (Ms,     _) -> foldl (fn (val,M) ->
					   foldSubTermsEvalOrder f val M)
					  val Ms

	 | TypedTerm (M,_,    _) -> foldSubTermsEvalOrder f val M

         | Pi        (_,  M,  _) -> foldSubTermsEvalOrder f val M

        %| And       (tms,    _) -> foldl (fn (val,tms) -> foldSubTermsEvalOrder f val tm) val tms % really want join/meet of fold results

         | _  -> val

   in
     case term of
       | Lambda _ -> recVal
       | _        -> f (term, recVal)

 op [b,r] foldSubTermsEvalOrderPat (f : ATerm b * r -> r) (val : r) (pat : APattern b) : r =
   case pat of
     | RestrictedPat(_,t,_) -> foldSubTermsEvalOrder f val t
     | _ -> val

 op [b,r] foldSubPatterns (f : APattern b * r -> r) (result : r) (pattern : APattern b) : r =
   let result = f (pattern,result) in
   case pattern of
     | AliasPat(p1, p2,_) ->
       foldSubPatterns f (foldSubPatterns f result p1) p2
     | EmbedPat(_, Some pat,_,_) -> foldSubPatterns f result pat
     | RecordPat(fields,_) ->
       foldl (fn (r,(_,p))-> foldSubPatterns f r p) result fields
     | QuotientPat  (pat,_,_,_) -> foldSubPatterns f result pat
     | RestrictedPat(pat,_,_) -> foldSubPatterns f result pat
     | TypedPat     (pat,_,_) -> foldSubPatterns f result pat
     | _ -> result

op [b,r] foldTypesInTerm (f: r * AType b -> r) (init: r) (tm: ATerm b): r =
  let result = Ref init in
  (mapTerm (id, fn s -> (result := f(!result, s); s), id) tm;
   !result)

op [b,r] foldTypesInType (f: r * AType b -> r) (init: r) (tm: AType b): r =
  let result = Ref init in
  (mapType (id, fn s -> (result := f(!result, s); s), id) tm;
   !result)

op [b,r] foldTypesInPattern (f: r * AType b -> r) (init: r) (tm: APattern b): r =
  let result = Ref init in
  (mapPattern (id, fn s -> (result := f(!result, s); s), id) tm;
   !result)

 %%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%
 %%%                Recursive TSP Replacement
 %%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%
 %%% "TSP" means "Term, Type, Pattern"

 type ReplaceType a = (ATerm    a -> Option (ATerm    a)) *
                      (AType    a -> Option (AType    a)) *
                      (APattern a -> Option (APattern a))

 op [b] replaceTerm ((tsp as (term_map, _, _)) : ReplaceType b) (term : ATerm b) : ATerm b =
  let

    def replace term =
      case term of

	| Apply       (           t1,            t2, a) ->
	  Apply       (replaceRec t1, replaceRec t2, a)

	| ApplyN      (               terms,  a) ->
	  ApplyN      (map replaceRec terms,  a)

	| Record      (                                           row, a) ->
	  Record      (map (fn (id, trm) -> (id, replaceRec trm)) row, a)

	| Bind        (bnd, vars, trm, a) ->
	  Bind        (bnd,
		       map (fn (id, ty)-> (id, replaceType tsp ty)) vars,
		       replaceRec trm,
		       a)
	  
	| The        ((id,ty), trm, a) ->
	  The        ((id, replaceType tsp ty), replaceRec trm, a)
	  
	| Let         (decls, bdy, a) ->
	  Let         (map (fn (pat, trm)-> (replacePattern tsp pat, replaceRec trm)) decls,
		       replaceRec bdy,
		       a)
	  
	| LetRec      (decls, bdy, a) ->
	  LetRec      (map (fn (id, trm) -> (id, replaceRec trm)) decls,
		       replaceRec bdy,
		       a)
	  
	| Var         ((id,                 ty), a) ->
	  Var         ((id, replaceType tsp ty), a)
	  
	| Fun         (top,                 ty, a) ->
	  Fun         (top, replaceType tsp ty, a)
	  
	| Lambda      (match, a) ->
	  Lambda      (map (fn (pat, cond, trm)->
                            (replacePattern tsp pat,
                             replaceRec     cond,
                             replaceRec     trm))
		           match,
		       a)
	  
	| IfThenElse  (           t1,            t2,            t3, a) ->
	  IfThenElse  (replaceRec t1, replaceRec t2, replaceRec t3, a)
	  
	| Seq         (               terms, a) ->
	  Seq         (map replaceRec terms, a)
	  
	| TypedTerm   (           trm,                 ty, a) ->
	  TypedTerm   (replaceRec trm, replaceType tsp ty, a)
	  
        | Pi          (tvs,            tm, a) ->  % TODO: can replaceRec alter vars?
	  Pi          (tvs, replaceRec tm, a)

        | And         (               tms, a) ->
	  maybeMkAndTerm (map replaceRec tms, a)

        | Any _ -> term

        | _  -> term  

    def replaceRec term =
      %% Pre-Node traversal: possibly replace node before checking if leaves should be replaced
      case term_map term of
	| None         -> replace term
	| Some newTerm -> newTerm

  in
    replaceRec term

 op [b] replaceType ((tsp as (_, type_map, _)) : ReplaceType b) (ty : AType b) : AType b =
   let

     def replace ty =
       case ty of
	 | Arrow     (           s1,            s2, a) ->
           Arrow     (replaceRec s1, replaceRec s2, a)

	 | Product   (                                           row, a) ->
	   Product   (map (fn (id, ty) -> (id, replaceRec ty)) row, a)
	   
	 | CoProduct (                                              row,  a) ->
	   CoProduct (map (fn (id, opt) -> (id, replaceRecOpt opt)) row,  a)
	   
	 | Quotient  (           ty,                 trm, a) ->
	   Quotient  (replaceRec ty, replaceTerm tsp trm, a)
	   
	 | Subtype   (           ty,                 trm, a) ->
	   Subtype   (replaceRec ty, replaceTerm tsp trm, a)
	   
	 | Base      (qid,                tys, a) ->
	   Base      (qid, map replaceRec tys, a)
	   
	 | Boolean _ -> ty

        %| TyVar     ??
        %| MetaTyVar ??

         | Pi        (tvs,            ty, a) -> % TODO: can replaceRec alter vars?
	   Pi        (tvs, replaceRec ty, a) 

         | And       (               tys, a) ->
	   maybeAndType (map replaceRec tys, a)

	 | Any _ -> ty

	 | _ -> ty

     def replaceRecOpt opt_ty =
       case opt_ty of
	 | None     -> None
	 | Some ty -> Some (replaceRec ty)

     def replaceRec ty =
       %% Pre-Node traversal: possibly replace node before checking if leaves should be replaced
       case type_map ty of
	 | None        -> replace ty
	 | Some newTy -> newTy

   in
     replaceRec ty

 op [b] replacePattern ((tsp as (_, _, pattern_map)) : ReplaceType b) (pattern : APattern b) : APattern b =
   let

     def replace pattern =
       case pattern of

	 | AliasPat     (           p1,            p2, a) ->
           AliasPat     (replaceRec p1, replaceRec p2, a)

	 | VarPat       ((v,                 ty), a) ->
	   VarPat       ((v, replaceType tsp ty), a)

	 | EmbedPat     (id, Some             pat,                  ty, a) ->
	   EmbedPat     (id, Some (replaceRec pat), replaceType tsp ty, a)
	   
	 | EmbedPat     (id, None,                                  ty, a) ->
	   EmbedPat     (id, None,                  replaceType tsp ty, a)
	   
	 | RecordPat    (                                     fields, a) ->
	   RecordPat    (map (fn (id,p)-> (id, replaceRec p)) fields, a)
	   
	 | WildPat      (                ty, a) ->
	   WildPat      (replaceType tsp ty, a)

	 | QuotientPat  (           pat, qid, tys, a) -> 
	   QuotientPat  (replaceRec pat, qid, tys, a)

	 | RestrictedPat(           pat,                 trm, a) ->
	   RestrictedPat(replaceRec pat, replaceTerm tsp trm, a)

       % | TypedPat ??
       % | BoolPat   ??
       % | NatPat    ??
       % | StringPat ??
       % | CharPat   ??
	   
	 | _ -> pattern

     def replaceRec pattern =
       %% Pre-Node traversal: possibly replace node before checking if leaves should be replaced
       case pattern_map pattern of
	 | None        -> replace pattern
	 | Some newPat -> newPat

   in
     replaceRec pattern

 %%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%
 %%%                Recursive TSP Application (for side-effects)
 %%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%
 %%% "TSP" means "Term, Type, Pattern"

 type appTSP a = (ATerm    a -> ()) *
                 (AType    a -> ()) *
                 (APattern a -> ())

 type ATermOpt a = Option(ATerm a)
 type ATypeOpt a = Option(AType a)

 type ATypeScheme  b = TyVars * AType b
 type ATermScheme  b = TyVars * ATerm b
 type ATypeSchemes b = List (ATypeScheme b)
 type ATermSchemes b = List (ATermScheme b)

 op [a] appTerm ((tsp as (term_app, _, _)) : appTSP a) (term : ATerm a) : () =
   let 

     def appT (tsp, term) =
       case term of

	 | Apply      (t1, t2,       _) -> (appRec t1; appRec t2)

	 | ApplyN     (terms,        _) -> app appRec terms

	 | Record     (row,          _) -> app (fn (id, trm) -> appRec trm) row

	 | Bind       (_, vars, trm, _) -> (app (fn (id, ty) -> appType tsp ty) vars;
					    appRec trm)

	 | The        ((id,ty), trm,    _) -> (appType tsp ty; appRec trm)

	 | Let        (decls, bdy,   _) -> (app (fn (pat, trm) ->
						 (appPattern tsp pat;
						  appRec trm))
					        decls;
					    appRec bdy)

	 | LetRec     (decls, bdy,   _) -> (app (fn (id, trm) -> appRec trm) decls;
					    appRec bdy)

	 | Var        ((id, ty),    _) -> appType tsp ty
	 
	 | Fun        (top, ty,     _) -> appType tsp ty
	 
	 | Lambda     (match,        _) -> app (fn (pat, cond, trm) ->
						(appPattern tsp pat;
						 appRec cond;
						 appRec trm))
	                                       match

	 | IfThenElse (t1, t2, t3,   _) -> (appRec t1; appRec t2; appRec t3)

	 | Seq        (terms,        _) -> app appRec terms

	 | TypedTerm  (trm, ty,     _) -> (appRec trm; appType tsp ty)

	 | Pi         (tvs, tm,      _) -> appRec tm

	 | And        (tms,          _) -> app appRec tms

	 | _  -> ()

     def appRec term = 
       %% Post-node traversal: leaves first
       (appT (tsp, term); term_app term)

   in
     appRec term

 op [a] appType ((tsp as (_, ty_app, _)) : appTSP a) (ty : AType a) : () =
   let 

     def appS (tsp, ty) =
       case ty of
	 | Arrow     (s1,  s2,   _) -> (appRec s1;  appRec s2)
	 | Product   (row,       _) -> app (fn (id, ty) -> appRec ty) row
	 | CoProduct (row,       _) -> app (fn (id, opt) -> appTypeOpt tsp opt) row
	 | Quotient  (ty, trm,  _) -> (appRec ty; appTerm tsp trm)
	 | Subtype   (ty, trm,  _) -> (appRec ty; appTerm tsp trm)
	 | Base      (qid, tys, _) -> app appRec tys
	 | Boolean               _  -> ()

	%| TyVar     ??
	%| MetaTyVar ??

	 | Pi        (tvs, ty, _) -> appRec ty
	 | And       (tys,     _) -> app appRec tys
	 | Any                  _  -> ()

         | _                       -> ()

     def appRec ty =
       %% Post-node traversal: leaves first
       (appS (tsp, ty); ty_app ty)

   in
     appRec ty

 op [a] appPattern ((tsp as (_, _, pattern_app)) : appTSP a) (pat : APattern a) : () =
   let 

     def appP (tsp, pat) =
       case pat of
	 | AliasPat     (p1, p2,           _) -> (appRec p1; appRec p2)
	 | VarPat       ((v, ty),          _) -> appType tsp ty
	 | EmbedPat     (id, Some pat, ty, _) -> (appRec pat; appType tsp ty)
	 | EmbedPat     (id, None, ty,     _) -> appType tsp ty
	 | RecordPat    (fields,           _) -> app (fn (id, p) -> appRec p) fields
	 | WildPat      (ty,               _) -> appType tsp ty
	 | QuotientPat  (pat, _, _,        _) -> appRec pat
	 | RestrictedPat(pat, trm,         _) -> appRec pat
        %| TypedPat  ??
        %| BoolPat   ??
        %| NatPat    ??
	%| StringPat ??
        %| CharPat   ??
	 | _                                   -> ()

     def appRec pat = (appP (tsp, pat); pattern_app pat)

   in
     appRec pat

 op [a] appTypeOpt (tsp : appTSP a) (opt_type : ATypeOpt a) : () =
   case opt_type of
     | None     -> ()
     | Some ty -> appType tsp ty

 op [a] appTermOpt (tsp : appTSP a) (opt_term : ATermOpt a) : () =
   case opt_term of
     | None     -> ()
     | Some trm -> appTerm tsp trm

 op [a] appTypeSchemes (tsp : appTSP a) (type_schemes : ATypeSchemes a) : () =
   app (fn (_,ty) -> appType tsp ty) type_schemes

 op [a] appTermSchemes (tsp : appTSP a) (term_schemes : ATermSchemes a) : () =
   app (fn (_,term) -> appTerm tsp term) term_schemes

 %%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%
 %%%                Misc Base Terms
 %%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%

 op [b] boolType? (s : AType b) : Bool =
   case s of
     | Boolean _ -> true
     | _ -> false

 op [b] stringType? (s : AType b) : Bool =
   case s of
     | Base (Qualified ("String",  "String"),  [], _) -> true
     | _ -> false

 op [b] charType? (s : AType b) : Bool =
   case s of
     | Base (Qualified ("Char",  "Char"),  [], _) -> true
     | _ -> false

 op [b] natType? (s : AType b) : Bool =
   case s of
     | Base (Qualified ("Nat",     "Nat"),     [], _) -> true
     | _ -> false

 op [b] intType? (s : AType b) : Bool =
   case s of
     | Base (Qualified ("Integer", "Int"),     [], _) -> true
     | _ -> false

 %%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%
 %%%  Misc constructors
 %%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%
 
  op [a] mkAndOp (pos:a):ATerm a =
   let bool_type = Boolean pos in
   let binary_bool_type = Arrow (Product ([("1",bool_type), ("2",bool_type)], pos),
				 bool_type,
				 pos)
   in
     Fun (And, binary_bool_type, pos)

  op [a] mkOrOp (pos:a):ATerm a =
   let bool_type = Boolean pos in
   let binary_bool_type = Arrow (Product ([("1",bool_type), ("2",bool_type)], pos),
				 bool_type,
				 pos)
   in
     Fun (Or, binary_bool_type, pos)

 op [b] mkABase (qid : QualifiedId, tys : List (AType b), a : b) : AType b = Base (qid, tys, a)

 op [b] mkTrueA (a : b) : ATerm b = Fun (Bool true,  Boolean a, a)

 op [b] mkFalseA (a : b) : ATerm b = Fun (Bool false, Boolean a, a)

 op [a] listType?(ty: AType a): Bool =
   case ty of
     | Base (Qualified ("List",      "List"), [_], _) -> true
     | Base (Qualified (UnQualified, "List"), [_], _) -> true
     | Base (Qualified ("List",      "List1"), [_], _) -> true
     | Base (Qualified (UnQualified, "List1"), [_], _) -> true
     | Subtype (sty, _, _) -> listType? sty
     | _ -> false

 op [a] isFiniteList (term : ATerm a) : Option (List (ATerm a)) =  
   case term of
     | Fun (Op (Qualified(q, "Nil"), _), ty, _) | listType? ty -> Some []
     | Fun (Embed (Qualified(q, "Nil"), false), ty, _) | listType? ty -> Some []
     | Apply (Fun (Op(Qualified(q, "Cons"), _), 
		   Arrow (Product ([("1", _), ("2", ty)], _), _, _), _),
	      Record ([(_, t1), (_, t2)], _), _)
       | listType? ty
       -> (case isFiniteList t2 of
             | Some terms -> Some (t1 :: terms)
             | _ ->  None)
     | ApplyN ([Fun (Op (Qualified(q, "Cons"), _), 
		     Arrow (Product ([("1", _), ("2",  ty1)], _),
			    ty2, _), _),
		Record ([(_, t1), (_, t2)], _), _], _)
       | listType? ty1 && listType? ty2
       -> (case isFiniteList t2 of
             | Some terms -> Some (t1 :: terms)
             | _  ->  None)
     | _ -> None

 op [a] isFiniteListPat (pattern : APattern a) : Option (List (APattern a)) =  
   case pattern of
     | EmbedPat (Qualified(q, "Nil"), None, ty, _) -> Some []
     | EmbedPat (Qualified(q, "Cons"), 
		 Some (RecordPat ([("1", p1), ("2", p2)], _)), 
		 ty, _)
       | listType? ty
       -> 
       (case isFiniteListPat p2 of
	  | Some patterns -> Some (p1 :: patterns)
	  | _ ->  None)
     | _ -> None

op [a] printTermType(t: ATerm a): String =
  case t of
    | Apply _ -> "Apply"
    | ApplyN _ -> "ApplyN"
    | Record _ -> "Record"
    | Bind _ -> "Bind"
    | The _ -> "The"
    | Let _ -> "Let"
    | LetRec _ -> "LetRec"
    | Var _ -> "Var"
    | Fun _ -> "Fun"
    | Lambda _ -> "Lambda"
    | IfThenElse _ -> "IfThenElse"
    | Seq _ -> "Seq"
    | TypedTerm _ -> "TypedTerm"
    | Transform _ -> "Transform"
    | Pi _ -> "Pi"
    | And _ -> "And"
    | Any _ -> "Any"

op [a] infixFn?(f: AFun a): Bool =
  case f of
    | Op(Qualified(_, s), Infix _) -> true
    | And -> true
    | Or -> true
    | Implies -> true
    | Iff -> true
    | Equals -> true
    | NotEquals -> true
    | _ -> false

op [a] infixFnTm?(tm: ATerm a): Bool =
  case tm of
    | Fun(f, _, _) -> infixFn? f
    | _ -> false

end-spec



