MetaSlang qualifying spec
 import /Library/Legacy/Utilities/State  % for MetaTyVar's
 import /Library/Legacy/Utilities/System
 import /Library/Legacy/DataStructures/ListPair

 op AnnSpecPrinter.printTerm   : [a] ATerm    a -> String %  defined in ../Specs/Printer, which imports this spec (circularity)
 op AnnSpecPrinter.printSort   : [a] ASort    a -> String %  defined in ../Specs/Printer, which imports this spec (circularity)
 op AnnSpecPrinter.printPattern: [a] APattern a -> String %  defined in ../Specs/Printer, which imports this spec (circularity)

 %%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%
 %%%                QualifiedId
 %%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%
 %%%  Basic structure for naming things

 type Id = String
 type Qualifier = Id

 %% This is the key used in the qualifier maps for UnQualified Id
 op UnQualified : Qualifier
 def UnQualified = "<unqualified>" % a non-parsable id

 %% The Qualifier's for id's in a spec are established independently
 %% from the name of the spec:  all, some, or none might have the
 %% name of the spec as their qualifier, and the same qualifier can
 %% be used in multiple specs.

 type QualifiedId = | Qualified Qualifier * Id

 %% An annotated qualified id can record extra information,
 %% e.g. the precise position of the name.
 type AQualifiedId a = QualifiedId * a

 %% the following are invoked by the parser to make qualified names
 def mkUnQualifiedId  id      =  Qualified (UnQualified, id)
 def mkQualifiedId    (q, id) =  Qualified (q,           id)
 def [a] mkAUnQualifiedId (id,     x : a) = (Qualified (UnQualified, id), x)
 def [a] mkAQualifiedId   (q,  id, x : a) = (Qualified (q,           id), x)

 op  unQualifiedId?: QualifiedId -> Bool
 def unQualifiedId? id =
   case id of
     | Qualified(UnQualified, _) -> true
     | _ -> false

 op mainId(Qualified(_,main_id): QualifiedId): String = main_id

 %% These are used by translation, morphism code
 def unqualified_Boolean = mkUnQualifiedId "Boolean"               % used by translate
 def Boolean_Boolean     = mkQualifiedId ("Boolean", "Boolean")    % used by translate
 def syntactic_qid? (Qualified(q,id)) =                            % used by translate, morphism
   if q = "Boolean" || q = UnQualified then                        % used by translate, morphism
     (case id of
	| "~"   -> true
	| "&"   -> true  % TODO: deprecate
	| "&&"  -> true
	| "or"  -> true  % TODO: deprecate
	| "||"  -> true
	| "=>"  -> true
	| "<=>" -> true
	| "="   -> true
	| "~="  -> true
	| _ -> false)
   else
     false
	
 %% This is useful in some error messages, where you want to be very explicit:
  op explicitPrintQualifiedId : QualifiedId -> String
 def explicitPrintQualifiedId (Qualified (q, id)) =
   if q = UnQualified then
     id
   else
     q ^ "." ^ id

  op QualifiedId.show : QualifiedId -> String
 def QualifiedId.show = printQualifiedId

 %% This is useful for most normal messages, where you want to be terse:
  op printQualifiedId : QualifiedId -> String
 def printQualifiedId (Qualified (q, id)) =
   if q = UnQualified then
     id
   else
     printQualifierDotId (q, id)

  op printQualifierDotId : Qualifier * Id -> String
 def printQualifierDotId (q, id) =
   if q = "Nat"     ||
      q = "String"  ||
      q = "Char"    ||
      q = UnQualified
   then id
   else q ^ "." ^ id

 %% This is useful when printing names for Lisp, C, Java, etc.:
  op printUnderbarQualifiedId : QualifiedId -> String
 def printUnderbarQualifiedId (Qualified (q, id)) =
   if q = UnQualified then
     id
   else
     printQualifierUnderbarId (q, id)

  op printQualifierUnderbarId : Qualifier * Id -> String
 def printQualifierUnderbarId (q, id) =
   if q = "Nat"     ||
      q = "String"  ||
      q = "Char"    ||
      q = UnQualified
   then id
   else q ^ "_" ^ id

 def printAliases aliases =
   case aliases of
     | [] -> fail "printAliases: empty name list"
     | [name] -> printQualifiedId name
     | first::rest ->
       "{" ^ (printQualifiedId first) ^
       (foldl (fn (str, qid) -> str ^ ", " ^ printQualifiedId qid)
	      ""
	      rest)
       ^ "}"

 %%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%

 type SortNames      = List SortName
 type OpNames        = List OpName
 type PropertyNames  = List PropertyName

 type SortName       = QualifiedId
 type OpName         = QualifiedId
 type PropertyName   = QualifiedId

 type Aliases        = QualifiedIds
 type QualifiedIds   = List QualifiedId

 %%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%
 %%%                Type Variables
 %%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%

 type TyVar   = Id
 type TyVars  = List TyVar

 %%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%
 %%%                Terms
 %%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%
 %%% ATerm, ASort, APattern, AFun, AVar, AMatch, and MetaTyVar
 %%%  are all mutually recursive types.

 %% Terms are tagged with auxiliary information such as
 %% location information and free variables for use in
 %% various transformation steps.

 type ATerm b =
  | Apply        ATerm b * ATerm b                       * b
  | ApplyN       List (ATerm b)                          * b % Before elaborateSpec
  | Record       List (Id * ATerm b)                     * b
  | Bind         Binder * List (AVar b)      * ATerm b   * b
  | The          AVar b * ATerm b                        * b
  | Let          List (APattern b * ATerm b) * ATerm b   * b
  | LetRec       List (AVar b     * ATerm b) * ATerm b   * b
  | Var          AVar b                                  * b
  | Fun          AFun b * ASort b                        * b
  | Lambda       AMatch b                                * b
  | IfThenElse   ATerm b * ATerm b * ATerm b             * b
  | Seq          List (ATerm b)                          * b
  | SortedTerm   ATerm b * ASort b                       * b
  | Transform    List(ATransformExpr b)                  * b  % For specifying refinement by script
  | Pi           TyVars * ATerm b                        * b  % for now, used only at top level of defn's
  | And          List (ATerm b)                          * b  % for now, used only by colimit and friends -- meet (or join) not be confused with boolean AFun And 
                                                              % We might want to record a quotient of consistent terms plus a list of inconsistent pairs,
                                                              % but then the various mapping functions become much trickier.
  | Any                                                    b  % e.g. "op f : Nat -> Nat"  has defn:  SortedTerm (Any noPos, Arrow (Nat, Nat, p1), noPos)
 
 type Binder =
  | Forall
  | Exists
  | Exists1

 type AVar b = Id * ASort b

 type AMatch b = List (APattern b * ATerm b * ATerm b)

 type ASort b =
  | Arrow        ASort b * ASort b                   * b
  | Product      List (Id * ASort b)                 * b
  | CoProduct    List (Id * Option (ASort b))        * b
  | Quotient     ASort b * ATerm b                   * b
  | Subsort      ASort b * ATerm b                   * b
  | Base         QualifiedId * List (ASort b)        * b  % Typechecker verifies that QualifiedId refers to some sortInfo
  | Boolean                                            b
  | TyVar        TyVar                               * b
  | MetaTyVar    AMetaTyVar b                        * b  % Before elaborateSpec
  | Pi           TyVars * ASort b                    * b  % for now, used only at top level of defn's
  | And          List (ASort b)                      * b  % for now, used only by colimit and friends -- meet (or join)
                                                          % We might want to record a quotient of consistent sorts plus a list of inconsistent pairs,
                                                          % but then the various mapping functions become much trickier.
  | Any                                                b  % e.g. "sort S a b c "  has defn:  Pi ([a,b,c], Any p1, p2)

 type APattern b =
  | AliasPat      APattern b * APattern b             * b
  | VarPat        AVar b                              * b
  | EmbedPat      Id * Option (APattern b) * ASort b  * b
  | RecordPat     List(Id * APattern b)               * b
  | WildPat       ASort b                             * b
  | BoolPat       Bool                                * b
  | NatPat        Nat                                 * b
  | StringPat     String                              * b
  | CharPat       Char                                * b
  | QuotientPat   APattern b * SortName               * b
  | RestrictedPat APattern b * ATerm b                * b
  | SortedPat     APattern b * ASort b                * b  % Before elaborateSpec

 type AFun b =

  | Not
  | And
  | Or
  | Implies
  | Iff
  | Equals
  | NotEquals

  | Quotient       SortName
  | Choose         SortName
  | Restrict
  | Relax

  | PQuotient      SortName
  | PChoose        SortName

  | Op             QualifiedId * Fixity
  | Project        Id
  | RecordMerge             % <<
  | Embed          Id * Bool
  | Embedded       Id
  | Select         Id
  | Nat            Nat
  | Char           Char
  | String         String
  | Bool           Bool
  % hacks to avoid ambiguity during parse of A.B.C, etc.
  | OneName        Id * Fixity         % Before elaborateSpec
  | TwoNames       Id * Id * Fixity    % Before elaborateSpec

 type Fixity        = | Nonfix 
                      | Infix Associativity * Precedence 
                      | Unspecified 
                      %% The following is used only when combining specs,
                      %% as within colimit, to allow us to delay the
                      %% raising of errors at inopportune times.
                      | Error (List Fixity) 

 %% Currently Specware doesn't allow "NotAssoc" but is there for Haskell translation compatibility
 type Associativity = | Left | Right | NotAssoc
 type Precedence    = Nat

 type AMetaTyVar      b = Ref ({link     : Option (ASort b),
                                uniqueId : Nat,
                                name     : String })

 type AMetaTyVars     b = List (AMetaTyVar b)
 type AMetaSortScheme b = AMetaTyVars b * ASort b

 type SpecCalc.SCTerm   %% defined in /Languages/SpecCalculus/AbstractSyntax/Types

 type ATransformExpr a =
    | Name String * a
    | Number Nat * a
    | Str String * a
    | Qual String * String * a
    | SCTerm SCTerm * a
    | Item String * ATransformExpr a * a       % e.g. unfold map
    | Tuple List (ATransformExpr a) * a
    | Record List(String * ATransformExpr a) * a
    | ApplyOptions ATransformExpr a * List (ATransformExpr a) * a
    | Apply ATransformExpr a * List (ATransformExpr a) * a

 %%% Predicates
 op product?: [a] ASort a -> Bool
 def product? s =
   case s of
     | Product _ -> true
     | _         -> false

  op maybePiSort : [b] TyVars * ASort b -> ASort b
 def maybePiSort (tvs, srt) =
   case tvs of
     | [] -> srt
     | _ -> Pi (tvs, srt, sortAnn srt)

  op maybePiTerm : [b] TyVars * ATerm b -> ATerm b
 def maybePiTerm (tvs, tm) =
   case tvs of
     | [] -> tm
     | _ -> Pi (tvs, tm, termAnn tm)

op [a] maybePiSortedTerm(tvs: TyVars, o_ty: Option(ASort a), tm: ATerm a): ATerm a =
  let s_tm = case o_ty of
               | Some ty -> SortedTerm(tm, ty, termAnn tm)
               | None -> tm
  in
  maybePiTerm(tvs, s_tm)

op [a] piTypeAndTerm(tvs: TyVars, ty: ASort a, tms: List(ATerm a)): ATerm a =
  let (main_tm, pos) = case tms of
                         | [] -> (And(tms, sortAnn ty), sortAnn ty)
                         | [tm] -> (tm, termAnn tm)
                         | tms -> (And(tms, termAnn(head tms)), termAnn (head tms))
  in
  maybePiTerm(tvs, SortedTerm(main_tm, ty, pos))

op [a] typeTermPairsToTerm(ty_tm_prs: List(ASort a * ATerm a)): ATerm a =
  case ty_tm_prs of
    | [(ty, tm)] -> SortedTerm(tm, ty, termAnn tm)
    | (_, tm) :: _ -> And(map (fn (ty, tm) -> SortedTerm(tm, ty, sortAnn ty))
                            ty_tm_prs,
                          termAnn tm)

op [a] maybePiAndSortedTerm(tvs: TyVars, ty_tm_prs: List(ASort a * ATerm a)): ATerm a =
  maybePiTerm(tvs, typeTermPairsToTerm ty_tm_prs)


 %%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%
 %%%                Fields
 %%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%

 %% A fundamental assumption for
 %%
 %% . Records
 %% . Product sorts
 %% . CoProduct sorts
 %%
 %% is that the fields are always sorted in alphabetical order
 %% according to their labels (Id).
 %% For example, a tuple with 10 fields is sorted internally:
 %% {1,10,2,3,4,5,6,7,8,9}
 %%
 %% This invariant is established by the parser and must be
 %% maintained by all transformations.

 type AFields b = List (AField b)
 type AField  b = FieldName * ASort b  % used by products and co-products
 type FieldName = String

  op getField: [a] List (Id * ATerm a) * Id -> Option(ATerm a)
 def getField (m, id) =
   case findLeftmost (fn (id1,_) -> id = id1) m of
     | None      -> None
     | Some(_,t) -> Some t

 op [a] getTermField(l:  List (Id * ASort a), id: Id): Option(ASort a) =
   case findLeftmost (fn (id1,_) -> id = id1) l of
     | None      -> None
     | Some(_,s) -> Some s

 %%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%
 %%%                Term Annotations
 %%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%

  op termAnn: [a] ATerm a -> a
 def termAnn tm =
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
     | SortedTerm (_,_,   a) -> a
     | Transform  (_,     a) -> a
     | Pi         (_,_,   a) -> a
     | And        (_,     a) -> a
     | Any                a  -> a

  op withAnnT: [a] ATerm a * a -> ATerm a
 def withAnnT (tm, a) =
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
     | SortedTerm (t,s,      b) -> if a = b then tm else SortedTerm (t, s,       a)
     | Transform  (t,        b) -> if a = b then tm else Transform  (t,          a)
     | Pi         (tvs, t,   b) -> if a = b then tm else Pi         (tvs, t,     a)
     | And        (l,        b) -> if a = b then tm else And        (l,          a)
     | Any                   b  -> if a = b then tm else Any                     a

  op sortAnn: [a] ASort a -> a
 def sortAnn srt =
   case srt of
     | Arrow     (_,_, a) -> a
     | Product   (_,   a) -> a
     | CoProduct (_,   a) -> a
     | Quotient  (_,_, a) -> a
     | Subsort   (_,_, a) -> a
     | Base      (_,_, a) -> a
     | Boolean         a  -> a
     | TyVar     (_,   a) -> a
     | MetaTyVar (_,   a) -> a
     | Pi        (_,_, a) -> a
     | And       (_,   a) -> a
     | Any             a  -> a

  op patAnn: [a] APattern a -> a
 def patAnn pat =
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
     | QuotientPat  (_,_,   a) -> a
     | RestrictedPat(_,_,   a) -> a
     | SortedPat    (_,_,   a) -> a

  op withAnnP: [a] APattern a * a -> APattern a
 def withAnnP (pat, b) =
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
     | QuotientPat   (p,t,     a) -> if b = a then pat else QuotientPat  (p,t,     b)
     | RestrictedPat (p,t,     a) -> if b = a then pat else RestrictedPat(p,t,     b)
     | SortedPat     (p,s,     a) -> if b = a then pat else SortedPat    (p,s,     b)

  op withAnnS: [a] ASort a * a -> ASort a
 def withAnnS (srt, a) =
  % Avoid creating new structure if possible
   case srt of
     | Arrow     (s1,s2,    b) -> if a = b then srt else Arrow     (s1,s2,    a)
     | Product   (fields,   b) -> if a = b then srt else Product   (fields,   a)
     | CoProduct (fields,   b) -> if a = b then srt else CoProduct (fields,   a)
     | Quotient  (ss,t,     b) -> if a = b then srt else Quotient  (ss,t,     a)
     | Subsort   (ss,t,     b) -> if a = b then srt else Subsort   (ss,t,     a)
     | Base      (qid,srts, b) -> if a = b then srt else Base      (qid,srts, a)
     | Boolean              b  -> if a = b then srt else Boolean a
     | TyVar     (tv,       b) -> if a = b then srt else TyVar     (tv,       a)
     | MetaTyVar (mtv,      b) -> if a = b then srt else MetaTyVar (mtv,      a)
     | Pi        (tvs, t,   b) -> if a = b then srt else Pi        (tvs, t,   a)
     | And       (types,    b) -> if a = b then srt else And       (types,    a)
     | Any                  b  -> if a = b then srt else Any       a

 %%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%
 %%%                Sort components
 %%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%

 op unpackSort    : [b] ASort b -> TyVars * ASort b
 op sortTyVars    : [b] ASort b -> TyVars 
 op sortInnerSort : [b] ASort b -> ASort b

 def unpackSort s =
   case s of
     | Pi (tvs, srt, _) -> (tvs, srt)
     | And (tms, _) -> ([], s) %  fail ("unpackSort: Trying to unpack an And of sorts.")
     | _ -> ([], s)

 def sortTyVars srt =
   case srt of
     | Pi (tvs, _, _) -> tvs
     | And _ -> [] % fail ("sortTyVars: Trying to extract type vars from an And of sorts.")
     | _ -> []

 def sortInnerSort srt =
   case srt of
     | Pi (_, srt, _) -> srt
     | And _ -> srt % fail ("sortInneSort: Trying to extract inner sort from an And of sorts.")
     | _ -> srt

 op [a] anySort?(t: ASort a): Bool =
   case t of
     | Any _        -> true
     | Pi(_, tm, _) -> anySort? tm
     | And(tms, _)  -> forall? anySort? tms
     | _ -> false

 %%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%
 %%%                Term components
 %%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%

 op unpackTerm    : [a] ATerm a -> TyVars * ASort a * ATerm a
 op termTyVars    : [b] ATerm b -> TyVars
 op termSort      : [b] ATerm b -> ASort b
 op termInnerTerm : [b] ATerm b -> ATerm b

 op maybeAndSort  : [b] List (ASort b) * b -> ASort b % Defined in Equalities.sw
 op maybeAndTerm  : [b] List (ATerm b) * b -> ATerm b % Defined in Equalities.sw

 op [a] anyTerm?(t: ATerm a): Bool =
   case t of
     | Any _                 -> true
     | Pi(_, tm, _)          -> anyTerm? tm
     | SortedTerm(tm, _, _)  -> anyTerm? tm
     | And(tms, _)           -> forall? anyTerm? tms
     | Lambda([(_,_,tm)], _) -> anyTerm? tm     % Arguments given but no body
     | _ -> false

 op [a] transformSteps?(t: ATerm a): Option(List(ATransformExpr a)) =
   case t of
     | Transform(steps, _)   -> Some steps
     | Any _                 -> None
     | Pi(_, tm, _)          -> transformSteps? tm
     | SortedTerm(tm, _, _)  -> transformSteps? tm
     | And(tms, _)           -> None
     | Lambda([(_,_,tm)], _) -> transformSteps? tm     % Arguments given but no body
     | _ -> None

 def [a] unpackTerm t =
   let def unpack(t: ATerm a, tvs: TyVars, o_ty: Option(ASort a)): TyVars * (ASort a) * (ATerm a) =
        case t of
	 | Pi (tvs, tm, _) -> unpack(tm, tvs, o_ty)
         | SortedTerm(tm, ty, _) -> (case ty of
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
                   | None -> termSort t,
                 t)
   in
   let (tvs, ty, tm) = unpack(t, [], None) in
   % let _ = if embed? And tm then writeLine("unpack:\n"^printTerm t^"\n"^printTerm tm) else () in
   (tvs, ty, tm)

 def termTyVars tm =
   case tm of
     | Pi (tvs, _, _) -> tvs
     | And _ -> fail ("termTyVars: Trying to extract type vars from an And of terms.")
     | _ -> []

 def termSort term =
   case term of
     | Apply      (t1,t2,   _) -> (case termSort t1 of
				     | Arrow(dom,rng,_) -> rng
                                     | Subsort(Arrow(dom,rng,_),_,_) -> rng
				     | _ -> System.fail ("Cannot extract sort of application:\n"
							 ^ printTerm term))
     | ApplyN     ([t1,t2], _) -> (case termSort t1 of
				     | Arrow(dom,rng,_) -> rng
				     | _ -> System.fail ("Cannot extract sort of application "
							 ^ printTerm term))

     | Record     (fields,  a)              -> Product (List.map (fn (id, t) -> (id, termSort t)) fields, a)
     | Bind       (_,_,_,   a)              -> Boolean a
     | Let        (_,term,  _)              -> termSort term
     | LetRec     (_,term,  _)              -> termSort term
     | Var        ((_,srt), _)              -> srt
     | Fun        (_,srt,   _)              -> srt
     | The        ((_,srt),_,_)             -> srt
     | Lambda     ([(pat,_,body)], a)    -> Arrow(patternSort pat, termSort body, a)
     | Lambda     (Cons((pat,_,body),_), a) ->
       let dom = case pat of
                   | RestrictedPat(p, t, a) -> patternSort p
                   | _ -> patternSort pat
       in Arrow(dom, termSort body, a)
     | Lambda     ([],                   _) -> System.fail "termSort: Ill formed lambda abstraction"
     | IfThenElse (_,t2,t3, _)              -> termSort t2
     | Seq        (_,       a)              -> Product([],a)
     | SortedTerm (_,   s,  _)              -> s
     | Pi         (tvs, t,  a)              -> Pi (tvs, termSort t, a) 
     | And        (tms,     a)              -> maybeAndSort (map termSort tms,  a)
     | Any                  a               -> Any a
     | mystery -> fail ("\n No match in termSort with: " ^ (anyToString mystery) ^ "\n")

 def termInnerTerm tm =
   case tm of
     | Pi (_, tm, _) -> termInnerTerm tm
     | And (tm::r,pos) ->
       if embed? Transform tm
         then termInnerTerm(And(r, pos))
         else termInnerTerm tm
     | SortedTerm (tm, _, _) -> termInnerTerm tm
     | _                     -> tm

 op [a] innerTerms(tm: ATerm a): List (ATerm a) =
   case tm of
     | Pi         (_, tm, _) -> innerTerms tm
     | And        (tms,_)    -> foldl (fn (rtms,tm) -> rtms ++ innerTerms tm) [] tms
     | SortedTerm (tm, _, _) -> innerTerms tm
    %| Any        _          -> []
     | _                     -> [tm]

 op [a] numTerms(tm: ATerm a): Nat = length(unpackSortedTerms tm).2

 op [a] unpackFirstTerm(t: ATerm a): TyVars * ASort a * ATerm a =
   %let (tvs, ty, tm) = unpackTerm t in
   let (tvs, (ty1, tm1) :: _) = unpackSortedTerms t in
   (tvs, ty1, tm1)

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

 op [a] unpackSortedTerms(tm: ATerm a): TyVars * List(ASort a * ATerm a) =
   let def unpackTm(tm: ATerm a, ty: ASort a): List(ASort a * ATerm a) =
         case tm of
           | And (tms, _) -> foldr (fn (tm, result) -> unpackTm(tm, ty) ++ result) [] tms
           | SortedTerm (s_tm, ty, _) -> unpackTm(s_tm, ty)
           | _ -> [(ty, tm)]
   in   
   case tm of
     | Pi (tvs, tm, _) -> (tvs, (unpackSortedTerms tm).2)
     | And (tms, _) ->
       ([], foldr (fn (tm, result) -> (unpackSortedTerms tm).2 ++ result) [] tms)
     | SortedTerm (tm, ty, _) -> ([], unpackTm(tm, ty))
     | _                      -> ([], [(termSort tm, tm)])

 op [a] unpackBasicTerm(tm: ATerm a): TyVars * ASort a * ATerm a =
   case tm of
     | Pi (tvs, SortedTerm (tm, ty, _), _) -> (tvs, ty, tm)
     | SortedTerm (tm, ty, _) -> ([], ty, tm)
     | _                      -> ([], Any(termAnn tm), tm)


 op [a] unpackNthTerm(t: ATerm a, n: Nat): TyVars * ASort a * ATerm a =
   % let _ = writeLine(printTerm t) in
   let (tvs, ty_tms) = unpackSortedTerms t in
   let len = length ty_tms in
   if len = 0 then (tvs, Any(termAnn t), t)
     else let (ty, tm) = ty_tms@(max(len - n - 1, 0)) in
          % let _ = writeLine("unpackNthTerm: "^show n^"\n"^printTerm(SortedTerm(tm, ty, termAnn t))^"\n"^printTerm t) in
          (tvs, ty, tm)

 op [a] replaceNthTerm(full_tm: ATerm a, i: Nat, n_tm: ATerm a): ATerm a =
   let tms = innerTerms full_tm in
   let len = length tms in
   if i >= len then fail("Less than "^show (i+1)^" refined terms")
   else
   let (pref, _, post) = splitAt(tms, len - i - 1) in
   maybeAndTerm(pref++(n_tm::post), termAnn full_tm)


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
         | SortedTerm(tm, ty, a) -> SortedTerm(flattenAnds tm, ty, a)
         | _ -> tm
   in
   % let _ = writeLine("fla:\n"^printTerm tm^"\n -->"^printTerm result) in
   result

 %%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%
 %%%                Pattern components
 %%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%

 op patternSort : [b] APattern b -> ASort b

 def patternSort pat =
   case pat of
     | AliasPat     (p1,_,    _) -> patternSort p1
     | VarPat       ((_,s),   _) -> s
     | EmbedPat     (_,_,s,   _) -> s
     | RecordPat    (fields,  a) -> Product (map (fn (id, p) -> (id, patternSort p)) fields, a)
     | WildPat      (srt,     _) -> srt
     | BoolPat      (_,       a) -> Boolean a
     | NatPat       (n,       a) -> mkABase  (Qualified ("Nat",     "Nat"),     [], a)
     | StringPat    (_,       a) -> mkABase  (Qualified ("String",  "String"),  [], a)
     | CharPat      (_,       a) -> mkABase  (Qualified ("Char",    "Char"),    [], a)
     | QuotientPat  (p, qid,  a) -> mkABase  (qid,                              [], a)
       %% WARNING:
       %% The result for QuotientPat is missing potential tyvars (it simply uses []),
       %% so users of that result must be prepared to handle that discrepency between 
       %% this result and the actual type referenced.
     | RestrictedPat(p, t,    a) ->
       Subsort(patternSort p,Lambda([(p,mkTrueA a,t)],a),a)
     | SortedPat    (_, srt,  _) -> srt

 op [a] deRestrict(p: APattern a): APattern a =
   case p of
     | RestrictedPat(p,_,_) -> p
     | _ -> p

 %%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%
 %%%                Recursive TSP Mappings
 %%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%
 %%% "TSP" means "Term, Sort, Pattern"

 type TSP_Maps b = (ATerm    b -> ATerm    b) *
                   (ASort    b -> ASort    b) *
                   (APattern b -> APattern b)

 op mapTerm    : [b] TSP_Maps b -> ATerm    b -> ATerm    b
 op mapSort    : [b] TSP_Maps b -> ASort    b -> ASort    b
 op mapPattern : [b] TSP_Maps b -> APattern b -> APattern b

 def mapTerm (tsp as (term_map,_,_)) term =
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
	   let newVars = map (fn (id, srt)-> (id, mapSort tsp srt)) vars in
	   let newTrm = mapRec trm in
	   if newVars = vars && newTrm = trm then
	     term
	   else
	     Bind (bnd, newVars, newTrm, a)

	 | The (var as (id,srt), trm, a) ->
	   let newVar = (id, mapSort tsp srt) in
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
	   let newDecls = map (fn ((id, srt), trm) ->
			       ((id, mapSort tsp srt),
				mapRec trm))
	                      decls
	   in
	   let newBdy = mapRec bdy in
	   if newDecls = decls && newBdy = bdy then
	     term
	   else
	     LetRec (newDecls, newBdy, a)

	 | Var ((id, srt), a) ->
	   let newSrt = mapSort tsp srt in
	   if newSrt = srt then
	     term
	   else
	     Var ((id, newSrt), a)

	 | Fun (f, srt, a) ->
	   let newSrt = mapSort tsp srt in
	   if newSrt = srt then
	     term
	   else
	     Fun (f, newSrt, a)

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

	 | SortedTerm (trm, srt, a) ->
	   let newTrm = mapRec trm in
	   let newSrt = mapSort tsp srt in
	   if newTrm = trm && newSrt = srt then
	     term
	   else
	     SortedTerm (newTrm, newSrt, a)

         | Pi  (tvs, t, a) -> Pi (tvs, mapRec t,   a) % TODO: what if map alters vars??

         | And (tms, a)    -> maybeAndTerm (map mapRec tms, a)

         | _           -> term

     def mapRec term =
       %% apply map to leaves, then apply map to result
       term_map (mapT (tsp, term))

   in
     mapRec term

 def mapSort (tsp as (_, sort_map, _)) srt =
   let

     %% Written with explicit parameter passing to avoid closure creation
     def mapS (tsp, sort_map, srt) =
       case srt of

	 | Arrow (s1, s2, a) ->
	   let newS1 = mapRec (tsp, sort_map, s1) in
	   let newS2 = mapRec (tsp, sort_map, s2) in
	   if newS1 = s1 && newS2 = s2 then
	     srt
	   else
	     Arrow (newS1, newS2, a)
	   
	 | Product (row, a) ->
	   let newRow = mapSRow (tsp, sort_map, row) in
	   if newRow = row then
	     srt
	   else
	     Product (newRow, a)
	     
	 | CoProduct (row, a) ->
	   let newRow = mapSRowOpt (tsp, sort_map, row) in
	   if newRow = row then
	     srt
	   else
	     CoProduct (newRow, a)
	       
	 | Quotient (super_sort, trm, a) ->
	   let newSsrt = mapRec (tsp, sort_map, super_sort) in
	   let newTrm =  mapTerm tsp trm in
	   if newSsrt = super_sort && newTrm = trm then
	     srt
	   else
	     Quotient (newSsrt, newTrm, a)
		 
	 | Subsort (sub_sort, trm, a) ->
	   let newSsrt = mapRec (tsp, sort_map, sub_sort) in
	   let newTrm =  mapTerm tsp trm in
	   if newSsrt = sub_sort && newTrm = trm then
	     srt
	   else
	     Subsort (newSsrt, newTrm, a)
		   
	 | Base (qid, srts, a) ->
	   let newSrts = mapSLst (tsp, sort_map, srts) in
	   if newSrts = srts then
	     srt
	   else
	     Base (qid, newSrts, a)
		     
	 | Boolean _ -> srt
		     
       % | TyVar ??
		     
	 | MetaTyVar (mtv, pos) ->
	   let {name,uniqueId,link} = ! mtv in
	   (case link of
	      | None -> srt
	      | Some ssrt ->
	        let newssrt = mapRec (tsp, sort_map, ssrt) in
		if newssrt = ssrt then
		  srt
		else
		  MetaTyVar(Ref {name     = name,
				 uniqueId = uniqueId,
				 link     = Some newssrt},
			    pos))

         | Pi  (tvs, srt, a) -> Pi (tvs, mapRec (tsp, sort_map, srt), a)  % TODO: what if map alters vars?

         | And (srts,     a) -> maybeAndSort (map (fn srt -> mapRec (tsp, sort_map, srt)) srts, a)

         | Any  _            -> srt

	 | _ -> srt

     def mapSLst (tsp, sort_map, srts) =
       case srts of
	 | [] -> []
	 | ssrt::rsrts -> Cons(mapRec  (tsp, sort_map, ssrt),
			       mapSLst (tsp, sort_map, rsrts))

     def mapSRowOpt (tsp, sort_map, row) =
       case row of
	 | [] -> []
	 | (id,optsrt)::rrow -> Cons ((id, mapRecOpt (tsp, sort_map, optsrt)),
				      mapSRowOpt (tsp, sort_map, rrow))

     def mapSRow (tsp, sort_map, row) =
       case row of
	 | [] -> []
	 | (id,ssrt)::rrow -> Cons ((id, mapRec (tsp, sort_map, ssrt)),
				    mapSRow (tsp, sort_map, rrow))

     def mapRecOpt (tsp, sort_map, opt_sort) =
       case opt_sort of
	 | None      -> None
	 | Some ssrt -> Some (mapRec (tsp, sort_map, ssrt))

     def mapRec (tsp, sort_map, srt) =
       %% apply map to leaves, then apply map to result
       sort_map (mapS (tsp, sort_map, srt))

   in
     mapRec (tsp, sort_map, srt)

 def mapPattern (tsp as (_, _, pattern_map)) pattern =
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
	   
	 | VarPat ((v, srt), a) ->
	   let newSrt = mapSort tsp srt in
	   if newSrt = srt then
	     pattern
	   else
	     VarPat ((v, newSrt), a)
	     
	 | EmbedPat (id, Some pat, srt, a) ->
	   let newPat = mapRec pat in
	   let newSrt = mapSort tsp srt in
	   if newPat = pat && newSrt = srt then
	     pattern
	   else
	     EmbedPat (id, Some newPat, newSrt, a)
	       
	 | EmbedPat (id, None, srt, a) ->
	   let newSrt = mapSort tsp srt in
	   if newSrt = srt then
	     pattern
	   else
	     EmbedPat (id, None, newSrt, a)
		 
	 | RecordPat (fields, a) ->
	   let newFields = map (fn (id, p) -> (id, mapRec p)) fields in
	   if newFields = fields then
	     pattern
	   else
	     RecordPat (newFields, a)
		   
	 | WildPat (srt, a) ->
	   let newSrt = mapSort tsp srt in
	   if newSrt = srt then
	     pattern
	   else
	     WildPat (newSrt, a)
		     
	 | QuotientPat (pat, qid, a) ->
	   let newPat = mapRec pat in
	   if newPat = pat then
	     pattern
	   else
	     QuotientPat (newPat, qid, a)
			 
	 | RestrictedPat (pat, trm, a) ->
	   let newPat = mapRec pat in
	   let newTrm = mapTerm tsp trm in
	   if newPat = pat && newTrm = trm then
	     pattern
	   else
	     RestrictedPat (newPat, newTrm, a)
			 
	 | SortedPat (pat, srt, a) ->
	   let newPat = mapRec pat in
	   let newSrt = mapSort tsp srt in
	   if newPat = pat && newSrt = srt then
	     pattern
	   else
	     SortedPat (newPat, newSrt, a)
			   
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

 %% Like mapTerm but ignores sorts
  op mapSubTerms: [a] (ATerm a -> ATerm a) -> ATerm a -> ATerm a
 def mapSubTerms f term =
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
	   let newDecls = map (fn (pat, trm) -> (pat, mapRec trm)) decls in
	   let newBdy = mapRec bdy in
	   if newDecls = decls && newBdy = bdy then
	     term
	   else
	     Let (newDecls, newBdy, a)
		   
	 | LetRec (decls, bdy, a) ->
	   let newDecls = map (fn ((id, srt), trm) -> ((id, srt), mapRec trm)) decls in
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
			   
	 | SortedTerm (trm, srt, a) ->
	   let newTrm = mapRec trm in
	   if newTrm = trm then
	     term
	   else
	     SortedTerm (newTrm, srt, a)
			     
         | Pi  (tvs, t, a) -> Pi (tvs, mapRec t, a)  % TODO: what if map alters vars?

         | And (tms, a)    -> maybeAndTerm (map mapT tms, a)

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

 %%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%
 %%%                Recursive Term Search
 %%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%

  op existsSubTerm : [b] (ATerm b -> Bool) -> ATerm b -> Bool
 def existsSubTerm pred? term =
   pred? term ||
   (case term of

      | Apply       (M, N,     _) -> existsSubTerm pred? M || existsSubTerm pred? N

      | ApplyN      (Ms,       _) -> exists? (existsSubTerm pred?) Ms

      | Record      (fields,   _) -> exists? (fn (_,M) -> existsSubTerm pred? M) fields

      | Bind        (_,_,M,    _) -> existsSubTerm pred? M

      | The         (_,M,      _) -> existsSubTerm pred? M

      | Let         (decls, M, _) -> existsSubTerm pred? M ||
                                     exists? (fn (_,M) -> existsSubTerm pred? M) decls

      | LetRec      (decls, M, _) -> existsSubTerm pred? M ||
				     exists? (fn (_,M) -> existsSubTerm pred? M) decls

      | Var         _             -> false
				     
      | Fun         _             -> false

      | Lambda      (rules,    _) -> exists? (fn (p, c, M) ->
                                                existsSubTermPat pred? p ||
                                                existsSubTerm pred? c ||
                                                existsSubTerm pred? M)
                                            rules

      | IfThenElse  (M, N, P,  _) -> existsSubTerm pred? M ||
			  	     existsSubTerm pred? N ||
				     existsSubTerm pred? P

      | Seq         (Ms,       _) -> exists? (existsSubTerm pred?) Ms

      | SortedTerm  (M, srt,   _) -> existsSubTerm pred? M

      | Pi          (tvs, t,   _) -> existsSubTerm pred? t

      | And         (tms,      _) -> exists? (existsSubTerm pred?) tms

      | _  -> false
      )				    

 op  existsSubTermPat : [b] (ATerm b -> Bool) -> APattern b -> Bool
 def existsSubTermPat pred? pat =
   case pat of
     | RestrictedPat(_,t,_) -> existsSubTerm pred? t
     | _ -> false

 op  existsPattern? : [b] (APattern b -> Bool) -> APattern b -> Bool
 def existsPattern? pred? pattern =
   pred? pattern ||
   (case pattern of
     | AliasPat(p1, p2,_) ->
       existsPattern? pred? p1 || existsPattern? pred? p2
     | EmbedPat(id, Some pat,_,_) -> existsPattern? pred? pat
     | RecordPat(fields,_) ->
       exists? (fn (_,p)-> existsPattern? pred? p) fields
     | QuotientPat  (pat,_,_) -> existsPattern? pred? pat
     | RestrictedPat(pat,_,_) -> existsPattern? pred? pat
     | SortedPat    (pat,_,_) -> existsPattern? pred? pat
     | _ -> false)

 op [a] existsInType? (pred?: ASort a -> Bool) (ty: ASort a): Bool =
   pred? ty ||
   (case ty of
      | Arrow(x,y,_) -> existsInType? pred? x || existsInType? pred? y
      | Product(prs,_) -> exists? (fn (_,f_ty) -> existsInType? pred? f_ty) prs
      | CoProduct(prs,_)  -> exists? (fn (_,o_f_ty) ->
                                       case o_f_ty of
                                         | Some f_ty -> existsInType? pred? f_ty
                                         | None -> false)
                               prs
      | Quotient(x,_,_) -> existsInType? pred? x
      | Subsort(x,_,_) -> existsInType? pred? x
      | And(tys,_) -> exists? (existsInType? pred?) tys
      | _ -> false)

op [a] existsTypeInPattern? (pred?: ASort a -> Bool) (pat: APattern a): Bool =
  existsPattern? (fn p ->
                  case p of
                    | VarPat ((_, ty), _)    -> existsInType? pred? ty
                    | WildPat(ty, _)         -> existsInType? pred? ty
                    | EmbedPat (_, _, ty, _) -> existsInType? pred? ty
                    | SortedPat(_, ty, _)    -> existsInType? pred? ty
                    | _ -> false)
    pat

op [a] existsTypeInTerm? (pred?: ASort a -> Bool) (tm: ATerm a): Bool =
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
                   | SortedTerm(_, ty, _) -> existsInType? pred? ty
                   | _ -> false)
    tm

 %% folds function over all the subterms in top-down order
  op foldSubTerms : [b,r] (ATerm b * r -> r) -> r -> ATerm b -> r
 def foldSubTerms f val term =
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

     | Lambda    (rules,    _) -> foldl (fn (val,(p, c, M)) ->
					 foldSubTerms f (foldSubTerms f (foldSubTermsPat f val p) c) M)
					newVal rules

     | IfThenElse(M, N, P,  _) -> foldSubTerms f
					       (foldSubTerms f 
						             (foldSubTerms f newVal M) 
						             N)
					       P

     | Seq       (Ms,       _) -> foldl (fn (val,M) -> foldSubTerms f val M) newVal Ms

     | SortedTerm(M,   _,   _) -> foldSubTerms f newVal M

     | Pi        (_,   M,   _) -> foldSubTerms f newVal M

     | And       (tm1::tms, _) -> foldSubTerms f newVal tm1

     | _  -> newVal

 op  foldSubTermsPat : [b,r] (ATerm b * r -> r) -> r -> APattern b -> r
 def foldSubTermsPat f val pat =
   case pat of
     | RestrictedPat(_,t,_) -> foldSubTerms f val t
     | _ -> val


  op foldSubTermsEvalOrder : [b,r] (ATerm b * r -> r) -> r -> ATerm b -> r
 def foldSubTermsEvalOrder f val term =
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

	 | SortedTerm(M,_,    _) -> foldSubTermsEvalOrder f val M

         | Pi        (_,  M,  _) -> foldSubTermsEvalOrder f val M

        %| And       (tms,    _) -> foldl (fn (val,tms) -> foldSubTermsEvalOrder f val tm) val tms % really want join/meet of fold results

         | _  -> val

   in
     case term of
       | Lambda _ -> recVal
       | _        -> f (term, recVal)

 op  foldSubTermsEvalOrderPat : [b,r] (ATerm b * r -> r) -> r -> APattern b -> r
 def foldSubTermsEvalOrderPat f val pat =
   case pat of
     | RestrictedPat(_,t,_) -> foldSubTermsEvalOrder f val t
     | _ -> val

 op  foldSubPatterns : [b,r] (APattern b * r -> r) -> r -> APattern b -> r
 def foldSubPatterns f result pattern =
   let result = f (pattern,result) in
   case pattern of
     | AliasPat(p1, p2,_) ->
       foldSubPatterns f (foldSubPatterns f result p1) p2
     | EmbedPat(id, Some pat,_,_) -> foldSubPatterns f result pat
     | RecordPat(fields,_) ->
       foldl (fn (r,(_,p))-> foldSubPatterns f r p) result fields
     | QuotientPat  (pat,_,_) -> foldSubPatterns f result pat
     | RestrictedPat(pat,_,_) -> foldSubPatterns f result pat
     | SortedPat    (pat,_,_) -> foldSubPatterns f result pat
     | _ -> result

op [b,r] foldTypesInTerm (f: r * ASort b -> r) (init: r) (tm: ATerm b): r =
  let result = Ref init in
  (mapTerm (id, fn s -> (result := f(!result, s); s), id) tm;
   !result)

op [b,r] foldTypesInType (f: r * ASort b -> r) (init: r) (tm: ASort b): r =
  let result = Ref init in
  (mapSort (id, fn s -> (result := f(!result, s); s), id) tm;
   !result)

op [b,r] foldTypesInPattern (f: r * ASort b -> r) (init: r) (tm: APattern b): r =
  let result = Ref init in
  (mapPattern (id, fn s -> (result := f(!result, s); s), id) tm;
   !result)

 %%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%
 %%%                Recursive TSP Replacement
 %%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%
 %%% "TSP" means "Term, Sort, Pattern"

 type ReplaceSort a = (ATerm    a -> Option (ATerm    a)) *
                      (ASort    a -> Option (ASort    a)) *
                      (APattern a -> Option (APattern a))

 op replaceTerm    : [b] ReplaceSort b -> ATerm    b -> ATerm    b
 op replaceSort    : [b] ReplaceSort b -> ASort    b -> ASort    b
 op replacePattern : [b] ReplaceSort b -> APattern b -> APattern b


 def replaceTerm (tsp as (term_map, _, _)) term =
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
		       map (fn (id, srt)-> (id, replaceSort tsp srt)) vars,
		       replaceRec trm,
		       a)
	  
	| The        ((id,srt), trm, a) ->
	  The        ((id, replaceSort tsp srt), replaceRec trm, a)
	  
	| Let         (decls, bdy, a) ->
	  Let         (map (fn (pat, trm)-> (replacePattern tsp pat, replaceRec trm)) decls,
		       replaceRec bdy,
		       a)
	  
	| LetRec      (decls, bdy, a) ->
	  LetRec      (map (fn (id, trm) -> (id, replaceRec trm)) decls,
		       replaceRec bdy,
		       a)
	  
	| Var         ((id,                 srt), a) ->
	  Var         ((id, replaceSort tsp srt), a)
	  
	| Fun         (top,                 srt, a) ->
	  Fun         (top, replaceSort tsp srt, a)
	  
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
	  
	| SortedTerm  (           trm,                 srt, a) ->
	  SortedTerm  (replaceRec trm, replaceSort tsp srt, a)
	  
        | Pi          (tvs,            tm, a) ->  % TODO: can replaceRec alter vars?
	  Pi          (tvs, replaceRec tm, a)

        | And         (               tms, a) ->
	  maybeAndTerm (map replaceRec tms, a)

        | Any _ -> term

        | _  -> term  

    def replaceRec term =
      %% Pre-Node traversal: possibly replace node before checking if leaves should be replaced
      case term_map term of
	| None         -> replace term
	| Some newTerm -> newTerm

  in
    replaceRec term

 def replaceSort (tsp as (_, sort_map, _)) srt =
   let

     def replace srt =
       case srt of
	 | Arrow     (           s1,            s2, a) ->
           Arrow     (replaceRec s1, replaceRec s2, a)

	 | Product   (                                           row, a) ->
	   Product   (map (fn (id, srt) -> (id, replaceRec srt)) row, a)
	   
	 | CoProduct (                                              row,  a) ->
	   CoProduct (map (fn (id, opt) -> (id, replaceRecOpt opt)) row,  a)
	   
	 | Quotient  (           srt,                 trm, a) ->
	   Quotient  (replaceRec srt, replaceTerm tsp trm, a)
	   
	 | Subsort   (           srt,                 trm, a) ->
	   Subsort   (replaceRec srt, replaceTerm tsp trm, a)
	   
	 | Base      (qid,                srts, a) ->
	   Base      (qid, map replaceRec srts, a)
	   
	 | Boolean _ -> srt

        %| TyVar     ??
        %| MetaTyVar ??

         | Pi        (tvs,            srt, a) -> % TODO: can replaceRec alter vars?
	   Pi        (tvs, replaceRec srt, a) 

         | And       (               srts, a) ->
	   maybeAndSort (map replaceRec srts, a)

	 | Any _ -> srt

	 | _ -> srt

     def replaceRecOpt opt_srt =
       case opt_srt of
	 | None     -> None
	 | Some srt -> Some (replaceRec srt)

     def replaceRec srt =
       %% Pre-Node traversal: possibly replace node before checking if leaves should be replaced
       case sort_map srt of
	 | None        -> replace srt
	 | Some newSrt -> newSrt

   in
     replaceRec srt

 def replacePattern (tsp as (_, _, pattern_map)) pattern =
   let

     def replace pattern =
       case pattern of

	 | AliasPat     (           p1,            p2, a) ->
           AliasPat     (replaceRec p1, replaceRec p2, a)

	 | VarPat       ((v,                 srt), a) ->
	   VarPat       ((v, replaceSort tsp srt), a)

	 | EmbedPat     (id, Some             pat,                  srt, a) ->
	   EmbedPat     (id, Some (replaceRec pat), replaceSort tsp srt, a)
	   
	 | EmbedPat     (id, None,                                  srt, a) ->
	   EmbedPat     (id, None,                  replaceSort tsp srt, a)
	   
	 | RecordPat    (                                     fields, a) ->
	   RecordPat    (map (fn (id,p)-> (id, replaceRec p)) fields, a)
	   
	 | WildPat      (                srt, a) ->
	   WildPat      (replaceSort tsp srt, a)

	 | QuotientPat  (           pat, qid, a) -> 
	   QuotientPat  (replaceRec pat, qid, a)

	 | RestrictedPat(           pat,                 trm, a) ->
	   RestrictedPat(replaceRec pat, replaceTerm tsp trm, a)

       % | SortedPat ??
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
 %%% "TSP" means "Term, Sort, Pattern"

 type appTSP a = (ATerm    a -> ()) *
                 (ASort    a -> ()) *
                 (APattern a -> ())

 type ATermOpt a = Option(ATerm a)
 type ASortOpt a = Option(ASort a)

 type ASortScheme  b = TyVars * ASort b
 type ATermScheme  b = TyVars * ATerm b
 type ASortSchemes b = List (ASortScheme b)
 type ATermSchemes b = List (ATermScheme b)

 op appTerm        : [a] appTSP a -> ATerm        a -> ()
 op appSort        : [a] appTSP a -> ASort        a -> ()
 op appPattern     : [a] appTSP a -> APattern     a -> ()
 op appTermOpt     : [a] appTSP a -> ATermOpt     a -> ()
 op appSortOpt     : [a] appTSP a -> ASortOpt     a -> ()
 op appSortSchemes : [a] appTSP a -> ASortSchemes a -> ()
 op appTermSchemes : [a] appTSP a -> ATermSchemes a -> ()

 def appTerm (tsp as (term_app, _, _)) term =
   let 

     def appT (tsp, term) =
       case term of

	 | Apply      (t1, t2,       _) -> (appRec t1; appRec t2)

	 | ApplyN     (terms,        _) -> app appRec terms

	 | Record     (row,          _) -> app (fn (id, trm) -> appRec trm) row

	 | Bind       (_, vars, trm, _) -> (app (fn (id, srt) -> appSort tsp srt) vars;
					    appRec trm)

	 | The        ((id,srt), trm,    _) -> (appSort tsp srt; appRec trm)

	 | Let        (decls, bdy,   _) -> (app (fn (pat, trm) ->
						 (appPattern tsp pat;
						  appRec trm))
					        decls;
					    appRec bdy)

	 | LetRec     (decls, bdy,   _) -> (app (fn (id, trm) -> appRec trm) decls;
					    appRec bdy)

	 | Var        ((id, srt),    _) -> appSort tsp srt
	 
	 | Fun        (top, srt,     _) -> appSort tsp srt
	 
	 | Lambda     (match,        _) -> app (fn (pat, cond, trm) ->
						(appPattern tsp pat;
						 appRec cond;
						 appRec trm))
	                                       match

	 | IfThenElse (t1, t2, t3,   _) -> (appRec t1; appRec t2; appRec t3)

	 | Seq        (terms,        _) -> app appRec terms

	 | SortedTerm (trm, srt,     _) -> (appRec trm; appSort tsp srt)

	 | Pi         (tvs, tm,      _) -> appRec tm

	 | And        (tms,          _) -> app appRec tms

	 | _  -> ()

     def appRec term = 
       %% Post-node traversal: leaves first
       (appT (tsp, term); term_app term)

   in
     appRec term

 def appSort (tsp as (_, srt_app, _)) srt =
   let 

     def appS (tsp, srt) =
       case srt of
	 | Arrow     (s1,  s2,   _) -> (appRec s1;  appRec s2)
	 | Product   (row,       _) -> app (fn (id, srt) -> appRec srt) row
	 | CoProduct (row,       _) -> app (fn (id, opt) -> appSortOpt tsp opt) row
	 | Quotient  (srt, trm,  _) -> (appRec srt; appTerm tsp trm)
	 | Subsort   (srt, trm,  _) -> (appRec srt; appTerm tsp trm)
	 | Base      (qid, srts, _) -> app appRec srts
	 | Boolean               _  -> ()

	%| TyVar     ??
	%| MetaTyVar ??

	 | Pi        (tvs, srt, _) -> appRec srt
	 | And       (srts,     _) -> app appRec srts
	 | Any                  _  -> ()

         | _                       -> ()

     def appRec srt =
       %% Post-node traversal: leaves first
       (appS (tsp, srt); srt_app srt)

   in
     appRec srt

 def appPattern (tsp as (_, _, pattern_app)) pat =
   let 

     def appP (tsp, pat) =
       case pat of
	 | AliasPat     (p1, p2,            _) -> (appRec p1; appRec p2)
	 | VarPat       ((v, srt),          _) -> appSort tsp srt
	 | EmbedPat     (id, Some pat, srt, _) -> (appRec pat; appSort tsp srt)
	 | EmbedPat     (id, None, srt,     _) -> appSort tsp srt
	 | RecordPat    (fields,            _) -> app (fn (id, p) -> appRec p) fields
	 | WildPat      (srt,               _) -> appSort tsp srt
	 | QuotientPat  (pat, _,            _) -> appRec pat
	 | RestrictedPat(pat, trm,          _) -> appRec pat
        %| SortedPat ??
        %| BoolPat   ??
        %| NatPat    ??
	%| StringPat ??
        %| CharPat   ??
	 | _                                   -> ()

     def appRec pat = (appP (tsp, pat); pattern_app pat)

   in
     appRec pat

 def appSortOpt tsp opt_sort =
   case opt_sort of
     | None     -> ()
     | Some srt -> appSort tsp srt

 def appTermOpt tsp opt_term =
   case opt_term of
     | None     -> ()
     | Some trm -> appTerm tsp trm

 def appSortSchemes tsp sort_schemes =
   app (fn (_,srt) -> appSort tsp srt) sort_schemes

 def appTermSchemes tsp term_schemes =
   app (fn (_,term) -> appTerm tsp term) term_schemes

 %%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%
 %%%                Misc Base Terms
 %%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%

 op boolSort?    : [b] ASort b -> Bool
 op stringSort?  : [b] ASort b -> Bool
 op natSort?     : [b] ASort b -> Bool
 op intSort?     : [b] ASort b -> Bool
 op charSort?    : [b] ASort b -> Bool

 def boolSort? s =
   case s of
     | Boolean _ -> true
     | _ -> false

 def stringSort? s =
   case s of
     | Base (Qualified ("String",  "String"),  [], _) -> true
     | _ -> false

 def charSort? s =
   case s of
     | Base (Qualified ("Char",  "Char"),  [], _) -> true
     | _ -> false

 def natSort? s =
   case s of
     | Base (Qualified ("Nat",     "Nat"),     [], _) -> true
     | _ -> false

 def intSort? s =
   case s of
     | Base (Qualified ("Integer", "Int"),     [], _) -> true
     | _ -> false

 %%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%
 %%%  Misc constructors
 %%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%
 
  op mkAndOp : [a] a -> ATerm a
 def mkAndOp a =
   let bool_sort = Boolean a in
   let binary_bool_sort = Arrow (Product ([("1",bool_sort), ("2",bool_sort)], a),
				 bool_sort,
				 a)
   in
     Fun (And, binary_bool_sort, a)

  op mkABase : [b] QualifiedId * List (ASort b) * b -> ASort b
 def mkABase (qid, srts, a) = Base (qid, srts, a)

 op mkTrueA  : [b] b -> ATerm b
 op mkFalseA : [b] b -> ATerm b

 def mkTrueA  a = Fun (Bool true,  Boolean a, a)
 def mkFalseA a = Fun (Bool false, Boolean a, a)


 op [a] isFiniteList (term : ATerm a) : Option (List (ATerm a)) =  
   case term of
     | Fun (Embed ("Nil", false), Base (Qualified("List", "List"), _, _), _) -> Some []
     | Apply (Fun (Embed("Cons", true), 
		   Arrow (Product ([("1", _), ("2", Base (Qualified("List", "List"), _, _))], 
				   _),
			  _,
			  _),
		   _),
	      Record ([(_, t1), (_, t2)], _),
	      _)
       -> 
       (case isFiniteList t2 of
	  | Some terms -> Some (Cons (t1, terms))
	  | _ ->  None)
     | ApplyN ([Fun (Embed ("Cons", true), 
		     Arrow (Product ([("1", _), ("2", Base (Qualified("List", "List"), _, _))], 
				     _),
			    Base (Qualified("List", "List1"), _, _),
			    _),
		     _),
		Record ([(_, t1), (_, t2)], _),
		_],
	       _) 
       -> 
       (case isFiniteList t2 of
	  | Some terms -> Some (Cons (t1, terms))
	  | _  ->  None)
     | _ -> None


endspec
