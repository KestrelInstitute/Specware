MetaSlang qualifying spec {
 import /Library/Base
 import /Library/Legacy/Utilities/State  % for MetaTyVar's
 import /Library/Legacy/DataStructures/ListPair

 op AnnSpecPrinter.printTerm  : [a] ATerm       a -> String %  defined in ../Specs/Printer, which imports this spec (circularity)

 %%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%
 %%%                QualifiedId
 %%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%
 %%%  Basic structure for naming things

 sort Id = String
 sort Qualifier = Id

 %% This is the key used in the qualifier maps for UnQualified Id
 op UnQualified : Qualifier
 def UnQualified = "<unqualified>" % a non-parsable id

 %% The Qualifier's for id's in a spec are established independently
 %% from the name of the spec:  all, some, or none might have the
 %% name of the spec as their qualifier, and the same qualifier can
 %% be used in multiple specs.

 sort QualifiedId = | Qualified Qualifier * Id

 %% An annotated qualified id can record extra information,
 %% e.g. the precise position of the name.
 sort AQualifiedId a = QualifiedId * a

 %% the following are invoked by the parser to make qualified names
 def mkUnQualifiedId  id      =  Qualified (UnQualified, id)
 def mkQualifiedId    (q, id) =  Qualified (q,           id)
 def [a] mkAUnQualifiedId (id,     x : a) = (Qualified (UnQualified, id), x)
 def [a] mkAQualifiedId   (q,  id, x : a) = (Qualified (q,           id), x)

 %% These are used by translation, morphism code
 def unqualified_Boolean = mkUnQualifiedId "Boolean"               % used by translate
 def Boolean_Boolean     = mkQualifiedId ("Boolean", "Boolean")    % used by translate
 def syntactic_qid? (Qualified(q,id)) =                            % used by translate, morphism
   if q = "Boolean" or q = UnQualified then                        % used by translate, morphism
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

 %% This is useful for most normal messages, where you want to be terse:
  op printQualifiedId : QualifiedId -> String
 def printQualifiedId (Qualified (q, id)) =
   if q = UnQualified then
     id
   else
     printQualifierDotId (q, id)

  op printQualifierDotId : Qualifier * Id -> String
 def printQualifierDotId (q, id) =
   if q = "Nat"     or
      q = "String"  or
      q = "Char"    or
      q = UnQualified
   then id
   else q ^ "." ^ id

 def printAliases aliases =
   case aliases of
     | [] -> fail "printAliases: empty name list"
     | [name] -> printQualifiedId name
     | first::rest ->
       "{" ^ (printQualifiedId first) ^
       (foldl (fn (qid, str) -> str ^ ", " ^ printQualifiedId qid)
	      ""
	      rest)
       ^ "}"

 %%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%
 %%%                Type Variables
 %%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%

 sort TyVar   = Id
 sort TyVars  = List TyVar

 %%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%
 %%%                Terms
 %%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%
 %%% ATerm, ASort, APattern, AFun, AVar, AMatch, and MetaTyVar
 %%%  are all mutually recursive types.

 %% Terms are tagged with auxiliary information such as
 %% location information and free variables for use in
 %% various transformation steps.

 sort ATerm b =
  | Apply        ATerm b * ATerm b                       * b
  | ApplyN       List (ATerm b)                          * b % Before elaborateSpec
  | Record       List (Id * ATerm b)                     * b
  | Bind         Binder * List (AVar b)      * ATerm b   * b
  | Let          List (APattern b * ATerm b) * ATerm b   * b
  | LetRec       List (AVar b     * ATerm b) * ATerm b   * b
  | Var          AVar b                                  * b
  | Fun          AFun b * ASort b                        * b
  | Lambda       AMatch b                                * b
  | IfThenElse   ATerm b * ATerm b * ATerm b             * b
  | Seq          List (ATerm b)                          * b
  | SortedTerm   ATerm b * ASort b                       * b
  | Pi           TyVars * ATerm b                        * b  % for now, used only at top level of defn's
  | And          List (ATerm b)                          * b  % for now, used only by colimit and friends -- meet (or join) not be confused with boolean AFun And 
                                                              % We might want to record a quotient of consistent terms plus a list of inconsistent pairs,
                                                              % but then the various mapping functions become much trickier.
  | Any                                                    b  % e.g. "op f : Nat -> Nat"  has defn:  SortedTerm (Any noPos, Arrow (Nat, Nat, p1), noPos)
 
 sort Binder =
  | Forall
  | Exists

 sort AVar b = Id * ASort b

 sort AMatch b = List (APattern b * ATerm b * ATerm b)

 sort ASort b =
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

 sort APattern b =
  | AliasPat     APattern b * APattern b             * b
  | VarPat       AVar b                              * b
  | EmbedPat     Id * Option (APattern b) * ASort b  * b
  | RecordPat    List(Id * APattern b)               * b
  | WildPat      ASort b                             * b
  | BoolPat      Boolean                             * b
  | NatPat       Nat                                 * b
  | StringPat    String                              * b
  | CharPat      Char                                * b
  | RelaxPat     APattern b * ATerm b                * b
  | QuotientPat  APattern b * ATerm b                * b
  | SortedPat    APattern b * ASort b                * b  % Before elaborateSpec

 sort AFun b =

  | Not
  | And
  | Or
  | Implies
  | Iff
  | Equals
  | NotEquals

  | Quotient
  | Choose
  | Restrict
  | Relax

  | PQuotient      ATerm b
  | PChoose        ATerm b
  | PRestrict      ATerm b
  | PRelax         ATerm b

  | Op             QualifiedId * Fixity
  | Project        Id
  | RecordMerge             % <<
  | Embed          Id * Boolean
  | Embedded       Id
  | Select         Id
  | Nat            Nat
  | Char           Char
  | String         String
  | Bool           Boolean
  % hacks to avoid ambiguity during parse of A.B.C, etc.
  | OneName        Id * Fixity         % Before elaborateSpec
  | TwoNames       Id * Id * Fixity    % Before elaborateSpec

 sort Fixity        = | Nonfix | Infix Associativity * Precedence | Unspecified
 sort Associativity = | Left | Right
 sort Precedence    = Nat

 sort AMetaTyVar      b = Ref ({link     : Option (ASort b),
                                uniqueId : Nat,
                                name     : String })

 sort AMetaTyVars     b = List (AMetaTyVar b)
 sort AMetaSortScheme b = AMetaTyVars b * ASort b

 %%% Predicates
 op product?: [a] ASort a -> Boolean
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

  op maybeAndSort : [b] List (ASort b) * b -> ASort b
 def maybeAndSort (srts, pos) =
   let compressed_sorts =
       foldl (fn (srt, new_srts) ->
	      case sortInnerSort srt of
	       %| Any _ -> new_srts % causes evil
		| _ -> 
		  if exists (fn new_srt -> equalSort? (srt, new_srt)) new_srts then
		    new_srts
		  else
		    new_srts ++ [srt])
             []
	     srts
   in
   case compressed_sorts of
     | []    -> Any pos
     | [srt] -> srt
     | _     -> And (srts, pos)

  op maybeAndTerm : [b] List (ATerm b) * b -> ATerm b
 def maybeAndTerm (tms, pos) =
   let compressed_terms =
       foldl (fn (tm, new_tms) ->
	      case termInnerTerm tm of
	       %| Any _ -> new_tms   % causes evil
		| _ -> 
		  if exists (fn new_tm -> equalTerm? (tm, new_tm)) new_tms then
		    new_tms
		  else
		    new_tms ++ [tm])
             []
	     tms
   in
   case compressed_terms of
     | []   -> Any pos
     | [tm] -> tm
     | _    -> And (tms, pos)

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

 sort AFields b = List (AField b)
 sort AField  b = FieldName * ASort b  % used by products and co-products
 sort FieldName = String

  op getField: [a] List (Id * ATerm a) * Id -> Option(ATerm a)
 def getField (m, id) =
   case find (fn (id1,_) -> id = id1) m of
     | None      -> None
     | Some(_,t) -> Some t

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
     | IfThenElse (_,_,_, a) -> a
     | Seq        (_,     a) -> a
     | SortedTerm (_,_,   a) -> a
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
     | Let        (l,t,      b) -> if a = b then tm else Let        (l, t,       a)
     | LetRec     (l,t,      b) -> if a = b then tm else LetRec     (l, t,       a)
     | Var        (v,        b) -> if a = b then tm else Var        (v,          a)
     | Fun        (f,s,      b) -> if a = b then tm else Fun        (f, s,       a)
     | Lambda     (m,        b) -> if a = b then tm else Lambda     (m,          a)
     | IfThenElse (t1,t2,t3, b) -> if a = b then tm else IfThenElse (t1, t2, t3, a)
     | Seq        (l,        b) -> if a = b then tm else Seq        (l,          a)
     | SortedTerm (t,s,      b) -> if a = b then tm else SortedTerm (t, s,       a)
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
     | AliasPat    (_,_,   a) -> a
     | VarPat      (_,     a) -> a
     | EmbedPat    (_,_,_, a) -> a
     | RecordPat   (_,     a) -> a
     | WildPat     (_,     a) -> a
     | BoolPat     (_,     a) -> a
     | NatPat      (_,     a) -> a
     | StringPat   (_,     a) -> a
     | CharPat     (_,     a) -> a
     | RelaxPat    (_,_,   a) -> a
     | QuotientPat (_,_,   a) -> a
     | SortedPat   (_,_,   a) -> a

  op withAnnP: [a] APattern a * a -> APattern a
 def withAnnP (pat, b) =
   case pat of
     | AliasPat    (p1,p2,   a) -> if b = a then pat else AliasPat    (p1,p2,   b)
     | VarPat      (v,       a) -> if b = a then pat else VarPat      (v,       b)
     | EmbedPat    (i,p,s,   a) -> if b = a then pat else EmbedPat    (i,p,s,   b)
     | RecordPat   (f,       a) -> if b = a then pat else RecordPat   (f,       b)
     | WildPat     (s,       a) -> if b = a then pat else WildPat     (s,       b)
     | BoolPat     (bp,      a) -> if b = a then pat else BoolPat     (bp,      b)
     | NatPat      (n,       a) -> if b = a then pat else NatPat      (n,       b)
     | StringPat   (s,       a) -> if b = a then pat else StringPat   (s,       b)
     | CharPat     (c,       a) -> if b = a then pat else CharPat     (c,       b)
     | RelaxPat    (p,t,     a) -> if b = a then pat else RelaxPat    (p,t,     b)
     | QuotientPat (p,t,     a) -> if b = a then pat else QuotientPat (p,t,     b)
     | SortedPat   (p,s,     a) -> if b = a then pat else SortedPat   (p,s,     b)

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
     | Boolean              b  -> if a = b then srt else Boolean              a
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

 %%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%
 %%%                Term components
 %%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%

 op unpackTerm    : [b] ATerm b -> TyVars * ASort b * ATerm b
 op termTyVars    : [b] ATerm b -> TyVars
 op termSort      : [b] ATerm b -> ASort b
 op termInnerTerm : [b] ATerm b -> ATerm b

 def unpackTerm t =
   let (tvs, tm) = 
       case t of
	 | Pi (tvs, tm, _) -> (tvs, tm)
	 | And _ -> fail ("unpackTerm: Trying to unpack an And of terms.")
	 | _ -> ([], t)
   in
   case tm of
     | SortedTerm (tm, srt, _) -> (tvs, srt,         tm) 
     | _                       -> (tvs, termSort tm, tm)

 def termTyVars tm =
   case tm of
     | Pi (tvs, _, _) -> tvs
     | And _ -> fail ("termTyVars: Trying to extract type vars from an And of terms.")
     | _ -> []

 def termSort term =
   case term of
     | Apply      (t1,t2,   _) -> (case termSort t1 of
				     | Arrow(dom,rng,_) -> rng
				     | _ -> System.fail ("Cannot extract sort of application "
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
     | Lambda     (Cons((pat,_,body),_), a) -> Arrow(patternSort pat, termSort body, a)
     | Lambda     ([],                   _) -> System.fail "termSort: Ill formed lambda abstraction"
     | IfThenElse (_,t2,t3, _)              -> termSort t2
     | Seq        (_,       a)              -> Product([],a)
     | SortedTerm (_,   s,  _)              -> s
     | Pi         (tvs, t,  a)              -> Pi (tvs, termSort t, a) 
     | And        (tms,     a)              -> maybeAndSort (map termSort tms,  a)
     | Any                  a               -> Any a
     | mystery -> fail ("\n No match in termSort with: " ^ (anyToString mystery) ^ "\n")

 def termInnerTerm tm =
   let tm = 
       case tm of
	 | Pi (_, tm, _) -> tm
	 | And _ -> fail ("termInnerTerm: Trying to extract inner term from an And of terms.")
	 | _ -> tm
   in
     case tm of
       | SortedTerm (tm, _, _) -> tm
       | _                     -> tm

 %%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%
 %%%                Pattern components
 %%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%

 op patternSort : [b] APattern b -> ASort b

 def patternSort pat =
   case pat of
     | AliasPat    (p1,_,    _) -> patternSort p1
     | VarPat      ((_,s),   _) -> s
     | EmbedPat    (_,_,s,   _) -> s
     | RecordPat   (fields,  a) -> Product (map (fn (id, p) -> (id, patternSort p)) fields, a)
     | WildPat     (srt,     _) -> srt
     | BoolPat     (_,       a) -> Boolean a
     | NatPat      (n,       a) -> mkABase  (Qualified ("Nat",     "Nat"),     [], a)
     | StringPat   (_,       a) -> mkABase  (Qualified ("String",  "String"),  [], a)
     | CharPat     (_,       a) -> mkABase  (Qualified ("Char",    "Char"),    [], a)
     | RelaxPat    (p, pred, a) -> Subsort  (patternSort p, pred,                  a)
     | QuotientPat (p, t,    a) -> Quotient (patternSort p, t,                     a)
     | SortedPat   (_, srt,  _) -> srt

 %%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%
 %%%                Term Equalities
 %%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%

 op equalTerm?          : [a,b] ATerm    a * ATerm    b -> Boolean
 op equalSort?          : [a,b] ASort    a * ASort    b -> Boolean
 op equalPattern?       : [a,b] APattern a * APattern b -> Boolean
 op equalFun?           : [a,b] AFun     a * AFun     b -> Boolean
 op equalVar?           : [a,b] AVar     a * AVar     b -> Boolean

 %% term equality ignoring sorts
 op equalTermStruct?    : [a,b] ATerm    a * ATerm    b -> Boolean
 op equalPatternStruct? : [a,b] APattern a * APattern b -> Boolean
 op equalFunStruct?     : [a,b] AFun     a * AFun     b -> Boolean
 op equalVarStruct?     : [a,b] AVar     a * AVar     b -> Boolean

  op equalList? : [a,b] List a * List b * (a * b -> Boolean) -> Boolean
 def equalList? (x, y, eqFn) =
   (length x) = (length y) &&
   (case (x, y) of
      | ([],              [])             -> true
      | (head_x::tail_x,  head_y::tail_y) -> eqFn (head_x, head_y) &&
                                             equalList? (tail_x, tail_y, eqFn)
      | _ -> false)

  op equalOpt? : [a,b] Option a * Option b * (a * b -> Boolean) -> Boolean
 def equalOpt? (x, y, eqFn) =
   case (x, y) of
     | (None,    None)    -> true
     | (Some x1, Some y1) -> eqFn (x1, y1)
     | _ -> false

 def equalTerm? (t1, t2) =
   case (t1, t2) of

     | (Apply      (x1, y1,      _),
        Apply      (x2, y2,      _)) -> equalTerm? (x1, x2) && equalTerm? (y1, y2)

     | (ApplyN     (xs1,         _),
        ApplyN     (xs2,         _)) -> equalList? (xs1, xs2, equalTerm?)

     | (Record     (xs1,         _),
        Record     (xs2,         _)) -> equalList? (xs1, xs2,
                                                    fn ((label1, x1), (label2, x2)) ->
                                                       label1 = label2 &&
                                                       equalTerm? (x1, x2))

     | (Bind       (b1, vs1, x1, _),
        Bind       (b2, vs2, x2, _)) -> b1 = b2 &&
                                        %% Could check modulo alpha conversion...
                                        equalList? (vs1, vs2, equalVar?) &&
                                        equalTerm? (x1,  x2)

     | (Let        (pts1, b1,    _),
        Let        (pts2, b2,    _)) -> equalTerm? (b1, b2) &&
                                        equalList? (pts1, pts2,
                                                    fn ((p1, t1), (p2, t2)) ->
                                                      equalPattern? (p1, p2) &&
                                                      equalTerm?    (t1, t2))

     | (LetRec     (vts1, b1,    _),
        LetRec     (vts2, b2,    _)) -> equalTerm? (b1, b2) &&
                                        equalList? (vts1, vts2,
                                                    fn ((v1, t1), (v2, t2)) ->
                                                     equalVar?  (v1, v2) &&
                                                     equalTerm? (t1, t2))

     | (Var        (v1,          _),
        Var        (v2,          _)) -> equalVar? (v1, v2)

     | (Fun        (f1, s1,      _),
        Fun        (f2, s2,      _)) -> equalFun? (f1, f2) && equalSort? (s1, s2)

     | (Lambda     (xs1,         _),
        Lambda     (xs2,         _)) -> equalList? (xs1, xs2,
                                                    fn ((p1, c1, b1), (p2, c2, b2)) ->
                                                      equalPattern?  (p1, p2) &&
                                                      equalTerm?     (c1, c2) &&
                                                      equalTerm?     (b1, b2))

     | (IfThenElse (c1, x1, y1,  _),
        IfThenElse (c2, x2, y2,  _)) -> equalTerm? (c1, c2) &&
                                        equalTerm? (x1, x2) &&
                                        equalTerm? (y1, y2)

     | (Seq        (xs1,         _),
        Seq        (xs2,         _)) -> equalList? (xs1, xs2, equalTerm?)

     | (SortedTerm (x1, s1,      _),
        SortedTerm (x2, s2,      _)) -> equalTerm? (x1, x2) && equalSort? (s1, s2)

     | (Pi         (tvs1, tm1,   _), 
        Pi         (tvs2, tm2,   _)) -> tvs1 = tvs2 && equalTerm? (tm1, tm2) % TODO: handle alpha equivalence

     | (And        (tms1,        _), 
        And        (tms2,        _)) -> foldl (fn (t1, t2, eq?) -> eq? && equalTerm? (t1, t2))
					      true
					      (tms1, tms2)

     | (Any  _,    Any  _)           -> true  % TODO: Tricky -- should this be some kind of lisp EQ test?

     | _ -> false

 def equalSort? (s1, s2) =
   case (s1,s2) of

     | (Arrow     (x1, y1,  _),
        Arrow     (x2, y2,  _)) -> equalSort? (x1, x2) && equalSort? (y1, y2)

     | (Product   (xs1,     _),
        Product   (xs2,     _)) -> equalList? (xs1, xs2,
                                               fn ((l1, x1), (l2, x2)) ->
					       l1 = l2 &&
					       equalSort? (x1, x2))

     | (CoProduct (xs1,     _),
        CoProduct (xs2,     _)) -> equalList? (xs1, xs2,
                                               fn ((l1, x1), (l2, x2)) ->
					       l1 = l2 &&
					       equalOpt? (x1, x2, equalSort?))

     | (Quotient  (x1, t1,  _),
        Quotient  (x2, t2,  _)) -> equalSort? (x1, x2) && equalTerm? (t1, t2)

     | (Subsort   (x1, t1,  _),
        Subsort   (x2, t2,  _)) -> equalSort? (x1, x2) && equalTerm? (t1, t2)

     | (Base      (q1, xs1, _),
        Base      (q2, xs2, _)) -> q1 = q2 && equalList? (xs1, xs2, equalSort?)

     | (Boolean _, Boolean _)   -> true

     | (TyVar     (v1,      _),
        TyVar     (v2,      _)) -> v1 = v2

     | (MetaTyVar (mtv1,    _),
        MetaTyVar (mtv2,    _)) ->
       let ({link=link1, uniqueId=id1, name}) = ! mtv1 in
       let ({link=link2, uniqueId=id2, name}) = ! mtv2 in
       id1 = id2 or
       (case (link1,link2) of
	  %% This case handles the situation where an
	  %%  unlinked MetaTyVar is compared against itself.
          | (Some ls1, Some ls2) -> equalSort? (ls1, ls2)
	  %% The following two cases handle situations where
	  %%  MetaTyVar X is linked to unlinked MetaTyVar Y
	  %%  and we are comparing X with Y (or Y with X).
	  | (Some ls1, _)        -> equalSort? (ls1, s2)
	  | (_,        Some ls2) -> equalSort? (s1,  ls2)
	  | _ -> false)

     | (MetaTyVar (mtv1, _), _) ->
       let ({link=link1, uniqueId=id1, name}) = ! mtv1 in
       (case link1 of
	  | Some ls1 -> equalSort? (ls1, s2)
	  | _ -> false)

     | (_, MetaTyVar (mtv2, _)) ->
       let ({link=link2, uniqueId=id2, name}) = ! mtv2 in
       (case link2 of
	  | Some ls2 -> equalSort? (s1, ls2)
	  | _ -> false)

     | (Pi         (tvs1, s1,    _), 
        Pi         (tvs2, s2,    _)) -> tvs1 = tvs2 && 
					equalSort? (s1, s2) % TODO: handle alpha equivalence

     | (And        (srts1,       _),  
        And        (srts2,       _)) -> %% TODO: Handle reordering?
					foldl (fn (s1, s2, eq?) ->  
					       eq? && equalSort? (s1, s2))
					      true
					      (srts1, srts2)

     | (Any  _,    Any  _)           -> true  % TODO: Tricky -- should this be some kind of lisp EQ test?

     | _ -> false

 def equalPattern? (p1, p2) =
   case (p1, p2) of

     | (AliasPat    (x1, y1,      _),
        AliasPat    (x2, y2,      _)) -> equalPattern? (x1, x2) && equalPattern? (y1, y2)

     | (VarPat      (v1,          _),
        VarPat      (v2,          _)) -> equalVar? (v1, v2)

     | (EmbedPat    (i1, op1, s1, _),
        EmbedPat    (i2, op2, s2, _)) -> i1 = i2 &&
                                         equalSort? (s1,  s2) &&
                                         equalOpt?  (op1, op2, equalPattern?)

     | (RecordPat   (xs1,         _),
        RecordPat   (xs2,         _)) -> equalList? (xs1, xs2,
                                                     fn ((label1, x1), (label2, x2)) ->
                                                        label1 = label2 &&
                                                        equalPattern? (x1, x2))

     | (WildPat     (s1,          _),
        WildPat     (s2,          _)) -> equalSort? (s1, s2)

     | (BoolPat     (x1,          _),
        BoolPat     (x2,          _)) -> x1 = x2

     | (NatPat      (x1,          _),
        NatPat      (x2,          _)) -> x1 = x2

     | (StringPat   (x1,          _),
        StringPat   (x2,          _)) -> x1 = x2

     | (CharPat     (x1,          _),
        CharPat     (x2,          _)) -> x1 = x2

     | (RelaxPat    (x1, t1,      _),
        RelaxPat    (x2, t2,      _)) -> equalPattern? (x1, x2) && equalTerm? (t1, t2)

     | (QuotientPat (x1, t1,      _),
        QuotientPat (x2, t2,      _)) -> equalPattern? (x1, x2) && equalTerm? (t1, t2)

     | (SortedPat   (x1, t1,      _),
        SortedPat   (x2, t2,      _)) -> equalPattern? (x1, x2) && equalSort? (t1, t2)

     | _ -> false

 def equalFun? (f1, f2) =
   case (f1, f2) of

     | (Not,          Not         ) -> true
     | (And,          And         ) -> true
     | (Or,           Or          ) -> true
     | (Implies,      Implies     ) -> true
     | (Iff,          Iff         ) -> true
     | (Equals,       Equals      ) -> true
     | (NotEquals,    NotEquals   ) -> true

     | (Quotient,     Quotient    ) -> true
     | (Choose,       Choose      ) -> true
     | (Restrict,     Restrict    ) -> true
     | (Relax,        Relax       ) -> true

     | (PQuotient t1, PQuotient t2) -> equalTerm? (t1, t2)
     | (PChoose   t1, PChoose   t2) -> equalTerm? (t1, t2)
     | (PRestrict t1, PRestrict t2) -> equalTerm? (t1, t2)
     | (PRelax    t1, PRelax    t2) -> equalTerm? (t1, t2)

     | (Op        x1, Op        x2) -> x1 = x2
     | (Project   x1, Project   x2) -> x1 = x2
     | (RecordMerge,  RecordMerge ) -> true
     | (Embed     x1, Embed     x2) -> x1 = x2
     | (Embedded  x1, Embedded  x2) -> x1 = x2
    %| (Select    x1, Select    x2) -> x1 = x2
     | (Nat       x1, Nat       x2) -> x1 = x2
     | (Char      x1, Char      x2) -> x1 = x2
     | (String    x1, String    x2) -> x1 = x2
     | (Bool      x1, Bool      x2) -> x1 = x2

     | (OneName   x1, OneName   x2) -> x1.1 = x2.1
     | (TwoNames  x1, TwoNames  x2) -> (x1.1 = x2.1) && (x1.2 = x2.2)

     | _ -> false

 def equalVar? ((id1,s1), (id2,s2)) = 
   id1 = id2 && equalSort? (s1, s2)

  op equalTyVar?: TyVar * TyVar -> Boolean
 def equalTyVar? (tyVar1, tyVar2) = 
   tyVar1 = tyVar2

  op equalTyVars?: TyVars * TyVars -> Boolean
 def equalTyVars? (tyVars1, tyVars2) =
   all (fn (tyV1, tyV2) -> equalTyVar? (tyV1, tyV2)) 
       (tyVars1, tyVars2)

 def equalTermStruct? (t1, t2) =
   case (t1, t2) of

     | (Apply      (x1, y1,      _),
        Apply      (x2, y2,      _)) -> equalTermStruct? (x1, x2) && equalTermStruct? (y1, y2)

     | (ApplyN     (xs1,         _),
        ApplyN     (xs2,         _)) -> equalList? (xs1, xs2, equalTermStruct?)

     | (Record     (xs1,         _),
        Record     (xs2,         _)) -> equalList? (xs1, xs2,
                                                    fn ((label1, x1), (label2, x2)) ->
						    label1 = label2 &&
						    equalTermStruct? (x1, x2))

     | (Bind       (b1, vs1, x1, _),
        Bind       (b2, vs2, x2, _)) -> b1 = b2 &&
                                        %% Could check modulo alpha conversion...
                                        equalList? (vs1, vs2, equalVarStruct?) &&
                                        equalTermStruct? (x1,  x2)

     | (Let        (pts1, b1,    _),
        Let        (pts2, b2,    _)) -> equalTermStruct? (b1, b2) &&
                                        equalList? (pts1, pts2,
                                                    fn ((p1, t1), (p2, t2)) ->
						    equalPatternStruct? (p1, p2) &&
						    equalTermStruct?    (t1, t2))

     | (LetRec     (vts1, b1,    _),
        LetRec     (vts2, b2,    _)) -> equalTermStruct? (b1, b2) &&
                                        equalList? (vts1, vts2,
                                                    fn ((v1, t1),(v2, t2)) ->
						    equalVarStruct?  (v1, v2) &&
						    equalTermStruct? (t1, t2))

     | (Var        (v1,          _),
        Var        (v2,          _)) -> equalVarStruct? (v1, v2)

     | (Fun        (f1, _,       _),
        Fun        (f2, _,       _)) -> equalFunStruct? (f1, f2)

     | (Lambda     (xs1,         _),
        Lambda     (xs2,         _)) -> equalList? (xs1, xs2,
                                                    fn ((p1, c1, b1), (p2, c2, b2)) ->
						    equalPatternStruct?  (p1, p2) &&
						    equalTermStruct?     (c1, c2) &&
						    equalTermStruct?     (b1, b2))

     | (IfThenElse (c1, x1, y1,  _),
        IfThenElse (c2, x2, y2,  _)) -> equalTermStruct? (c1, c2) &&
                                        equalTermStruct? (x1, x2) &&
                                        equalTermStruct? (y1, y2)

     | (Seq        (xs1,         _),
        Seq        (xs2,         _)) -> equalList? (xs1, xs2, equalTermStruct?)

     | (SortedTerm (x1, s1,      _),
        SortedTerm (x2, s2,      _)) -> equalTermStruct? (x1, x2)

     | (Pi         (tvs1, t1,    _), 
        Pi         (tvs2, t2,    _)) -> tvs1 = tvs2 && equalTermStruct? (t1, t2) % TODO: handle alpha equivalence

     | (And        (tms1,        _), 
        And        (tms2,        _)) -> foldl (fn (t1, t2, eq?) -> eq? && equalTermStruct? (t1, t2))
					      true
					      (tms1, tms2)

     | (Any  _,    Any  _)           -> true % TODO: Tricky -- should this be some kind of lisp EQ test?

     | _ -> false

 def equalFunStruct? (f1, f2) =
   case (f1, f2) of

     | (Not,                  Not         )         -> true
     | (And,                  And         )         -> true
     | (Or,                   Or          )         -> true
     | (Implies,              Implies     )         -> true
     | (Iff,                  Iff         )         -> true
     | (Equals,               Equals      )         -> true
     | (NotEquals,            NotEquals   )         -> true

     | (Quotient,             Quotient    )         -> true
     | (Choose,               Choose      )         -> true
     | (Restrict,             Restrict    )         -> true
     | (Relax,                Relax       )         -> true

     | (PQuotient t1,         PQuotient t2)         -> equalTermStruct? (t1, t2)
     | (PChoose   t1,         PChoose   t2)         -> equalTermStruct? (t1, t2)
     | (PRestrict t1,         PRestrict t2)         -> equalTermStruct? (t1, t2)
     | (PRelax    t1,         PRelax    t2)         -> equalTermStruct? (t1, t2)

     | (Op        x1,         Op        x2)         -> x1 = x2
     | (Project   x1,         Project   x2)         -> x1 = x2
     | (RecordMerge,          RecordMerge)          -> true
     | (Embed     x1,         Embed     x2)         -> x1 = x2
     | (Embedded  x1,         Embedded  x2)         -> x1 = x2
    %| (Select    x1,         Select    x2)         -> x1 = x2
     | (Nat       x1,         Nat       x2)         -> x1 = x2
     | (Char      x1,         Char      x2)         -> x1 = x2
     | (String    x1,         String    x2)         -> x1 = x2
     | (Bool      x1,         Bool      x2)         -> x1 = x2

     | (OneName   x1,         OneName   x2)         ->  x1.1 = x2.1
     | (TwoNames  x1,         TwoNames  x2)         -> (x1.1 = x2.1) && (x1.2 = x2.2)
     | (OneName   x1,         TwoNames  x2)         ->  x1.1 = x2.2
     | (TwoNames  x1,         OneName   x2)         ->  x1.2 = x2.1
     | (Op (Qualified x1, _), TwoNames  x2)         -> (x1.1 = x2.1) && (x1.2 = x2.2)
     | (TwoNames  x1,         Op (Qualified x2, _)) -> (x1.1 = x2.1) && (x1.2 = x2.2)
     | (OneName   x1,         Op (Qualified x2, _)) ->  x1.1 = x2.2
     | (Op (Qualified x1, _), OneName   x2)         ->  x1.2 = x2.1

     | _ -> false

 def equalPatternStruct? (p1, p2) =
   case (p1, p2) of

     | (AliasPat    (x1, y1,      _),
        AliasPat    (x2, y2,      _)) -> equalPatternStruct? (x1, x2) && 
                                         equalPatternStruct? (y1, y2)

     | (VarPat      (v1,          _),
        VarPat      (v2,          _)) -> equalVarStruct? (v1, v2)

     | (EmbedPat    (i1, op1, _,  _),
        EmbedPat    (i2, op2, _,  _)) -> i1 = i2 &&
                                         equalOpt?  (op1, op2, equalPatternStruct?)

     | (RecordPat   (xs1,         _),
        RecordPat   (xs2,         _)) -> equalList? (xs1, xs2,
                                                     fn ((label1, x1), (label2, x2)) ->
						     label1 = label2 &&
						     equalPatternStruct? (x1, x2))

     | (WildPat     (s1,          _),
        WildPat     (s2,          _)) -> equalSort? (s1, s2)

     | (BoolPat     (x1,          _),
        BoolPat     (x2,          _)) -> x1 = x2

     | (NatPat      (x1,          _),
        NatPat      (x2,          _)) -> x1 = x2

     | (StringPat   (x1,          _),
        StringPat   (x2,          _)) -> x1 = x2

     | (CharPat     (x1,          _),
        CharPat     (x2,          _)) -> x1 = x2

     | (RelaxPat    (x1, t1,      _),
        RelaxPat    (x2, t2,      _)) -> equalPatternStruct? (x1, x2) && equalTermStruct? (t1, t2)

     | (QuotientPat (x1, t1,      _),
        QuotientPat (x2, t2,      _)) -> equalPatternStruct? (x1, x2) && equalTermStruct? (t1, t2)

     | (SortedPat   (x1, _,       _),
        SortedPat   (x2, _,       _)) -> equalPatternStruct? (x1, x2)

     | _ -> false

 def equalVarStruct? ((id1,_), (id2,_)) = id1 = id2

 %%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%
 %%%                Recursive TSP Mappings
 %%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%
 %%% "TSP" means "Term, Sort, Pattern"

 sort TSP_Maps b = (ATerm    b -> ATerm    b) *
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

         | Any _           -> term

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

         | Pi  (tvs, srt, a) -> Pi (tvs, mapS (tsp, sort_map, srt), a)  % TODO: what if map alters vars?

         | And (srts,     a) -> maybeAndSort (map (fn srt -> mapS (tsp, sort_map, srt)) srts, a)

         | Any  _            -> srt

	 | _ -> srt

     def mapSLst (tsp, sort_map, srts) =
       case srts of
	 | [] -> []
	 | ssrt::rsrts -> cons(mapRec  (tsp, sort_map, ssrt),
			       mapSLst (tsp, sort_map, rsrts))

     def mapSRowOpt (tsp, sort_map, row) =
       case row of
	 | [] -> []
	 | (id,optsrt)::rrow -> cons ((id, mapRecOpt (tsp, sort_map, optsrt)),
				      mapSRowOpt (tsp, sort_map, rrow))

     def mapSRow (tsp, sort_map, row) =
       case row of
	 | [] -> []
	 | (id,ssrt)::rrow -> cons ((id, mapRec (tsp, sort_map, ssrt)),
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
		     
	 | RelaxPat (pat, trm, a) ->
	   let newPat = mapRec pat in
	   let newTrm = mapTerm tsp trm in
	   if newPat = pat && newTrm = trm then
	     pattern
	   else
	     RelaxPat (newPat, newTrm, a)
		       
	 | QuotientPat (pat, trm, a) ->
	   let newPat = mapRec pat in
	   let newTrm = mapTerm tsp trm in
	   if newPat = pat && newTrm = trm then
	     pattern
	   else
	     QuotientPat (newPat, newTrm, a)
			 
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
	   let newVars = map (fn (id,srt)-> (id, srt)) vars in
	   let newTrm = mapRec trm in
	   if newVars = vars && newTrm = trm then
	     term
	   else
	     Bind (bnd, newVars, newTrm, a)
		 
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
			       (pat, mapRec cond, mapRec trm))
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

         | Any  _ -> term
			     
     def mapRec term =
       %% apply map to leaves, then apply map to result
       f (mapT term)

   in
     mapRec term

 %%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%
 %%%                Recursive Term Search
 %%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%

  op existsSubTerm : [b] (ATerm b -> Boolean) -> ATerm b -> Boolean
 def existsSubTerm pred? term =
   pred? term or
   (case term of

      | Apply       (M, N,     _) -> existsSubTerm pred? M or existsSubTerm pred? N

      | ApplyN      (Ms,       _) -> exists (existsSubTerm pred?) Ms

      | Record      (fields,   _) -> exists (fn (_,M) -> existsSubTerm pred? M) fields

      | Bind        (_,_,M,    _) -> existsSubTerm pred? M

      | Let         (decls, M, _) -> existsSubTerm pred? M or
                                     exists (fn (_,M) -> existsSubTerm pred? M) decls

      | LetRec      (decls, M, _) -> existsSubTerm pred? M or
				     exists (fn (_,M) -> existsSubTerm pred? M) decls

      | Var         _             -> false
				     
      | Fun         _             -> false

      | Lambda      (rules,    _) -> exists (fn (_, c, M) -> 
					     existsSubTerm pred? c or
					     existsSubTerm pred? M)
                                            rules

      | IfThenElse  (M, N, P,  _) -> existsSubTerm pred? M or
			  	     existsSubTerm pred? N or
				     existsSubTerm pred? P

      | Seq         (Ms,       _) -> exists (existsSubTerm pred?) Ms

      | SortedTerm  (M, srt,   _) -> existsSubTerm pred? M

      | Pi          (tvs, t,   _) -> existsSubTerm pred? t

      | And         (tms,      _) -> exists (existsSubTerm pred?) tms

      | Any                    _  -> false
      )				    

 %% folds function over all the subterms in top-down order
 %% Other orders such as evaluation order would be useful
  op foldSubTerms : [b,r] (ATerm b * r -> r) -> r -> ATerm b -> r
 def foldSubTerms f val term =
   let newVal = f (term, val) in
   case term of

     | Apply     (M, N, _)     -> foldSubTerms f (foldSubTerms f newVal M) N

     | ApplyN    (Ms,       _) -> foldl (fn (M,val)     -> foldSubTerms f val M) newVal Ms

     | Record    (fields, _)   -> foldl (fn ((_,M),val) -> foldSubTerms f val M) newVal fields

     | Bind      (_,_,M,    _) -> foldSubTerms f newVal M

     | Let       (decls, N, _) -> foldl (fn ((_,M),val) -> foldSubTerms f val M)
                                        (foldSubTerms f newVal N) 
					decls

     | LetRec    (decls, N, _) -> foldl (fn ((_,M),val) -> (foldSubTerms f val M))
				        (foldSubTerms f newVal N) 
					decls

     | Var _                   -> newVal

     | Fun _                   -> newVal

     | Lambda    (rules,    _) -> foldl (fn ((_, c, M),val) ->
					 foldSubTerms f (foldSubTerms f val c) M)
					newVal rules

     | IfThenElse(M, N, P,  _) -> foldSubTerms f
					       (foldSubTerms f 
						             (foldSubTerms f newVal M) 
						             N)
					       P

     | Seq       (Ms,       _) -> foldl (fn (M,val) -> foldSubTerms f val M) newVal Ms

     | SortedTerm(M,   _,   _) -> foldSubTerms f newVal M

     | Pi        (_,   M,   _) -> foldSubTerms f newVal M

    %| And       (tms,      _) -> foldl (fn (tm,val) -> foldSubTerms f val tm) newVal tms % really want join/meet of fold results

     | Any                  _  -> newVal

  op foldSubTermsEvalOrder : [b,r] (ATerm b * r -> r) -> r -> ATerm b -> r
 def foldSubTermsEvalOrder f val term =
   let recVal =
       case term of

	 | Apply     (M as Lambda (rules,  _), N, _) ->	% case statement
	   let val = (foldSubTermsEvalOrder f val N) in
	   foldl (fn ((_,c,M),val) ->
		  foldSubTermsEvalOrder f (foldSubTermsEvalOrder f val c) M)
	         val rules

	 | Apply     (M,N,    _) -> foldSubTermsEvalOrder f
	                                                  (foldSubTermsEvalOrder f val M)
							  N

	 | ApplyN    (Ms,     _) -> foldl (fn (M,val) -> 
					   foldSubTermsEvalOrder f val M)
		                          val Ms

	 | Record    (fields, _) -> foldl (fn ((_,M),val) -> 
					    foldSubTermsEvalOrder f val M)
					  val fields

	 | Bind      (_,_,M,  _) -> foldSubTermsEvalOrder f val M

	 | Let       (decls,N,_) -> let dval = foldl (fn ((_, M), val) ->
						      foldSubTermsEvalOrder f val M)
						     val decls
				    in 
				      foldSubTermsEvalOrder f dval N

	 | LetRec    (decls,N,_) -> foldl (fn ((_, M), val) -> 
					   foldSubTermsEvalOrder f val M)
				          (foldSubTermsEvalOrder f val N) 
					  decls

	 | Var _                 -> val

	 | Fun _                 -> val

	 | Lambda    (rules,  _) -> let val = f (term, val) in
				    %% lambda is evaluated before its contents
				    %% this is an approximation as we don't know when
				    %% contents will be evaluated
				    foldl (fn ((_, c, M), val) ->
					   foldSubTermsEvalOrder f
					                         (foldSubTermsEvalOrder f val c) 
								 M)
					  val rules

         | IfThenElse(M,N,P,  _) -> foldSubTermsEvalOrder f
				 	                  (foldSubTermsEvalOrder f
							                         (foldSubTermsEvalOrder f val M) 
										 N)
							  P

	 | Seq       (Ms,     _) -> foldl (fn (M, val) ->
					   foldSubTermsEvalOrder f val M)
					  val Ms

	 | SortedTerm(M,_,    _) -> foldSubTermsEvalOrder f val M

         | Pi        (_,  M,  _) -> foldSubTermsEvalOrder f val M

        %| And       (tms,    _) -> foldl (fn (tms, val) -> foldSubTermsEvalOrder f val tm) val tms % really want join/meet of fold results

         | Any                _  -> val

   in
     case term of
       | Lambda _ -> recVal
       | _        -> f (term, recVal)


 %%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%
 %%%                Recursive TSP Replacement
 %%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%
 %%% "TSP" means "Term, Sort, Pattern"

 sort ReplaceSort a = (ATerm    a -> Option (ATerm    a)) *
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

	 | AliasPat    (           p1,            p2, a) ->
           AliasPat    (replaceRec p1, replaceRec p2, a)

	 | VarPat      ((v,                 srt), a) ->
	   VarPat      ((v, replaceSort tsp srt), a)

	 | EmbedPat    (id, Some             pat,                  srt, a) ->
	   EmbedPat    (id, Some (replaceRec pat), replaceSort tsp srt, a)
	   
	 | EmbedPat    (id, None,                                  srt, a) ->
	   EmbedPat    (id, None,                  replaceSort tsp srt, a)
	   
	 | RecordPat   (                                     fields, a) ->
	   RecordPat   (map (fn (id,p)-> (id, replaceRec p)) fields, a)
	   
	 | WildPat     (                srt, a) ->
	   WildPat     (replaceSort tsp srt, a)

	 | RelaxPat    (           pat,                 trm, a) ->
	   RelaxPat    (replaceRec pat, replaceTerm tsp trm, a)
	   
	 | QuotientPat (           pat,                 trm, a) ->
	   QuotientPat (replaceRec pat, replaceTerm tsp trm, a)

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

 sort appTSP a = (ATerm    a -> ()) *
                 (ASort    a -> ()) *
                 (APattern a -> ())

 sort ATermOpt a = Option(ATerm a)
 sort ASortOpt a = Option(ASort a)

 sort ASortScheme  b = TyVars * ASort b
 sort ATermScheme  b = TyVars * ATerm b
 sort ASortSchemes b = List (ASortScheme b)
 sort ATermSchemes b = List (ATermScheme b)

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

	 | Any                       _  -> ()

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
       (appS (tsp, srt); 
	srt_app srt)

   in
     appRec srt

 def appPattern (tsp as (_, _, pattern_app)) pat =
   let 

     def appP (tsp, pat) =
       case pat of
	 | AliasPat    (p1, p2,            _) -> (appRec p1; appRec p2)
	 | VarPat      ((v, srt),          _) -> appSort tsp srt
	 | EmbedPat    (id, Some pat, srt, _) -> (appRec pat; appSort tsp srt)
	 | EmbedPat    (id, None, srt,     _) -> appSort tsp srt
	 | RecordPat   (fields,            _) -> app (fn (id, p) -> appRec p) fields
	 | WildPat     (srt,               _) -> appSort tsp srt
	 | RelaxPat    (pat, trm,          _) -> (appRec pat; appTerm tsp trm)
	 | QuotientPat (pat, trm,          _) -> (appRec pat; appTerm tsp trm)
        %| SortedPat ??
        %| BoolPat   ??
        %| NatPat    ??
	%| StringPat ??
        %| CharPat   ??
	 | _                                  -> ()

     def appRec pat = 
       (appP (tsp, pat); 
	pattern_app pat)

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

 op boolSort?    : [b] ASort b -> Boolean
 op stringSort?  : [b] ASort b -> Boolean
 op natSort?     : [b] ASort b -> Boolean
 op integerSort? : [b] ASort b -> Boolean
 op charSort?    : [b] ASort b -> Boolean

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

 def integerSort? s =
   case s of
     | Base (Qualified ("Integer",     "Integer"),     [], _) -> true
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
}
