% derived from SW4/Languages/MetaSlang/ADT/Terms/ATerm.sl, v1.2

MetaSlang qualifying spec { 
 import /Library/Base
 import /Library/Legacy/Utilities/State  % for MetaTyVar's

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
 def mkUnQualifiedId  id                 =  Qualified (UnQualified, id)
 def mkQualifiedId    (qualifier, id)    =  Qualified (qualifier,   id)
 def fa (a) mkAUnQualifiedId (id,            x : a) = (Qualified (UnQualified, id), x) 
 def fa (a) mkAQualifiedId   (qualifier, id, x : a) = (Qualified (qualifier,   id), x)

 op printQualifiedId : QualifiedId -> String
 def printQualifiedId (Qualified (qualifier, id)) =
  if qualifier = UnQualified then
    id
  else 
    printQualifierDotId (qualifier, id)

 op printQualifierDotId : Qualifier * Id -> String
 def printQualifierDotId (qualifier, id) =
  if qualifier = "Nat"     or 
     qualifier = "Boolean" or
     qualifier = "String"  or
     qualifier = "Char"    or
     qualifier = UnQualified
  then id
  else qualifier^"."^id

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
  | Bind         Binder * List (AVar b) * ATerm b        * b
  | Let          List (APattern b * ATerm b) * ATerm b   * b
  | LetRec       List (AVar b * ATerm b) * ATerm b       * b
  | Var          AVar b                                  * b
  | Fun          AFun b * ASort b                        * b
  | Lambda       AMatch b                                * b
  | IfThenElse   ATerm b * ATerm b * ATerm b             * b
  | Seq          List (ATerm b)                          * b
  | SortedTerm   ATerm b * ASort b                       * b

 sort Binder = 
  | Forall 
  | Exists 

 sort AVar b = Id * ASort b

 %% AMatch b = List (APattern b * Condition * ATerm b)
 sort AMatch b = List (APattern b * ATerm b * ATerm b) 

 sort ASort b =  
  | Arrow        ASort b * ASort b                   * b
  | Product      List (Id * ASort b)                 * b
  | CoProduct    List (Id * Option (ASort b))        * b
  | Quotient     ASort b * ATerm b                   * b
  | Subsort      ASort b * ATerm b                   * b
  | Base         QualifiedId * List (ASort b)        * b
%  | Base        QualifiedId * List (ASort b)        * b  % Before elaborateSpec
  | TyVar        TyVar                               * b
  | MetaTyVar    AMetaTyVar b                        * b  % Before elaborateSpec
       
 sort APattern b = 
  | AliasPat     APattern b * APattern b             * b
  | VarPat       AVar b                              * b
  | EmbedPat     Id * Option (APattern b) * ASort b  * b
  | RecordPat    List(Id * APattern b)               * b
  | WildPat      ASort b                             * b
  | StringPat    String                              * b
  | BoolPat      Boolean                             * b
  | CharPat      Char                                * b
  | NatPat       Nat                                 * b
  | RelaxPat     APattern b * ATerm b                * b
  | QuotientPat  APattern b * ATerm b                * b
  | SortedPat    APattern b * ASort b                * b  % Before elaborateSpec

 sort AFun b = 
  | Equals 
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

 sort Fixity        = | Nonfix | Infix Associativity * Precedence
 sort Associativity = | Left | Right
 sort Precedence    = Nat


 sort AMetaTyVar      b = Ref ({link     : Option (ASort b),
                                uniqueId : Nat,
                                name     : String }) 

 sort AMetaTyVars     b = List (AMetaTyVar b)
 sort AMetaSortScheme b = AMetaTyVars b * ASort b 

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

 %%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%
 %%%                Term Annotations
 %%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%

 op termAnn: fa(a) ATerm a -> a 
 def termAnn(t) = 
  case t of
     | ApplyN     (_,     a) -> a
     | Record     (_,     a) -> a
     | Bind       (_,_,_, a) -> a
     | Let        (_,_,   a) -> a  
     | LetRec     (_,_,   a) -> a
     | Var        (_,     a) -> a
     | SortedTerm (_,_,   a) -> a
     | Fun        (_,_,   a) -> a
     | Lambda     (_,     a) -> a
     | IfThenElse (_,_,_, a) -> a
     | Seq        (_,     a) -> a

 op sortAnn: fa(a) ASort a -> a
 def sortAnn(s) =
  case s of
     | Arrow     (_,_, a) -> a
     | Product   (_,   a) -> a
     | CoProduct (_,   a) -> a
     | Quotient  (_,_, a) -> a
     | Subsort   (_,_, a) -> a
     | Base     (_,_, a) -> a
     | TyVar     (_,   a) -> a
     | MetaTyVar (_,   a) -> a

 %op patAnn: fa(a) APattern a -> a        % Not needed yet

 op withAnnS: fa(a) ASort a * a -> ASort a
 def withAnnS(s,a) =
  case s of
     | Arrow     (s1,s2,    _) -> Arrow     (s1,s2,    a)
     | Product   (fields,   _) -> Product   (fields,   a)
     | CoProduct (fields,   _) -> CoProduct (fields,   a)
     | Quotient  (s,t,      _) -> Quotient  (s,t,      a)
     | Subsort   (s,t,      _) -> Subsort   (s,t,      a)
     | Base     (qid,srts, _) -> Base     (qid,srts, a)
     | TyVar     (tv,       _) -> TyVar     (tv,       a)
     | MetaTyVar (tv,       _) -> MetaTyVar (tv,       a)

 %%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%
 %%%                Term Sorts
 %%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%

 op termSort    : fa(b) ATerm    b -> ASort b
 op patternSort : fa(b) APattern b -> ASort b

 def termSort (term) = 
  case term of
     | Apply      (t1,t2,   _) ->
        (case termSort t1 of
           | Arrow(dom,rng,_) -> rng
           | _ -> System.fail ("Cannot extract sort of application " 
                                                  ^ System.toString term))
     | ApplyN     ([t1,t2], _) ->
        (case termSort t1 of
           | Arrow(dom,rng,_) -> rng
           | _ -> System.fail ("Cannot extract sort of application "
                                                  ^ System.toString term))
     | Bind       (_,_,_,   a) -> mkABase (Qualified ("Boolean", "Boolean"), [], a)
     | Record     (fields,  a) -> Product(List.map (fn (id,t) -> (id,termSort t)) fields, 
                                          a)
     | Let        (_,term,  _) -> termSort term
     | LetRec     (_,term,  _) -> termSort term
     | Var        ((_,srt), _) -> srt
     | Fun        (_,srt,   _) -> srt
     | IfThenElse (_,t2,t3, _) -> termSort t2
     | Seq        (_,       a) -> Product([],a)
     | SortedTerm (_,s,     _) -> s
     | Lambda     (Cons((pat,_,body),_), a) -> Arrow(patternSort pat, termSort body, a)
     | Lambda     ([],                   _) -> System.fail "Ill formed lambda abstraction"
     | _ -> System.fail "Non-exhaustive match in termSort"
    
 def patternSort (pat) = 
  case pat of
     | WildPat     (srt,     _) -> srt
     | AliasPat    (p1,_,    _) -> patternSort p1
     | VarPat      ((_,s),   _) -> s
     | EmbedPat    (_,_,s,   _) -> s
     | RecordPat   (fields,  a) -> Product(map (fn(id,p) -> (id,patternSort p)) fields, a)
     | StringPat   (_,       a) -> mkABase  (Qualified ("String",  "String"),  [], a)
     | NatPat      (n,       a) -> mkABase  (Qualified ("Nat",     "Nat"),     [], a)
     | BoolPat     (_,       a) -> mkABase  (Qualified ("Boolean", "Boolean"), [], a)
     | CharPat     (_,       a) -> mkABase  (Qualified ("Char",    "Char"),    [], a)
     | RelaxPat    (p, pred, a) -> Subsort  (patternSort p, pred,                  a)
     | QuotientPat (p, t,    a) -> Quotient (patternSort p, t,                     a)
     | SortedPat   (_, srt,  _) -> srt


 %%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%
 %%%                Term Equalities
 %%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%

 op equalTerm?    : fa(a,b) ATerm    a * ATerm    b -> Boolean
 op equalSort?    : fa(a,b) ASort    a * ASort    b -> Boolean
 op equalPattern? : fa(a,b) APattern a * APattern b -> Boolean
 op equalFun?     : fa(a,b) AFun     a * AFun     b -> Boolean
 op equalVar?     : fa(a,b) AVar     a * AVar     b -> Boolean

 op equalList? : fa(a,b) List a * List b * (a * b -> Boolean) -> Boolean
 def equalList? (x, y, eqFn) =
  (length x) = (length y) &
  (case (x, y) of
      | ([],              [])             -> true
      | (head_x::tail_x,  head_y::tail_y) -> eqFn (head_x, head_y) & 
                                             equalList? (tail_x, tail_y, eqFn)
      | _ -> false)

 op equalOpt? : fa(a,b) Option a * Option b * (a * b -> Boolean) -> Boolean
 def equalOpt? (x, y, eqFn) =
  case (x, y) of
     | (None,    None)    -> true
     | (Some x1, Some y1) -> eqFn (x1, y1)
     | _ -> false

 def equalTerm? (t1, t2) =
  case (t1, t2) of

     | (Apply      (x1, y1,      _), 
        Apply      (x2, y2,      _)) -> equalTerm? (x1, x2) & equalTerm? (y1, y2)

     | (ApplyN     (xs1,         _),   
        ApplyN     (xs2,         _)) -> equalList? (xs1, xs2, equalTerm?)

     | (Record     (xs1,         _), 
        Record     (xs2,         _)) -> equalList? (xs1, xs2, 
                                                    fn ((label1,x1),(label2,x2)) -> 
                                                       label1 = label2 & 
                                                       equalTerm? (x1, x2))

     | (Bind       (b1, vs1, x1, _),
        Bind       (b2, vs2, x2, _)) -> b1 = b2 & 
                                        %% Could check modulo alpha conversion...
                                        equalList? (vs1, vs2, equalVar?) &
                                        equalTerm? (x1,  x2)

     | (Let        (pts1, b1,    _),
        Let        (pts2, b2,    _)) -> equalTerm? (b1, b2) &
                                        equalList? (pts1, pts2,
                                                    fn ((p1,t1),(p2,t2)) -> 
                                                      equalPattern? (p1, p2) & 
                                                      equalTerm?    (t1, t2))

     | (LetRec     (vts1, b1,    _),
        LetRec     (vts2, b2,    _)) -> equalTerm? (b1, b2) &
                                        equalList? (vts1, vts2,
                                                    fn ((v1,t1),(v2,t2)) -> 
                                                     equalVar?  (v1, v2) & 
                                                     equalTerm? (t1, t2))

     | (Var        (v1,          _),
        Var        (v2,          _)) -> equalVar?(v1,v2)

     | (Fun        (f1, s1,      _),
        Fun        (f2, s2,      _)) -> equalFun?(f1,f2) & equalSort?(s1,s2)

     | (Lambda     (xs1,         _),
        Lambda     (xs2,         _)) -> equalList? (xs1, xs2,
                                                    fn ((p1,c1,b1),(p2,c2,b2)) ->
                                                      equalPattern?  (p1, p2) & 
                                                      equalTerm?     (c1, c2) & 
                                                      equalTerm?     (b1, b2))

     | (IfThenElse (c1, x1, y1,  _),
        IfThenElse (c2, x2, y2,  _)) -> equalTerm? (c1, c2) & 
                                        equalTerm? (x1, x2) & 
                                        equalTerm? (y1, y2)

     | (Seq        (xs1,         _),
        Seq        (xs2,         _)) -> equalList? (xs1, xs2, equalTerm?)

     | (SortedTerm (x1, s1,      _),
        SortedTerm (x2, s2,      _)) -> equalTerm? (x1, x2) & equalSort? (s1, s2)

     | _ -> false

 def equalSort? (s1, s2) =
  case (s1,s2) of
     | (Arrow     (x1, y1,  _), 
        Arrow     (x2, y2,  _)) -> equalSort? (x1, x2) & equalSort? (y1, y2)
     | (Product   (xs1,     _), 
        Product   (xs2,     _)) -> equalList? (xs1, xs2,
                                               fn ((l1,x1),(l2,x2)) -> 
                                                  l1 = l2 & 
                                                  equalSort? (x1, x2))
     | (CoProduct (xs1,     _), 
        CoProduct (xs2,     _)) -> equalList? (xs1, xs2, 
                                               fn ((l1,x1),(l2,x2)) -> 
                                                  l1 = l2 & 
                                                  equalOpt? (x1, x2, equalSort?))
     | (Quotient  (x1, t1,  _), 
        Quotient  (x2, t2,  _)) -> equalSort? (x1, x2) & equalTerm? (t1, t2)
     | (Subsort   (x1, t1,  _), 
        Subsort   (x2, t2,  _)) -> equalSort? (x1, x2) & equalTerm? (t1, t2)
     | (Base      (q1, xs1, _), 
        Base      (q2, xs2, _)) -> q1 = q2 & equalList? (xs1, xs2, equalSort?)
     | (TyVar     (v1,      _), 
        TyVar     (v2,      _)) -> v1 = v2

     | (MetaTyVar (v1,      _), 
        MetaTyVar (v2,      _)) ->
          let ({link=link1, uniqueId=id1, name}) = ! v1 in
          let ({link=link2, uniqueId=id2, name}) = ! v2 in
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

     | (MetaTyVar (v1,      _),
        _                     ) ->
          let ({link=link1, uniqueId=id1, name}) = ! v1 in
            (case link1 of
               | Some ls1 -> equalSort? (ls1, s2)
               | _ -> false)

     | (_,
        MetaTyVar (v2,      _)) ->
          let ({link=link2, uniqueId=id2, name}) = ! v2 in
            (case link2 of
               | Some ls2 -> equalSort? (s1, ls2)
               | _ -> false)

     | _ -> false

 def equalPattern?(p1,p2) =
  case (p1, p2) of
     | (AliasPat    (x1, y1,      _),
        AliasPat    (x2, y2,      _)) -> equalPattern?(x1,x2) & equalPattern?(y1,y2)

     | (VarPat      (v1,          _),
        VarPat      (v2,          _)) -> equalVar?(v1,v2)

     | (EmbedPat    (i1, op1, s1, _),
        EmbedPat    (i2, op2, s2, _)) -> i1 = i2 & 
                                         equalSort? (s1,  s2) & 
                                         equalOpt?  (op1, op2, equalPattern?)

     | (RecordPat   (xs1,         _),
        RecordPat   (xs2,         _)) -> equalList? (xs1, xs2, 
                                                     fn ((label1,x1), (label2,x2)) -> 
                                                        label1 = label2 & 
                                                        equalPattern? (x1, x2))

     | (WildPat     (s1,          _),
        WildPat     (s2,          _)) -> equalSort?(s1,s2)

     | (StringPat   (x1,          _),
        StringPat   (x2,          _)) -> x1 = x2

     | (BoolPat     (x1,          _),
        BoolPat     (x2,          _)) -> x1 = x2

     | (CharPat     (x1,          _),
        CharPat     (x2,          _)) -> x1 = x2

     | (NatPat      (x1,          _),
        NatPat      (x2,          _)) -> x1 = x2

     | (RelaxPat    (x1, t1,      _),
        RelaxPat    (x2, t2,      _)) -> equalPattern?(x1,x2) & equalTerm?(t1,t2)

     | (QuotientPat (x1, t1,      _),
        QuotientPat (x2, t2,      _)) -> equalPattern?(x1,x2) & equalTerm?(t1,t2)

     | (SortedPat   (x1, t1,      _),
        SortedPat   (x2, t2,      _)) -> equalPattern?(x1,x2) & equalSort?(t1,t2)

     | _ -> false

 def equalFun? (f1, f2) =
  case (f1, f2) of
     | (PQuotient t1,       PQuotient t2)       -> equalTerm? (t1, t2)
     | (PChoose   t1,       PChoose   t2)       -> equalTerm? (t1, t2)
     | (PRestrict t1,       PRestrict t2)       -> equalTerm? (t1, t2)
     | (PRelax    t1,       PRelax    t2)       -> equalTerm? (t1, t2)

     | (Equals,             Equals      )       -> true
     | (Quotient,           Quotient    )       -> true
     | (Choose,             Choose      )       -> true
     | (Restrict,           Restrict    )       -> true
     | (Relax,              Relax       )       -> true

     | (Op        x1,       Op        x2)       -> x1 = x2
     | (Project   x1,       Project   x2)       -> x1 = x2
     | (Embed     x1,       Embed     x2)       -> x1 = x2
     | (Embedded  x1,       Embedded  x2)       -> x1 = x2
     % | (Select    x1,       Select    x2)       -> x1 = x2
     | (Nat       x1,       Nat       x2)       -> x1 = x2
     | (Char      x1,       Char      x2)       -> x1 = x2
     | (String    x1,       String    x2)       -> x1 = x2
     | (Bool      x1,       Bool      x2)       -> x1 = x2

     | (OneName   x1,       OneName   x2)       -> x1 = x2
     | (TwoNames  x1,       TwoNames  x2)       -> x1 = x2 
     | _ -> false

 def equalVar? ((id1,s1), (id2,s2)) = id1 = id2 & equalSort? (s1, s2)

 %%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%
 %%%                Recursive TSP Mappings
 %%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%
 %%% "TSP" means "Term, Sort, Pattern"

 sort TSP_Maps b = (ATerm    b -> ATerm    b) *
                   (ASort    b -> ASort    b) * 
                   (APattern b -> APattern b)

 op mapTerm    : fa(b) TSP_Maps b -> ATerm    b -> ATerm    b
 op mapSort    : fa(b) TSP_Maps b -> ASort    b -> ASort    b
 op mapPattern : fa(b) TSP_Maps b -> APattern b -> APattern b

 def mapTerm (tsp_maps as (term_map,_,_)) term = 
  %%
  %% traversal of term with post-order applications of term_map
  %%
  %% i.e. recursively apply term_map to result of mapping over term
  %%
  %% i.e. term will be revised using term_map on its components,
  %% then term_map will be applied to the revised term.
  %%
  let 
   def mapT (tsp_maps,term) = 
    case term of
       | Fun        (top,                  srt,  a) ->
         let newSrt = mapSort tsp_maps srt in
	 if srt = newSrt then term
	  else Fun(top, newSrt,  a)

       | Var        ((id,                  srt), a) ->
         let newSrt = mapSort tsp_maps srt in
	 if srt = newSrt then term
          else Var((id, newSrt), a)

       | Let        (decls, bdy, a) -> 
	 let newDecls = map (fn (pat, trm) -> (mapPattern tsp_maps pat, mapRec trm)) decls in
	 let newBdy = mapRec bdy in
	 if decls = newDecls & bdy = newBdy then term
	   else Let (newDecls, newBdy, a)

       | LetRec     (decls, bdy, a) -> 
	 let newDecls = map (fn ((id, srt), trm) -> ((id, mapSort tsp_maps srt),
						     mapRec trm))
	                  decls in
	 let newBdy = mapRec bdy in
	 if decls = newDecls & bdy = newBdy then term
	   else LetRec(newDecls, newBdy, a)

       | Record     (row, a) -> 
	 let newRow = map (fn (id,trm) -> (id, mapRec trm)) row in
	 if row = newRow then term
	   else Record(newRow,a)

       | IfThenElse (       t1,        t2,        t3, a) -> 
	 let newT1 = mapRec t1 in
	 let newT2 = mapRec t2 in
	 let newT3 = mapRec t3 in
	 if newT1 = t1 & newT2 = t2 & newT3 = t3 then term
	   else IfThenElse (newT1, newT2, newT3, a)

       | Lambda     (match, a) -> 
         let newMatch = map (fn (pat, cond, trm)->
			      (mapPattern tsp_maps pat, mapRec cond, mapRec trm))
                          match in
	 if match = newMatch then term
	   else Lambda (newMatch, a)

       | Bind       (bnd, vars, trm, a) -> 
	 let newVars = map (fn (id,srt)-> (id, mapSort tsp_maps srt)) vars in
	 let newTrm = mapRec trm in
	 if vars = newVars & trm = newTrm then term
	   else Bind (bnd, newVars, newTrm, a)

       | Apply      (       t1,        t2,  a) ->
	 let newT1 = mapRec t1 in
	 let newT2 = mapRec t2 in
	 if newT1 = t1 & newT2 = t2 then term
	  else Apply(mapRec newT1, mapRec newT2,  a)

       | Seq        (                terms, a) -> 
	 let newTerms = map mapRec terms in
	 if newTerms = terms then term
	   else Seq(newTerms, a)

       | ApplyN     (                terms, a) -> 
	 let newTerms = map mapRec terms in
	 if newTerms = terms then term
	   else ApplyN (newTerms, a)

       | SortedTerm (       trm,                  srt, a) -> 
	 let newTrm = mapRec trm in
         let newSrt = mapSort tsp_maps srt in
	 if newTrm = trm & srt = newSrt then term
	   else SortedTerm (newTrm, newSrt, a)
   def mapRec term = 
     %% apply map to leaves, then apply map to result
     term_map (mapT (tsp_maps,term))
  in
    mapRec term

 def mapSort (tsp_maps as (_,sort_map,_)) srt =
  let
   %% Written with explicit parameter passing to avoid closure creation
   def mapS (tsp_maps,sort_map,srt) = 
    case srt of
       | CoProduct (row,       a) ->
         let newRow = mapSRowOpt (tsp_maps,sort_map,row) in
	 if newRow = row then srt
	   else CoProduct (newRow, a)
       | Product   (row,       a) -> 
         let newRow = mapSRow (tsp_maps,sort_map,row) in
	 if newRow = row then srt
	   else Product (newRow, a)
       | Arrow     (s1,  s2,   a) ->
	 let newS1 = mapRec (tsp_maps,sort_map,s1) in
	 let newS2 = mapRec (tsp_maps,sort_map,s2) in
	 if newS1 = s1 & newS2 = s2 then srt
	   else Arrow (newS1,  newS2, a)
       | Quotient  (ssrt, trm,  a) ->
	 let newSsrt = mapRec (tsp_maps,sort_map,ssrt) in
	 let newTrm =  mapTerm tsp_maps trm in
	 if newSsrt = ssrt & newTrm = trm then srt
	   else Quotient (newSsrt, newTrm,  a)
       | Subsort   (ssrt, trm,  a) ->
	 let newSsrt = mapRec (tsp_maps,sort_map,ssrt) in
	 let newTrm =  mapTerm tsp_maps trm in
	 if newSsrt = ssrt & newTrm = trm then srt
	   else Subsort (newSsrt, newTrm,  a)
     % | Subset    (ssrt, trm,  a) -> Subset    (mapRec ssrt, mapTerm tsp_maps trm, a)
       | Base      (qid, srts, a) ->
	 let newSrts = mapSLst(tsp_maps,sort_map,srts) in
	 if newSrts = srts then srt
	   else Base (qid, newSrts, a)
       | MetaTyVar(tv,pos) -> 
	   let {name,uniqueId,link} = ! tv in
	   (case link
	      of None -> srt
	       | Some ssrt ->
	         let newssrt = mapRec (tsp_maps,sort_map,ssrt) in
		 if newssrt = ssrt then srt
		  else MetaTyVar(Ref {name = name,uniqueId = uniqueId,
				      link = Some newssrt},pos))
       | _ -> srt

   def mapSLst (tsp_maps,sort_map,srts) =
     case srts of
       | [] -> []
       | ssrt::rsrts -> cons(mapRec(tsp_maps,sort_map,ssrt),
			     mapSLst(tsp_maps,sort_map,rsrts))

   def mapSRowOpt (tsp_maps,sort_map,row) =
     case row of
       | [] -> []
       | (id,optsrt)::rrow -> cons((id,mapRecOpt(tsp_maps,sort_map,optsrt)),
				   mapSRowOpt(tsp_maps,sort_map,rrow))

   def mapSRow (tsp_maps,sort_map,row) =
     case row of
       | [] -> []
       | (id,ssrt)::rrow -> cons((id,mapRec(tsp_maps,sort_map,ssrt)),
				 mapSRow(tsp_maps,sort_map,rrow))

   def mapRecOpt (tsp_maps,sort_map,opt_sort) = 
     case opt_sort of
       | None     -> None
       | Some ssrt -> Some (mapRec (tsp_maps,sort_map,ssrt))
   def mapRec (tsp_maps,sort_map,srt) = 
     %% apply map to leaves, then apply map to result
     sort_map (mapS (tsp_maps,sort_map,srt))
  in
    mapRec (tsp_maps,sort_map,srt)

 def mapPattern (tsp_maps as (_,_,pattern_map)) pattern = 
  let
   def mapP (tsp_maps,pattern) = 
    case pattern of

       | AliasPat    (p1,        p2,        a)     -> 
         let newP1 = mapRec p1 in
         let newP2 = mapRec p2 in
	 if newP1 = p1 & newP2 = p2 then pattern
	   else AliasPat (newP1, newP2, a)

       | EmbedPat    (id, Some pat,         srt,                  a) -> 
	 let newPat = mapRec pat in
	 let newSrt = mapSort tsp_maps srt in
	 if newPat = pat & newSrt = srt then pattern
	   else EmbedPat (id, Some newPat, newSrt, a)

       | EmbedPat    (id, None, srt,                  a) -> 
	 let newSrt = mapSort tsp_maps srt in
	 if newSrt = srt then pattern
	   else EmbedPat    (id, None, newSrt, a)

       | RelaxPat    (pat,        trm,                  a) -> 
	 let newPat = mapRec pat in
	 let newTrm = mapTerm tsp_maps trm in
	 if newPat = pat & newTrm = trm then pattern
	   else RelaxPat (newPat, newTrm, a)

       | QuotientPat (pat, trm, a) -> 
	 let newPat = mapRec pat in
	 let newTrm = mapTerm tsp_maps trm in
	 if newPat = pat & newTrm = trm then pattern
	   else QuotientPat (newPat, newTrm, a)

       | VarPat      ((v, srt),                  a) -> 
	 let newSrt = mapSort tsp_maps srt in
	 if newSrt = srt then pattern
	   else VarPat ((v, newSrt), a)

       | WildPat     (srt,                  a) -> 
	 let newSrt = mapSort tsp_maps srt in
	 if newSrt = srt then pattern
	   else WildPat (newSrt, a)

       | RecordPat   (fields, a) -> 
	 let newFields = map (fn (id, p) -> (id, mapRec p)) fields in
	 if newFields = fields then pattern
	   else RecordPat (newFields, a)

       | SortedPat   (pat,        srt,                  a) -> 
	 let newPat = mapRec pat in
	 let newSrt = mapSort tsp_maps srt in
	 if newPat = pat & newSrt = srt then pattern
	   else SortedPat   (newPat, newSrt, a)

       | _ -> pattern

   def mapRec (pattern) = 
     %% apply map to leaves, then apply map to result
     pattern_map (mapP (tsp_maps, pattern))

  in
    mapRec pattern

 %%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%
 %%%                Recursive Term Search
 %%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%

 op existsSubTerm : fa(b) (ATerm b -> Boolean) -> ATerm b -> Boolean

 def existsSubTerm pred? term = 
  pred? term or
  (case term of
      | Var         _             -> false
      | Fun         _             -> false

      | Apply       (M, N,     _) -> existsSubTerm pred? M or existsSubTerm pred? N

      | Record      (fields,   _) -> exists (fn (_,M) -> existsSubTerm pred? M) fields

      | Let         (decls, M, _) -> existsSubTerm pred? M or 
                                     exists (fn (_,M) -> existsSubTerm pred? M) decls

      | LetRec      (decls, M, _) -> existsSubTerm pred? M or 
                                     exists (fn (_,M) -> existsSubTerm pred? M) decls

      | Seq         (Ms,       _) -> exists (existsSubTerm pred?) Ms

      | IfThenElse  (M, N, P,  _) -> existsSubTerm pred? M or 
                                     existsSubTerm pred? N or
                                     existsSubTerm pred? P

      | Bind        (_,_,M,    _) -> existsSubTerm pred? M

      | Lambda      (rules,    _) -> exists (fn (_, c, M) -> existsSubTerm pred? c or
                                                             existsSubTerm pred? M)
                                            rules     

      | ApplyN      (Ms,       _) -> exists (existsSubTerm pred?) Ms

      | SortedTerm  (M, srt,   _) -> existsSubTerm pred? M)


 %%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%
 %%%                Recursive TSP Replacement
 %%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%
 %%% "TSP" means "Term, Sort, Pattern"

 sort ReplaceSort a = (ATerm    a -> Option (ATerm    a)) * 
                      (ASort    a -> Option (ASort    a)) * 
                      (APattern a -> Option (APattern a))

 op replaceTerm    : fa(b) ReplaceSort b -> ATerm    b -> ATerm    b
 op replaceSort    : fa(b) ReplaceSort b -> ASort    b -> ASort    b
 op replacePattern : fa(b) ReplaceSort b -> APattern b -> APattern b


 def replaceTerm (tsp_maps as (term_map, _, _)) term = 
  let
   def replace term = 
    case term of
       | Fun         (top, srt,                      a) -> 
         Fun         (top, replaceSort tsp_maps srt, a)

       | Var         ((id, srt),                      a) -> 
         Var         ((id, replaceSort tsp_maps srt), a)

       | Let         (decls, bdy, a) -> 
         Let         (map (fn (pat, trm)-> (replacePattern tsp_maps pat, replaceRec trm))
                          decls,
                      replaceRec bdy,
                      a)

       | LetRec      (decls, bdy, a) -> 
         LetRec      (map (fn (id, trm) -> (id, replaceRec trm)) decls,
                      replaceRec bdy,
                      a)

       | Record      (row,                                             a) -> 
         Record      (map (fn (id, trm) -> (id, replaceRec trm)) row,  a)


       | IfThenElse  (t1,            t2,            t3,            a) -> 
         IfThenElse  (replaceRec t1, replaceRec t2, replaceRec t3, a)

       | Lambda      (match, a) -> 
         Lambda      (map (fn (pat, cond, trm)->
                            (replacePattern tsp_maps pat, 
                             replaceRec     cond, 
                             replaceRec     trm))
                           match,
                      a)

       | Bind        (bnd, vars, trm, a) -> 
         Bind        (bnd, 
                      map (fn (id, srt)-> (id, replaceSort tsp_maps srt)) vars,
                      replaceRec trm,
                      a)

       | Apply       (t1,            t2,            a) -> 
         Apply       (replaceRec t1, replaceRec t2, a)

       | Seq         (terms,                 a) -> 
         Seq         (map replaceRec terms,  a)

       | ApplyN      (terms,                 a) -> 
         ApplyN      (map replaceRec terms,  a)

       | SortedTerm  (trm,            srt,                      a) -> 
         SortedTerm  (replaceRec trm, replaceSort tsp_maps srt, a)
   def replaceRec term = 
     %% Pre-Node traversal: possibly replace node before checking if leaves should be replaced
     case term_map term of
       | None         -> replace term
       | Some newTerm -> newTerm
  in
    replaceRec term

 def replaceSort (tsp_maps as (_, sort_map, _)) srt = 
  let
   def replace srt = 
    case srt of
       | CoProduct (row,                                                a) -> 
         CoProduct (map (fn (id, opt) -> (id, replaceRecOpt opt)) row,  a)

       | Product   (row,                                               a) -> 
         Product   (map (fn (id, srt) -> (id, replaceRec srt)) row,    a)

       | Arrow     (s1,            s2,            a) -> 
         Arrow     (replaceRec s1, replaceRec s2, a)

       | Quotient  (srt,            trm,                      a) ->
         Quotient  (replaceRec srt, replaceTerm tsp_maps trm, a)

       | Subsort   (srt,            trm,                      a) ->
         Subsort   (replaceRec srt, replaceTerm tsp_maps trm, a)

       | Base      (qid, srts,                 a) ->
         Base      (qid, map replaceRec srts,  a)

       | Base     (qid, srts,                 a) -> 
         Base     (qid, map replaceRec srts,  a)

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

 def replacePattern (tsp_maps as (_,_,pattern_map)) pattern = 
  let
   def replace pattern = 
    case pattern of
       | AliasPat    (p1,            p2,            a) -> 
         AliasPat    (replaceRec p1, replaceRec p2, a)

       | EmbedPat    (id, Some pat,              srt,                      a) ->
         EmbedPat    (id, Some (replaceRec pat), replaceSort tsp_maps srt, a)

       | EmbedPat    (id, None,                  srt,                      a) ->
         EmbedPat    (id, None,                  replaceSort tsp_maps srt, a)

       | RelaxPat    (pat,            trm,                      a) ->
         RelaxPat    (replaceRec pat, replaceTerm tsp_maps trm, a)

       | QuotientPat (pat,            trm,                      a) ->
         QuotientPat (replaceRec pat, replaceTerm tsp_maps trm, a)

       | VarPat      ((v, srt),                      a) -> 
         VarPat      ((v, replaceSort tsp_maps srt), a)

       | WildPat     (srt,                           a) -> 
         WildPat     (replaceSort tsp_maps srt,      a)

       | RecordPat   (fields,                                      a) ->
         RecordPat   (map (fn (id,p)-> (id, replaceRec p)) fields, a)

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

 op appTerm        : fa(a) appTSP a -> ATerm        a -> ()
 op appSort        : fa(a) appTSP a -> ASort        a -> ()
 op appPattern     : fa(a) appTSP a -> APattern     a -> ()
 op appTermOpt     : fa(a) appTSP a -> ATermOpt     a -> ()
 op appSortOpt     : fa(a) appTSP a -> ASortOpt     a -> ()
 op appSortSchemes : fa(a) appTSP a -> ASortSchemes a -> ()
 op appTermSchemes : fa(a) appTSP a -> ATermSchemes a -> ()


 def appTerm (tsp_apps as (term_app,_,_)) term =
  let def appT (tsp_apps, term) =
       (case term of
	  | Fun        (top, srt,     _) -> appSort tsp_apps srt
	  | Var        ((id, srt),    _) -> appSort tsp_apps srt
	  | Let        (decls, bdy,   _) -> (app (fn (pat, trm) -> 
						  (appPattern tsp_apps pat; 
						   appRec trm)) 
					     decls;
					     appRec bdy)
	  | LetRec     (decls, bdy,   _) -> (app (fn (id, trm) -> appRec trm) decls;
					     appRec bdy)
	  | Record     (row,          _) -> app (fn (id, trm) -> appRec trm) row
	  | IfThenElse (t1, t2, t3,   _) -> (appRec t1; appRec t2; appRec t3)
	  | Lambda     (match,        _) -> app (fn (pat, cond, trm) -> 
						 (appPattern tsp_apps pat; 
						  appRec cond;
						  appRec trm))
	                                      match
	  | Bind       (_, vars, trm, _) -> (app (fn (id, srt) -> appSort tsp_apps srt) vars;
					     appRec trm)
	  | Apply      (t1, t2,       _) -> (appRec t1; appRec t2)
	  | Seq        (terms,        _) -> app appRec terms
	  | ApplyN     (terms,        _) -> app appRec terms
	  | SortedTerm (trm, srt,     _) -> (appRec trm; appSort tsp_apps srt))
      def appRec term = % term was tm ??
	%% Post-node traversal: leaves first
	(appT (tsp_apps, term); term_app term)
  in 
    appRec term
 
 def appSort (tsp_apps as (_, srt_app, _)) srt = 
  let def appS (tsp_apps, srt) =
       case srt of
          | CoProduct (row,       _) -> app (fn (id, opt) -> appSortOpt tsp_apps opt) row
          | Product   (row,       _) -> app (fn (id, srt) -> appRec srt) row
          | Arrow     (s1,  s2,   _) -> (appRec s1;  appRec s2)
          | Quotient  (srt, trm,  _) -> (appRec srt; appTerm tsp_apps trm)
          | Subsort   (srt, trm,  _) -> (appRec srt; appTerm tsp_apps trm)
          | Base      (qid, srts, _) -> app appRec srts
          | Base     (qid, srts, _) -> app appRec srts
          | _                        -> ()

      def appRec srt = 
	%% Post-node traversal: leaves first
	(appS (tsp_apps, srt); srt_app srt)
  in
    appRec srt

 def appPattern (tsp_apps as (_, _, pattern_app)) pat =
  let def appP(tsp_apps,pat) =
	case pat of
	  | AliasPat    (p1, p2,            _) -> (appRec p1; appRec p2)
	  | EmbedPat    (id, Some pat, srt, _) -> (appRec pat; appSort tsp_apps srt)
	  | EmbedPat    (id, None, srt,     _) -> appSort tsp_apps srt
	  | RelaxPat    (pat, trm,          _) -> (appRec pat; appTerm tsp_apps trm)
	  | QuotientPat (pat, trm,          _) -> (appRec pat; appTerm tsp_apps trm)
	  | VarPat      ((v, srt),          _) -> appSort tsp_apps srt
	  | WildPat     (srt,               _) -> appSort tsp_apps srt
	  | RecordPat   (fields,            _) -> app (fn (id, p) -> appRec p) fields
	  | _                                  -> ()
      def appRec pat = (appP(tsp_apps, pat); pattern_app pat)
  in
    appRec pat

 def appSortOpt tsp_apps opt_sort =
   case opt_sort of
     | None     -> ()
     | Some srt -> appSort tsp_apps srt

 def appTermOpt tsp_apps opt_term =
   case opt_term of
     | None     -> ()
     | Some trm -> appTerm tsp_apps trm

 def appSortSchemes tsp_apps sort_schemes =
   app (fn (_,srt) -> appSort tsp_apps srt) sort_schemes

 def appTermSchemes tsp_apps term_schemes =
   app (fn (_,term) -> appTerm tsp_apps term) term_schemes

 %%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%
 %%%                Misc Base Terms
 %%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%

 op boolSort?   : fa(b) ASort b -> Boolean
 op stringSort? : fa(b) ASort b -> Boolean
 op natSort?    : fa(b) ASort b -> Boolean

 def boolSort? s =
  case s of
    | Base (Qualified ("Boolean", "Boolean"), [], _) -> true
    | _ -> false

 def stringSort?(s) = 
  case s of
    | Base (Qualified ("String",  "String"),  [], _) -> true
    | _ -> false

 def natSort?(s) = 
  case s of
    | Base (Qualified ("Nat",     "Nat"),     [], _) -> true
    | _ -> false

 op mkABase : fa(b) QualifiedId * List (ASort b) * b -> ASort b
 def mkABase (qid, srts, a) = Base (qid, srts, a)

 op boolASort : fa(b) b -> ASort b
 def boolSort a = mkABase (Qualified ("Boolean", "Boolean"), [], a)

 op mkTrueA  : fa(b) b -> ATerm b
 op mkFalseA : fa(b) b -> ATerm b

 def mkTrueA (a) = Fun (Bool true,  boolSort a, a)
 def mkFalseA(a) = Fun (Bool false, boolSort a, a)
}
