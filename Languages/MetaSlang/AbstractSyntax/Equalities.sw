MetaSlang qualifying spec

 import AnnTerm

 %%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%
 %%%                Term Equalities
 %%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%
 %%% Naming convention:  To avoid confusion when both Foo and Foos exist
 %%%                      (e.g. when type Foos = List Foo)
 %%%                      we use "equalFoo" to compare two Foo's,
 %%%                      and "equalFoos" to compare two Foos'es.
 %%%                     This converts less fluently into English, but is 
 %%%                      ultimately less confusing.
 %%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%

 op equalTerm?          : [a,b] ATerm    a * ATerm    b -> Bool
 op equalType?          : [a,b] AType    a * AType    b -> Bool
 op equalPattern?       : [a,b] APattern a * APattern b -> Bool
 op equalFun?           : [a,b] AFun     a * AFun     b -> Bool
 op equalVar?           : [a,b] AVar     a * AVar     b -> Bool
 op equalTransform?     : [a,b] ATransformExpr a * ATransformExpr b -> Bool

 %% term equality ignoring types
 op equalTermStruct?    : [a,b] ATerm    a * ATerm    b -> Bool
 op equalPatternStruct? : [a,b] APattern a * APattern b -> Bool
 op equalFunStruct?     : [a,b] AFun     a * AFun     b -> Bool
 op equalVarStruct?     : [a,b] AVar     a * AVar     b -> Bool

  op equalList? : [a,b] List a * List b * (a * b -> Bool) -> Bool
 def equalList? (x, y, eqFn) =
   (length x) = (length y) &&
   (case (x, y) of
      | ([],              [])             -> true
      | (head_x::tail_x,  head_y::tail_y) -> eqFn (head_x, head_y) &&
                                             equalList? (tail_x, tail_y, eqFn)
      | _ -> false)

  op equalOpt? : [a,b] Option a * Option b * (a * b -> Bool) -> Bool
 def equalOpt? (x, y, eqFn) =
   case (x, y) of
     | (None,    None)    -> true
     | (Some x1, Some y1) -> eqFn (x1, y1)
     | _ -> false

 op traceEqualTerm?: Bool = false

 def equalTerm? (t1, t2) =
   let result = 
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

         | (The       (v1, x1, _),
            The       (v2, x2, _)) -> %% Could check modulo alpha conversion...
                                        equalVar? (v1, v2) &&
                                        equalTerm? (x1, x2)

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

         | (Fun        (f1, s1,      _),       %% If the ops are the same, don't need to check type
            Fun        (f2, s2,      _)) -> equalFun? (f1, f2) && (embed? Op f1 || equalType? (s1, s2))

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

         | (TypedTerm  (x1, s1,      _),
            TypedTerm  (x2, s2,      _)) -> equalTerm? (x1, x2) && equalType? (s1, s2)

         | (Transform  (t1s,         _),
            Transform  (t2s,         _)) -> equalTransformList?(t1s, t2s)

         | (Pi         (tvs1, tm1,   _), 
            Pi         (tvs2, tm2,   _)) -> tvs1 = tvs2 && equalTerm? (tm1, tm2) % TODO: handle alpha equivalence

         | (And        (tms1,        _), 
            And        (tms2,        _)) -> foldl (fn (eq?, t1, t2) -> eq? && equalTerm? (t1, t2))
                                                  true
                                                  (tms1, tms2)

         | (Any  _,    Any  _)           -> true  % TODO: Tricky -- should this be some kind of lisp EQ test?

         | _ -> false
   in
   let _ = if traceEqualTerm? && ~result then writeLine(printTerm t1^" ~=t "^printTerm t2^"\n"
                                                        ^printTermType t1^" ~=tt "^printTermType t2) else () in
   result

 def equalType? (s1, s2) =
   equalTypeSubtype?(s1, s2, false)
 
%% Given two types, return true if they are equal (modulo
%% annotations). If `ignore_subtypes` is true, then this identifies
%% types `{s | P }` and `{s' | Q }`, if `s` and `s'` are identified,
%% effectively ignoring subtype constraints, as the name suggests.
 op [a, b] equalTypeSubtype?(s1: AType a, s2: AType b, ignore_subtypes?: Bool): Bool =
   let def equalType?(s1, s2) =
         let result =
             case (s1,s2) of

               | (Arrow     (x1, y1,  _),
                  Arrow     (x2, y2,  _)) -> equalType? (x1, x2) && equalType? (y1, y2)

               | (Product   (xs1,     _),
                  Product   (xs2,     _)) -> equalList? (xs1, xs2,
                                                         fn ((l1, x1), (l2, x2)) ->
                                                         l1 = l2 &&
                                                         equalType? (x1, x2))

               | (CoProduct (xs1,     _),
                  CoProduct (xs2,     _)) -> equalList? (xs1, xs2,
                                                         fn ((l1, x1), (l2, x2)) ->
                                                         l1 = l2 &&
                                                         equalOpt? (x1, x2, equalType?))

               | (Quotient  (x1, t1,  _),
                  Quotient  (x2, t2,  _)) -> equalType? (x1, x2) && equalTerm? (t1, t2)

               | (Subtype   (x1, t1,  _), _) | ignore_subtypes? -> equalType?(x1, s2) 

               | (_,   Subtype (x2, t2,  _)) | ignore_subtypes? -> equalType?(s1, x2) 

               | (Subtype   (x1, t1,  _),
                  Subtype   (x2, t2,  _)) -> equalType? (x1, x2) && equalTerm? (t1, t2)

               % These cases are useful until we remove "Boolean" as an alternative for "Bool"
               | (Boolean _, Base(Qualified("Bool", "Bool"), [], _)) -> true
               | (Base(Qualified("Bool", "Bool"), [], _), Boolean _) -> true

               | (Base      (q1, xs1, _),
                  Base      (q2, xs2, _)) -> q1 = q2 && equalList? (xs1, xs2, equalType?)

               | (Boolean _, Boolean _)   -> true

               | (TyVar     (v1,      _),
                  TyVar     (v2,      _)) -> v1 = v2

               | (MetaTyVar (mtv1,    _),
                  MetaTyVar (mtv2,    _)) ->
                 let ({link=link1, uniqueId=id1, name}) = ! mtv1 in
                 let ({link=link2, uniqueId=id2, name}) = ! mtv2 in
                 id1 = id2 ||
                 (case (link1,link2) of
                    %% This case handles the situation where an
                    %%  unlinked MetaTyVar is compared against itself.
                    | (Some ls1, Some ls2) -> equalType? (ls1, ls2)
                    %% The following two cases handle situations where
                    %%  MetaTyVar X is linked to unlinked MetaTyVar Y
                    %%  and we are comparing X with Y (or Y with X).
                    | (Some ls1, _)        -> equalType? (ls1, s2)
                    | (_,        Some ls2) -> equalType? (s1,  ls2)
                    | _ -> false)

               | (MetaTyVar (mtv1, _), _) ->
                 let ({link=link1, uniqueId=id1, name}) = ! mtv1 in
                 (case link1 of
                    | Some ls1 -> equalType? (ls1, s2)
                    | _ -> false)

               | (_, MetaTyVar (mtv2, _)) ->
                 let ({link=link2, uniqueId=id2, name}) = ! mtv2 in
                 (case link2 of
                    | Some ls2 -> equalType? (s1, ls2)
                    | _ -> false)

               | (Pi         (tvs1, s1,    _), 
                  Pi         (tvs2, s2,    _)) -> tvs1 = tvs2 && 
                                                  equalType? (s1, s2) % TODO: handle alpha equivalence

               | (And        (srts1,       _),  
                  And        (srts2,       _)) -> %% TODO: Handle reordering?
                                                  foldl (fn (eq?, s1, s2) ->  
                                                         eq? && equalType? (s1, s2))
                                                        true
                                                        (srts1, srts2)

               %% The following two cases handle comparisons of "X" with "And (X, Y)"
               %%  where X and Y are equivalent, but not equal, types.
               %%
               %% This can happen for the type of the dfn field of an opinfo
               %%  for some op that had both a decl and a def, which gave it two
               %%  types that are equivalent, but not equal.
               %%
               %% This was noticed as a problem for subsitution, which calls subtractSpec and 
               %% then complains if any types and ops from the dom spec of the morphism have
               %% failed to find a match in the spec that morphism is being applied to.

               | (And (srts1, _),  _) -> foldl (fn (eq?, s1) -> eq? || equalType? (s1, s2)) false srts1
               | (_,  And (srts2, _)) -> foldl (fn (eq?, s2) -> eq? || equalType? (s1, s2)) false srts2

               | (Any  _,    Any  _)           -> true  % TODO: Tricky -- should this be some kind of lisp EQ test?

               | _ -> false
         in
         let _ = if traceEqualTerm? && ~result then writeLine(printType s1^" ~=s "^printType s2) else () in
         result
   in
   equalType?(s1, s2)

 def equalPattern? (p1, p2) =
   let result =
        case (p1, p2) of

      | (AliasPat    (x1, y1,      _),
         AliasPat    (x2, y2,      _)) -> equalPattern? (x1, x2) && equalPattern? (y1, y2)

      | (VarPat      (v1,          _),
         VarPat      (v2,          _)) -> equalVar? (v1, v2)

      | (EmbedPat    (i1, op1, s1, _),
         EmbedPat    (i2, op2, s2, _)) -> i1 = i2 &&
                                          equalType? (s1,  s2) &&
                                          equalOpt?  (op1, op2, equalPattern?)

      | (RecordPat   (xs1,         _),
         RecordPat   (xs2,         _)) -> equalList? (xs1, xs2,
                                                      fn ((label1, x1), (label2, x2)) ->
                                                         label1 = label2 &&
                                                         equalPattern? (x1, x2))

      | (WildPat      (s1,          _),
         WildPat      (s2,          _)) -> equalType? (s1, s2)

      | (BoolPat      (x1,          _),
         BoolPat      (x2,          _)) -> x1 = x2

      | (NatPat       (x1,          _),
         NatPat       (x2,          _)) -> x1 = x2

      | (StringPat    (x1,          _),
         StringPat    (x2,          _)) -> x1 = x2

      | (CharPat      (x1,          _),
         CharPat      (x2,          _)) -> x1 = x2

      | (QuotientPat  (x1, qid1,    _),
         QuotientPat  (x2, qid2,    _)) -> equalPattern? (x1, x2) && qid1 = qid2

      | (RestrictedPat(x1, t1,      _),
         RestrictedPat(x2, t2,      _)) -> equalPattern? (x1, x2) && equalTerm? (t1, t2)

      | (TypedPat     (x1, t1,      _),
         TypedPat     (x2, t2,      _)) -> equalPattern? (x1, x2) && equalType? (t1, t2)

      | _ -> false
    in
    let _ = if traceEqualTerm? && ~ result then writeLine(printPattern p1^" ~=p "^printPattern p2) else () in
    result

 def equalFun? (f1, f2) =
   case (f1, f2) of

     | (Not,          Not         ) -> true
     | (And,          And         ) -> true
     | (Or,           Or          ) -> true
     | (Implies,      Implies     ) -> true
     | (Iff,          Iff         ) -> true
     | (Equals,       Equals      ) -> true
     | (NotEquals,    NotEquals   ) -> true

     | (Quotient  qid1, Quotient  qid2) -> qid1 = qid2
     | (Choose    qid1, Choose    qid2) -> qid1 = qid2
     | (Restrict,       Restrict      ) -> true
     | (Relax,          Relax         ) -> true

     | (PQuotient qid1, PQuotient qid2) -> qid1 = qid2
     | (PChoose   qid1, PChoose   qid2) -> qid1 = qid2

     | (Op   (x1,f1), Op   (x2,f2)) -> x1 = x2 && (f1 = f2 || f1 = Unspecified || f2 = Unspecified)
     | (Project   x1, Project   x2) -> x1 = x2
     | (RecordMerge,  RecordMerge ) -> true
     | (Embed     x1, Embed     x2) -> x1 = x2
     | (Embedded  x1, Embedded  x2) -> x1 = x2
     | (Select    x1, Select    x2) -> x1 = x2
     | (Nat       x1, Nat       x2) -> x1 = x2
     | (Char      x1, Char      x2) -> x1 = x2
     | (String    x1, String    x2) -> x1 = x2
     | (Bool      x1, Bool      x2) -> x1 = x2

     | (OneName   x1, OneName   x2) -> x1.1 = x2.1
     | (TwoNames  x1, TwoNames  x2) -> (x1.1 = x2.1) && (x1.2 = x2.2)

     | _ -> false

 def equalVar? ((id1,s1), (id2,s2)) = 
   id1 = id2 && equalType? (s1, s2)

 op [a] equalVars?(vs1: List(AVar a), vs2: List(AVar a)): Bool =
   equalList?(vs1, vs2, equalVar?)

  op equalTyVar?: TyVar * TyVar -> Bool
 def equalTyVar? (tyVar1, tyVar2) = 
   tyVar1 = tyVar2

  op equalTyVars?: TyVars * TyVars -> Bool
 def equalTyVars? (tyVars1, tyVars2) =
   all (fn (tyV1, tyV2) -> equalTyVar? (tyV1, tyV2)) 
       (tyVars1, tyVars2)

 op equalTyVarSets?(tyVars1: TyVars, tyVars2: TyVars): Bool =
   length tyVars1 = length tyVars2
     && forall? (fn tyV1 -> tyV1 in? tyVars2) tyVars1

 def equalTransform?(t1, t2) =
   case (t1, t2) of
     | (Name(s1, _), Name(s2, _)) -> s1 = s2
     | (Number(n1, _), Number(n2, _)) -> n1 = n2
     | (Str(s1, _), Str(s2, _)) -> s1 = s2
     | (Qual(s1, t1, _), Qual(s2, t2, _)) -> s1 = s2 && t1 = t2
     % | (SCTerm (sct1,_), SCTerm (sct2)) -> sameSCTerm?(sct1, sct2)
     | (Item(s1, t1, _), Item(s2, t2, _)) -> s1 = s2 && equalTransform?(t1, t2)
     | (Repeat(l1, _), Repeat(l2, _)) -> equalTransformList?(l1, l2)
     | (Tuple(l1, _), Tuple(l2, _)) -> equalTransformList?(l1, l2)
     | (Record(l1, _), Record(l2, _)) ->
       length l1 = length l1 && forall? (fn ((l1i,t1i),(l2i, t2i)) -> l1i = l2i && equalTransform?(t1i, t2i)) (zip(l1, l1))
     | (Options(l1, _), Options(l2, _)) -> equalTransformList?(l1, l2) 
     | (Block(l1, _), Options(l2, _)) -> equalTransformList?(l1, l2) 
     | (At(qids1, comm1, _), At(qids2, comm2, _)) -> qids1 = qids2 && equalTransform?(comm1, comm2)
     | (Command(t1, l1, _), Command(t2, l2, _)) -> t1 = t2 && equalTransformList?(l1, l2)
     | _ -> false

 op [a,b] equalTransformList?(t1s: List(ATransformExpr a) , t2s: List(ATransformExpr b)): Bool =
   length t1s = length t2s && forall? equalTransform? (zip(t1s, t2s))

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

     | (The       (v1, x1, _),
        The       (v2, x2, _)) -> %% Could check modulo alpha conversion...
                                      equalVarStruct? (v1,v2) &&
                                      equalTermStruct? (x1,x2)

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

     | (TypedTerm  (x1, s1,      _),
        TypedTerm  (x2, s2,      _)) -> equalTermStruct? (x1, x2)

     | (Transform  (t1s,         _),
        Transform  (t2s,         _)) -> equalTransformList?(t1s, t2s)

     | (Pi         (tvs1, t1,    _), 
        Pi         (tvs2, t2,    _)) -> tvs1 = tvs2 && equalTermStruct? (t1, t2) % TODO: handle alpha equivalence

     | (And        (tms1,        _), 
        And        (tms2,        _)) -> foldl (fn (eq?, t1, t2) -> eq? && equalTermStruct? (t1, t2))
					      true
					      (tms1, tms2)

     | (Any  _,    Any  _)           -> true  % TODO: Tricky -- should this be some kind of lisp EQ test?

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

     | (Quotient   -,         Quotient   _)         -> true
     | (Choose     _,         Choose     _)         -> true
     | (Restrict,             Restrict    )         -> true
     | (Relax,                Relax       )         -> true

     | (PQuotient qid1,       PQuotient qid2)       -> qid1 = qid2
     | (PChoose   qid1,       PChoose   qid2)       -> qid1 = qid2

     | (Op        x1,         Op        x2)         -> x1 = x2
     | (Project   x1,         Project   x2)         -> x1 = x2
     | (RecordMerge,          RecordMerge)          -> true
     | (Embed     x1,         Embed     x2)         -> x1 = x2
     | (Embedded  x1,         Embedded  x2)         -> x1 = x2
     | (Select    x1,         Select    x2)         -> x1 = x2
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

     | (WildPat      (s1,          _),
        WildPat      (s2,          _)) -> equalType? (s1, s2)

     | (BoolPat      (x1,          _),
        BoolPat      (x2,          _)) -> x1 = x2

     | (NatPat       (x1,          _),
        NatPat       (x2,          _)) -> x1 = x2

     | (StringPat    (x1,          _),
        StringPat    (x2,          _)) -> x1 = x2

     | (CharPat      (x1,          _),
        CharPat      (x2,          _)) -> x1 = x2

     | (QuotientPat  (x1, qid1,    _),
        QuotientPat  (x2, qid2,    _)) -> equalPatternStruct? (x1, x2) && qid1 = qid2

     | (RestrictedPat(x1, t1,      _),
        RestrictedPat(x2, t2,      _)) -> equalPatternStruct? (x1, x2) && equalTermStruct? (t1, t2)

     | (TypedPat     (x1, _,       _),
        TypedPat     (x2, _,       _)) -> equalPatternStruct? (x1, x2)

     | _ -> false

 def equalVarStruct? ((id1,_), (id2,_)) = id1 = id2

  %% List Term set operations
  op [a] termIn?(t1: ATerm a, tms: List (ATerm a)): Bool =
    exists? (fn t2 -> equalTerm?(t1,t2)) tms

  op [a] termsDiff(tms1: List (ATerm a), tms2: List (ATerm a)): List (ATerm a) =
    filter(fn t1 -> ~(termIn?(t1, tms2))) tms1

  op [a] termsUnion(tms1: List (ATerm a), tms2: List (ATerm a)): List (ATerm a) =
    termsDiff(tms1,tms2) ++ tms2

  op [a] termsIntersect(tms1: List (ATerm a), tms2: List (ATerm a)): List (ATerm a) =
    filter(fn t1 -> termIn?(t1, tms2)) tms1

  op [a] typeIn?(t1: AType a, tms: List (AType a)): Bool =
    exists? (fn t2 -> equalType?(t1,t2)) tms

 op [a] removeDuplicateTerms(tms: List (ATerm a)): List (ATerm a) =
   case tms of
     | []    -> []
     | [t]   -> [t]
     | t1::r -> let nr = removeDuplicateTerms r in
                if termIn?(t1, nr) then nr
                  else t1::nr

 def MetaSlang.maybeAndType (srts, pos) =
   let non_dup_types =
       foldl (fn (pending_srts, srt) ->
                if exists? (fn pending_srt -> equalType? (srt, pending_srt)) pending_srts then
                  pending_srts
                else
                  pending_srts ++ [srt])
             []
	     srts
   in
     let compressed_types = filter (fn srt -> case srt of | Any _ -> false | _ -> true) non_dup_types in
     case compressed_types of
       | [] -> 
         (case non_dup_types of
            | []  -> Any pos
            | [s] -> s
            | _   -> And (non_dup_types, pos))
       | [srt] -> srt
       | _     -> And (srts, pos)

 op traceMaybeAndTerm? : Bool = false

op [a] compatibleTypes?(ty1: AType a, ty2: AType a): Bool =
  anyType? ty1 || anyType? ty2 || equalTypeSubtype?(ty1, ty2, true)

op [a] chooseDefinedType(ty1: AType a, ty2: AType a): AType a =
  if anyType? ty1 then ty2 else ty1

op [a] compatibleTerms?(tm1: ATerm a, tm2: ATerm a): Bool =
  anyTerm? tm1 || anyTerm? tm2 || equalTerm?(tm1, tm2)
 
op [a] chooseDefinedTerm(tm1: ATerm a, tm2: ATerm a): ATerm a =
  if anyTerm? tm1 then tm2 else tm1

op [a] chooseLonger(l1: List a, l2: List a): List a =
  if length l2 > length l1 then l2 else l1

op [a] maybeAndTerm (tms: List(ATerm a), pos: a): ATerm a =
  let tvs_type_term_triples = flatten (map unpackTypedTerms tms) in
  let non_dup_triples =
      foldr (fn (triple as (tvs, ty, tm), pending_tms) ->
               case pending_tms of
                 | [] -> [triple]
                 | (o_tvs, o_ty, o_tm) :: old_tms ->
                   if compatibleTypes?(ty, o_ty) && compatibleTerms?(tm, o_tm)
                     then (chooseLonger(tvs, o_tvs),
                           chooseDefinedType(ty, o_ty),
                           chooseDefinedTerm(tm, o_tm))
                          :: old_tms
                     else triple :: pending_tms)
            []
            tvs_type_term_triples
  in
  let result = maybePiAndTypedTerm(non_dup_triples) in
  let _ = if traceMaybeAndTerm? && (length non_dup_triples > 1) then
            let _ = app (fn (tvs, ty, tm) -> writeLine(anyToString tvs^printTerm tm^": "
                                                         ^printType ty)) non_dup_triples in
            let _ = writeLine("=>") in
            let _ = writeLine(printTerm result) in
            let _ = writeLine("---") in
            ()
          else
            ()
  in 
  result

(*

 def describe_and_term tm =
   let s = if existsSubTerm (fn tm -> case tm of | ApplyN _ -> true | _ -> false) tm then
            "ApplyN: "
           else
            "        "
   in
   writeLine (s ^ printTerm tm)

 def MetaSlang.maybeAndTerm (tms, pos) =
   let tms = andTerms tms in
   let defns =
       foldl (fn (pending_tms, tm) ->
                if anyTerm? tm then
                  pending_tms
                else
                  pending_tms ++ [tm])
             []
	     tms
   in
   let non_dup_terms =
       foldl (fn (pending_tms, tm) ->
                if anyTerm? tm then
                  if exists? (fn pending_tm -> equalType? (termType tm, termType pending_tm)) pending_tms then
                    pending_tms
                  else
                    pending_tms ++ [tm]
                else
                  pending_tms)
             defns
	     tms
   in
   let x = 
   case non_dup_terms of
     | []   -> Any pos
     | [tm] -> tm
     | (Pi(tvs, TypedTerm(Any _, ty, a1), a2)) :: r_tms ->
       Pi(tvs, TypedTerm(mkAnd r_tms, ty, a1), a2) 
     | (TypedTerm(Any _, ty, a1)) :: r_tms ->
       TypedTerm(mkAnd r_tms, ty, a1)
     | _    -> And (non_dup_terms, pos)
   in
   let _ = if traceMaybeAndTerm? && (length non_dup_terms > 1) then
             let _ = map (fn tm -> describe_and_term tm) non_dup_terms in
             let _ = writeLine("=>") in
             let _ = writeLine(printTerm x) in
             let _ = writeLine("---") in
             ()
           else
             ()
   in 
   x
*)

end-spec
