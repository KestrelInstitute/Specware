MetaSlang qualifying spec

 import AnnTerm

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
       id1 = id2 ||
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

     %% The following two cases handle comparisons of "X" with "And (X, Y)"
     %%  where X and Y are equivalent, but not equal, sorts.
     %%
     %% This can happen for the sort of the dfn field of an opinfo
     %%  for some op that had both a decl and a def, which gave it two
     %%  sorts that are equivalent, but not equal.
     %%
     %% This was noticed as a problem for subsitution, which calls subtractSpec and 
     %% then complains if any sorts and ops from the dom spec of the morphism have
     %% failed to find a match in the spec that morphism is being applied to.

     | (And (srts1, _),  _) -> foldl (fn (s1, eq?) -> eq? || equalSort? (s1, s2)) false srts1
     | (_,  And (srts2, _)) -> foldl (fn (s2, eq?) -> eq? || equalSort? (s1, s2)) false srts2

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

     | (WildPat      (s1,          _),
        WildPat      (s2,          _)) -> equalSort? (s1, s2)

     | (BoolPat      (x1,          _),
        BoolPat      (x2,          _)) -> x1 = x2

     | (NatPat       (x1,          _),
        NatPat       (x2,          _)) -> x1 = x2

     | (StringPat    (x1,          _),
        StringPat    (x2,          _)) -> x1 = x2

     | (CharPat      (x1,          _),
        CharPat      (x2,          _)) -> x1 = x2

     | (QuotientPat  (x1, t1,      _),
        QuotientPat  (x2, t2,      _)) -> equalPattern? (x1, x2) && equalTerm? (t1, t2)

     | (RestrictedPat(x1, t1,      _),
        RestrictedPat(x2, t2,      _)) -> equalPattern? (x1, x2) && equalTerm? (t1, t2)

     | (SortedPat    (x1, t1,      _),
        SortedPat    (x2, t2,      _)) -> equalPattern? (x1, x2) && equalSort? (t1, t2)

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

     | (SortedTerm (x1, s1,      _),
        SortedTerm (x2, s2,      _)) -> equalTermStruct? (x1, x2)

     | (Pi         (tvs1, t1,    _), 
        Pi         (tvs2, t2,    _)) -> tvs1 = tvs2 && equalTermStruct? (t1, t2) % TODO: handle alpha equivalence

     | (And        (tms1,        _), 
        And        (tms2,        _)) -> foldl (fn (t1, t2, eq?) -> eq? && equalTermStruct? (t1, t2))
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

     | (Quotient,             Quotient    )         -> true
     | (Choose,               Choose      )         -> true
     | (Restrict,             Restrict    )         -> true
     | (Relax,                Relax       )         -> true

     | (PQuotient t1,         PQuotient t2)         -> equalTermStruct? (t1, t2)
     | (PChoose   t1,         PChoose   t2)         -> equalTermStruct? (t1, t2)

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

     | (WildPat      (s1,          _),
        WildPat      (s2,          _)) -> equalSort? (s1, s2)

     | (BoolPat      (x1,          _),
        BoolPat      (x2,          _)) -> x1 = x2

     | (NatPat       (x1,          _),
        NatPat       (x2,          _)) -> x1 = x2

     | (StringPat    (x1,          _),
        StringPat    (x2,          _)) -> x1 = x2

     | (CharPat      (x1,          _),
        CharPat      (x2,          _)) -> x1 = x2

     | (QuotientPat  (x1, t1,      _),
        QuotientPat  (x2, t2,      _)) -> equalPatternStruct? (x1, x2) && equalTermStruct? (t1, t2)

     | (RestrictedPat(x1, t1,      _),
        RestrictedPat(x2, t2,      _)) -> equalPatternStruct? (x1, x2) && equalTermStruct? (t1, t2)

     | (SortedPat    (x1, _,       _),
        SortedPat    (x2, _,       _)) -> equalPatternStruct? (x1, x2)

     | _ -> false

 def equalVarStruct? ((id1,_), (id2,_)) = id1 = id2

 %%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%
 %%%                equivTerm? (equal modulo alpa-conversion)
 %%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%

 op  equivTerm?: [a,b] ATerm a * ATerm b -> Boolean
 def equivTerm?(t1,t2) = equivTermAux?(t1,t2,[])

 type VarNameSubst = List(String * String)

 op  equivTermAux?: [a,b] ATerm a * ATerm b * VarNameSubst -> Boolean
 def equivTermAux? (t1, t2, sb) =
   case (t1, t2) of

     | (Apply      (x1, y1,      _),
        Apply      (x2, y2,      _)) -> equivTermAux? (x1, x2, sb) && equivTermAux? (y1, y2, sb)

     | (ApplyN     (xs1,         _),
        ApplyN     (xs2,         _)) -> equalList? (xs1, xs2, fn(t1, t2) -> equivTermAux?(t1, t2, sb))

     | (Record     (xs1,         _),
        Record     (xs2,         _)) -> equalList? (xs1, xs2,
                                                    fn ((label1, x1), (label2, x2)) ->
                                                       label1 = label2 &&
                                                       equivTermAux? (x1, x2, sb))

     | (Bind       (b1, vs1, x1, _),
        Bind       (b2, vs2, x2, _)) -> b1 = b2 &&
                                        %% Could check modulo alpha conversion...
                                        (case compareVarList (vs1, vs2, sb) of
					   | Some new_sb -> equivTermAux? (x1,  x2, new_sb)
					   | None -> false)

     | (The       (v1, x1, _),
        The       (v2, x2, _)) -> %% Could check modulo alpha conversion...
                                    equalVarWrtSubst? (v1, v2, sb) &&
                                    equivTermAux? (x1, x2, sb)

     | (Let        (pts1, b1,    _),
        Let        (pts2, b2,    _)) -> equivTermAux? (b1, b2, sb) &&
                                        equalList? (pts1, pts2,
                                                    fn ((p1, t1), (p2, t2)) ->
						      %% Should return a subst
                                                      equalPattern? (p1, p2) &&
                                                      equivTermAux?    (t1, t2, sb))

     | (LetRec     (vts1, b1,    _),
        LetRec     (vts2, b2,    _)) -> equivTermAux? (b1, b2, sb) &&
                                        equalList? (vts1, vts2,
                                                    fn ((v1, t1), (v2, t2)) ->
						      %% Should return a subst
                                                     equalVar?  (v1, v2) &&
                                                     equivTermAux? (t1, t2, sb))

     | (Var        (v1,          _),
        Var        (v2,          _)) -> equalVarWrtSubst? (v1, v2, sb)

     | (Fun        (f1, s1,      _),
        Fun        (f2, s2,      _)) -> equalFun? (f1, f2) && equalSort? (s1, s2)

     | (Lambda     (xs1,         _),
        Lambda     (xs2,         _)) -> equalList? (xs1, xs2,
                                                    fn ((p1, c1, b1), (p2, c2, b2)) ->
						      %% Should return a subst
                                                      equalPattern?  (p1, p2) &&
                                                      equivTermAux?     (c1, c2, sb) &&
                                                      equivTermAux?     (b1, b2, sb))

     | (IfThenElse (c1, x1, y1,  _),
        IfThenElse (c2, x2, y2,  _)) -> equivTermAux? (c1, c2, sb) &&
                                        equivTermAux? (x1, x2, sb) &&
                                        equivTermAux? (y1, y2, sb)

     | (Seq        (xs1,         _),
        Seq        (xs2,         _)) -> equalList? (xs1, xs2, fn(t1, t2) -> equivTermAux?(t1, t2, sb))

     | (SortedTerm (x1, s1,      _),
        SortedTerm (x2, s2,      _)) -> equivTermAux? (x1, x2, sb) && equalSort? (s1, s2)

     | (Pi         (tvs1, tm1,   _), 
        Pi         (tvs2, tm2,   _)) -> tvs1 = tvs2 && equivTermAux? (tm1, tm2, sb) % TODO: handle alpha equivalence

     | (And        (tms1,        _), 
        And        (tms2,        _)) -> foldl (fn (t1, t2, eq?) -> eq? && equivTermAux? (t1, t2, sb))
					      true
					      (tms1, tms2)

     | (Any  _,    Any  _)           -> true  % TODO: Tricky -- should this be some kind of lisp EQ test?

     | _ -> false

 op  compareVarList: [a,b] List (AVar a) * List (AVar b) * VarNameSubst -> Option VarNameSubst
 def compareVarList(vs1,vs2,sb) =
   if length vs1 ~= length vs2 then None
   else
   let def comp(vs1,vs2,sb) =
         case (vs1,vs2) of
	   | ([],[]) -> Some sb
	   | ((id1,s1)::rvs1,(id2,s2)::rvs2) ->
	     if equalSort?(s1, s2)
	       then comp(rvs1,rvs2,if id1 = id2 then sb else Cons((id1,id2),sb))
	       else None
   in
   comp(vs1,vs2,sb)

 op  equalVarWrtSubst?: [a,b] AVar a * AVar b * VarNameSubst -> Boolean
 def equalVarWrtSubst?((id1,_),(id2,_),sb) =
   id1 = id2 or exists (fn (ids1,ids2) -> id2 = ids2) sb

 def MetaSlang.maybeAndSort (srts, pos) =
   let compressed_sorts =
       foldl (fn (srt, pending_srts) ->
	      case pending_srts of
		| [] -> [srt]
		| [pending_srt] ->
		  (case (sortInnerSort srt, sortInnerSort pending_srt) of
		     | (Any _ , _)     -> [pending_srt]
		     | (_,      Any _) -> [srt]
		     | _ ->
		       case sortInnerSort srt of
			 | Any _ -> pending_srts
			 | _ ->
			   if exists (fn pending_srt -> equalSort? (srt, pending_srt)) pending_srts then
			     pending_srts
			   else
			     pending_srts ++ [srt])
		| _ ->
		  if exists (fn pending_srt -> equalSort? (srt, pending_srt)) pending_srts then
		    pending_srts
		  else
		    pending_srts ++ [srt])
             []
	     srts
   in
   case compressed_sorts of
     | []    -> Any pos
     | [srt] -> srt
     | _     -> And (srts, pos)

 def MetaSlang.maybeAndTerm (tms, pos) =
   let compressed_terms =
       foldl (fn (tm, pending_tms) ->
	      case pending_tms of
		| [] -> [tm]
		| [pending_tm] ->
		  (case (termInnerTerm tm, termInnerTerm pending_tm) of
		     | (Any _, _)    -> 
		       if equalSort? (termSort tm, termSort pending_tm) then
			 [pending_tm]
		       else
			 [pending_tm, tm]
		     | (_,    Any _) -> 
		       if equalSort? (termSort tm, termSort pending_tm) then
			 [tm]
		       else
			 [pending_tm, tm]
		     | _ ->
		       if exists (fn pending_tm -> equalTerm? (tm, pending_tm)) pending_tms then
			 pending_tms
		       else
			 pending_tms ++ [tm])
		| _ ->
		  if exists (fn pending_tm -> equalTerm? (tm, pending_tm)) pending_tms then
		    pending_tms
		  else
		    pending_tms ++ [tm])
             []
	     tms
   in
     case compressed_terms of
       | []   -> Any pos
       | [tm] -> tm
       | _    -> And (tms, pos)

end-spec
