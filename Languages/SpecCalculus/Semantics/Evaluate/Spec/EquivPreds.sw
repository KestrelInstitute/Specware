SpecCalc qualifying spec 
 import ../../Environment

 %%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%
 %%%      Term Equivalences wrt aliases
 %%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%
 %%% These are patterned after equalTerm? etc. in AnnTerm.sw

 op equivTerm?    : [a] ASpec a -> ATerm    a * ATerm    a -> Boolean
 op equivSort?    : [a] ASpec a -> ASort    a * ASort    a -> Boolean
 op equivPattern? : [a] ASpec a -> APattern a * APattern a -> Boolean
 op equivFun?     : [a] ASpec a -> AFun     a * AFun     a -> Boolean
 op equivVar?     : [a] ASpec a -> AVar     a * AVar     a -> Boolean

  op equivList? : [a,b] ASpec a -> List b * List b * (ASpec a -> b * b -> Boolean) -> Boolean
 def equivList? spc (x, y, eqFn) =
  (length x) = (length y) &
  (case (x, y) of
      | ([],              [])             -> true
      | (head_x::tail_x,  head_y::tail_y) -> eqFn spc (head_x, head_y) & 
                                             equivList? spc (tail_x, tail_y, eqFn)
      | _ -> false)

  op equivOpt? : [a,b] ASpec a -> Option b * Option b * (ASpec a -> b * b -> Boolean) -> Boolean
 def equivOpt? spc (x, y, eqFn) =
  case (x, y) of
     | (None,    None)    -> true
     | (Some x1, Some y1) -> eqFn spc (x1, y1)
     | _ -> false

 def equivTerm? spc (t1, t2) =
  case (t1, t2) of

     | (Apply      (x1, y1,      _), 
        Apply      (x2, y2,      _)) -> equivTerm? spc (x1, x2) & equivTerm? spc (y1, y2)

     | (ApplyN     (xs1,         _),   
        ApplyN     (xs2,         _)) -> equivList? spc (xs1, xs2, equivTerm?)

     | (Record     (xs1,         _), 
        Record     (xs2,         _)) -> equivList? spc  (xs1, xs2, 
							 fn spc -> fn ((label1,x1),(label2,x2)) -> 
							 label1 = label2 & 
							 equivTerm? spc (x1, x2))

     | (Bind       (b1, vs1, x1, _),
        Bind       (b2, vs2, x2, _)) -> b1 = b2 & 
                                        %% Could check modulo alpha conversion...
                                        equivList? spc (vs1, vs2, equivVar?) &
                                        equivTerm? spc (x1,  x2)

     | (Let        (pts1, b1,    _),
        Let        (pts2, b2,    _)) -> equivTerm? spc (b1, b2) &
                                        equivList? spc (pts1, pts2,
							fn spc -> fn ((p1,t1),(p2,t2)) -> 
							equivPattern? spc (p1, p2) & 
							equivTerm?    spc (t1, t2))

     | (LetRec     (vts1, b1,    _),
        LetRec     (vts2, b2,    _)) -> equivTerm? spc  (b1, b2) &
                                        equivList? spc  (vts1, vts2,
							 fn spc -> fn ((v1,t1),(v2,t2)) -> 
							 equivVar?  spc (v1, v2) & 
							 equivTerm? spc (t1, t2))

     | (Var        (v1,          _),
        Var        (v2,          _)) -> equivVar? spc (v1, v2)

     | (Fun        (f1, s1,      _),
        Fun        (f2, s2,      _)) -> equivFun? spc (f1,f2) & equivSort? spc (s1,s2)

     | (Lambda     (xs1,         _),
        Lambda     (xs2,         _)) -> equivList? spc  (xs1, xs2,
							 fn spc -> fn ((p1,c1,b1),(p2,c2,b2)) ->
							 equivPattern? spc (p1, p2) & 
							 equivTerm?    spc (c1, c2) & 
							 equivTerm?    spc (b1, b2))

     | (IfThenElse (c1, x1, y1,  _),
        IfThenElse (c2, x2, y2,  _)) -> equivTerm? spc (c1, c2) & 
                                        equivTerm? spc (x1, x2) & 
                                        equivTerm? spc (y1, y2)

     | (Seq        (xs1,         _),
        Seq        (xs2,         _)) -> equivList? spc (xs1, xs2, equivTerm?)

     | (SortedTerm (x1, s1,      _),
        SortedTerm (x2, s2,      _)) -> equivTerm? spc (x1, x2) & equivSort? spc (s1, s2)

     | _ -> false

 def equivSort? spc (s1, s2) =
  case (s1, s2) of
     | (Arrow     (x1, y1,  _), 
        Arrow     (x2, y2,  _)) -> equivSort? spc (x1, x2) & equivSort? spc (y1, y2)
     | (Product   (xs1,     _), 
        Product   (xs2,     _)) -> equivList? spc (xs1, xs2,
						   fn spc -> fn ((l1,x1),(l2,x2)) -> 
						   l1 = l2 & 
						   equivSort? spc (x1, x2))
     | (CoProduct (xs1,     _), 
        CoProduct (xs2,     _)) -> equivList? spc (xs1, xs2, 
						   fn spc -> fn ((l1,x1),(l2,x2)) -> 
						   l1 = l2 & 
						   equivOpt? spc (x1, x2, equivSort?))
     | (Quotient  (x1, t1,  _), 
        Quotient  (x2, t2,  _)) -> equivSort? spc (x1, x2) & equivTerm? spc (t1, t2)
     | (Subsort   (x1, t1,  _), 
        Subsort   (x2, t2,  _)) -> equivSort? spc (x1, x2) & equivTerm? spc (t1, t2)
     | (Base      (q1, xs1, _), 
        Base      (q2, xs2, _)) -> (findTheSort (spc, q1) = findTheSort (spc, q2)) 
                                   & (equivList? spc (xs1, xs2, equivSort?))
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
               | (Some ls1, Some ls2) -> equivSort? spc (ls1, ls2)
               %% The following two cases handle situations where
               %%  MetaTyVar X is linked to unlinked MetaTyVar Y
               %%  and we are comparing X with Y (or Y with X).
               | (Some ls1, _)        -> equivSort? spc (ls1, s2)
               | (_,        Some ls2) -> equivSort? spc (s1,  ls2)
               | _ -> false)

     | (MetaTyVar (v1,      _),
        _                    ) ->
          let ({link=link1, uniqueId=id1, name}) = ! v1 in
            (case link1 of
               | Some ls1 -> equivSort? spc (ls1, s2)
               | _ -> false)

     | (_,
        MetaTyVar (v2,      _)) ->
          let ({link=link2, uniqueId=id2, name}) = ! v2 in
            (case link2 of
               | Some ls2 -> equivSort? spc (s1, ls2)
               | _ -> false)


     | (Boolean _ , Boolean _) -> true
     | (Base _,  _     ) -> (let s3 = myUnfoldSort (spc, s1) in
			     if s1 = s3 then
			       false
			     else
			       equivSort? spc (s3,  s2))
     | (_,       Base _) -> (let s3 = myUnfoldSort (spc, s2) in
			     if s2 = s3 then
			       false
			     else
			       equivSort? spc (s1,  s3))

     | _ -> false


 def myUnfoldSort (spc, s1) = 
   let Base (qid, ts, pos) = s1 in
   case findAllSorts (spc, qid) of
     | [] -> s1
     | info::_ ->
       (let defs = sortInfoDefs info in
	case defs of
	  | [] -> 
	    Base (primarySortName info, ts, pos)
	  | _ ->
	    let first_def :: _ = defs in
	    let (tvs, srt) = unpackSort first_def in
	    myInstantiateScheme (ts, tvs, srt))

  op myInstantiateScheme : [a] List (ASort a) * TyVars * ASort a -> ASort a
 def [a] myInstantiateScheme (types, tvs, srt) = 
   if null tvs then
     srt
   else
     let tyVarMap = zip (tvs, types) in
     let
        def mapTyVar (tv : TyVar, tvs : List (TyVar * ASort a), pos) : ASort a = 
            case tvs of
              | [] -> TyVar (tv, pos)
	      | (tv1,s)::tvs -> 
	        if tv = tv1 then s else mapTyVar (tv, tvs, pos)
     in
     let
        def cp (srt : ASort a) : ASort a =
	  case srt of
	    | TyVar (tv, pos) -> mapTyVar (tv, tyVarMap, pos)
	    | srt -> srt
     in
       mapSort (id, cp, id) srt

 def equivPattern? spc (p1,p2) =
  case (p1, p2) of
     | (AliasPat    (x1, y1,      _),
        AliasPat    (x2, y2,      _)) -> equivPattern? spc (x1,x2) & equivPattern? spc (y1,y2)

     | (VarPat      (v1,          _),
        VarPat      (v2,          _)) -> equivVar? spc (v1, v2)

     | (EmbedPat    (i1, op1, s1, _),
        EmbedPat    (i2, op2, s2, _)) -> i1 = i2 & 
                                         equivSort? spc (s1,  s2) & 
                                         equivOpt?  spc (op1, op2, equivPattern?)

     | (RecordPat   (xs1,         _),
        RecordPat   (xs2,         _)) -> equivList? spc  (xs1, xs2, 
							  fn spc -> fn ((label1,x1), (label2,x2)) -> 
							  label1 = label2 & 
							  equivPattern? spc (x1, x2))

     | (WildPat     (s1,          _),
        WildPat     (s2,          _)) -> equivSort? spc (s1,s2)

     | (StringPat   (x1,          _),
        StringPat   (x2,          _)) -> x1 = x2

     | (BoolPat     (x1,          _),
        BoolPat     (x2,          _)) -> x1 = x2

     | (CharPat     (x1,          _),
        CharPat     (x2,          _)) -> x1 = x2

     | (NatPat      (x1,          _),
        NatPat      (x2,          _)) -> x1 = x2

     | (RelaxPat    (x1, t1,      _),
        RelaxPat    (x2, t2,      _)) -> equivPattern? spc (x1, x2) & equivTerm? spc (t1, t2)

     | (QuotientPat (x1, t1,      _),
        QuotientPat (x2, t2,      _)) -> equivPattern? spc (x1, x2) & equivTerm? spc (t1, t2)

     | (SortedPat   (x1, t1,      _),
        SortedPat   (x2, t2,      _)) -> equivPattern? spc (x1, x2) & equivSort? spc (t1, t2)

     | _ -> false

 def equivFun? spc (f1, f2) =
  case (f1, f2) of
     | (PQuotient t1,       PQuotient t2)       -> equivTerm? spc (t1, t2)
     | (PChoose   t1,       PChoose   t2)       -> equivTerm? spc (t1, t2)
     | (PRestrict t1,       PRestrict t2)       -> equivTerm? spc (t1, t2)
     | (PRelax    t1,       PRelax    t2)       -> equivTerm? spc (t1, t2)

     | (Not,                Not         )       -> true
     | (And,                And         )       -> true
     | (Or,                 Or          )       -> true
     | (Implies,            Implies     )       -> true
     | (Iff,                Iff         )       -> true
     | (Equals,             Equals      )       -> true
     | (NotEquals,          NotEquals   )       -> true

     | (Quotient,           Quotient    )       -> true
     | (Choose,             Choose      )       -> true
     | (Restrict,           Restrict    )       -> true
     | (Relax,              Relax       )       -> true

     %  (q,f) matches QualifiedId * Fixity
     | (Op   (q1,f1),       Op   (q2,f2))       -> f1 = f2 & (findTheOp (spc, q1) = findTheOp (spc, q2))
     | (Project   x1,       Project   x2)       -> x1 = x2
     | (Embed     x1,       Embed     x2)       -> x1 = x2
     | (Embedded  x1,       Embedded  x2)       -> x1 = x2
    %| (Select    x1,       Select    x2)       -> x1 = x2
     | (Nat       x1,       Nat       x2)       -> x1 = x2
     | (Char      x1,       Char      x2)       -> x1 = x2
     | (String    x1,       String    x2)       -> x1 = x2
     | (Bool      x1,       Bool      x2)       -> x1 = x2

     | (OneName   x1,       OneName   x2)       -> x1.1 = x2.1
     | (TwoNames  x1,       TwoNames  x2)       -> (x1.1 = x2.1) & (x1.2 = x2.2) 
     | _ -> false

 def equivVar? spc ((id1,s1), (id2,s2)) = 
   id1 = id2 & 
   equivSort? spc (s1, s2)


endspec
