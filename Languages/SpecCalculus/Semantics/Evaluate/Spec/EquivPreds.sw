SpecCalc qualifying spec 
 import ../../Environment
 import /Languages/MetaSlang/Specs/Elaborate/Utilities % unifySorts

 %%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%
 %%%      Equivalences, expanding definitions
 %%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%
 %%% These are patterned after equalTerm? etc. in AnnTerm.sw

 op equivSort?    : Spec -> Boolean -> MS.Sort * MS.Sort -> Boolean
 op equivTerm?    : Spec -> MS.Term    * MS.Term    -> Boolean
 op equivFun?     : Spec -> MS.Fun     * MS.Fun     -> Boolean
 op equivPattern? : Spec -> MS.Pattern * MS.Pattern -> Boolean
 op equivVar?     : Spec -> MS.Var     * MS.Var     -> Boolean

 %%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%
 %%%      Sort Equivalences, expanding definitions
 %%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%

 def equivSort? spc ignoreSubsorts? (s1, s2) =
   (equivTypes? spc (s1, s2))
   ||
   (let env = initialEnv (spc, "internal") in
    unifySorts env ignoreSubsorts? s1 s2 )

 %%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%
 %%%      Term Equivalences, expanding definitions
 %%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%

  op equivList? : [b] Spec -> List b * List b * (Spec -> b * b -> Boolean) -> Boolean
 def equivList? spc (x, y, eqFn) =
  (length x) = (length y) &&
  (case (x, y) of
      | ([],              [])             -> true
      | (head_x::tail_x,  head_y::tail_y) -> eqFn spc (head_x, head_y) && 
                                             equivList? spc (tail_x, tail_y, eqFn)
      | _ -> false)

  op equivOpt? : [b] Spec -> Option b * Option b * (Spec -> b * b -> Boolean) -> Boolean
 def equivOpt? spc (x, y, eqFn) =
  case (x, y) of
     | (None,    None)    -> true
     | (Some x1, Some y1) -> eqFn spc (x1, y1)
     | _ -> false

 def equivTerm? spc (t1, t2) =
   (equivTerms? spc (t1, t2))
   ||
   (case (t1, t2) of

     | (Apply      (x1, y1,      _), 
        Apply      (x2, y2,      _)) -> equivTerm? spc (x1, x2) && equivTerm? spc (y1, y2)

     | (ApplyN     (xs1,         _),   
        ApplyN     (xs2,         _)) -> equivList? spc (xs1, xs2, equivTerm?)

     | (Record     (xs1,         _), 
        Record     (xs2,         _)) -> equivList? spc  (xs1, xs2, 
							 fn spc -> fn ((label1,x1),(label2,x2)) -> 
							 label1 = label2 && 
							 equivTerm? spc (x1, x2))

     | (Bind       (b1, vs1, x1, _),
        Bind       (b2, vs2, x2, _)) -> b1 = b2 && 
                                        %% TODO: Could check modulo alpha conversion...
                                        equivList? spc (vs1, vs2, equivVar?) &&
                                        equivTerm? spc (x1,  x2)

     | (Let        (pts1, b1,    _),
        Let        (pts2, b2,    _)) -> equivTerm? spc (b1, b2) &&
                                        equivList? spc (pts1, pts2,
							fn spc -> fn ((p1,t1),(p2,t2)) -> 
							equivPattern? spc (p1, p2) && 
							equivTerm?    spc (t1, t2))

     | (LetRec     (vts1, b1,    _),
        LetRec     (vts2, b2,    _)) -> equivTerm? spc  (b1, b2) &&
                                        equivList? spc  (vts1, vts2,
							 fn spc -> fn ((v1,t1),(v2,t2)) -> 
							 equivVar?  spc (v1, v2) && 
							 equivTerm? spc (t1, t2))

     | (Var        (v1,          _),
        Var        (v2,          _)) -> equivVar? spc (v1, v2)

     | (Fun        (f1, s1,      _),
        Fun        (f2, s2,      _)) -> equivFun? spc (f1,f2) && equivSort? spc false (s1,s2)

     | (Lambda     (xs1,         _),
        Lambda     (xs2,         _)) -> equivList? spc  (xs1, xs2,
							 fn spc -> fn ((p1,c1,b1),(p2,c2,b2)) ->
							 equivPattern? spc (p1, p2) && 
							 equivTerm?    spc (c1, c2) && 
							 equivTerm?    spc (b1, b2))

     | (IfThenElse (c1, x1, y1,  _),
        IfThenElse (c2, x2, y2,  _)) -> equivTerm? spc (c1, c2) && 
                                        equivTerm? spc (x1, x2) && 
                                        equivTerm? spc (y1, y2)

     | (Seq        (xs1,         _),
        Seq        (xs2,         _)) -> equivList? spc (xs1, xs2, equivTerm?)

     | (SortedTerm (x1, s1,      _),
        SortedTerm (x2, s2,      _)) -> equivTerm? spc (x1, x2) && equivSort? spc false (s1, s2)

     %% TODO: Could check modulo alpha conversion for Pi terms...
     | (Pi (_,x1,_),  _          ) -> equivTerm? spc (x1, t2) 
     | (_,            Pi (_,x2,_)) -> equivTerm? spc (t1, x2) 

     | _ -> false)

 def equivFun? spc (f1, f2) =
  case (f1, f2) of
     | (PQuotient qid1,     PQuotient qid2)     -> qid1 = qid2
     | (PChoose   qid1,     PChoose   qid2)     -> qid1 = qid2

     | (Not,                Not         )       -> true
     | (And,                And         )       -> true
     | (Or,                 Or          )       -> true
     | (Implies,            Implies     )       -> true
     | (Iff,                Iff         )       -> true
     | (Equals,             Equals      )       -> true
     | (NotEquals,          NotEquals   )       -> true

     | (Quotient qid1,      Quotient  qid2)     -> qid1 = qid2
     | (Choose   qid1,      Choose    qid2)     -> qid1 = qid2
     | (Restrict,           Restrict    )       -> true
     | (Relax,              Relax       )       -> true

     %  (q,f) matches QualifiedId * Fixity
     | (Op   (q1,f1),       Op   (q2,f2))       -> f1 = f2 && (findTheOp (spc, q1) = findTheOp (spc, q2))
     | (Project   x1,       Project   x2)       -> x1 = x2
     | (Embed     x1,       Embed     x2)       -> x1 = x2
     | (Embedded  x1,       Embedded  x2)       -> x1 = x2
    %| (Select    x1,       Select    x2)       -> x1 = x2
     | (Nat       x1,       Nat       x2)       -> x1 = x2
     | (Char      x1,       Char      x2)       -> x1 = x2
     | (String    x1,       String    x2)       -> x1 = x2
     | (Bool      x1,       Bool      x2)       -> x1 = x2

     | (OneName   x1,       OneName   x2)       -> x1.1 = x2.1
     | (TwoNames  x1,       TwoNames  x2)       -> (x1.1 = x2.1) && (x1.2 = x2.2) 
     | _ -> false

 %%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%
 %%%      Pattern Equivalences, expanding definitions
 %%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%

 def equivPattern? spc (p1,p2) =
   (equivPatterns? spc (p1, p2))
   ||
   (case (p1, p2) of
     | (AliasPat    (x1, y1,      _),
        AliasPat    (x2, y2,      _)) -> equivPattern? spc (x1,x2) && equivPattern? spc (y1,y2)

     | (VarPat      (v1,          _),
        VarPat      (v2,          _)) -> equivVar? spc (v1, v2)

     | (EmbedPat    (i1, op1, s1, _),
        EmbedPat    (i2, op2, s2, _)) -> i1 = i2 && 
                                         equivSort? spc false (s1, s2) && 
                                         equivOpt?  spc (op1, op2, equivPattern?)

     | (RecordPat   (xs1,         _),
        RecordPat   (xs2,         _)) -> equivList? spc  (xs1, xs2, 
							  fn spc -> fn ((label1,x1), (label2,x2)) -> 
							  label1 = label2 && 
							  equivPattern? spc (x1, x2))

     | (WildPat     (s1,          _),
        WildPat     (s2,          _)) -> equivSort? spc false (s1,s2)

     | (StringPat   (x1,          _),
        StringPat   (x2,          _)) -> x1 = x2

     | (BoolPat     (x1,          _),
        BoolPat     (x2,          _)) -> x1 = x2

     | (CharPat     (x1,          _),
        CharPat     (x2,          _)) -> x1 = x2

     | (NatPat      (x1,          _),
        NatPat      (x2,          _)) -> x1 = x2

     | (QuotientPat (x1, qid1,    _),
        QuotientPat (x2, qid2,    _)) -> equivPattern? spc (x1, x2) && qid1 = qid2

     | (RestrictedPat (x1, t1,    _),
        RestrictedPat (x2, t2,    _)) -> equivPattern? spc (x1, x2) && equivTerm? spc (t1, t2)

     | (SortedPat   (x1, t1,      _),
        SortedPat   (x2, t2,      _)) -> equivPattern? spc (x1, x2) && equivSort? spc false (t1, t2)

     | _ -> false)


 %%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%
 %%%      Var Equivalences, expanding definitions for sorts
 %%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%

 def equivVar? spc ((id1,s1), (id2,s2)) = 
   (id1 = id2)
   &&
   %% May want to make the ignoreSubsort? be a parameter rather than false
   (equivSort? spc false (s1, s2))


endspec
