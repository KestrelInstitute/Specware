(* Copyright 2015 Kestrel Institute. See file LICENSE for license details *)

AnnSpec qualifying spec

 import AnnSpec
 import /Languages/MetaSlang/AbstractSyntax/Equalities
 import /Languages/MetaSlang/AbstractSyntax/DiffTerm
 import ExpandType

 %%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%
 %%%      Equivalences wrt alpha-conversion and type expansion
 %%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%

 op equivTerm?    : Spec -> MSTerm    * MSTerm    -> Bool
 op equivPattern? : Spec -> MSPattern * MSPattern -> Bool
 op equivVar?     : Spec -> MSVar     * MSVar     -> Bool

 op similarType?  : Spec -> MSType    * MSType    -> Bool  % assumes A and A|p are similar
 op equivType?    : Spec -> MSType    * MSType    -> Bool  % assumes A and A|p are not equivalent

 def Utilities.unifyTerm? spc (t1, t2) = equivTerm? spc (t1, t2) % hack to avoid circularity

 %%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%
 %%% Naming convention:  To avoid confusion when both Foo and Foos exist
 %%%                      (e.g. when type Foos = List Foo), we use
 %%%                      "equalFoo"  or "equivFoo" to compare two Foo's, and
 %%%                      "equalFoos" or "equivFoo" to compare two Foos'es.
 %%%                     This converts less fluently into English, but is 
 %%%                      ultimately less confusing.
 %%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%

 %%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%
 %%%      Utilities for comparing structures
 %%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%

 op  equivList? : [b] Spec -> List b * List b * (Spec -> b * b -> Bool) -> Bool
 def equivList? spc (x, y, eqFn) =
  (length x) = (length y) &&
  (case (x, y) of
      | ([],              [])             -> true
      | (head_x::tail_x,  head_y::tail_y) -> eqFn spc (head_x, head_y) && 
                                             equivList? spc (tail_x, tail_y, eqFn)
      | _ -> false)

  op equivOpt? : [b] Spec -> Option b * Option b * (Spec -> b * b -> Bool) -> Bool
 def equivOpt? spc (x, y, eqFn) =
  case (x, y) of
     | (None,    None)    -> true
     | (Some x1, Some y1) -> eqFn spc (x1, y1)
     | _ -> false

 %%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%
 %%%      Terms
 %%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%

   %% def equivTerm? spc (t1, t2) =
   %%   let new? = new_equivTerm? spc (t1, t2) in
   %%   let _ = 
   %%       let old? = old_equivTerm? spc (t1, t2) in
   %%       if old? = new? then
   %%         ()
   %%       else
   %%         let env = initialEnv (spc, "internal") in
   %%         let all_diffs = diffTerm [] (t1, t2) in
   %%         let filtered_diffs = foldl (fn (diffs,diff) ->
   %%                                       case diff of
   %%                                         | Types (x,y) ->	
   %%                                           if new_equivType? spc (x, y) then
   %%                                             diffs
   %%                                           else
   %%                                             [diff] ++ diffs
   %%                                         | _ -> 
   %%                                           [diff] ++ diffs)
   %%                                    []
   %%                                    all_diffs
   %%         in
   %%         let _ = toScreen("\n----------\n") in
   %%         let _ = toScreen("Old = " ^ toString old? ^ ", new = " ^ toString new? ^ "\n") in
   %%         let _ = toScreen (foldl (fn (s,x) -> s ^  "   " ^ anyToString x ^ "\n") "\nDiffs[c]" all_diffs) in
   %%         let _ = toScreen (foldl (fn (s,x) -> s ^  "   " ^ anyToString x ^ "\n") "\nDiffs[d]" filtered_diffs) in
   %%         let _ = toScreen("\n") in
   %%         let _ = toScreen("X = " ^ anyToString t1 ^ "\n") in
   %%         let _ = toScreen("Y = " ^ anyToString t2 ^ "\n") in
   %%         let _ = toScreen("\n----------\n") in
   %%         let _ = myBreak 33 in
   %%         ()
   %%   in
   %%   new?
   %%
   %% op  myBreak : Nat -> Nat
   %% def myBreak n = n

 def equivTerm? spc (x, y) =
   (equalTermAlpha? (x, y))
   ||
   (let env = initialEnv (spc, "internal") in
    let all_diffs = diffTerm [] (x, y) in
    let filtered_diffs = foldl (fn (diffs,diff) ->
                                  case diff of
                                    | Types (x,y) ->	
                                      if similarType? spc (x, y) then % allow A to match A|p, e.g. 0:Nat to match 0:Int
                                        diffs
                                      else
                                        [diff] ++ diffs
	                            | Terms (Fun (Op (qid_x, fixity_x), type_x, _),
                                             Fun (Op (qid_y, fixity_y), type_y, _)) 
                                      ->
	                              if (fixity_x = fixity_y && findTheOp (spc, qid_x) = findTheOp (spc, qid_y)) then
                                        diffs
	                              else
	                                [diff] ++ diffs
                                    | _ -> 
                                      [diff] ++ diffs)
                               []
                               all_diffs
    in
      empty? filtered_diffs)

   %% op  old_equivTerm? : Spec -> MS.Term * MS.Term -> Bool
   %% def old_equivTerm? spc (t1, t2) =
   %%   (equalTerm? (t1, t2))
   %%   ||
   %%   (case (t1, t2) of
   %%
   %%     | (Apply      (x1, y1,      _), 
   %%        Apply      (x2, y2,      _)) -> old_equivTerm? spc (x1, x2) && old_equivTerm? spc (y1, y2)
   %%
   %%     | (ApplyN     (xs1,         _),   
   %%        ApplyN     (xs2,         _)) -> equivList? spc (xs1, xs2, old_equivTerm?)
   %%
   %%     | (Record     (xs1,         _), 
   %%        Record     (xs2,         _)) -> equivList? spc  (xs1, xs2, 
   %%							 fn spc -> fn ((label1,x1),(label2,x2)) -> 
   %%							 label1 = label2 && 
   %%							 old_equivTerm? spc (x1, x2))
   %%
   %%     | (Bind       (b1, vs1, x1, _),
   %%        Bind       (b2, vs2, x2, _)) -> b1 = b2 && 
   %%                                        %% TODO: Could check modulo alpha conversion...
   %%                                        equivList? spc (vs1, vs2, equivVar?) &&
   %%                                        old_equivTerm? spc (x1,  x2)
   %%
   %%     | (Let        (pts1, b1,    _),
   %%        Let        (pts2, b2,    _)) -> old_equivTerm? spc (b1, b2) &&
   %%                                        equivList? spc (pts1, pts2,
   %%							fn spc -> fn ((p1,t1),(p2,t2)) -> 
   %%							old_equivPattern? spc (p1, p2) && 
   %%							old_equivTerm?    spc (t1, t2))
   %%
   %%     | (LetRec     (vts1, b1,    _),
   %%        LetRec     (vts2, b2,    _)) -> old_equivTerm? spc  (b1, b2) &&
   %%                                        equivList? spc  (vts1, vts2,
   %%							 fn spc -> fn ((v1,t1),(v2,t2)) -> 
   %%							 equivVar?  spc (v1, v2) && 
   %%							 old_equivTerm? spc (t1, t2))
   %%
   %%     | (Var        (v1,          _),
   %%        Var        (v2,          _)) -> equivVar? spc (v1, v2)
   %%
   %%     | (Fun        (f1, s1,      _),
   %%        Fun        (f2, s2,      _)) -> old_equivFun? spc (f1,f2) && equivType? spc (s1,s2)
   %%
   %%     | (Lambda     (xs1,         _),
   %%        Lambda     (xs2,         _)) -> equivList? spc  (xs1, xs2,
   %%							 fn spc -> fn ((p1,c1,b1),(p2,c2,b2)) ->
   %%							 old_equivPattern? spc (p1, p2) && 
   %%							 old_equivTerm?    spc (c1, c2) && 
   %%							 old_equivTerm?    spc (b1, b2))
   %%
   %%     | (IfThenElse (c1, x1, y1,  _),
   %%        IfThenElse (c2, x2, y2,  _)) -> old_equivTerm? spc (c1, c2) && 
   %%                                        old_equivTerm? spc (x1, x2) && 
   %%                                        old_equivTerm? spc (y1, y2)
   %%
   %%     | (Seq        (xs1,         _),
   %%        Seq        (xs2,         _)) -> equivList? spc (xs1, xs2, old_equivTerm?)
   %%
   %%     | (TypedTerm (x1, s1,      _),
   %%        TypedTerm (x2, s2,      _)) -> old_equivTerm? spc (x1, x2) && equivType? spc (s1, s2)
   %%
   %%     %% TODO: Could check modulo alpha conversion for Pi terms...
   %%     | (Pi (_,x1,_),  _          ) -> old_equivTerm? spc (x1, t2) 
   %%     | (_,            Pi (_,x2,_)) -> old_equivTerm? spc (t1, x2) 
   %%
   %%     | _ -> false)
   %%
   %% op  old_equivFun? : Spec -> MS.Fun * MS.Fun -> Bool
   %% def old_equivFun? spc (f1, f2) =
   %%  case (f1, f2) of
   %%     | (PQuotient qid1,     PQuotient qid2)     -> qid1 = qid2
   %%     | (PChoose   qid1,     PChoose   qid2)     -> qid1 = qid2
   %%
   %%     | (Not,                Not         )       -> true
   %%     | (And,                And         )       -> true
   %%     | (Or,                 Or          )       -> true
   %%     | (Implies,            Implies     )       -> true
   %%     | (Iff,                Iff         )       -> true
   %%     | (Equals,             Equals      )       -> true
   %%     | (NotEquals,          NotEquals   )       -> true
   %%
   %%     | (Quotient qid1,      Quotient  qid2)     -> qid1 = qid2
   %%     | (Choose   qid1,      Choose    qid2)     -> qid1 = qid2
   %%     | (Restrict,           Restrict    )       -> true
   %%     | (Relax,              Relax       )       -> true
   %%
   %%     %  (q,f) matches QualifiedId * Fixity
   %%     | (Op   (q1,f1),       Op   (q2,f2))       -> f1 = f2 && (findTheOp (spc, q1) = findTheOp (spc, q2))
   %%     | (Project   x1,       Project   x2)       -> x1 = x2
   %%     | (Embed     x1,       Embed     x2)       -> x1 = x2
   %%     | (Embedded  x1,       Embedded  x2)       -> x1 = x2
   %%    %| (Select    x1,       Select    x2)       -> x1 = x2
   %%     | (Nat       x1,       Nat       x2)       -> x1 = x2
   %%     | (Char      x1,       Char      x2)       -> x1 = x2
   %%     | (String    x1,       String    x2)       -> x1 = x2
   %%     | (Bool      x1,       Bool      x2)       -> x1 = x2
   %%
   %%     | (OneName   x1,       OneName   x2)       -> x1.1 = x2.1
   %%     | (TwoNames  x1,       TwoNames  x2)       -> (x1.1 = x2.1) && (x1.2 = x2.2) 
   %%     | _ -> false

 %%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%
 %%%      Type Equivalences
 %%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%

   %% def equivType? spc (x, y) =
   %%   let new? = new_equivType? spc (x, y) in
   %%   let _ = 
   %%       let old? = old_equivType? spc (x, y) in
   %%       if old? = new? then
   %%         ()
   %%       else
   %%         let env = initialEnv (spc, "internal") in
   %%         let all_diffs      = diffType [] (x, y) in
   %%         let filtered_diffs = foldl (fn (diffs,diff) ->
   %%                                       case diff of
   %%                                         | Types (x,y) ->	
   %%                                           let _ = toScreen("x  = " ^ anyToString x  ^ "\n") in
   %%                                           let _ = toScreen("y  = " ^ anyToString y  ^ "\n") in
   %%                                           let x2 = expandType (env, x) in
   %%                                           let y2 = expandType (env, y) in
   %%                                           let _ = toScreen("x2 = " ^ anyToString x2 ^ "\n") in
   %%                                           let _ = toScreen("y2 = " ^ anyToString y2 ^ "\n") in
   %%                                           %% treat A and A|p as non-equivalent
   %%                                           if new_equivType? spc (x2, y2) then
   %%                                             diffs
   %%                                           else
   %%                                             [diff] ++ diffs
   %%                                         | _ -> 
   %%                                           [diff] ++ diffs)
   %%                                    []
   %%                                    all_diffs
   %%         in
   %%         let _ = toScreen("\n----------\n") in
   %%         let _ = toScreen("Old = " ^ toString old? ^ ", new = " ^ toString new? ^ "\n") in
   %%         let _ = toScreen (foldl (fn (s,x) -> s ^  "   " ^ anyToString x ^ "\n") "\nDiffs[a]" all_diffs) in
   %%         let _ = toScreen (foldl (fn (s,x) -> s ^  "   " ^ anyToString x ^ "\n") "\nDiffs[b]" filtered_diffs) in
   %%         let _ = toScreen("\n") in
   %%         let _ = toScreen("S1 = " ^ anyToString x ^ "\n") in
   %%         let _ = toScreen("S2 = " ^ anyToString y ^ "\n") in
   %%         let _ = toScreen("\n----------\n") in
   %%         let _ = myBreak 44 in
   %%         ()
   %%   in
   %%     new?
   %%
   %%
   %% op  new_equivType? : Spec -> MS.Type * MS.Type -> Bool

 def equivType? spc (x, y) =
    equivTypeSubType? spc (x, y) false

 op debugEquivType?: Bool = false

 op equivTypeSubType? (spc: Spec) (x: MSType, y: MSType) (ignore_subtypes?: Bool): Bool =
   let _ = if debugEquivType?
            then writeLine(printType x^" =?= "^printType y) else ()
   in
   let 
     def aux x y prior_diffs =
       (equalTypeSubtype? (x, y, ignore_subtypes?))
       ||
       (let env = initialEnv (spc, "internal") in
        let diffs = diffType [] (x, y) in
        forall? (fn diff ->
                   %% Coproducts are the only reasonable way to get 
                   %% recursively defined types, so we shouldn't need
                   %% an occurence check to avoid infinite expansions,
                   %% but someone might present us with pathological
                   %% types such as T = T * T, or T = T | p.
                   %% So we start with an occurrence check...
                   case diff of
                     | Types (x,y) ->	
                       if exists? (fn old_diff ->
                                    case old_diff of
                                      | Types (old_x, old_y) ->
                                        equalTypeSubtype? (x, old_x, ignore_subtypes?)
                                         && equalTypeSubtype? (y, old_y, ignore_subtypes?)
                                      | _ -> false)
                         prior_diffs
                         then
                           %% let _ = toScreen("\nOccurrence check for " ^ anyToString (x, y) ^ "\n") in
                           %% let _ = toScreen("\namong " ^ anyToString prior_diffs ^ "\n") in
                           false
                       else if equalTypeSubtype? (x, y, ignore_subtypes?) then 
                         true
                            else
                              let (x,y) = if ignore_subtypes?
                                           then (removeSubtypes x, removeSubtypes y)
                                           else (x,y)
                              in
                              let x2 = expandType (env, x) in
                              let y2 = expandType (env, y) in
                              %% treat A and A|p as non-equivalent
                              if equalTypeSubtype? (x, x2, ignore_subtypes?)
                                  && equalTypeSubtype? (y, y2, ignore_subtypes?) then
                                false
                              else 
                                equivTypeSubType? spc (x2, y2) ignore_subtypes? ||
                                aux x2 y2 (prior_diffs ++ diffs)
                     | _ -> ignore_subtypes?)
             diffs)
   in
   let result = aux x y [] in
   let _ = if debugEquivType?
            then writeLine(printType x^(if result then " = " else " ~= ")^printType y) else ()
   in
   result

   %% op  old_equivType? : Spec -> MS.Type * MS.Type -> Bool
   %% def old_equivType? spc (s1, s2) =
   %%   (equalType? (s1, s2))
   %%   ||
   %%   (let env = initialEnv (spc, "internal") in
   %%    %% treat A and A|p as non-equivalent
   %%    unifyTypes env false s1 s2 )

 %% used by checkRecursiveCall in TypeObligations.sw
 def similarType? spc (s1, s2) =
   (equalTypeSubtype? (s1, s2, true))
   ||
   (let env = initialEnv (spc, "internal") in
    %% treat A and A|p as similar
    unifyTypes env Ignore s1 s2)

 op removeSubtypes (ty: MSType): MSType = 
  case ty
    of Subtype (s_ty, _, _) -> removeSubtypes s_ty
     | _ -> ty


 %%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%
 %%%      Pattern Equivalences, expanding definitions
 %%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%

   %% def equivPattern? spc (p1,p2) =
   %%   let old? = old_equivPattern? spc (p1,p2) in
   %%   let new? = new_equivPattern? spc (p1, p2) in
   %%   let _ = (if new? = old? then
   %%             ()
   %%            else
   %%             toScreen("\nequivPattern?, old? = " ^ toString old? ^ " new? = " ^ toString new? ^ "\n"))
   %%   in	
   %%     old?
   %%
   %% op  new_equivPattern? : Spec -> MS.Pattern * MS.Pattern -> Bool

 def equivPattern? spc (p1,p2) =
   case diffPattern [] (p1, p2) of
     | Some (equivs, diffs) -> 
       %% for now at least, any discrepency in patterns 
       %% only if they bind the same vars
       (forall? (fn diff -> 
                   case diff of 
                     | Types      (t1, t2) -> equivType? spc (t1, t2)
                     | Terms      (t1, t2) -> equivTerm? spc (t1, t2)
                     | MetaTyVars _ -> false) % TODO: ??
	    diffs)
       &&
       %% for now at least, patterns are considered equivalent
       %% only if they bind the same vars
       (forall? (fn equiv ->
                   case equiv of
                     | TypeVars (v1, v2) -> v1 = v2  
                     | TermVars (v1, v2) -> equivVar? spc (v1, v2))
            equivs)
     | _ -> false	

   %% op  old_equivPattern? : Spec -> MS.Pattern * MS.Pattern -> Bool
   %% def old_equivPattern? spc (p1,p2) =
   %%   (equalPattern? (p1, p2))
   %%   ||
   %%   (case (p1, p2) of
   %%     | (AliasPat    (x1, y1,      _),
   %%        AliasPat    (x2, y2,      _)) -> old_equivPattern? spc (x1,x2) && old_equivPattern? spc (y1,y2)
   %%
   %%     | (VarPat      (v1,          _),
   %%        VarPat      (v2,          _)) -> equivVar? spc (v1, v2)
   %%
   %%     | (EmbedPat    (i1, op1, s1, _),
   %%        EmbedPat    (i2, op2, s2, _)) -> i1 = i2 && 
   %%                                         equivType? spc (s1, s2) && 
   %%                                         equivOpt?  spc (op1, op2, old_equivPattern?)
   %%
   %%     | (RecordPat   (xs1,         _),
   %%        RecordPat   (xs2,         _)) -> equivList? spc  (xs1, xs2, 
   %% 	 	 	 	 	 	 	  fn spc -> fn ((label1,x1), (label2,x2)) -> 
   %% 	 	 	 	 	 	 	  label1 = label2 && 
   %% 	 	 	 	 	 	 	  old_equivPattern? spc (x1, x2))
   %%
   %%     | (WildPat     (s1,          _),
   %%        WildPat     (s2,          _)) -> equivType? spc (s1,s2)
   %%
   %%     | (StringPat   (x1,          _),
   %%        StringPat   (x2,          _)) -> x1 = x2
   %%
   %%     | (BoolPat     (x1,          _),
   %%        BoolPat     (x2,          _)) -> x1 = x2
   %%
   %%     | (CharPat     (x1,          _),
   %%        CharPat     (x2,          _)) -> x1 = x2
   %%
   %%     | (NatPat      (x1,          _),
   %%        NatPat      (x2,          _)) -> x1 = x2
   %%
   %%     | (QuotientPat (x1, qid1,    _),
   %%        QuotientPat (x2, qid2,    _)) -> old_equivPattern? spc (x1, x2) && qid1 = qid2
   %%
   %%     | (RestrictedPat (x1, t1,    _),
   %%        RestrictedPat (x2, t2,    _)) -> old_equivPattern? spc (x1, x2) && old_equivTerm? spc (t1, t2)
   %%
   %%     | (TypedPat   (x1, t1,      _),
   %%        TypedPat   (x2, t2,      _)) -> old_equivPattern? spc (x1, x2) && equivType? spc (t1, t2)
   %%
   %%     | _ -> false)
   %%

 %%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%
 %%%      Var Equivalences, expanding definitions for types
 %%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%

 def equivVar? spc ((id1,s1), (id2,s2)) = 
   (id1 = id2)
   &&
   %% May want to make the ignoreSubtype? be a parameter rather than false
   (equivType? spc (s1, s2))

 op equivTermIn? (spc: Spec) (t1: MSTerm, tms: MSTerms): Bool =
   exists? (fn t2 -> equivTerm? spc (t1,t2)) tms

end-spec
