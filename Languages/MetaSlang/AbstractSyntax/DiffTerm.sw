(* Copyright 2015 Kestrel Institute. See file LICENSE.text for license details *)

AnnSpec qualifying spec

 import Equalities
 import /Languages/MetaSlang/Specs/MSTerm

 %%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%
 %%%      Equivalences wrt alpha-conversion and type expansion
 %%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%

 type Diffs  = List Diff
 type Diff   = | Types (MSType * MSType)
               | Terms (MSTerm * MSTerm)
               | MetaTyVars (MetaTyVar * MetaTyVar)

 type Equivs = List Equiv
 type Equiv  = | TypeVars (TyVar * TyVar)
               | TermVars (MSVar * MSVar)

 %%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%

 op  diffTermList : Equivs -> MSTerms * MSTerms -> Diffs
 def diffTermList equivs (x, y) =
   let
     def aux (x, y) =
       case (x, y) of
         | ([], []) -> []
         | (head_x::tail_x,  head_y::tail_y) -> 
           (diffTerm equivs (head_x, head_y)) ++ aux (tail_x, tail_y) 
         | _ -> fail("can't get here")
   in
     aux (x, y)

 op  matchingVars? : Equivs -> MSVar * MSVar -> Bool
 def matchingVars? equivs (v1, v2) =
   case equivs of
     | [] -> false
     | (TermVars (x1, x2)) :: equivs ->
       if v1.1 = x1.1 then 
         v2.1 = x2.1
       else if v2.1 = x2.1 then
         v1.1 = x1.1
       else
         matchingVars? equivs (v1, v2)
     | _ :: equivs ->
       matchingVars? equivs (v1, v2)

 op  equateTyVars : List TyVar * List TyVar -> Equivs 
 def equateTyVars (tvs1, tvs2) =
   case (tvs1, tvs2) of
     | ([], []) -> []
     | (tv1 :: tail1, tv2 :: tail2) ->
       [TypeVars (tv1,tv2)]
       ++ 
       equateTyVars (tail1, tail2)

 op  matchingTyVars? : Equivs -> TyVar * TyVar -> Bool
 def matchingTyVars? equivs (v1, v2) =
   case equivs of
     | [] -> false
     | (TypeVars (x1, x2)) :: equivs ->
       if v1 = x1 then 
         v2 = x2
       else if v2 = x2 then
         v1 = x1
       else
         matchingTyVars? equivs (v1, v2)
     | _ :: equivs ->
       matchingTyVars? equivs (v1, v2)

 %%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%

 op diffTerm    : Equivs -> MSTerm    * MSTerm     -> Diffs
 op diffType    : Equivs -> MSType    * MSType     -> Diffs
 op diffPattern : Equivs -> MSPattern * MSPattern  -> Option (Equivs * Diffs)
 op diffVars    : Equivs -> MSVars    * MSVars     -> Equivs * Diffs

 %%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%
 %%%      Terms
 %%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%

 def diffTerm outer_equivs (t1, t2) =
   if equalTerm? (t1, t2) then
     []
   else
     case (t1, t2) of

       | (Apply (x1, y1, _), Apply (x2, y2, _)) -> 
         (diffTerm outer_equivs (x1, x2)) ++ 
         (diffTerm outer_equivs (y1, y2))

       | (ApplyN (xs1, _), ApplyN (xs2, _)) | length xs1 = length xs2  -> 
         diffTermList outer_equivs (xs1, xs2)

       | (Record (fields1, _), Record (fields2, _)) ->
         (let 
            def aux (fields1, fields2) =
              case (fields1, fields2) of
                | ([], []) -> Some []
                | ((label1,x1) :: tail1, (label2,x2) :: tail2) ->
                  (if label1 = label2 then
                     case aux (tail1, tail2) of
                       | Some d2 ->
                         Some (d2 ++ diffTerm outer_equivs (x1, x2))
                       | _ -> None  % propagate complete mismatch out
                   else
                     None)   % complete mismatch for this field
                | _ -> None  % complete mismatch -- differing number of fields
          in
            case aux (fields1, fields2) of
              | Some diffs -> diffs
              | _ -> 
                %% complete mismatch -- 
                %%  different number of fields,
                %%  or labels for some fields don't match
                [Terms (t1, relabel_vars_in_term outer_equivs t2)])

       | (Bind (b1, vs1, x1, _), Bind (b2, vs2, x2, _)) | b1 = b2 && length vs1 = length vs2 ->
         let (local_equivs, local_diffs) = diffVars outer_equivs (vs1, vs2) in
         let equivs      = local_equivs ++ outer_equivs in 
         let inner_diffs = diffTerm outer_equivs (x1, x2) in
         let inner_diffs = (if local_var_mismatch? local_equivs inner_diffs then
                              [Terms (t1, relabel_vars_in_term equivs t2)] 
                            else
                              inner_diffs)
         in
          local_diffs ++ inner_diffs

       | (Let (pts1, b1, _),  Let (pts2, b2, _)) -> 
         (let 
            def aux (pts1, pts2) =
              case (pts1, pts2) of
                | ([],[]) -> Some ([],[])
                | ((pat1, term1) :: tail1, (pat2, term2) :: tail2) ->
                  (case diffPattern outer_equivs (pat1, pat2) of
                     | Some (head_equivs, pat_diffs) ->
                       let term_diffs = diffTerm outer_equivs (term1, term2) in
                       let head_diffs = pat_diffs ++ term_diffs in
                       (case aux (tail1, tail2) of
                          | Some (tail_equivs, tail_diffs) ->
                            Some (head_equivs ++ tail_equivs,
                                  head_diffs  ++ tail_diffs)
                          | _ -> None)
                     | _ -> None)
                | _ -> None
          in
            case aux (pts1, pts2) of
              | Some (local_equivs, pat_diffs) ->
                let equivs = local_equivs ++ outer_equivs in
                let body_diffs = diffTerm equivs (b1, b2) in
                if local_var_mismatch? local_equivs body_diffs then
                  [Terms (t1, relabel_vars_in_term equivs t2)]
                else
                  pat_diffs ++ body_diffs
              | _ -> 
                [Terms (t1, relabel_vars_in_term outer_equivs t2)])


       | (LetRec (vts1, body1, _), LetRec (vts2, body2, _)) | length vts1 = length vts2 ->
         (let 
            def diff_vars (vts1, vts2) : (Equivs * Diffs) =
              case (vts1, vts2) of
                | ([], []) -> ([], [])
                | ((v1,_) :: tail1, (v2,_) :: tail2) ->
                  let head_equivs = [TermVars (v1,v2)] in
                  let head_diffs  = diffType outer_equivs (v1.2, v2.2) in
                  let (tail_equivs, tail_diffs) = diff_vars (tail1, tail2) in
                  (head_equivs ++ tail_equivs,
                   head_diffs  ++ tail_diffs)

            def diff_args (vts1, vts2) =
             case (vts1, vts2) of
               | ([],[]) -> Some []
               | ((_, term1) :: tail1, (_, term2) :: tail2) ->
                 (case diff_args (tail1, tail2) of
                    | Some tail_diffs ->
                      Some (diffTerm outer_equivs (term1, term2) ++ tail_diffs)
                    | _ -> None)
          in
          let (local_equivs, local_diffs) = diff_vars (vts1, vts2) in
          let equivs = local_equivs ++ outer_equivs in
          local_diffs ++
          (case diff_args (vts1, vts2) of
            | Some pat_diffs ->
              let body_diffs = diffTerm equivs (body1, body2) in
              if local_var_mismatch? local_equivs body_diffs then
                [Terms (t1, relabel_vars_in_term equivs t2)]
              else
                pat_diffs ++ body_diffs
            | _ -> 
              [Terms (t1, relabel_vars_in_term outer_equivs t2)]))

       | (Var (v1, _), Var (v2, _)) | matchingVars? outer_equivs (v1,v2) ->
         %% if match fails, we'll end up with vars in the diff list and later processing will complain
         []

       | (Fun (f1, t1, _), Fun (f2, t2, _)) | equalFun? (f1,f2) ->
         diffType outer_equivs (t1,t2)

       | (Lambda (matches1, _), Lambda (matches2, _)) ->
         (let 
            def diff_matches (matches1, matches2) =
              case (matches1, matches2) of
                | ([], []) -> Some []
                | ((p1,c1,b1) :: tail1, (p2,c2,b2) :: tail2) ->
                  (case diff_matches (tail1, tail2) of
                     | Some tail_diffs ->
                       (case diffPattern outer_equivs (p1, p2) of
                          | Some (local_equivs, new_diffs) ->
                            let equivs = local_equivs ++ outer_equivs in
                            let cond_diffs = diffTerm equivs (c1, c2) in
                            let body_diffs = diffTerm equivs (b1, b2) in
                            let diffs = cond_diffs ++ body_diffs in
                            if local_var_mismatch? local_equivs diffs then
                              None 
                            else
                              Some (diffs ++ tail_diffs)
                          | _ -> None)  % complete mismatch for current pair 
                     | _ -> None)       % propagate complete mismatch out
                | _ -> None             % different number of cases
          in
            case diff_matches (matches1, matches2) of
              | Some diffs -> diffs
              | _ -> [Terms (t1, relabel_vars_in_term outer_equivs t2)])

       | (IfThenElse (c1, x1, y1, _), IfThenElse (c2, x2, y2, _)) -> 
         (diffTerm outer_equivs (c1, c2)) ++ 
         (diffTerm outer_equivs (x1, x2)) ++
         (diffTerm outer_equivs (y1, y2))

       | (Seq (xs1, _), Seq (xs2, _)) | length xs1 = length xs2 ->
         diffTermList outer_equivs (xs1, xs2)

       | (TypedTerm (x1, t1, _), TypedTerm (x2, t2, _)) -> 
         (diffTerm outer_equivs (x1, x2)) ++
         (diffType outer_equivs (t1, t2))

       | (Pi (tvs1,x1,_), Pi (tvs2,x2,_)) | length tvs1 = length tvs2 ->
         let equivs = equateTyVars (tvs1, tvs2) ++ outer_equivs in
         diffTerm equivs (x1, x2)

       | _ -> 
         %% when all else fails, pair up the original terms
         [Terms (t1, relabel_vars_in_term outer_equivs t2)]

 def local_var_mismatch? equivs diffs =
   %%
   %% In general, if vars mismatch, the overall terms are a mismatch, e.g.:
   %%
   %%   fa (x,y) F(x,y) -> F(y,x)
   %%   fa (x,y) F(x,y) -> F(x,y)
   %%
   %% The diffs will be just [Term (x,y),Term (y,x)]  (from the consequents).
   %%
   %% But 'fa(x) x' is equivalent to 'fa(y) y', so a simple post-comparison of those
   %% differing terms would accept them as equivalent, and we would wrongly accept 
   %% the overall terms as equivalent.  Hence we must notice this situation and return
   %% a mismatch on the overall terms.
   %%
   %% In fact, we consider the overall terms to mismatch if any var anywhere in either 
   %% term mismatches, e.g.: for the following pair:
   %%
   %%   fa (x,y) F(x,y) -> F(y,x)
   %%   fa (x,y) F(x,y) -> F(y,3)
   %%
   %% diffs would be [Terms (x,3)], and we would consider the the overall terms to mismatch.
   %% 
   exists? (fn pair -> 
             case pair of
               | TermVars (v1,v2) ->
                 (exists? (fn diff -> 
                            case diff of 
                              | Terms (Var (x,_), _) | x = v1 -> true
                              | Terms (_, Var (y,_)) | y = v2 -> true
                              | _ -> false)
                          diffs)
               | _ -> false)
          equivs


 def diffType equivs (t1, t2) =
 %   if t1 = t2 then     []   else
     case (t1, t2) of
       | (Boolean _, Boolean _)   -> []

       | (Arrow (x1, y1, _), Arrow (x2, y2, _)) -> 
         (diffType equivs (x1, x2)) ++ 
         (diffType equivs (y1, y2))

       | (Product (fields1, _), Product  (fields2, _)) | length fields1 = length fields2 ->
         (let
            def aux (fields1, fields2) =
              case (fields1, fields2) of         
                | ([], []) -> Some []
                | ((id1, t1)::tail1, (id2, t2)::tail2) ->
                  if id1 = id2 then
                    case aux (tail1, tail2) of
                      | Some tail_diffs -> 
                        Some ((diffType equivs (t1, t2)) ++ tail_diffs)
                      | _ -> None
                  else
                    None
          in
            case aux (fields1, fields2) of
              | Some diffs -> diffs
              | _ ->
                [Types (t1, relabel_vars_in_type equivs t2)])
         
       | (CoProduct (fields1, _), CoProduct (fields2, _)) ->
         (let
            def aux (fields1, fields2) =
              case (fields1, fields2) of         
                | ([], []) -> Some []
                | ((id1, t1)::tail1, (id2, t2)::tail2) ->
                  if id1 = id2 then
                    case aux (tail1, tail2) of
                      | Some tail_diffs -> 
                        (case (t1, t2) of
                           | (Some t1, Some t2) -> Some ((diffType equivs (t1, t2)) ++ tail_diffs)
                           | (None,    None)    -> Some tail_diffs
                           | _ -> None)
                      | _ -> None
                  else
                    None
          in
            case aux (fields1, fields2) of
              | Some diffs -> diffs
              | _ ->
                [Types (t1, relabel_vars_in_type equivs t2)])

       | (Quotient (type1, rel1, _), Quotient (type2, rel2, _)) -> 
         (diffType equivs (type1, type2)) ++
         (diffTerm equivs (rel1,  rel2))

       | (Subtype  (type1, pred1, _), Subtype (type2, pred2, _)) ->
         (diffType equivs (type1, type2)) ++
         (diffTerm equivs (pred1, pred2))

       | (Base (qid1, args1, _), Base (qid2, args2, _)) | qid1 = qid2 && length args1 = length args2 ->
         let
           def aux (args1, args2) =
             case (args1, args2) of
               | ([],[]) -> []
               | (t1 :: tail1, t2 :: tail2) ->
                 (diffType equivs (t1, t2)) ++ aux (tail1, tail2)
         in
           aux (args1, args2) 
           
       | (TyVar (tv1, _), TyVar (tv2, _)) | matchingTyVars? equivs (tv1, tv2) ->
         %% if match fails, we'll end up with vars in the diff list and later processing will complain
         []
         
       | (MetaTyVar (mtv1, _), MetaTyVar (mtv2, _)) -> 
         (if (!mtv1).uniqueId = (!mtv2).uniqueId then
            []
          else
            case ((!mtv1).link, (!mtv2).link) of
              | (Some t1, Some t2) -> diffType equivs (t1, t2)
              | (Some t1, _)       -> diffType equivs (t1, t2)
              | (_,       Some t2) -> diffType equivs (t1, t2)
              | _ ->
                [MetaTyVars (mtv1, mtv2)])

       | (MetaTyVar (mtv1, _), _) ->
         (case (!mtv1).link of
            | Some t1 -> diffType equivs (t1, t2)
            | _ -> [Types (t1, relabel_vars_in_type equivs t2)])

       | (_, MetaTyVar (mtv2, _)) ->
         (case (!mtv2).link of
            | Some t2 -> diffType equivs (t1, t2)
            | _ -> [Types (t1, relabel_vars_in_type equivs t2)])

       | (Pi (tvs1, t1, _), Pi (tvs2, t2, _)) | length tvs1 = length tvs2 ->
         let local_equivs = equateTyVars (tvs1, tvs2) in
         let equivs = local_equivs ++ equivs in
         let diffs = diffType equivs (t1, t2) in
         if local_tyvar_mismatch? local_equivs diffs then
           [Types (t1, relabel_vars_in_type equivs t2)]
         else
           diffs

       | (And (types1, _), And (types2, _)) | length types1 = length types2 ->
         (let 
            def aux (types1, types2) =
              case (types1, types2) of
                | ([],[]) -> []
                | (t1 :: tail1, t2 :: tail2) ->
                  (diffType equivs (t1, t2)) ++
                  aux (tail1, tail2)
          in
            aux (types2, types2))


       | _ -> 
         [Types (t1, relabel_vars_in_type equivs t2)]
         
 op  backtranslate_tsp : Equivs -> TSP_Maps Position
 def backtranslate_tsp equivs = 
   let
     def back_translate_vars trm =
       case trm of
         | Var (v, pos) ->
           (case (findLeftmost (fn equiv -> 
                                  case equiv of
                                    | TermVars (_,y) -> y.1 = v.1
                                    | _ -> false)
                    equivs)
              of
              | Some (TermVars (x,_)) -> Var(x,noPos)
              | _ -> trm)
         | _ -> trm

     def back_translate_tyvars typ =
       case typ of
         | TyVar (tv, pos) ->
           (case (findLeftmost (fn equiv -> 
                                  case equiv of
                                    | TypeVars (_,y) -> y = tv
                                    | _ -> false)
                    equivs)
              of
              | Some (TypeVars (x,_)) -> TyVar(x,noPos)
              | _ -> typ)
         | _ -> typ
   in
     (back_translate_vars,
      back_translate_tyvars,
      fn pat -> pat)

 def relabel_vars_in_term equivs term =
   mapTerm (backtranslate_tsp equivs) term

 def relabel_vars_in_type equivs typ =
   mapType (backtranslate_tsp equivs) typ

 def local_tyvar_mismatch? equivs diffs =
   %%
   %% See note above for local_var_mismatch?
   %% The analogous situation holds for type vars.
   %%
   exists? (fn pair -> 
             case pair of
               | TypeVars (tv1,tv2) ->
                 (exists? (fn diff -> 
                            case diff of 
                              | Types (TyVar (x,_), _) | x = tv1 -> true
                              | Types (_, TyVar (y,_)) | y = tv2 -> true
                              | _ -> false)
                          diffs)
               | _ -> false)
          equivs

 %%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%
 %%%      Pattern Equivalences, expanding definitions
 %%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%

 def no_new_equivs = Some ([], [])

 def diffPattern outer_equivs (p1,p2) =
   %% returns just the new equivs, not including outer_equivs
   case (p1, p2) of
     | (AliasPat (x1, y1, _), AliasPat (x2, y2, _)) -> 
       (case (diffPattern outer_equivs (x1,x2), diffPattern outer_equivs (y1,y2)) of
          | (Some (e1,d1), Some (e2,d2)) -> 
            Some (e1 ++ e2, d1 ++ d2)
          | _ -> None)
       
     | (VarPat (v1, _), VarPat (v2,_)) -> 
       Some ([TermVars (v1,v2)], [])

     | (EmbedPat (i1, op1, t1, _), EmbedPat (i2, op2, t2, _)) -> 
       if i1 = i2 then
         let tdiffs = diffType outer_equivs (t1, t2) in
           case (op1, op2) of
             | (Some p1, Some p2) ->
               (case diffPattern outer_equivs (p1, p2) of
                  | Some (equivs, pdiffs) ->
                    Some (equivs, pdiffs ++ tdiffs)
                  | _ -> None)
             | (None, None) ->
               Some ([], tdiffs)
             | _ -> None
         else
           None

       | (RecordPat (xs1, _), RecordPat (xs2, _)) -> 
         let 
           def aux (xs1, xs2) =
             case (xs1, xs2) of
               | ([],[]) ->  no_new_equivs
               | ((label1, x1) :: tail1, (label2, x2) :: tail2) | label1 = label2 ->
                 (case aux (tail1, tail2) of
                    | Some (tail_equivs, tail_diffs) ->
                      (case diffPattern outer_equivs (x1, x2) of
                         | Some (head_equivs, head_diffs) ->
                           Some (head_equivs ++ tail_equivs,
                                 head_diffs ++ tail_diffs)
                         | _ -> None)
                    | _ -> None)
               | _ -> None
         in
           aux (xs1, xs2)
           
       | (WildPat   (s1, _), WildPat   (s2, _)) -> no_new_equivs
       | (StringPat (x1, _), StringPat (x2, _)) -> if x1 = x2 then no_new_equivs else None
       | (BoolPat   (x1, _), BoolPat   (x2, _)) -> if x1 = x2 then no_new_equivs else None
       | (CharPat   (x1, _), CharPat   (x2, _)) -> if x1 = x2 then no_new_equivs else None
       | (NatPat    (x1, _), NatPat    (x2, _)) -> if x1 = x2 then no_new_equivs else None

       | (QuotientPat (p1, qid1, _, _), QuotientPat (p2, qid2, _, _)) -> 
         (if qid1 = qid2 then % TODO: handle aliases
            diffPattern outer_equivs (p1, p2)
          else
            None)

       | (RestrictedPat (p1, t1, _), RestrictedPat (p2, t2, _)) -> 
         (case diffPattern outer_equivs (p1, p2) of
            | Some (equivs, pdiffs) -> 
              Some (equivs, pdiffs ++ diffTerm equivs (t1, t2))
            | _ -> None)

       | (TypedPat (p1, t1, _), TypedPat (p2, t2, _)) -> 
         (case diffPattern outer_equivs (p1, p2) of
            | Some (equivs, pdiffs) -> 
              Some (equivs, pdiffs ++ diffType equivs (t1, t2))
            | _ -> None)

       | _ -> None

 def diffVars outer_equivs (vs1, vs2) =
   case (vs1, vs2) of
     | ([], []) -> ([], [])
     | (v1 :: tail1, v2 :: tail2) ->
       let head_equivs = [TermVars (v1,v2)] in
       let head_diffs  = diffType outer_equivs (v1.2, v2.2) in
       let (tail_equivs, tail_diffs) = diffVars outer_equivs (tail1, tail2) in
       (head_equivs ++ tail_equivs,
        head_diffs  ++ tail_diffs)

end-spec
