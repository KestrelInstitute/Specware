(* Copyright 2015 Kestrel Institute. See file LICENSE for license details *)

SpecCalc qualifying spec
 import /Languages/MetaSlang/Specs/AnnSpec
 import /Languages/MetaSlang/Specs/MSTerm            % Term, Type, Pattern
 import /Languages/MetaSlang/Specs/StandardSpec      % Spec
 import /Library/Legacy/DataStructures/ListUtilities % listUnion
 import /Languages/MetaSlang/Specs/Utilities         % patVars

 op  removeVarOpCaptures : Spec    -> Spec 

 op  deconflictTerm      : MSTerm    -> MSTerm    
 op  deconflictTermRec   : MSTerm    -> MSTerm    * Bool * VarNames

 op  deconflictType      : MSType    -> MSType    
 op  deconflictTypeRec   : MSType    -> MSType    * Bool * VarNames

 op  deconflictPattern   : MSPattern -> MSPattern 
 op  deconflictPatRec    : MSPattern -> MSPattern * Bool * VarNames

 type VarNames = List Id

 %%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%

 %% This version is essentially a no-op, 
 %% to allow testing in preparation for the real code

 def removeVarOpCaptures spc =
   let new_types = mapTypeInfos (fn info -> info << {dfn = deconflictType info.dfn}) spc.types in
   let new_ops   = mapOpInfos   (fn info -> info << {dfn = deconflictTerm info.dfn}) spc.ops   in
   let new_elts  = map (fn el ->
			case el of
			  | Property(ptype, name, tvs, fm, a) -> Property(ptype, name, tvs, deconflictTerm fm, a)
			  | _ -> el)
                     spc.elements
   in
   spc << {types    = new_types,
	   ops      = new_ops,
	   elements = new_elts}

 %%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%

 def deconflictTerm term =
   let (new_term, _, _) = deconflictTermRec term in
   new_term

 def deconflictType srt =
   let (new_srt, _, _) = deconflictTypeRec srt in
   new_srt

 def deconflictPattern pat =
   let (new_pat, _, _) = deconflictPatRec pat in
   new_pat

 %%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%

 def deconflictTermRec term =
   %%
   %% two values are constructed in parallel, using post-order construction:
   %%
   %%   a rebuilt (or reused) term
   %%   all the op names seen within that term
   %%
   %%   If a term binds a var that has the same name as one of the ops,
   %%   that term will be rebuilt to use a new var name.
   %%   otherwise the original term will be returned intact.
   case term of

     | Apply (t1, t2, a) ->
       let (new_t1, changed1?, op_names_1) = deconflictTermRec t1 in
       let (new_t2, changed2?, op_names_2) = deconflictTermRec t2 in
       let changed? = changed1? || changed2? in
       (if changed? then
	  Apply (new_t1, new_t2, a)
	else
	  term,
	changed?,
	listUnion (op_names_1, op_names_2))

     | ApplyN (tms, a) ->
       let (new_tms, tms_changed?, all_op_names) = 
           foldl (fn ((new_tms, tms_changed?, all_op_names), tm) ->
		  let (new_tm, tm_changed?, op_names) = deconflictTermRec tm in
		  (new_tms ++ [new_tm], 
		   tms_changed? || tm_changed?,
		   listUnion (op_names, all_op_names)))
	         ([],false,[])
		 tms
       in
	 (if tms_changed? then
	    ApplyN (new_tms, a)
	  else
	    term,
	  tms_changed?,
	  all_op_names)

     | Record (row, a) ->
       let (new_row, row_changed?, all_op_names) = 
           foldl (fn ((new_row, row_changed?, all_op_names), (id, tm)) -> 
		  let (new_tm, tm_changed?, op_names) = deconflictTermRec tm in
		  (new_row ++ [(id, new_tm)], 
		   row_changed? || tm_changed?,
		   listUnion (op_names, all_op_names)))
	         ([],false,[])
		 row 
       in
	 (if row_changed? then
	    Record (new_row, a)
	  else
	    term,
	  row_changed?,
	  all_op_names)

     | Bind (bnd, vars, tm, a) ->
       let (new_tm, tm_changed?, tm_op_names) = deconflictTermRec tm in
       let (new_vars, vars_changed?, vars_op_names, captures) = 
           foldl (fn ((new_vars, vars_changed?, all_op_names, captures), (id, srt)) -> 
		  let (new_srt, srt_changed?, op_names) = deconflictTypeRec srt in
		  let new_captures = (if id in? tm_op_names then
					captures ++ [id]
				      else
					captures) 
		  in
		  (new_vars ++ [(id, new_srt)], 
		   vars_changed? || srt_changed?,
		   listUnion (op_names, all_op_names),
		   new_captures))
	         ([],false,[],[])
		 vars 
       in
       let changed? = vars_changed? || tm_changed? in
       let new_term = 
           if changed? then
	     Bind (bnd, new_vars, new_tm, a)
	   else
	     term
       in
       let new_term = 
           case captures of
	     | [] -> new_term
	     | _ ->  substitute2(new_term,[],StringSet.addList (empty, tm_op_names))
       in
	 (new_term,
	  changed? || (captures ~= []),
	  listUnion (vars_op_names, tm_op_names))

     | Let (decls, body, a) ->
       let (new_body, changed?, body_op_names) = deconflictTermRec body in
       let (new_decls, changed?, decls_op_names, captures) = 
           foldl (fn ((new_decls, changed?, decls_op_names, captures), decl as (pat, tm)) ->
		  let pvars = patVars pat in
		  let (new_pat, pat_changed?, pat_op_names) = deconflictPatRec  pat in
		  let (new_tm,  tm_changed?,  tm_op_names)  = deconflictTermRec tm  in
		  let new_captures = (foldl (fn (captures, (id,_)) ->
					     if id in? body_op_names then
					       captures ++ [id]
					     else
					       captures)
				            captures
					    pvars)
		  in
		  (new_decls ++ [(new_pat, new_tm)],
		   changed? || pat_changed? || tm_changed?,
		   listUnion (pat_op_names, listUnion (tm_op_names, decls_op_names)),
		   new_captures))
	         ([], changed?,[],[])
		 decls
       in
       let new_term =
           if changed? then
	     Let (new_decls, new_body, a)
	   else
	     term
       in
       let new_term =
           case captures of
	     | [] -> new_term
	     | _ ->  substitute2 (new_term, [], StringSet.addList (empty, body_op_names))
       in
	 (new_term,
	  changed? || (captures ~= []),
	  listUnion (decls_op_names, body_op_names))

     | LetRec (decls, body, a) ->
       let (new_body, body_changed?, body_op_names) = deconflictTermRec body in
       let (new_decls, decls_changed?, decls_op_names, captures) =
           foldl (fn ((new_decls, decls_changed?, decls_op_names, captures), ((id, srt), tm)) ->
		  let new_captures = (if id in? body_op_names then
					captures ++ [id]
				      else
					captures)
		  in
		  let (new_srt, srt_changed?, srt_op_names) = deconflictTypeRec srt in
		  let (new_tm,  tm_changed?,  tm_op_names)  = deconflictTermRec tm  in
		  (new_decls ++ [((id, new_srt), new_tm)],
		   decls_changed? || srt_changed? || tm_changed?,
		   listUnion (srt_op_names, listUnion (tm_op_names, decls_op_names)),
		   new_captures))
	         ([],false,[],[])
		 decls
       in
       let changed? = decls_changed? || body_changed? in
       let new_term =
           if changed? then
	     LetRec (new_decls, new_body, a)
	   else
	     term
       in
       let new_term =
           case captures of
	     | [] -> new_term
	     | _  -> substitute2(new_term,[],StringSet.addList (empty, body_op_names))
       in
	 (new_term,
	  changed? || (captures ~= []),
	  listUnion (decls_op_names, body_op_names))

     | Var ((id, srt), a) ->
       let (new_srt, srt_changed?, srt_op_names) = deconflictTypeRec srt in
       (if srt_changed? then
	  Var ((id, new_srt), a)
	else
	  term,
	srt_changed?,
	srt_op_names)

     | Fun (f, srt, a) ->
       let (new_srt, srt_changed?, srt_op_names) = deconflictTypeRec srt in
       let op_names = (case f of
			 | Op (Qualified(_,id),_) -> srt_op_names ++ [id]
			 | _ -> srt_op_names)
       in
       (if srt_changed? then
	  Fun (f, new_srt, a)
	else
	  term,
	srt_changed?,
	op_names)

     | Lambda (matches, a) ->
       let (new_matches, matches_changed?, matches_op_names, matches_captures) = 
           foldl (fn ((new_matches, matches_changed?, matches_op_names, matches_captures), (pat, cond, body)) ->
		  let pvars = patVars pat in
		  let (new_pat,  pat_changed?,  pat_op_names)  = deconflictPatRec  pat  in
		  let (new_cond, cond_changed?, cond_op_names) = deconflictTermRec cond in
		  let (new_body, body_changed?, body_op_names) = deconflictTermRec body in
		  let captures = foldl (fn (captures, (id,_)) ->
					if id in? body_op_names then
					  captures ++ [id]
					else
					  captures)
		                        matches_captures
					pvars
		  in
		  let match_changed? = pat_changed? || cond_changed? || body_changed? in
		  let new_match = (new_pat, new_cond, new_body) in
		  (new_matches ++ [new_match],
		   matches_changed? || match_changed? || (captures ~= []),
		   listUnion (pat_op_names,
			      listUnion (cond_op_names,
					 listUnion (body_op_names,
						    matches_op_names))),
		   captures))
	         ([],false,[], [])
		 matches
       in		 
       let new_term = 
           if matches_changed? then
	     Lambda (new_matches, a)
	   else
	     term
       in
       let new_term =
           case matches_captures of
	     | [] -> new_term
	     | _ -> 
	       substitute2 (new_term, [], StringSet.addList (empty, matches_op_names))
       in
	 (new_term,
	  matches_changed? || (matches_captures ~= []),
	  matches_op_names)

     | The (var as (id, srt), tm, a) ->
       let (new_tm, tm_changed?, tm_op_names) = deconflictTermRec tm in
       let (new_srt, srt_changed?, op_names) = deconflictTypeRec srt in
       let capture? = id in? tm_op_names in
       let changed? = srt_changed? || tm_changed? in
       let new_term = 
           if changed? then
	     The ((id, new_srt), new_tm, a)
	   else
	     term
       in
       let new_term = 
           if capture? then
	     substitute2(new_term,[],StringSet.addList (empty, tm_op_names))
	   else
	     new_term
       in
	 (new_term,
	  changed? || capture?,
	  listUnion (op_names, tm_op_names))

     | IfThenElse (t1, t2, t3, a) ->
       let (new_t1, t1_changed?, t1_op_names) = deconflictTermRec t1 in
       let (new_t2, t2_changed?, t2_op_names) = deconflictTermRec t2 in
       let (new_t3, t3_changed?, t3_op_names) = deconflictTermRec t3 in
       let changed? = t1_changed? || t2_changed? || t3_changed? in
       (if changed? then
	  IfThenElse (new_t1, new_t2, new_t3, a)
	else
	  term,
        changed?,
	listUnion (t1_op_names, listUnion (t2_op_names, t3_op_names)))

     | Seq (tms, a) ->
       let (new_tms, tms_changed?, tms_op_names) = 
           foldl (fn ((new_tms, tms_changed?, tms_op_names), tm) ->
		  let (new_tm, tm_changed?, tm_op_names) = deconflictTermRec tm in
		  (new_tms ++ [new_tm],
		   tms_changed? || tm_changed?,
		   listUnion (tm_op_names, tms_op_names)))
	         ([],false,[])
		 tms
       in
	 (if tms_changed? then
	    Seq (new_tms, a)
	  else
	    term,
	  tms_changed?,
	  tms_op_names)

     | TypedTerm (tm, srt, a) ->
       let (new_tm,  tm_changed?,  tm_op_names)  = deconflictTermRec tm  in
       let (new_srt, srt_changed?, srt_op_names) = deconflictTypeRec srt in
       let changed? = tm_changed? || srt_changed? in
       (if changed? then
	  TypedTerm (new_tm, new_srt, a)
	else
	  term,
	changed?,
	listUnion(srt_op_names, tm_op_names))

     | Pi  (tvs, tm, a) -> 
       let (new_tm,  tm_changed?,  tm_op_names)  = deconflictTermRec tm  in
       (if tm_changed? then
	  Pi (tvs, new_tm, a) 
	else
	  term,
        tm_changed?,
	tm_op_names)

     | And (tms, a)    -> 
       let (new_tms, tms_changed?, tms_op_names) =
           foldl (fn ((new_tms, tms_changed?, tms_op_names), tm) ->
		  let (new_tm, tm_changed?, tm_op_names) = deconflictTermRec tm in
		  (new_tms ++ [new_tm],
		   tms_changed? || tm_changed?,
		   listUnion (tm_op_names, tms_op_names)))
	         ([],false,[])
		 tms
       in
       (if tms_changed? then
	  And (new_tms, a)
	else
	  term,
        tms_changed?,
	tms_op_names)

     | Any _  -> (term, false, [])


 %%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%

 def deconflictTypeRec srt =

   case srt of

     | Arrow (s1, s2, a) ->
       let (new_s1, s1_changed?, s1_op_names) = deconflictTypeRec s1 in
       let (new_s2, s2_changed?, s2_op_names) = deconflictTypeRec s2 in
       let changed? = s1_changed? || s2_changed? in
       (if changed? then
	  Arrow (new_s1, new_s2, a)
	else
	  srt,
        changed?,
	listUnion (s1_op_names, s2_op_names))
	   
     | Product (row, a) ->
       let (new_row, row_changed?, row_op_names) = 
           foldl (fn ((new_row, row_changed?, row_op_names), (id, srt)) ->
		  let (new_srt, srt_changed?, srt_op_names) = deconflictTypeRec srt in
		  (new_row ++ [(id, new_srt)],
		   row_changed? || srt_changed?,
		   listUnion (srt_op_names, row_op_names)))
	         ([],false,[])
		 row
       in
	 (if row_changed? then
	    Product (new_row, a)
	  else
	    srt,
	  row_changed?,
	  row_op_names)
	     
     | CoProduct (row, a) ->
       let (new_row, row_changed?, row_op_names) = 
           foldl (fn ((new_row, row_changed?, row_op_names), (id, opt_srt)) ->
		  let (new_srt, srt_changed?, srt_op_names) = 
		      case opt_srt of
			| None -> (None, false, [])
			| Some srt -> 
			  let (srt, changed?, op_names) = deconflictTypeRec srt in
			  (Some srt, changed?, op_names)
		  in
		    (new_row ++ [(id, new_srt)],
		     row_changed? || srt_changed?,
		     listUnion (srt_op_names, row_op_names)))
	         ([],false,[])
		 row
       in
	 (if row_changed? then
	    CoProduct (new_row, a)
	  else
	    srt,
	  row_changed?,
	  row_op_names)

	       
     | Quotient (base_type, tm, a) ->
       let (new_base, base_changed?, base_op_names) = deconflictTypeRec base_type in
       let (new_tm,   tm_changed?,   tm_op_names)    = deconflictTermRec tm in
       let changed? = base_changed? || tm_changed? in
       (if changed? then
	  Quotient (new_base, new_tm, a)
	else
	  srt,
        changed?,
	listUnion (base_op_names, tm_op_names))

     | Subtype (super_type, tm, a) ->
       let (new_super, super_changed?, super_op_names) = deconflictTypeRec super_type in
       let (new_tm,    tm_changed?,    tm_op_names)    = deconflictTermRec tm in
       let changed? = super_changed? || tm_changed? in
       (if changed? then
	  Subtype (new_super, new_tm, a)
	else
	  srt,
        changed?,
	listUnion (super_op_names, tm_op_names))

     | Base (qid as Qualified(_,id), srts, a) ->
       let (new_srts, srts_changed?, srts_op_names) = 
           foldl (fn ((new_srts, srts_changed?, srts_op_names), srt) ->
		  let (new_srt, srt_changed?, srt_op_names) = deconflictTypeRec srt in
		  (new_srts ++ [srt],
		   srts_changed? || srt_changed?,
		   listUnion (srts_op_names, srt_op_names)))
	         ([],false,[])
		 srts
       in
	 (if srts_changed? then
	    Base (qid, new_srts, a)
	  else
	    srt,
	  srts_changed?,
	  srts_op_names)
		     
     | Boolean _ -> (srt, false, [])
		     
   % | TyVar ??
		     
     | MetaTyVar (mtv, a) ->
       (let {name,uniqueId,link} = ! mtv in
	case link of
	  | None -> (srt, false, [])
	  | Some xsrt ->
	    let (new_srt, srt_changed?, srt_op_names) = deconflictTypeRec xsrt in
	    (if srt_changed? then
	       MetaTyVar(Ref {name     = name,
			      uniqueId = uniqueId,
			      link     = Some new_srt},
			 a)
	     else
	       srt,
	     srt_changed?,
	     srt_op_names))

     | Pi (tvs, body, a) -> 
       let (new_body, body_changed?, body_op_names) = deconflictTypeRec body in
       (if body_changed? then
	  Pi (tvs, new_body, a)
	else
	  srt,
        body_changed?,
        body_op_names)
	  
     | And (srts, a) -> 
       let (new_srts, srts_changed?, srts_op_names) = 
           foldl (fn ((new_srts, srts_changed?, srts_op_names), srt) ->
		  let (new_srt, srt_changed?, srt_op_names) = deconflictTypeRec srt in
		  (new_srts ++ [srt],
		   srts_changed? || srt_changed?,
		   listUnion (srts_op_names, srt_op_names)))
	         ([],false,[])
		 srts
       in
	 (if srts_changed? then
	    And (new_srts, a)
	  else
	    srt,
	  srts_changed?,
	  srts_op_names)
		     
     | Any  _  -> (srt, false, [])

     | _ -> (srt, false, [])

 %%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%

 def deconflictPatRec pattern =
   case pattern of

     | AliasPat (p1, p2, a) ->
       let (new_p1, p1_changed?, p1_op_names) = deconflictPatRec p1 in
       let (new_p2, p2_changed?, p2_op_names) = deconflictPatRec p2 in
       let changed? = p1_changed? || p2_changed? in
       (if changed? then
	  AliasPat (new_p1, new_p2, a)
	else
	  pattern,
	changed?,
        listUnion (p1_op_names, p2_op_names))
	   
     | VarPat ((v, srt), a) ->
       let (new_srt, srt_changed?, srt_op_names) = deconflictTypeRec srt in
       let clashes = [] in
       (if srt_changed? then
	  VarPat ((v, new_srt), a)
	else
	  pattern,
	srt_changed?,
	srt_op_names)
	     
     | EmbedPat (id, Some pat, srt, a) ->
       let (new_pat, pat_changed?, pat_op_names) = deconflictPatRec pat in
       let (new_srt, srt_changed?, srt_op_names) = deconflictTypeRec srt in
       let changed? = pat_changed? || srt_changed? in
       (if changed? then
	  EmbedPat (id, Some new_pat, new_srt, a)
	else
	  pattern,
	changed?,
	listUnion (pat_op_names, srt_op_names))
	       
     | EmbedPat (id, None, srt, a) ->
       let (new_srt, srt_changed?, srt_op_names) = deconflictTypeRec srt in
       (if srt_changed? then
	  EmbedPat (id, None, new_srt, a)
	else
	  pattern,
	srt_changed?,
	srt_op_names)

     | RecordPat (fields, a) ->
       let (new_fields, fields_changed?, fields_op_names) =
           foldl (fn ((new_fields, fields_changed?, fields_op_names), (id, pat)) ->
		  let (new_pat, pat_changed?, pat_op_names) = deconflictPatRec pat in
		  (new_fields ++ [(id, new_pat)],
		   fields_changed? || pat_changed?,
		   listUnion (pat_op_names, fields_op_names)))
	         ([],false,[])
		 fields
       in
	 (if fields_changed? then
	    RecordPat (new_fields, a)
	  else
	    pattern,
	  fields_changed?,
	  fields_op_names)
		   
     | WildPat (srt, a) ->
       let (new_srt, srt_changed?, srt_op_names) = deconflictTypeRec srt in
       (if srt_changed? then
	  WildPat (new_srt, a)
	else
	  pattern,
	srt_changed?,
	srt_op_names)

     | QuotientPat (pat, qid, tys, a) ->
       let (new_pat, pat_changed?, pat_op_names) = deconflictPatRec pat in
       (if pat_changed? then
	  QuotientPat (new_pat, qid, tys, a)
	else
	  pattern,
	pat_changed?,
	pat_op_names)

     | RestrictedPat (pat, tm, a) ->
       let (new_pat, pat_changed?, pat_op_names) = deconflictPatRec pat in
       let (new_tm,  tm_changed?,  tm_op_names)  = deconflictTermRec tm  in
       let changed? = pat_changed? || tm_changed? in
       (if changed? then
	  RestrictedPat (new_pat, new_tm, a)
	else
	  pattern,
	changed?,
	listUnion (pat_op_names, tm_op_names))

     | TypedPat (pat, srt, a) ->
       let (new_pat, pat_changed?, pat_op_names) = deconflictPatRec  pat in
       let (new_srt, srt_changed?, srt_op_names) = deconflictTypeRec srt in
       let changed? = pat_changed? || srt_changed? in
       (if changed? then
	  TypedPat (new_pat, new_srt, a)
	else
	  pattern,
	changed?,
	listUnion (pat_op_names, srt_op_names))

   % | BoolPat   ??
   % | NatPat    ??
   % | StringPat ??
   % | CharPat   ??
	     
     | _ -> (pattern, false, [])


endspec
