SpecCalc qualifying spec 
 import ../../Environment
 import AccessSpec

 op addSort        : [a] List QualifiedId            -> ASort a -> ASpec a -> Position -> SpecCalc.Env (ASpec a)
 op addOp          : [a] List QualifiedId -> Fixity  -> ATerm a -> ASpec a -> Position -> SpecCalc.Env (ASpec a)

  %% called by evaluateSpecElem 
 def addSort new_names new_dfn old_spec pos =
  %%% some of the names may refer to previously declared sorts,
  %%% some of which may be identical
  %%% Collect the info's for such references
  let new_names = rev (removeDuplicates new_names) in % don't let duplicate names get into a sortinfo!
  let primaryName = hd new_names in
  let new_info = {names = new_names, 
		  dfn   = new_dfn}
  in
  let old_infos = foldl (fn (new_name, old_infos) ->
                         case findTheSort (old_spec, new_name) of
                           | Some info -> 
                             if exists (fn old_info -> info = old_info) old_infos then
                               old_infos
                             else
                               cons (info, old_infos)
                           | _ -> old_infos)
                        []
                        new_names
  in
  {
    mapM (fn name -> 
	  if basicQualifiedId? name then
	    raise (SpecError (pos, (printAliases new_names)^" is a basic type, hence cannot be redeclared."))
	  else
	    return ())
         new_names;
    new_sorts <-
     case old_infos of
       | [] ->
         %%  We're declaring a brand new sort.
         return (foldl (fn (name as Qualified (q, id), new_sorts) ->                         
                        insertAQualifierMap (new_sorts, q, id, new_info))
                       old_spec.sorts
                       new_names)
       | [old_info] ->
         %%  We're merging new information with a previously declared sort.
         let combined_names = listUnion (old_info.names, new_names) in
	 let combined_names = removeDuplicates combined_names in % redundant?
	 let (old_tvs, old_srt) = unpackFirstSortDef old_info in
	 let (new_tvs, new_srt) = unpackFirstSortDef new_info in
         if new_tvs = old_tvs then % TODO: for now at least, this is very literal -- should test for alpha-equivalence.
           (let old_dfn = old_info.dfn in
	    case (definedSort? old_dfn, definedSort? new_dfn) of
              | (false, false) ->
                %%  Old: Sort S    [or S(A,B), etc.]
                %%  New: Sort S    [or S(X,Y), etc.]
                raise (SpecError (pos, "Type "^(printAliases new_names)^" has been redeclared."))
              | (false,  true) ->
                %%  Old: Sort S (A,B)
                %%  New: Sort S (X,Y) = T(X,Y)
		let new_info = {names = combined_names, 
				dfn   = new_dfn}
		in
                return (foldl (fn (name as Qualified (q, id), new_sorts) ->                          
                               insertAQualifierMap (new_sorts, q, id, new_info))
                              old_spec.sorts
                              combined_names)
              | (true, false) ->
                %%  Old: Sort S (X,Y) = T(X,Y)
                %%  New: Sort S (A,B)
                raise (SpecError (pos, 
                                  "Type "^(printAliases new_names)^" has been redeclared"
                                  ^ "\n from "^ (printSort old_dfn)))
	      | _ ->
                %%  Old: Sort S (X,Y) = T(X,Y)
                %%  New: Sort S (A,B) = W(A,B)
                raise (SpecError (pos, 
                                  "Type "^(printAliases new_names)^" has been redefined"
                                  ^ "\n from "^ (printSort old_dfn)
                                  ^ "\n   to "^ (printSort new_dfn))))
         else
           %%  Old: Sort S (a)
           %%  New: Sort S (x,y)
           raise (SpecError (pos, 
                           "Type "^(printAliases new_names)^" has been redeclared or redefined"
                           ^"\n with new type variables "^(printTyVars new_tvs)
                           ^"\n    differing from prior "^(printTyVars old_tvs)))
       | _ ->
         %%  We're trying to merge information with two or more previously declared sorts.
         raise (SpecError (pos, 
                         "Sort "^(printAliases new_names)^" refers to multiple prior sorts"));
     sp <- return (setSorts (old_spec, new_sorts));
     return (appendElement (sp, if definedSort? new_dfn
			          then SortDef primaryName
				  else Sort primaryName))
    }

  %% called by evaluateSpecElem and LiftPattern
 def addOp new_names new_fixity new_dfn old_spec pos =
   addOrRefineOp new_names new_fixity new_dfn old_spec pos true

 def addOrRefineOp new_names new_fixity new_dfn old_spec pos addOnly? =
  %%% some of the names may refer to previously declared sorts,
  %%% some of which may be identical
  %%% Collect the info's for such references
  let new_names = rev (removeDuplicates new_names) in % don't let duplicate names get into an opinfo!
  let primaryName = hd new_names in
  let new_info = {names  = new_names, 
		  fixity = new_fixity, 
		  dfn    = new_dfn,
		  fullyQualified? = false}
  in
  let old_infos = foldl (fn (new_name, old_infos) ->
                         case findTheOp (old_spec, new_name) of
                           | Some info -> 
                             if exists (fn old_info -> info = old_info) old_infos then
                               old_infos
                             else
                               cons (info, old_infos)
                           | _ -> old_infos)
                        []
                        new_names
  in {
    mapM (fn name -> 
	  if basicQualifiedId? name then
	    raise (SpecError (pos, (printAliases new_names)^" is a basic op, hence cannot be redeclared."))
	  else
	    return ())
         new_names;
   new_ops <-
   case old_infos of
     | [] ->
       %%  We're declaring a brand new op
       return (foldl (fn (name as Qualified (q, id), new_ops) ->
                      insertAQualifierMap (new_ops, q, id, new_info))
                     old_spec.ops
                     new_names)

     | [old_info] ->
       %%  We're merging new information with a previously declared op.
       (let old_dfn = old_info.dfn in
	let combined_names = listUnion (old_info.names, new_names) in
	let combined_names = removeDuplicates combined_names in % redundant?
	let (old_tvs, old_srt, old_tm) = unpackFirstOpDef old_info in
	let (new_tvs, new_srt, new_tm) = unpackFirstOpDef new_info in
	let old_defined? = definedTerm? old_dfn in
	let new_defined? = definedTerm? new_dfn in
        case (old_defined?, new_defined?) of
          | (false, false) ->
            %%  Old: op foo : ...
            %%  New: op foo : ...
            raise (SpecError (pos, 
                              "Operator "^(printAliases new_names)^" has been redeclared"
                              ^ "\n from " ^ (printSort (maybePiSort (old_tvs, old_srt)))
                              ^ "\n   to " ^ (printSort (maybePiSort (new_tvs, new_srt)))))
          | (true, false) ->
	    %%  Old:  def foo ... = ...
	    %%  New:  op foo : ...
	    raise (SpecError (pos, 
			      "Operator "^(printAliases new_names)^" has been redeclared"
                              ^ "\n from " ^ (printTerm old_dfn)
                              ^ "\n   to " ^ (printTerm new_dfn)))
	  | _ ->
            %%  New: def foo 
	    (if ~addOnly?             %%  Old: op foo : ... or      (add definition)
	                              %%  Old: def foo : ... = ...  (replace definition)
	       or ~old_defined? then  %%  Old: op foo : ...
	       let happy? = (case new_tvs of
			       | [] ->
			       %%  Old:  op foo : ...
			       %%  New:  def foo x = ...
			       true
			       | _ -> 
			       %%  Old:  op foo : ...
			       %%  New:  def [a,b,c] foo ... = ...
			       new_tvs = old_tvs)
	       in
	       (if happy? then
		  let combined_srt = (case (old_srt, new_srt) of
					 | (Any _,       _) -> new_srt
					 | (_,       Any _) -> old_srt
					 | (MetaTyVar _, _) -> new_srt
					 | (_, MetaTyVar _) -> old_srt
					 | _ -> old_srt)   % TODO:  maybeAndSort ([old_srt, new_srt], sortAnn new_srt)
		  in
		  let combined_dfn = maybePiTerm (old_tvs, SortedTerm (new_tm, combined_srt, termAnn new_tm)) in
		  let combined_info = old_info << {names = combined_names, 
						    dfn   = combined_dfn,
						    fullyQualified? = false} 
		  in
		  return (foldl (fn (name as Qualified (q, id), new_ops) ->
				 insertAQualifierMap (new_ops, q, id, combined_info))
			  old_spec.ops
			  combined_names)
		else
		  raise (SpecError (pos, 
				    "Operator "^(printAliases new_names)^" has been redefined"
				    ^"\n with new type variables "^(printTyVars new_tvs)
				    ^"\n    differing from prior "^(printTyVars old_tvs))))
	     else
	       %%  def foo ...
	       raise (SpecError (pos, 
				 "Operator "^(printAliases new_names)^" has been redefined"
				 ^ "\n from " ^ (printTerm old_dfn)
				 ^ "\n   to " ^ (printTerm new_dfn)))))
     | _ ->
       %%  We're trying to merge information with two or more previously declared sorts.
       raise (SpecError (pos, 
                         "Op "^(printAliases new_names)^" refers to multiple prior ops"));

    sp <- return (setOps (old_spec, new_ops));
    return (appendElement (sp, if definedTerm? new_dfn
			         then OpDef primaryName
				 else Op primaryName))
   }

 %%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%

 op addImport      : [a] (SpecCalc.Term Position * Spec)        * ASpec a -> ASpec a
 op addProperty    : [a] (AProperty a)                          * ASpec a -> ASpec a
 op addAxiom       : [a] (PropertyName * TyVars * ATerm a)      * ASpec a -> ASpec a
 op addConjecture  : [a] (PropertyName * TyVars * ATerm a)      * ASpec a -> ASpec a
 op addTheorem     : [a] (PropertyName * TyVars * ATerm a)      * ASpec a -> ASpec a
 op addTheoremLast : [a] (PropertyName * TyVars * ATerm a)      * ASpec a -> ASpec a
 op addConjectures : [a] List (PropertyName * TyVars * ATerm a) * ASpec a -> ASpec a
 op addTheorems    : [a] List (PropertyName * TyVars * ATerm a) * ASpec a -> ASpec a
 op addComment     : [a] String                                 * ASpec a -> ASpec a
 op addPragma      : [a] (String * String * String)             * ASpec a -> ASpec a

 %% called by evaluateSpecImport
 def addImport ((specCalcTerm, imported_spec), spc) =
   appendElement (spc, Import (specCalcTerm, imported_spec, imported_spec.elements))

 %% called by evaluateSpecElem 

 def addProperty (new_property, spc) =
   let spc = setElements (spc, spc.elements ++ [Property new_property]) in
   spc    % addLocalPropertyName(spc,propertyName new_property)

 def addAxiom       ((name, tvs, formula), spc) = addProperty ((Axiom      : PropertyType, name, tvs, formula), spc) 
 def addConjecture  ((name, tvs, formula), spc) = addProperty ((Conjecture : PropertyType, name, tvs, formula), spc) 
 def addTheorem     ((name, tvs, formula), spc) = addProperty ((Theorem    : PropertyType, name, tvs, formula), spc) 

 def addTheoremLast ((name, tvs, formula), spc) =  
   setElements (spc, spc.elements ++ [Property(Theorem, name, tvs, formula)])

 def addConjectures (conjectures, spc) = foldl addConjecture spc conjectures
 def addTheorems    (theorems,    spc) = foldl addTheorem    spc theorems

 def addComment     (str, spc) = 
   let spc = setElements (spc, spc.elements ++ [Comment str]) in
   spc    % addLocalPropertyName(spc,propertyName new_property)

 def addPragma      ((prefix, body, postfix), spc) = 
   let spc = setElements (spc, spc.elements ++ [Pragma (prefix, body, postfix)]) in
   spc    % addLocalPropertyName(spc,propertyName new_property)

 %%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%

% op addLocalSortName     : [a] ASpec a * QualifiedId -> ASpec a
% op addLocalOpName       : [a] ASpec a * QualifiedId -> ASpec a
% op addLocalPropertyName : [a] ASpec a * QualifiedId -> ASpec a
 op addToNames           : QualifiedId * QualifiedIds -> QualifiedIds

% def addLocalSortName (spc, new_local_sort) =
%   let localSorts = spc.importInfo.localSorts in
%   if memberNames (new_local_sort, localSorts) then
%     spc
%   else 
%     setLocalSorts (spc, addToNames (new_local_sort, localSorts))

% def addLocalOpName (spc, new_local_op) =
%   let localOps = spc.importInfo.localOps in
%   if memberNames (new_local_op, localOps) then
%     spc
%   else 
%     setLocalOps (spc, addToNames (new_local_op, localOps))

(* Obsolete ?
 def addLocalPropertyName (spc, new_local_op) =
   let localProperties = spc.importInfo.localProperties in
   if memberNames (new_local_op, localProperties) then
     spc
   else 
     setLocalProperties (spc, addToNames (new_local_op, localProperties))
*)
 def addToNames (qid, qids) = cons (qid, qids)

endspec
