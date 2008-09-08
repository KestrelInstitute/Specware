SpecCalc qualifying spec 
 import ../../Environment
 import AccessSpec
 import /Languages/MetaSlang/Specs/Environment

 op addSort        :  List QualifiedId            -> Sort -> Spec -> Position -> SpecCalc.Env (Spec)
 op addOp          :  List QualifiedId -> Fixity  -> MS.Term -> Spec -> Position -> SpecCalc.Env (Spec)

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
	  if false then    % basicQualifiedId? name then
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
			          then SortDef (primaryName, pos)
				  else Sort (primaryName, pos)))
    }

  %% called by evaluateSpecElem and LiftPattern
 def addOp new_names new_fixity new_dfn old_spec pos =
   {(sp,_) <- addOrRefineOp new_names new_fixity new_dfn old_spec pos None true;
    return sp}

 op  addOrRefineOp: QualifiedIds -> Fixity -> MS.Term -> Spec -> Position -> Option SpecElement -> Boolean
                  -> SpecCalc.Env(Spec * SpecElement)
 def addOrRefineOp new_names new_fixity new_dfn old_spec pos opt_next_el addOnly? =
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
	  if false then    %basicQualifiedId? name then
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
    let el = case old_infos of
               | _::_ | addOnly? -> OpDef (primaryName, pos)
               | _ -> Op (primaryName, definedTerm? new_dfn, pos)
    in
    let sp = if exists (fn eli -> equalSpecElement?(el, eli)) sp.elements then sp
              else if old_infos = [] || addOnly?
                     then addElementBeforeOrAtEnd(sp, el, opt_next_el)
              else let elts = foldr (fn (eli, elts) ->
                                       case eli of
                                         | OpDef(qid,_) | qid = primaryName ->
                                           elts
                                         | Op(qid, _, _) | qid = primaryName ->
                                           el::elts
                                         | _ -> eli::elts)
                                 [] sp.elements
                   in
                   if member(el, elts)
                     then setElements(sp, elts)
                   else addElementBeforeOrAtEnd(sp, el, opt_next_el)
    in
    let sp = if old_infos = [] || addOnly? then sp
             else
             let dfn = (hd old_infos).dfn in
             let (tvs, ty, term) = unpackTerm dfn in
             if anyTerm? term
               then sp
             else
             let Qualified(q,nm) = primaryName in
             let initialFmla = defToTheorem(sp, ty, primaryName, term) in
             % let _ = writeLine("def_thm: "^printTerm initialFmla) in
             let liftedFmlas = [initialFmla] in % removePatternTop(sp, initialFmla) in
             let (_,thms) = foldl (fn(fmla,(i,result)) ->
                                     (i + 1,
                                      result ++ [mkConjecture(Qualified (q, nm^"__def"^(if i = 0 then ""
                                                                                          else toString i)),
                                                              tvs, fmla)]))
                              (0,[]) liftedFmlas
             in
             addElementsAfter(sp, thms, el)
    in
    return (sp, el)
    }

 %%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%

 op addImport      : [a] (SpecCalc.Term Position * Spec)    * ASpec a * a -> ASpec a
 op addProperty    : [a] (AProperty a)                          * ASpec a -> ASpec a
 op addAxiom       : [a] (PropertyName * TyVars * ATerm a * a)      * ASpec a -> ASpec a
 op addConjecture  : [a] (PropertyName * TyVars * ATerm a * a)      * ASpec a -> ASpec a
 op addTheorem     : [a] (PropertyName * TyVars * ATerm a * a)      * ASpec a -> ASpec a
 op addTheoremLast : [a] (PropertyName * TyVars * ATerm a * a)      * ASpec a -> ASpec a
 op addConjectures : [a] List (PropertyName * TyVars * ATerm a * a) * ASpec a -> ASpec a
 op addTheorems    : [a] List (PropertyName * TyVars * ATerm a * a) * ASpec a -> ASpec a
 op addComment     : [a] String * a                             * ASpec a -> ASpec a
 op addPragma      : [a] (String * String * String * a)         * ASpec a -> ASpec a

 %% called by evaluateSpecImport
 def addImport ((specCalcTerm, imported_spec), spc, a) =
   appendElement (spc, Import (specCalcTerm, imported_spec, imported_spec.elements, a))

 %% called by evaluateSpecElem 

 def addProperty (new_property, spc) =
   let spc = setElements (spc, spc.elements ++ [Property new_property]) in
   spc    % addLocalPropertyName(spc,propertyName new_property)

 def addAxiom       ((name, tvs, formula, a), spc) =
   addProperty ((Axiom      : PropertyType, name, tvs, formula, a), spc) 
 def addConjecture  ((name, tvs, formula, a), spc) =
   addProperty ((Conjecture : PropertyType, name, tvs, formula, a), spc) 
 def addTheorem     ((name, tvs, formula, a), spc) =
   addProperty ((Theorem    : PropertyType, name, tvs, formula, a), spc) 

 def addTheoremLast ((name, tvs, formula, a), spc) =  
   setElements (spc, spc.elements ++ [Property(Theorem, name, tvs, formula, a)])

 def addConjectures (conjectures, spc) = foldl addConjecture spc conjectures
 def addTheorems    (theorems,    spc) = foldl addTheorem    spc theorems

 def addComment     (str, a, spc) = 
   let spc = setElements (spc, spc.elements ++ [Comment (str,a)]) in
   spc    % addLocalPropertyName(spc,propertyName new_property)

 def addPragma      (pragma_content, spc) = 
   let spc = setElements (spc, spc.elements ++ [Pragma pragma_content]) in
   spc    % addLocalPropertyName(spc,propertyName new_property)

 def addElementsBeforeOrAtEnd(spc: Spec, new_elts: SpecElements, opt_old_elt: Option SpecElement): Spec =
   case opt_old_elt of
     | None -> setElements(spc, spc.elements ++ new_elts)
     | Some old_elt -> addElementsBefore(spc, new_elts, old_elt)

 def addElementBeforeOrAtEnd(spc: Spec, new_elt: SpecElement, opt_old_elt: Option SpecElement): Spec =
   case opt_old_elt of
     | None -> appendElement(spc, new_elt)
     | Some old_elt -> addElementBefore(spc, new_elt, old_elt)

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
