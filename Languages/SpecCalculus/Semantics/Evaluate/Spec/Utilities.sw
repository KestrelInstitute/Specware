SpecCalc qualifying spec 
 import ../../Environment
 import /Languages/MetaSlang/Specs/AnnSpec
 import SpecCalc qualifying
   (translate (translate /Library/Legacy/DataStructures/Monadic/SplayMap
     by {Monad._ +-> SpecCalc._})
     by {SpecCalc.Monad +-> SpecCalc.Env})
 import /Languages/MetaSlang/Specs/Elaborate/Utilities % for unfoldSort

  op addSort : [a] List QualifiedId -> ASort a -> ASpec a -> Position -> SpecCalc.Env (ASpec a)
 def addSort new_names new_dfn old_spec pos =
  %%% some of the names may refer to previously declared sorts,
  %%% some of which may be identical
  %%% Collect the info's for such references
  let new_names = rev (removeDuplicates new_names) in % don't let duplicate names get into a sortinfo!
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
  in {
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
                raise (SpecError (pos, "Sort "^(printAliases new_names)^" has been redeclared."))
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
                %%  TODO: Shouldn't this be an error???
                %%  Old: Sort S (X,Y) = T(X,Y)
                %%  New: Sort S (A,B)
		let new_info = old_info << {names = combined_names} in
                return (foldl (fn (name as Qualified (q, id), new_sorts) ->
                               insertAQualifierMap (new_sorts, q, id, new_info))
                              old_spec.sorts
                              combined_names)
              | _ ->
                %%  Old: Sort S (X,Y) = T(X,Y)
                %%  New: Sort S (A,B) = W(A,B)
                raise (SpecError (pos, 
                                  "Sort "^(printAliases new_names)^" has been redefined"
                                  ^ "\n from "^ (printSort old_dfn)
                                  ^ "\n   to "^ (printSort new_dfn))))
         else
           %%  Old: Sort S (a)
           %%  New: Sort S (x,y)
           raise (SpecError (pos, 
                           "Sort "^(printAliases new_names)^" has been redeclared or redefined"
                           ^"\n with new type variables "^(printTyVars new_tvs)
                           ^"\n    differing from prior "^(printTyVars old_tvs)))
       | _ ->
         %%  We're trying to merge information with two or more previously declared sorts.
         raise (SpecError (pos, 
                         "Sort "^(printAliases new_names)^" refers to multiple prior sorts"));
     sp <- return (setSorts (old_spec, new_sorts));
     foldM (fn sp -> fn name -> return (addLocalSortName (sp, name))) sp new_names
    }

 def printTyVars tvs =
   case tvs of
     | []     -> "()"
     | v1::vs -> "(" ^ v1 ^ (foldl (fn (v, str) -> str ^","^ v) "" vs) ^ ")"

  op addOp : [a] List QualifiedId -> Fixity -> ATerm a -> ASpec a -> Position -> SpecCalc.Env (ASpec a)
 def addOp new_names new_fixity new_dfn old_spec pos =
  %%% some of the names may refer to previously declared sorts,
  %%% some of which may be identical
  %%% Collect the info's for such references
  let new_names = rev (removeDuplicates new_names) in % don't let duplicate names get into an opinfo!
  let new_info = {names  = new_names, 
		  fixity = new_fixity, 
		  dfn    = new_dfn}
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
        case (definedTerm? old_dfn, definedTerm? new_dfn) of
          | (false, false) ->
            %%  Old: op foo : ...
            %%  New: op foo : ...
            raise (SpecError (pos, 
                              "Operator "^(printAliases new_names)^" has been redeclared"
                              ^ "\n from " ^ (printSort (maybePiSort (old_tvs, old_srt)))
                              ^ "\n   to " ^ (printSort (maybePiSort (new_tvs, new_srt)))))
          | (false, true) ->
            %%  Old: op foo 
            %%  New: def foo 
            let happy? = (case (new_tvs, new_srt) of
                            | ([], MetaTyVar _) -> 
                              %%  Old:  op foo : ...
                              %%  New:  def foo x = ...
                              true
                            | _ -> 
                              %%  Old:  op foo : ...
                              %%  New:  def [a,b,c] foo ... = ...
                              new_tvs = old_tvs)
            in
            if happy? then
	      let combined_dfn = maybePiTerm (old_tvs, SortedTerm (new_tm, old_srt, termAnn new_tm)) in
              let combined_info = old_info << {names = combined_names, 
					       dfn   = combined_dfn} 
	      in
              return (foldl (fn (name as Qualified (q, id), new_ops) ->
                             insertAQualifierMap (new_ops, q, id, combined_info))
                            old_spec.ops
                            combined_names)
            else
              raise (SpecError (pos, 
                                "Operator "^(printAliases new_names)^" has been redeclared or redefined"
                                ^"\n with new type variables "^(printTyVars new_tvs)
                                ^"\n    differing from prior "^(printTyVars old_tvs)))
          | (true, false) ->
	    %%  Old:  def foo ... = ...
	    %%  New:  op foo : ...
            let happy? = (case (old_tvs, old_srt) of
                            | ([], MetaTyVar _) -> 
                              %%  Old:  def foo ... = ...
                              %%  New:  op foo : ...
                              true
                            | (_, MetaTyVar _) -> 
                              %%  Old:  def [a,b,c] foo x = ...
                              %%  New:  op foo : ...
                              new_tvs = old_tvs
                            | _ -> 
                              %%  Old:  op foo : ...
                              %%  New:  op foo : ...
                              false)
            in
            if happy? then
              %%  Old:  def foo x = ...
              %%  New:  op foo : T
	      let combined_dfn = maybePiTerm (new_tvs, SortedTerm (old_tm, new_srt, termAnn old_tm)) in
	      let combined_info = old_info << {names  = combined_names, 
					       fixity = new_fixity, 
					       dfn    = combined_dfn}
	      in
              return (foldl (fn (name as Qualified (q, id), new_ops) ->
                             insertAQualifierMap (new_ops, q, id, combined_info))
                            old_spec.ops
                            combined_names)
            else
              %%  Old: op foo : 
              %%  New: op foo : 
	      %%  -or-
              %%  Old: def [a,b,c] foo ...
              %%  New: op foo : [x,y] T
              raise (SpecError (pos, 
                                "Operator "^(printAliases new_names)^" has been redeclared"
                                ^ "\n from type " ^ (printSort (maybePiSort (old_tvs, old_srt)))
                                ^ "\n   to type " ^ (printSort (maybePiSort (new_tvs, new_srt)))))
          | (true, true) ->
            %%  def foo ...
            %%  def foo ...
            raise (SpecError (pos, 
                              "Operator "^(printAliases new_names)^" has been redefined"
                              ^ "\n from " ^ (printTerm old_dfn)
                              ^ "\n   to " ^ (printTerm new_dfn))))
     | _ ->
       %%  We're trying to merge information with two or more previously declared sorts.
       raise (SpecError (pos, 
                         "Op "^(printAliases new_names)^" refers to multiple prior ops"));

    sp <- return (setOps (old_spec, new_ops));
    foldM (fn sp -> fn name -> return (addLocalOpName (sp, name))) sp new_names
   }

 % ------------------------------------------------------------------------

  op mergeSortInfo : [a] ASpec a -> ASortInfo a -> Option (ASortInfo a) -> Position -> SpecCalc.Env (ASortInfo a)
 def mergeSortInfo spc new_info opt_old_info pos =
   case opt_old_info of
     | None -> return new_info
     | Some old_info ->
       let names = listUnion (old_info.names, new_info.names) in % this order of args is more efficient
       let names = removeDuplicates names in % redundant?

       let old_tvs = firstSortDefTyVars old_info in
       let new_tvs = firstSortDefTyVars new_info in

       if new_tvs ~= old_tvs then % TODO: for now at least, this is very literal.
         raise (SpecError (pos, 
                           "Merged versions of Sort "^(printAliases names)^" have differing type variables:"
                           ^"\n "^(printTyVars old_tvs)
                           ^"\n "^(printTyVars new_tvs)))
       else
       %  case (definedSort? old_dfn, definedSort? new_dfn) of
       %   | (false, _)     -> return (new_info << {names = names})
       %   | (_,     false) -> return (old_info << {names = names})
       %   | _            -> 
	     let (old_decls, old_defs) = sortInfoDeclsAndDefs old_info in
	     let (new_decls, new_defs) = sortInfoDeclsAndDefs new_info in
	     let combined_decls =
	         foldl (fn (new_decl, combined_decls) ->
			if exists (fn old_decl -> equalSort? (new_decl, old_decl)) combined_decls then
			  combined_decls
			else
			  cons (new_decl, combined_decls))
		       old_decls
		       new_decls
	     in
	     let combined_defs =
	         foldl (fn (new_def, combined_defs) ->
			if exists (fn old_def -> equalSort? (new_def, old_def)) combined_defs then
			  combined_defs
			else
			  cons (new_def, combined_defs))
		        old_defs
                        new_defs
             in
             %%% defer checks for errors until later, after the caller 
             %%% of this has had a chance to call compressDefs   
             %%% if length combined_defs > 1 then
             %%%   raise (SpecError (pos, 
             %%%                         foldl (fn (scheme, msg) -> msg ^ "\n" ^ (printSortScheme scheme)) 
             %%%                               ("Merged versions of Sort "^(printAliases names)^" have different definitions:\n")
             %%%                               combined_defs))
             %%% else
	     let combined_dfn = maybeAndSort (combined_decls ++ combined_defs, sortAnn new_info.dfn) in
	     return {names = names, dfn = combined_dfn}	       

  op mergeOpInfo : [a] ASpec a -> AOpInfo a -> Option (AOpInfo a) -> Position -> SpecCalc.Env (AOpInfo a)
 def mergeOpInfo spc new_info opt_old_info pos =
   case opt_old_info of
     | None -> return new_info
     | Some old_info ->
       let names = listUnion (old_info.names, new_info.names) in % this order of args is more efficient
       let names = removeDuplicates names in % redundant?

       if new_info.fixity ~= old_info.fixity then
         raise (SpecError (pos, "Merged versions of Op " ^ (printAliases names) ^ " have different fixity"))
       else
	 let (old_tvs, old_srt, _) = unpackFirstOpDef old_info in
	 let (new_tvs, new_srt, _) = unpackFirstOpDef new_info in

         %% TODO:  Need smarter test here?
         let happy? =
	     case ((old_tvs, old_srt), (new_tvs, new_srt)) of
	       | (([], MetaTyVar _), _)  -> 
	         %%  Old:  def foo ... = ...
	         true
	       | (_, ([], MetaTyVar _))  -> 
                 %%  New:  def foo ... = ...
                 true
	       | _ ->
                 %%  Old:  op ... : fa (...) ...  OR  def fa (...) ...  
                 %%  New:  op ... : fa (...) ...  OR  def fa (...) ...  
                 let _ =
		     if old_tvs ~= new_tvs || ~(equivSort? spc (old_srt, new_srt)) then
		       let old_srt = maybePiSort (old_tvs, old_srt) in
		       let new_srt = maybePiSort (new_tvs, new_srt) in
		       toScreen ("Merged versions of op " ^ (printAliases names) ^ " have possibly different sorts:"
				 ^ "\n " ^ (printSort old_srt)
				 ^ "\n " ^ (printSort new_srt)
				 ^ (if specwareWizard? then
				      "\n\n " ^ (anyToString old_srt)
				      ^ "\n " ^ (anyToString new_srt)
				      ^ "\n"
				    else
				      "\n"))
		     else
		       () 
		 in
		   new_tvs = old_tvs

         in
           if ~ happy? then
	     let old_srt = maybePiSort (old_tvs, old_srt) in
	     let new_srt = maybePiSort (new_tvs, new_srt) in
             raise (SpecError (pos,
			       "Merged versions of Op "^(printAliases names)^" have different sorts:"
			       ^ "\n " ^ (printSort old_srt)
			       ^ "\n " ^ (printSort new_srt)
			       ^ (if specwareWizard? then
				    "\n\n " ^ (anyToString old_srt)
				    ^ "\n " ^ (anyToString new_srt)
				    ^ "\n"
				  else
				    "\n")))
           else
            % case (definedTerm? old_dfn, definedTerm? new_dfn) of
            %   | (false, _    ) -> return (new_info << {names = names})
            %   | (_,     false) -> return (old_info << {names = names})
            %   | _            -> 
	         let (old_decls, old_defs) = opInfoDeclsAndDefs old_info in
	         let (new_decls, new_defs) = opInfoDeclsAndDefs new_info in
		 let combined_decls =
	             foldl (fn (new_decl, combined_decls) ->
			    if exists (fn old_decl -> equalTerm? (new_decl, old_decl)) combined_decls then
			      combined_decls
			    else
			      cons (new_decl, combined_decls))
		           old_decls
			   new_decls
		 in
                 let combined_defs =
                      foldl (fn (new_def, combined_defs) ->
                             if exists (fn old_def -> equalTerm? (new_def, old_def)) combined_defs then
                               combined_defs
                             else
                               cons (new_def, combined_defs))
		            old_defs
                            new_defs
                  in
                  %%% defer checks for errors until later, after the caller 
                  %%% of this has had a chance to call compressDefs   
                  %%% if length combined_defs > 1 then
                  %%%  raise (SpecError (pos, 
                  %%%                    foldl (fn (scheme, msg) -> msg ^ "\n" ^ (printTermScheme scheme)) 
                  %%%                          ("Merged versions of op "^(printAliases names)^" have different definitions:\n")
                  %%%                          combined_defs))
                  %%% else
		  let combined_dfn = maybeAndTerm (combined_decls ++ combined_defs, termAnn new_info.dfn) in
		  return (new_info << {names = names, 
				       dfn = combined_dfn})

 def printAliases (name::aliases) = 
   let 
      def print_qid (Qualified (q, id)) =
	if q = UnQualified then
	  id
	else
	  q ^ "." ^ id
   in
   let str = print_qid name in
   case aliases of
     | [] -> str
     | _  -> "{" ^ (foldl (fn (name, str) -> str ^ "," ^ print_qid name) str aliases) ^ "}"


  %%  To simplify the syntax for users, when a spec is expected, 
  %%  coerce a morphism to its codomain spec or a colimit to its apex spec.
  %%  If there is no obvious coercion, simply return the given value, unchanged.

  %% For some obscure reason, we need to make the type of coerceToSpec explicit here.
  def coerceToSpec (value : Value) : Value =  
    case value of
      | Morph   sm  -> Spec (cod sm)
      | Colimit col -> Spec (Cat.apex (Cat.cocone col))
      | _           -> value

  op complainIfAmbiguous : Spec -> Position -> Env Spec
  def complainIfAmbiguous spc pos =
    let ambiguous_sorts = 
        foldriAQualifierMap (fn (_, _, info, ambiguous_sorts) ->
			     let (decls, defs) = sortInfoDeclsAndDefs info in
			     if length decls <= 1 && length defs <= 1 then
			       ambiguous_sorts
			     else
			       ListUtilities.insert (info, ambiguous_sorts))
	                    []
			    spc.sorts
    in
    let ambiguous_ops = 
        foldriAQualifierMap (fn (_, _, info, ambiguous_ops) ->
			     let (decls, defs) = opInfoDeclsAndDefs info in
			     if length decls <= 1 && length defs <= 1 then
			       ambiguous_ops
			     else
			       ListUtilities.insert (info, ambiguous_ops))
	                    []
			    spc.ops
    in
    if ambiguous_sorts = [] & ambiguous_ops = [] then
      return spc
    else
      let sort_msg = 
          case ambiguous_sorts of
	    | [] -> ""
	    | _ ->
	      (foldl (fn (sort_info, msg) ->
		      msg ^ "\nsort " ^ (ppFormat (ppASortInfo sort_info)))
	             "\nAmbiguous sorts:"
		     ambiguous_sorts)
	      ^ "\n"
      in
      let op_msg = 
          case ambiguous_ops of
	    | [] -> ""
	    | _ ->
	      (foldl (fn (opinfo, msg) ->
		      msg ^ "\n\nop " ^ (ppFormat (ppAOpInfo opinfo)))
	             "\nAmbiguous ops: "
		     ambiguous_ops)
      in
      let msg = "\n" ^ sort_msg ^ op_msg ^ "\n" in
      raise (SpecError (pos, msg))

  op compressDefs : Spec -> Spec
  def compressDefs spc =
    let new_sorts = foldriAQualifierMap 
                     (fn (q, id, old_info, revised_sorts) ->
		      let new_info = compressSortDefs spc old_info in
		      if new_info = old_info then
			revised_sorts
		      else
			insertAQualifierMap (revised_sorts, q, id, new_info))
		     spc.sorts
		     spc.sorts
    in
    let new_ops = foldriAQualifierMap 
                     (fn (q, id, old_info, revised_ops) ->
		      let new_info = compressOpDefs spc old_info in
		      if new_info = old_info then
			revised_ops
		      else
			insertAQualifierMap (revised_ops, q, id, new_info))
		     spc.ops
		     spc.ops
    in
    {importInfo = spc.importInfo,
     sorts      = new_sorts,
     ops        = new_ops,
     properties = spc.properties}


  op compressSortDefs : Spec -> SortInfo -> SortInfo
  def compressSortDefs spc info =
    let (old_decls, old_defs) = sortInfoDeclsAndDefs info in
    case old_defs of
      | []  -> info
      | [_] -> info
      | _ ->
        let pos = sortAnn info.dfn in
        let (tvs, srt) = unpackFirstSortDef info in
        let tvs = map mkTyVar tvs in
	let xxx_defs = map (fn name -> mkBase (name, tvs)) info.names in
        let new_defs = 
	    foldl (fn (old_def, new_defs) ->
		   if ((exists (fn xxx_def -> equivSort? spc (old_def, xxx_def)) xxx_defs) %% ?
		       ||
		       (exists (fn new_def -> equivSort? spc (old_def, new_def)) new_defs))
		     then
		       new_defs
		   else
		     cons (old_def, new_defs))
                  []
		  old_defs
	in
	let new_dfn = maybeAndSort (old_decls ++ new_defs, pos) in
	info << {names = removeDuplicates info.names, 
		 dfn   = new_dfn}
        
  op compressOpDefs : Spec -> OpInfo -> OpInfo
  def compressOpDefs spc info =
    let (old_decls, old_defs) = opInfoDeclsAndDefs info in
    case old_defs of
      | []  -> info
      | [_] -> info
      | _ ->
	let pos = termAnn info.dfn in
        let new_defs = 
	    foldl (fn (old_def, new_defs) ->
		   if exists (fn new_def -> equivTerm? spc (old_def, new_def))
		             new_defs 
		     then
		       new_defs
		   else
		     cons (old_def, new_defs))
                  []
		  old_defs
	in
	let new_dfn = maybeAndTerm (old_decls ++ new_defs, pos) in
	info << {names = removeDuplicates info.names, 
		 dfn   = new_dfn}
	          
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


% --------------------------------------------------------------------------------

(**
 * the following "abuses" a spec as an attribute store; it looks for op-defs of the form
 *      def attrname = attrvalue
 * where attrvalue is a String.
 * This is used, for instance, to use a spec to define options for code 
 * generation (e.g. the Java package name etc.)
 *)
op getStringAttributesFromSpec: Spec -> StringMap.Map String
def getStringAttributesFromSpec spc =
  let ops = opsAsList spc in
  foldl (fn ((_ , id, info), map) ->
	 let defs = opInfoDefs info in
	 case defs of
	   | term :: _ ->
	     (let (_, _, tm) = unpackTerm term in
	      case tm of
		| Fun (String val,_,_) -> StringMap.insert (map, id, val)
		| _ -> map)
	   | _ -> map)
	StringMap.empty
	ops


 sort AttrValue = | String String | Nat Nat | StringList (List String) | Bool Boolean | Null

 (**
  * reads an "option" spec and returns the value of the given operator using the AttrValue sort
  * as result type.
  *)
 op getAttributeFromSpec: Spec * String -> AttrValue
 def getAttributeFromSpec (spc, aname) =
   let
     def extractList (t, list) =
       case t of
	 | Apply(Fun(Embed(Cons,_),_,_),Record([(_,Fun(String elem,_,_)),(_,t)],_),_) ->
	   extractList (t, concat (list, [elem]))
	 | _ -> list
   in
   let
     def getAttrFromOps ops =
       case ops of
	 | [] -> Null
	 | (_, id, info)::ops ->
           if (id = aname) then
	     let defs = opInfoDefs info in
	     case defs of
	       | term :: _ ->
	         (let (_, _, tm) = unpackTerm term in
		  case tm of
		    | Fun   (String val,      _, _) -> String val
		    | Fun   (Nat    val,      _, _) -> Nat    val
		    | Fun   (Bool   val,      _, _) -> Bool   val
		    | Fun   (Embed  (Nil, _), _, _) -> StringList []
		    | Apply (Fun (Embed (Cons,_), _, _),
			     Record([(_, Fun (String elem,_,_)), (_,t)],_),
			     _) ->
		      StringList (extractList (t, [elem]))
		    | _ -> getAttrFromOps ops)
	       | _ -> getAttrFromOps ops
	  else
	    getAttrFromOps ops
  in
    getAttrFromOps (opsAsList spc)

 (**
  * returns whether or not id is declared without a definition
  * as sort in spc
  *)
  op sortIsDefinedInSpec?: Spec * Sort -> Boolean
 def sortIsDefinedInSpec? (spc, srt) =
  case srt of
    | Base (Qualified (_,id),_,_) -> sortIdIsDefinedInSpec? (spc, id)
    | Boolean _ -> true
    | _ -> false

  op sortIdIsDefinedInSpec?: Spec * Id -> Boolean
 def sortIdIsDefinedInSpec? (spc, id) =
   let srts = sortsAsList spc in
   case find (fn (_, id0, _) -> id0 = id) srts of
     | Some (_,_,info) -> definedSortInfo? info
     | _ -> false 

 op opIdIsDefinedInSpec?: Spec * Id -> Boolean
 def opIdIsDefinedInSpec?(spc,id) =
   let ops = opsAsList spc in
   case find (fn (_, id0, _) -> id0 = id) ops of
     | Some (_,_,info) -> definedOpInfo? info
     | _ -> false


% --------------------------------------------------------------------------------
(**
 * merges the two given specs into one
 *)

 op mergeSpecs: Spec * Spec -> Spec
 def mergeSpecs (spc1, spc2) =
   let srts = foldriAQualifierMap
                (fn (q, id, info, map) -> insertAQualifierMap (map, q, id, info))
		spc1.sorts 
		spc2.sorts
   in
   let ops = foldriAQualifierMap
               (fn (q, id, info, map) -> insertAQualifierMap (map, q, id, info))
	       spc1.ops 
	       spc2.ops
   in
   let props = foldr (fn(prop as (pname,_,_,_),props) ->
		      if exists (fn(pname0,_,_,_) -> pname=pname0) props then
			props
		      else 
			cons(prop,props))
                     spc1.properties 
		     spc2.properties
  in
  let spc = initialSpecInCat in  % maybe emptySpec would be ok, but this is safer
  let spc = setSorts      (spc, srts)  in
  let spc = setOps        (spc, ops)   in
  let spc = setProperties (spc, props) in
  spc

% --------------------------------------------------------------------------------
(**
 * returns the list of qualified id's that are declared in the spec (sorts and ops)
 *)

 op getDeclaredQualifiedIds: Spec -> List QualifiedId
 def getDeclaredQualifiedIds spc =
   let qids = foldriAQualifierMap
                (fn (q, id, _, qids) -> cons (Qualified (q, id), qids))
	        [] 
	        spc.sorts
   in
   let qids = foldriAQualifierMap
                (fn (q, id, _, qids) -> cons (Qualified (q, id), qids))
		qids 
		spc.ops
   in
     qids

% --------------------------------------------------------------------------------

   op basicQualifier?   : Qualifier   -> Boolean
   op basicQualifiedId? : QualifiedId -> Boolean

  def basicQualifiers = [
			 "Boolean",    % can appear in raw translation rules
			 "Char", 
			 "Compare",
			 "Functions",  % TODO: add Relations ?
			 "Integer", 
			 "Integer_",   % special hack
			 "List",
			 "Nat",
			 "Option",
			 "String",
			 "WFO"         % TODO: basic ??
			]

  def basicQualifier?              q     = member (q, basicQualifiers)
  def basicQualifiedId? (Qualified(q,_)) = member (q, basicQualifiers)

endspec
