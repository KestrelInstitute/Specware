SpecCalc qualifying spec 
 import ../../Environment

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


endspec
