SpecCalc qualifying spec 
 import ../../Environment
 import /Languages/MetaSlang/Specs/AnnSpec
 import SpecCalc qualifying
   (translate (translate /Library/Legacy/DataStructures/Monadic/SplayMap
     by {Monad._ +-> SpecCalc._})
     by {SpecCalc.Monad +-> SpecCalc.Env})
 import /Languages/MetaSlang/Specs/Elaborate/Utilities % for unfoldSort

 op addSort :
   fa (a) List QualifiedId
       -> TyVars
       -> List (ASortScheme a)
       -> ASpec a
       -> Position
       -> SpecCalc.Env (ASpec a)

 def addSort new_sort_names new_type_vars  new_defs old_spec position =
  %%% some of the names may refer to previously declared sorts,
  %%% some of which may be identical
  %%% Collect the info's for such references
  let new_sort_names = rev (removeDuplicates new_sort_names) in % don't let duplicate names get into a sortinfo!
  let old_infos = foldl (fn (new_name, old_infos) ->
                         case findTheSort (old_spec, new_name) of
                           | Some info -> 
                             if exists (fn old_info -> info = old_info) old_infos then
                               old_infos
                             else
                               cons (info, old_infos)
                           | _ -> old_infos)
                        []
                        new_sort_names
  in {
   new_sorts <-
     case old_infos of
       | [] ->
         %%  We're declaring a brand new sort.
         let new_info = (new_sort_names, new_type_vars, new_defs) in
         return (foldl (fn (name as Qualified(qualifier, id), new_sorts) ->                         
                        insertAQualifierMap (new_sorts, qualifier, id, new_info))
                       old_spec.sorts
                       new_sort_names)
       | [old_info as (old_sort_names, old_type_vars, old_defs)] ->
         %%  We're merging new information with a previously declared sort.
         let combined_sort_names = listUnion (old_sort_names, new_sort_names) in
	 let combined_sort_names = removeDuplicates combined_sort_names in % redundant?
         if new_type_vars = old_type_vars then % TODO: for now at least, this is very literal -- should test for alpha-equivalence.
           (case (old_defs, new_defs) of
              | ([],   []) -> 
                %%  Old: Sort S    [or S(A,B), etc.]
                %%  New: Sort S    [or S(X,Y), etc.]
                raise (SpecError (position, "Sort "^(printAliases new_sort_names)^" has been redeclared."))
              | ([],   _::_) ->
                %%  Old: Sort S (A,B)
                %%  New: Sort S (X,Y) = T(X,Y)
                let new_info = (combined_sort_names, new_type_vars, new_defs) in
                return (foldl (fn (name as Qualified(qualifier, id), new_sorts) ->                          
                               insertAQualifierMap (new_sorts, qualifier, id, new_info))
                              old_spec.sorts
                              combined_sort_names)
              | (_::_, []) ->
                %%  TODO: Shouldn't this be an error???
                %%  Old: Sort S (X,Y) = T(X,Y)
                %%  New: Sort S (A,B)
                let new_info = (combined_sort_names, old_type_vars, old_defs) in
                return (foldl (fn (name as Qualified(qualifier, id), new_sorts) ->
                               insertAQualifierMap (new_sorts, qualifier, id, new_info))
                              old_spec.sorts
                              combined_sort_names)
              | (old_def::_,  new_def::_) ->
                %%  Old: Sort S (X,Y) = T(X,Y)
                %%  New: Sort S (A,B) = W(A,B)
                raise (SpecError (position, 
                                  "Sort "^(printAliases new_sort_names)^" has been redefined"
                                  ^ "\n from "^ (printSortScheme old_def)
                                  ^ "\n   to "^ (printSortScheme new_def))))
         else
           %%  Old: Sort S (a)
           %%  New: Sort S (x,y)
           raise (SpecError (position, 
                           "Sort "^(printAliases new_sort_names)^" has been redeclared or redefined"
                           ^"\n with new type variables "^(printTypeVars new_type_vars)
                           ^"\n    differing from prior "^(printTypeVars old_type_vars)))
       | _ ->
         %%  We're trying to merge information with two or more previously declared sorts.
         raise (SpecError (position, 
                         "Sort "^(printAliases new_sort_names)^" refers to multiple prior sorts"));
     sp <- return (setSorts (old_spec, new_sorts));
     foldM (fn sp -> fn name -> return (addLocalSortName (sp, name))) sp new_sort_names
    }

 def printTypeVars vars =
   case vars of
     | []     -> "()"
     | v1::vs -> "(" ^ v1 ^ (foldl (fn (v, str) -> str ^","^ v) "" vs) ^ ")"

 op addOp :
    fa (a) List QualifiedId
        -> Fixity
        -> ASortScheme a 
        -> List (ATermScheme a)
        -> ASpec a
        -> Position
        -> SpecCalc.Env (ASpec a)

 def addOp new_op_names
           new_fixity 
           (new_sort_scheme as (new_type_vars, new_sort)) 
           new_defs 
           old_spec 
           position 
  =
  %%% some of the names may refer to previously declared sorts,
  %%% some of which may be identical
  %%% Collect the info's for such references
  let new_op_names = rev (removeDuplicates new_op_names) in % don't let duplicate names get into an opinfo!
  let old_infos = foldl (fn (new_name, old_infos) ->
                         case findTheOp (old_spec, new_name) of
                           | Some info -> 
                             if exists (fn old_info -> info = old_info) old_infos then
                               old_infos
                             else
                               cons (info, old_infos)
                           | _ -> old_infos)
                        []
                        new_op_names
  in {
   new_ops <-
   case old_infos of
     | [] ->
       %%  We're declaring a brand new op
       let new_info = (new_op_names, new_fixity, new_sort_scheme, new_defs) in
       return (foldl (fn (name as Qualified(qualifier, id), new_ops) ->
                      insertAQualifierMap (new_ops, qualifier, id, new_info))
                     old_spec.ops
                     new_op_names)
     | [old_info as (old_op_names, 
                     old_fixity, 
                     old_sort_scheme as (old_type_vars, old_sort), 
                     old_defs)]
       ->
       %%  We're merging new information with a previously declared op.
       (let combined_op_names = listUnion (old_op_names, new_op_names) in
	let combined_op_names = removeDuplicates combined_op_names in % redundant?
        case (old_defs, new_defs) of
          | ([],   []) -> 
            %%  Old: op foo : ...
            %%  New: op foo : ...
            raise (SpecError (position, 
                              "Operator "^(printAliases new_op_names)^" has been redeclared"
                              ^ "\n from " ^ (printSortScheme old_sort_scheme)
                              ^ "\n   to " ^ (printSortScheme new_sort_scheme)))
          | ([],   _::_) -> 
            %%  Old: op foo 
            %%  New: def foo 
            let happy? = (case new_sort_scheme of
                            | ([], MetaTyVar _) -> 
                              %%  Old:  op foo : ...
                              %%  New:  def foo x = ...
                              true
                            | _ -> 
                              %%  Old:  op foo : ...
                              %%  New:  def fa (a,b,c) foo ... = ...
                              new_type_vars = old_type_vars)
            in
            if happy? then
              let new_info = (combined_op_names, old_fixity, old_sort_scheme, new_defs) in
              return (foldl (fn (name as Qualified(qualifier, id), new_ops) ->
                             insertAQualifierMap (new_ops, qualifier, id, new_info))
                            old_spec.ops
                            combined_op_names)
            else
              raise (SpecError (position, 
                                "Operator "^(printAliases new_op_names)^" has been redeclared or redefined"
                                ^"\n with new type variables "^(printTypeVars new_type_vars)
                                ^"\n    differing from prior "^(printTypeVars old_type_vars)))
          | (_::_, []) -> 
            let happy? = (case old_sort_scheme of
                            | ([], MetaTyVar _) -> 
                              %%  Old:  def foo ... = ...
                              %%  New:  op foo : ...
                              true
                            | (old_type_vars, MetaTyVar _) -> 
                              %%  Old:  def fa (a,b,c) foo x = ...
                              %%  New:  op foo : ...
                              new_type_vars = old_type_vars
                            | _ -> 
                              %%  Old:  op foo : ...
                              %%  New:  op foo : ...
                              false)
            in
            if happy? then
              %%  Old:  def foo x = ...
              %%  New:  op foo : T
              let new_info = (combined_op_names, new_fixity, new_sort_scheme, old_defs) in
              return (foldl (fn (name as Qualified(qualifier, id), new_ops) ->
                             insertAQualifierMap (new_ops, qualifier, id, new_info))
                            old_spec.ops
                            combined_op_names)
            else
              %%  Old: op foo : S
              %%  Old: def foo ...
              %%  New: op foo : T
              raise (SpecError (position, 
                                "Operator "^(printAliases new_op_names)^" has been redeclared"
                                ^ "\n from type " ^ (printSortScheme old_sort_scheme)
                                ^ "\n   to type " ^ (printSortScheme new_sort_scheme)))
          | (old_def::_, new_def::_) -> 
            %%  def foo ...
            %%  def foo ...
            raise (SpecError (position, 
                              "Operator "^(printAliases new_op_names)^" has been redefined"
                              ^ "\n from " ^ (printTermScheme old_def)
                              ^ "\n   to " ^ (printTermScheme new_def))))
     | _ ->
       %%  We're trying to merge information with two or more previously declared sorts.
       raise (SpecError (position, 
                         "Op "^(printAliases new_op_names)^" refers to multiple prior ops"));

    sp <- return (setOps (old_spec, new_ops));
    foldM (fn sp -> fn name -> return (addLocalOpName (sp, name))) sp new_op_names
   }

 % ------------------------------------------------------------------------

 op mergeSortInfo :
   fa(a) ASpec a
      -> ASortInfo a
      -> Option (ASortInfo a)
      -> Position
      -> SpecCalc.Env (ASortInfo a)
 def mergeSortInfo spc newPSortInfo optOldPSortInfo position =
   case (newPSortInfo,optOldPSortInfo) of
     | (_,None) -> return newPSortInfo
     | ((new_sort_names, new_type_vars, new_defs), Some (old_sort_names, old_type_vars, old_defs)) ->
       let sort_names = listUnion(old_sort_names,new_sort_names) in % this order of args is more efficient
       let sort_names = removeDuplicates sort_names in % redundant?
       if ~(new_type_vars = old_type_vars) then % TODO: for now at least, this is very literal.
         raise (SpecError (position, 
                           "Merged versions of Sort "^(printAliases sort_names)^" have differing type variables:"
                           ^"\n "^(printTypeVars old_type_vars)
                           ^"\n "^(printTypeVars new_type_vars)))
       else
         case (old_defs, new_defs) of
           | ([],   [])   -> return (sort_names, new_type_vars, [])
           | ([],   _::_) -> return (sort_names, new_type_vars, new_defs)
           | (_::_, [])   -> return (sort_names, old_type_vars, old_defs)
           | _            -> 
               let combined_defs =
                   foldl (fn (new_def, combined_defs) ->
                          if exists (fn old_def -> equalSortScheme? (new_def, old_def)) combined_defs then
                            combined_defs
                          else
                            cons (new_def, combined_defs))
                         old_defs                                      
                         new_defs
               in
               %%% defer checks for errors until later, after the caller 
               %%% of this has had a chance to call compressDefs   
               %%% if length combined_defs > 1 then
               %%%   raise (SpecError (position, 
               %%%                         foldl (fn (scheme, msg) -> msg ^ "\n" ^ (printSortScheme scheme)) 
               %%%                               ("Merged versions of Sort "^(printAliases sort_names)^" have different definitions:\n")
               %%%                               combined_defs))
               %%% else
               return (sort_names, old_type_vars, combined_defs)
    
 op mergeOpInfo :
   fa(a) ASpec a
      -> AOpInfo a
      -> Option (AOpInfo a)
      -> Position
      -> SpecCalc.Env (AOpInfo a)
 def mergeOpInfo spc newPOpInfo optOldPOpInfo position =
   case (newPOpInfo,optOldPOpInfo) of
     | (_,None) -> return newPOpInfo
     | ((new_op_names, new_fixity, new_sort_scheme, new_defs), Some (old_op_names, old_fixity, old_sort_scheme, old_defs)) ->
       let op_names = listUnion(old_op_names,new_op_names) in % this order of args is more efficient
       let op_names = removeDuplicates op_names in % redundant?
       if ~(new_fixity = old_fixity) then
         raise (SpecError (position, "Merged versions of Op " ^ (printAliases op_names) ^ " have different fixity"))
       else
         %% TODO:  Need smarter test here?
         let happy? =
           case (old_sort_scheme, new_sort_scheme) of
              | (([], MetaTyVar _), _)  -> 
                 %%  Old:  def foo ... = ...
                 true
              | (_, ([], MetaTyVar _))  -> 
                 %%  New:  def foo ... = ...
                 true
              | ((old_type_vars, old_srt), (new_type_vars, new_srt)) -> 
                 %%  Old:  op ... : fa (...) ...  OR  def fa (...) ...  
                 %%  New:  op ... : fa (...) ...  OR  def fa (...) ...  
                 let _ =
                    if ~(equivSortScheme? spc (old_sort_scheme,new_sort_scheme)) then
                      toScreen ("Merged versions of op " ^ (printAliases op_names) ^ " have possibly different sorts:"
                             ^ "\n " ^ (printSortScheme new_sort_scheme)
                             ^ "\n " ^ (printSortScheme old_sort_scheme) ^ "\n")
                    else () in
                 new_type_vars = old_type_vars
              | _ -> 
                 %% maybe the merged sorts are really equivalent (e.g., in a colimit)
                 true
         in
           if (~ happy?) then
             raise (SpecError (position,
                             "Merged versions of Op "^(printAliases op_names)^" have different sorts:"
                             ^ "\n " ^ (printSortScheme new_sort_scheme)
                             ^ "\n " ^ (printSortScheme old_sort_scheme)))
           else
             case (old_defs, new_defs) of
               | ([],   [])   -> return (op_names, new_fixity, new_sort_scheme, [])
               | ([],   _::_) -> return (op_names, new_fixity, new_sort_scheme, new_defs)
               | (_::_, [])   -> return (op_names, new_fixity, new_sort_scheme, old_defs)
               | _            -> 
                 let combined_defs =
                      foldl (fn (new_def, result_defs) ->
                             if exists (fn old_def -> equalTerm? (new_def.2, old_def.2)) result_defs then
                               result_defs
                             else
                               cons (new_def, result_defs))
                            old_defs                                     
                            new_defs
                  in
                  %%% defer checks for errors until later, after the caller 
                  %%% of this has had a chance to call compressDefs   
                  %%% if length combined_defs > 1 then
                  %%%  raise (SpecError (position, 
                  %%%                    foldl (fn (scheme, msg) -> msg ^ "\n" ^ (printTermScheme scheme)) 
                  %%%                          ("Merged versions of op "^(printAliases op_names)^" have different definitions:\n")
                  %%%                          combined_defs))
                  %%% else
                  return (op_names, new_fixity, new_sort_scheme, combined_defs)

 def printAliases (name::aliases) = 
   let 
      def print_qid (Qualified (qualifier, id)) =
	if qualifier = UnQualified then
	  id
	else
	  qualifier ^ "." ^ id
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
  def complainIfAmbiguous spc position =
    let ambiguous_sorts = 
        foldriAQualifierMap (fn (_, _, info as (_,_,defs), ambiguous_sorts) ->
			     case defs of
			       | []  -> ambiguous_sorts
			       | [_] -> ambiguous_sorts
			       | _   -> ListUtilities.insert (info, ambiguous_sorts))
	                    []
			    spc.sorts
    in
    let ambiguous_ops = 
        foldriAQualifierMap (fn (_, _, info as (_,_,_,defs), ambiguous_ops) ->
			     case defs of
			       | []  -> ambiguous_ops
			       | [_] -> ambiguous_ops
			       | _   -> ListUtilities.insert (info, ambiguous_ops))
                            []
			    spc.ops
    in
    if ambiguous_sorts = [] & ambiguous_ops = [] then
      return spc
    else
      let def print_qid (Qualified (qualifier, id)) =
            if qualifier = UnQualified then
	      id
	    else
	      qualifier^"."^id
      in
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
      raise (SpecError (position, msg))

  op compressDefs : Spec -> Spec
  def compressDefs spc =
    let new_sorts = foldriAQualifierMap 
                     (fn (qualifier, id, old_info, revised_sorts) ->
		      let new_info = compressSortDefs spc old_info in
		      if new_info = old_info then
			revised_sorts
		      else
			insertAQualifierMap (revised_sorts,
					     qualifier,
					     id,
					     new_info))
		     spc.sorts
		     spc.sorts
    in
    let new_ops = foldriAQualifierMap 
                     (fn (qualifier, id, old_info, revised_ops) ->
		      let new_info = compressOpDefs spc old_info in
		      if new_info = old_info then
			revised_ops
		      else
			insertAQualifierMap (revised_ops,
					     qualifier,
					     id,
					     new_info))
		     spc.ops
		     spc.ops
    in
    {importInfo = spc.importInfo,
     sorts      = new_sorts,
     ops        = new_ops,
     properties = spc.properties}


  op compressSortDefs : Spec -> SortInfo -> SortInfo
  def compressSortDefs spc (info as (names, tyVars:TyVars, old_defs)) =
    case old_defs of
      | []  -> info
      | [_] -> info
      | _ ->
        let tyVarsSorts = foldl (fn (tyVar, srts) -> cons (mkTyVar(tyVar), srts)) [] tyVars in
	let new_sorts = foldl (fn (name, srts) -> cons (mkBase(name, tyVarsSorts), srts))
	                      [] names in
	let new_sort_schemas = foldl (fn (srt, srtSchemas) -> cons ((tyVars, srt), srtSchemas)) [] new_sorts in
        let distinct_defs = 
	    foldl (fn (old_def:SortScheme, distinct_defs) ->
		   if (exists (fn new_sort_scheme -> 
			      equivSortScheme? spc (old_def, new_sort_scheme)) 
		             new_sort_schemas) or
		      exists (fn distinct_def -> 
			      equivSortScheme? spc (old_def, distinct_def)) 
		             distinct_defs
		     then
		       distinct_defs
		   else
		     cons (old_def, distinct_defs))
                  []
		  old_defs
	in
	(removeDuplicates names, tyVars, distinct_defs) % rev names?

  op compressOpDefs : Spec -> OpInfo -> OpInfo
  def compressOpDefs spc (info as (names, fixity, sort_scheme, old_defs)) =
    case old_defs of
      | []  -> info
      | [_] -> info
      | _ ->
        let distinct_defs = 
	    foldl (fn (old_def, distinct_defs) ->
		   if exists (fn distinct_def -> 
			      equivTermScheme? spc (old_def, distinct_def)) 
		             distinct_defs 
		     then
		       distinct_defs
		   else
		     cons (old_def, distinct_defs))
                  []
		  old_defs
	in
        (removeDuplicates names, fixity, sort_scheme, distinct_defs) % rev names?
	          
 %%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%
 %%%      Term Equivalences wrt aliases
 %%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%
 %%% These are patterned after equalTerm? etc. in AnnTerm.sw

 op equivTerm?    : fa(a) ASpec a -> ATerm    a * ATerm    a -> Boolean
 op equivSort?    : fa(a) ASpec a -> ASort    a * ASort    a -> Boolean
 op equivPattern? : fa(a) ASpec a -> APattern a * APattern a -> Boolean
 op equivFun?     : fa(a) ASpec a -> AFun     a * AFun     a -> Boolean
 op equivVar?     : fa(a) ASpec a -> AVar     a * AVar     a -> Boolean

 op equivList?    : fa(a,b) ASpec a -> List b * List b * (ASpec a -> b * b -> Boolean) -> Boolean
 def equivList? spc (x, y, eqFn) =
  (length x) = (length y) &
  (case (x, y) of
      | ([],              [])             -> true
      | (head_x::tail_x,  head_y::tail_y) -> eqFn spc (head_x, head_y) & 
                                             equivList? spc (tail_x, tail_y, eqFn)
      | _ -> false)

 op equivOpt? : fa (a,b) ASpec a -> Option b * Option b * (ASpec a -> b * b -> Boolean) -> Boolean
 def equivOpt? spc (x, y, eqFn) =
  case (x, y) of
     | (None,    None)    -> true
     | (Some x1, Some y1) -> eqFn spc (x1, y1)
     | _ -> false

 op equivTermScheme?: fa(a) ASpec a -> ATermScheme a * ATermScheme a -> Boolean
 def equivTermScheme? spc ((tyvs1, t1), (tyvs2, t2)) =
   tyvs1 = tyvs2 & 
   equivTerm? spc (t1, t2)

 op equivSortScheme?: fa(a) ASpec a -> ASortScheme a * ASortScheme a -> Boolean
 def equivSortScheme? spc ((tyvs1, s1), (tyvs2, s2)) =
   tyvs1 = tyvs2 & 
   equivSort? spc (s1, s2)

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
  case (s1,s2) of
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


 def myUnfoldSort (spc,s1) = 
   let Base (qid, ts, pos) = s1 in
   case findAllSorts (spc, qid) of
     | [] -> s1
     | sort_info::_ ->
       (case sort_info of
	  | (main_qid::_, _, []) -> 
	    Base (main_qid, ts, pos)
	  | (aliases, tvs, df :: _) ->
	    let (some_type_vars, some_def) = df in
	    myInstantiateScheme(ts, some_type_vars, some_def))

 op myInstantiateScheme : fa (a) List (ASort a) * TyVars * ASort a -> ASort a
 def fa (a) myInstantiateScheme (types, tyVars, srt) = 
   if null tyVars then
     srt
   else
     let mtvar_position = Internal "copySort" in
     let tyVarMap = zip (tyVars, types) in
     let
        def mapTyVar (tv : TyVar, tvs : List (TyVar * ASort a), pos) : ASort a = 
            case tvs
              of [] -> TyVar(tv,pos)
               | (tv1,s)::tvs -> 
                 if tv = tv1 then s else mapTyVar (tv, tvs, pos)
     in
     let
        def cp (srt : ASort a) : ASort a =
            case srt
              of TyVar (tv, pos) -> mapTyVar (tv, tyVarMap, pos)
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
def getStringAttributesFromSpec(spc) =
  let ops = opsAsList spc in
  foldl (fn((_,id,opinfo as (_,_,_,termSchemes)),map) ->
	 case termSchemes of
	   | (_,term)::_ ->
	     (case term of
		| Fun(String val,_,_) -> StringMap.insert(map,id,val)
		| _ -> map)
	   | _ -> map
	 ) StringMap.empty ops


sort AttrValue = | String String | Nat Nat | StringList (List String) | Bool Boolean | Null

(**
 * reads an "option" spec and returns the value of the given operator using the AttrValue sort
 * as result type.
 *)
op getAttributeFromSpec: Spec * String -> AttrValue
def getAttributeFromSpec(spc,aname) =
  let
    def extractList(t,list) =
      case t of
	| Apply(Fun(Embed(Cons,_),_,_),Record([(_,Fun(String elem,_,_)),(_,t)],_),_) ->
	  extractList(t,concat(list,[elem]))
	| _ -> list
  in
  let
    def getAttrFromOps(ops) =
      case ops of
	| [] -> Null
	| (_,id,opinfo as (_,_,_,termSchemes))::ops ->
          if (id = aname) then
	    (case termSchemes of
	       | (_,term)::_ ->
	         (case term of
		    | Fun(String val,_,_) -> String val
		    | Fun(Nat val,_,_) -> Nat val
		    | Fun(Bool val,_,_) -> Bool val
		    | Fun(Embed(Nil,_),_,_) -> StringList []
		    | Apply(Fun(Embed(Cons,_),_,_),Record([(_,Fun(String elem,_,_)),(_,t)],_),_) ->
		      StringList(extractList(t,[elem]))
		    | _ -> getAttrFromOps(ops))
	       | _ -> getAttrFromOps(ops))
	  else
	    getAttrFromOps(ops)
  in
    getAttrFromOps(opsAsList spc)

(**
 * returns whether or not id is declared without a definition
 * as sort in spc
 *)
op sortIsUnrefinedInSpec?: Spec * Sort -> Boolean
def sortIsUnrefinedInSpec?(spc,srt) =
  case srt of
    | Base(Qualified(_,id),_,_) ->
      sortIdIsUnrefinedInSpec?(spc,id)
    | _ -> false

op sortIdIsUnrefinedInSpec?: Spec * Id -> Boolean
def sortIdIsUnrefinedInSpec?(spc,id) =
  let srts = sortsAsList spc in
  case find (fn(_,id0,sortinfo) -> (id0 = id)) srts of
     | Some (_,_,(_,_,[])) -> true
     | _ -> false

op opIdIsDefinedInSpec?: Spec * Id -> Boolean
def opIdIsDefinedInSpec?(spc,id) =
  let ops = opsAsList spc in
  case find (fn(_,id0,opinfo) -> (id0 = id)) ops of
    | Some (_,_,(_,_,_,_::_)) -> true
    | _ -> false


% --------------------------------------------------------------------------------
(**
 * merges the two given specs into one
 *)

op mergeSpecs: Spec * Spec -> Spec
def mergeSpecs(spc1,spc2) =
  let srts = foldriAQualifierMap
             (fn(q,id,sinfo,map) -> insertAQualifierMap(map,q,id,sinfo))
	     spc1.sorts spc2.sorts
  in
  let ops = foldriAQualifierMap
             (fn(q,id,oinfo,map) -> insertAQualifierMap(map,q,id,oinfo))
	     spc1.ops spc2.ops
  in
  let props = foldr (fn(prop as (pname,_,_,_),props) ->
		     if exists (fn(pname0,_,_,_) -> pname=pname0) props
		       then props
		     else cons(prop,props)
		      ) spc1.properties spc2.properties
  in
  let spc = initialSpecInCat in  % maybe emptySpec would be ok, but this is safer
  let spc = setSorts(spc,srts) in
  let spc = setOps(spc,ops) in
  let spc = setProperties(spc,props) in
  spc

% --------------------------------------------------------------------------------
(**
 * returns the list of qualified id's that are declared in the spec (sorts and ops)
 *)

op getDeclaredQualifiedIds: Spec -> List QualifiedId
def getDeclaredQualifiedIds(spc) =
  let qids = foldriAQualifierMap
             (fn(q,id,_,qids) -> cons(Qualified(q,id),qids))
	     [] spc.sorts
  in
  let qids = foldriAQualifierMap
             (fn(q,id,_,qids) -> cons(Qualified(q,id),qids))
	     qids spc.ops
  in
  qids


endspec




