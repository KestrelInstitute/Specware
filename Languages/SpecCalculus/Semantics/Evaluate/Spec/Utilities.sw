
SpecCalc qualifying spec {
 import ../../Environment
 import /Languages/MetaSlang/Specs/PosSpec
 import /Library/Legacy/DataStructures/Monadic/SplayMap

 op addPSort : (QualifiedId * TyVars * Option PSort) * PosSpec -> Position -> SpecCalc.Env PosSpec
 def addPSort ((name as Qualified(qualifier, id), new_type_vars, new_opt_def), old_spec) position =
  %% qualifier could be "<unqualified>" !
  let old_sorts = old_spec.sorts in
  let old_qmap =
    case StringMap.find (old_sorts, qualifier) of
      | None          -> StringMap.empty
      | Some old_qmap -> old_qmap
  in {
    new_qmap <-  
      case StringMap.find (old_qmap, id) of
       | None -> return (StringMap.insert (old_qmap, id, ([name], new_type_vars, new_opt_def)))
       | Some (old_sort_names, old_type_vars, old_opt_def) -> 
          (case (new_opt_def, old_opt_def) of
            | (None,   None)   -> raise (SpecError (position, "Sort " ^ id ^ " has been redeclared"))
            | (Some _, None)   ->
                if length new_type_vars = length old_type_vars then
                  %%  Sort S (A,B)
                  %%  Sort S (X,Y) = T(X,Y)
                  return (StringMap.insert (old_qmap, id, (old_sort_names, new_type_vars, new_opt_def)))
                else
                  raise (SpecError (position, "Sort " ^ id ^ " redefined using different type variable lists"))
            | (None,   Some _) ->
                if length new_type_vars = length old_type_vars then
                  %%  Sort S (X,Y) = T(X,Y)
                  %%  Sort S (A,B)
                  return old_qmap % StringMap.insert(old_qmap, id, (old_sort_names, old_type_vars, old_opt_def))
                else 
                  raise (SpecError (position, "Sort " ^ id ^ " redefined using different type variable lists"))
            | (Some _, Some _) -> raise (SpecError (position,"Sort " ^ id ^ " has been redefined")));
    let new_sorts = StringMap.insert (old_sorts, qualifier, new_qmap) in 
    let sp = setSorts (old_spec, new_sorts) in
    return (addLocalSortName (sp, name))
  }

 op addPOp   : (QualifiedId * Fixity * PSortScheme * Option PTerm) * PosSpec -> Position -> SpecCalc.Env PosSpec
 def addPOp ((name as Qualified(qualifier, id), new_fixity, new_sort_scheme, new_opt_def),
             old_spec) position =
  %% qualifier could be "<unqualified>" !
  let old_ops = old_spec.ops in
  let old_qmap =
    case StringMap.find (old_ops, qualifier) of
      | None          -> StringMap.empty
      | Some old_qmap -> old_qmap
  in {
    new_qmap <-
      case StringMap.find (old_qmap, id) of
       | None -> return (StringMap.insert(old_qmap, id,
                                  ([name], new_fixity, new_sort_scheme, new_opt_def)))
       | Some (old_op_names, old_fixity, old_sort_scheme, old_opt_def) -> 
          (case (new_opt_def, old_opt_def) of
            | (None,   Some _) -> %%  def foo (x, y) = baz (x, y)
                                  %%  op foo : A * B -> C
                return (StringMap.insert(old_qmap, id, (old_op_names, new_fixity, new_sort_scheme, old_opt_def)))
            | (Some _, None)   -> %%  op foo : A * B -> C
                                  %%  def foo (x, y) = baz (x, y)
                return (StringMap.insert(old_qmap, id, (old_op_names, old_fixity, old_sort_scheme, new_opt_def)))
            | (None,   None)   -> %%  op foo : ...
                                  %%  op foo : ...
                raise (SpecError (position, "Operator " ^ id ^ " has been redeclared"))
            | (Some _, Some _) -> %%  def foo ...
                                  %%  def foo ...
                raise (SpecError (position, "Operator "^id^" has been redefined")));
    let new_ops = StringMap.insert (old_ops, qualifier, new_qmap) in
    let sp = setOps (old_spec, new_ops) in
    return (addLocalOpName (sp, name))
  }

 % ------------------------------------------------------------------------

 op mergePSortInfo :
      PSortInfo * Option PSortInfo * Qualifier * Id
   -> Position
   -> SpecCalc.Env PSortInfo
 def mergePSortInfo (newPSortInfo,optOldPSortInfo,qualifier,id) position =
   case (newPSortInfo,optOldPSortInfo) of
     | (_,None) -> return newPSortInfo
     | ((new_sort_names, new_type_vars, new_opt_def),
       Some (old_sort_names, old_type_vars, old_opt_def)) ->
         (if ~(length new_type_vars = length old_type_vars) then
           raise (SpecError (position,
                "Merged versions of Sort " ^ qualifier ^ "." ^ id ^ " have different type variable lists"))
         else
           let sort_names = listUnion(new_sort_names,old_sort_names) in
           case (new_opt_def, old_opt_def) of
             | (None,   None)   -> return (sort_names, new_type_vars, None)
             | (Some _, None)   -> return (sort_names, new_type_vars, new_opt_def)
             | (None,   Some _) -> return (sort_names, new_type_vars, old_opt_def)
             | (Some sNew, Some sOld) ->
                 if sNew = sOld then % Could use a smarter equivalence test
                   return (sort_names, new_type_vars, new_opt_def)
                 else
                   raise (SpecError (position,
                       "Merged versions of Sort " ^ qualifier ^ "." ^ id ^ " have different definitions")))
    
 op mergePOpInfo :
      POpInfo * Option POpInfo * Qualifier * Id
   -> Position
   -> SpecCalc.Env POpInfo
 def mergePOpInfo (newPOpInfo,optOldPOpInfo,qualifier,id) position =
   case (newPOpInfo,optOldPOpInfo) of
     | (_,None) -> return newPOpInfo
     | ((new_op_names, new_fixity, new_sort_scheme, new_opt_def),
       Some (old_op_names, old_fixity, old_sort_scheme, old_opt_def)) ->
         (if ~(new_fixity = old_fixity) then
           raise (SpecError (position, "Merged versions of Op "^qualifier^"."^id^" have different fixity"))
         else
           if ~(new_sort_scheme = old_sort_scheme) then % Could use a smarter equivalence test 
             raise (SpecError (position, "Merged versions of Op "^qualifier^"."^id^" have different sorts"))
           else
             let op_names = listUnion(new_op_names,old_op_names) in
             case (new_opt_def, old_opt_def) of
               | (None,   None)   -> return (op_names, new_fixity, new_sort_scheme, None)
               | (Some _, None)   -> return (op_names, new_fixity, new_sort_scheme, new_opt_def)
               | (None,   Some _) -> return (op_names, new_fixity, new_sort_scheme, old_opt_def)
               | (Some sNew, Some sOld) ->
                   if sNew = sOld then   % Could use a smarter equivalence test
                     return (op_names, new_fixity, new_sort_scheme, new_opt_def)
                   else
                     raise (SpecError (position, "Merged versions of Op "^qualifier^"."^id^" have different definitions")))

  sort Monad a = SpecCalc.Env a %%% Why is this necessary. Already done in Environment
  op foldOverQualifierMap :
    fa(a,b) (Qualifier * Id * a * b -> SpecCalc.Env b)
         -> b
         -> (AQualifierMap a)
         -> SpecCalc.Env b
  def foldOverQualifierMap = foldDoubleMap
}
