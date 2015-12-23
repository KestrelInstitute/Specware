(* Copyright 2015 Kestrel Institute. See file LICENSE for license details *)

SliceSpec qualifying spec 

%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%
%%% Old stuff that is deprecated
%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%

import ../Specs/AnalyzeRecursion

type QualifierSet = AQualifierMap Bool

op emptySet: QualifierSet = emptyAQualifierMap

op in? (Qualified(q,id): QualifiedId, s: QualifierSet) infixl 20 : Bool =
 some?(findAQualifierMap(s, q, id) )

op nin?  (Qualified(q,id): QualifiedId, s: QualifierSet) infixl 20 : Bool =
 none?(findAQualifierMap(s, q, id) )

op <| (s: QualifierSet, Qualified(x, y): QualifiedId) infixl 25 : QualifierSet =
 insertAQualifierMap(s, x, y, true)

op addList(s: QualifierSet, l: QualifiedIds): QualifierSet =
 foldl (<|) s l

%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%

op codeGenElement?(el: SpecElement): Bool =
 case el of
   | Pragma("#translate", _, "#end", _) -> true
   | Pragma _ -> false
   | _ -> true

op scrubSpec (spc : Spec, op_set : QualifierSet, type_set : QualifierSet) : Spec =
 let new_types =
     mapiPartialAQualifierMap (fn (q, id, v) ->
                                  if Qualified (q, id) in? type_set then
                                    Some v
                                  else 
                                    None)
                               spc.types
 in
 let new_ops =
     mapiPartialAQualifierMap (fn (q, id, v) ->
                                 if Qualified (q, id) in? op_set then
                                   Some v
                                 else 
                                   None)
                              spc.ops
 in
 let
   def filterElements (elements : SpecElements) : SpecElements =
     let
       def keep? el =
         case el of
           | Type     (qid,              _) -> qid in? type_set
           | TypeDef  (qid,              _) -> qid in? type_set
           | Op       (qid, _,           _) -> qid in? op_set && numRefinedDefs spc qid = 1
           | OpDef    (qid, refine_num,_,_) -> qid in? op_set && numRefinedDefs spc qid = refine_num + 1
           | Property (_, _, _, formula, _) ->
             forall? (fn qid -> qid in? op_set) (opsInTerm formula)
             && 
             forall? (fn qid -> qid in? type_set) (typesInTerm formula)
             % | Import   (_, _, elts,       _) -> exists? (fn el -> element_filter el) elts
           | Import _ -> true
           | _ -> codeGenElement? el
     in
     mapPartial (fn elt ->
                   if keep? elt then
                     Some (case elt of
                             | Import (s_tm, i_sp, elts,                a) ->
                               Import (s_tm, i_sp, filterElements elts, a)
                             | _ ->  elt)
                   else
                     None)
                elements
 in
 let new_elements = filterElements spc.elements in
 spc << {
         types    = new_types,
         ops      = new_ops, 
         elements = new_elements
         }

%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%

%% Haskell generation calls this directly...
op sliceSpecInfoForCode (spc        : Spec,
                         root_ops   : QualifiedIds, 
                         root_types : QualifiedIds) 
 : QualifierSet * QualifierSet =
 let chase_terms_in_types? = false in
 let chase_theorems?       = false in
 let 
   def cut_op?   (qid : QualifiedId) : Bool = false
   def cut_type? (qid : QualifiedId) : Bool = false
 in
 sliceSpecInfo (spc, root_ops, root_types, cut_op?, cut_type?, chase_terms_in_types?, chase_theorems?, false)

op [a] foldJustTerms (f : a -> MSTerm -> a) (acc: a) (term : MSTerm) (firstDefsOnly? : Bool) : a =
 %% foldTerm recurs into term within types and patterns: subtypes, quotients, etc.
 let foldOfChildren = 
      case term of
        | Let        (decls, bdy, _) -> foldJustTerms f (foldl (fn (acc, (_,tm)) -> foldJustTerms f acc tm firstDefsOnly?) acc decls) bdy firstDefsOnly?
        | LetRec     (decls, bdy, _) -> foldJustTerms f (foldl (fn (acc, (_,tm)) -> foldJustTerms f acc tm firstDefsOnly?) acc decls) bdy firstDefsOnly?
        | Record     (row,        _) -> foldl (fn (acc, (id,tm)) -> foldJustTerms f acc tm firstDefsOnly?) acc row
        | IfThenElse (t1, t2, t3, _) -> foldJustTerms f (foldJustTerms f (foldJustTerms f acc t1 firstDefsOnly?) t2 firstDefsOnly?) t3 firstDefsOnly?
        | Lambda     (match,      _) -> foldl (fn (acc,(_,cond,tm)) -> foldJustTerms f (foldJustTerms f acc cond firstDefsOnly?) tm firstDefsOnly?) acc match
        | Bind       (_, _, tm,   _) -> foldJustTerms f acc tm firstDefsOnly?
        | The        (_, tm,      _) -> foldJustTerms f acc tm firstDefsOnly?
        | Apply      (t1, t2,     _) -> foldJustTerms f (foldJustTerms f acc t1 firstDefsOnly?) t2 firstDefsOnly?
        | Seq        (tms,        _) -> foldl (fn (acc, tm) -> foldJustTerms f acc tm firstDefsOnly?) acc tms
        | ApplyN     (tms,        _) -> foldl (fn (acc, tm) -> foldJustTerms f acc tm firstDefsOnly?) acc tms
        | TypedTerm  (tm, _,      _) -> foldJustTerms f acc tm firstDefsOnly?
        | Pi         (_, tm,      _) -> foldJustTerms f acc tm firstDefsOnly?
        | And        (tms,        _) -> (if firstDefsOnly? then
                                           foldJustTerms f acc (head tms) firstDefsOnly?
                                         else
                                           foldl (fn (acc, tm) -> foldJustTerms f acc tm firstDefsOnly?) acc tms
                                           )
        | _ -> acc
 in
 f foldOfChildren term
 
op sliceSpecInfo (spc                   : Spec, 
                  root_ops              : QualifiedIds, 
                  root_types            : QualifiedIds, 
                  cut_op?               : QualifiedId -> Bool, % stop recursion at these, and do not include them
                  cut_type?             : QualifiedId -> Bool, % stop recursion at these, and do not include them
                  chase_terms_in_types? : Bool, 
                  chase_theorems?       : Bool,
                  firstDefsOnly?        : Bool  %%governs handling of And terms
                  )
 : QualifierSet * QualifierSet =
 let 
   def eq_op_qid (Qualified (q, id)) = Qualified (q, "eq_" ^ id)
      
   def findQuotientOpsIn typ =
     foldType (fn result -> fn _ -> result,
               fn result -> fn typ -> 
                 case typ of
                   | Quotient (_, Fun (Op (qid, _), _, _), _) -> result ++ [qid]
                   | _ -> result,
               fn result -> fn _ -> result)
              []
              typ

   def newOpsInTerm (tm, newopids, op_set, firstDefsOnly?) =
     if chase_terms_in_types? then
       %% FIXME pass firstDefsOnly? to foldTerm?
       foldTerm (fn opids -> fn tm ->
                   case tm of
                     | Fun (Op (qid,_), funtype, _) ->
                       % let _ = writeLine("new_ops_in_term: " ^ show qid ^ " : " ^ show (cut_op? qid)) in
                       if cut_op? qid then
                         opids
                       else if qid nin? opids  && qid nin? op_set then
                         qid :: opids
                            else
                              opids
                     | Fun (Equals, Arrow (Product ([("1", Base (type_qid, _, _)), _], _), _, _), _) ->
                       let eq_qid = eq_op_qid type_qid in
                       % let _ = writeLine("new_ops_in_term: " ^ show eq_qid ^ " : " ^ show (cut_op? eq_qid)) in
                       if cut_op? eq_qid then
                         opids
                       else if eq_qid nin? opids  && eq_qid nin? op_set then % avoid millions of duplicate entries
                         eq_qid :: opids
                       else
                         opids
                     | _ -> opids,
                 fn result -> fn _ -> result,
                 fn result -> fn _ -> result)
                newopids 
                tm
     else
       foldJustTerms (fn opids -> fn tm ->
                        case tm of
                          | Fun (Op (qid,_), funtype, _) ->
                            % let _ = writeLine("new_ops_in_term: " ^ show qid ^ " : " ^ show (cut_op? qid)) in
                            if cut_op? qid then
                              opids
                            else if qid nin? opids  && qid nin? op_set then
                              qid :: opids
                            else
                              opids
                          | Fun  (Quotient typename, typ, _) -> 
                            (case findTheType (spc, typename) of
                               | Some typeinfo -> 
                                 %% quotient functions may be needed at runtime...
                                 let quotients = findQuotientOpsIn typeinfo.dfn in
                                 % let _ = writeLine("For type " ^ show typename ^ " : " ^ anyToString typeinfo) in
                                 % let _ = writeLine("Quotients = " ^ anyToString quotients) in
                                 quotients ++ opids
                               | _ ->
                                 % let _ = writeLine("For type " ^ show typename ^ " : no typeinfo") in
                                 opids)
                          | Fun (Equals, Arrow (Product ([("1", Base (type_qid, _, _)), _], _), _, _), _) ->
                            let eq_qid = eq_op_qid type_qid in
                            % let _ = writeLine("new_ops_in_term: " ^ show eq_qid ^ " : " ^ show (cut_op? eq_qid)) in
                            if cut_op? eq_qid then
                              opids
                            else if eq_qid nin? opids  && eq_qid nin? op_set then % avoid millions of duplicate entries
                              eq_qid :: opids
                            else
                              opids
                          | _ -> opids)
                     newopids 
                     tm
                     firstDefsOnly?

   def newOpsInType (ty : MSType, newopids : QualifiedIds, op_set : QualifierSet) : QualifiedIds =
     if chase_terms_in_types? then
       foldType (fn opids -> fn tm ->
                   case tm of
                     | Fun (Op (qid,_), funtype, _) ->
                       % let _ = writeLine("new_ops_in_type: " ^ show qid ^ " : " ^ show (cut_op? qid)) in
                       if cut_op? qid then
                         opids
                       else if qid nin? opids && qid nin? op_set then
                         qid :: opids
                       else
                         opids
                     | Fun (Equals, Arrow (Product ([("1", Base (type_qid, _, _)), _], _), _, _), _) ->
                       let eq_qid = eq_op_qid type_qid in
                       % let _ = writeLine("new_ops_in_type: " ^ show eq_qid ^ " : " ^ show (cut_op? eq_qid)) in
                       if cut_op? eq_qid then
                         opids
                       else if eq_qid nin? opids  && eq_qid nin? op_set then % avoid millions of duplicate entries
                         eq_qid :: opids
                            else
                              opids
                     | _ -> opids,
                 fn result -> fn _ -> result,
                 fn result -> fn _ -> result)
                newopids 
                ty
     else
       newopids

   def newTypesInTerm (tm : MSTerm, newtypeids : QualifiedIds, type_set : QualifierSet) : QualifiedIds =
     foldTerm (fn result -> fn _ -> result,
               fn result -> fn t ->
                 case t of
                   | Base (qid,_,_) ->
                     % let _ = writeLine("new_types_in_term: " ^ show qid ^ " : " ^ show (cut_type? qid)) in
                     if cut_type? qid then
                       result
                     else if qid nin? result && qid nin? type_set then
                       qid :: result
                     else
                       result
                   | _ -> result,
               fn result -> fn _ -> result)
              newtypeids 
              tm
      
   def newTypesInType (ty : MSType, newtypeids : QualifiedIds, type_set : QualifierSet) : QualifiedIds =
     foldType (fn result -> fn _ -> result,
               fn result -> fn t ->
                 case t of
                   | Base (qid,_,_) ->
                     % let _ = writeLine("new_types_in_type: " ^ show qid ^ " : " ^ show (cut_type? qid)) in
                     if cut_type? qid then
                       result
                     else if qid nin? result && qid nin? type_set then
                       qid :: result
                     else
                       result
                   | _ -> result,
               fn result -> fn _ -> result)
              newtypeids 
              ty
      
   def iterateDeps (new_ops, new_types, op_set, type_set, n, firstDefsOnly?) =
     % let _ = writeLine ("================================================================================") in
     % let _ = writeLine ("Round " ^ show n) in
     if new_ops = [] && new_types = [] then 
       % let _ = writeLine ("Done") in
       % let _ = writeLine ("================================================================================") in
       (op_set, type_set)
     else
       % let _ = writeLine ("New ops:  " ^ anyToString new_ops) in
       % let _ = writeLine ("New type: " ^ anyToString new_types) in
       let op_set   = addList (op_set,   new_ops)   in
       let type_set = addList (type_set, new_types) in
       let new_ops_in_ops = 
           foldl (fn (newopids, qid) ->
                    % let _ = writeLine("new_ops_in_ops: " ^ show qid ^ " : " ^ show (cut_op? qid)) in
                    if cut_op? qid then
                      newopids
                    else
                      case findTheOp (spc, qid) of
                        | Some opinfo -> 
                          % let _ = writeLine("Scanning ops in op: " ^ show (primaryOpName opinfo)) in
                          % let _ = writeLine("               dfn: " ^ printTerm opinfo.dfn) in
                          newOpsInTerm (opinfo.dfn, newopids, op_set, firstDefsOnly?)
                        | None -> newopids)
                 [] 
                 new_ops
       in
       let new_ops_in_ops_or_types = 
           if chase_terms_in_types? then 
             foldl (fn (newopids, qid) ->
                      % let _ = writeLine("new_ops_in_types: " ^ show qid ^ " : " ^ show (cut_type? qid)) in
                      if cut_type? qid then
                        newopids
                      else
                        case findTheType (spc, qid) of
                          | Some typeinfo -> 
                            % let _ = writeLine("Scanning ops in type: " ^ show (primaryTypeName typeinfo)) in
                            newOpsInType(typeinfo.dfn, newopids, op_set)
                          | None -> newopids)
                   new_ops_in_ops
                   new_types
           else
             new_ops_in_ops
       in
       let new_types_in_ops = 
           foldl (fn (newtypeids, qid) ->
                    % let _ = writeLine("new_types_in_ops: " ^ show qid ^ " : " ^ show (cut_op? qid)) in
                    if cut_op? qid then
                      newtypeids
                    else
                      case findTheOp (spc, qid) of
                        | Some opinfo -> 
                          % let _ = writeLine("Scanning types in op: " ^ show (primaryOpName opinfo)) in
                          newTypesInTerm (opinfo.dfn, newtypeids, type_set)
                        | None -> newtypeids)
                 [] 
                 new_ops
       in
       let new_types_in_ops_or_types = 
           foldl (fn (newtypeids, qid) ->
                    % let _ = writeLine("new_types_in_types: " ^ show qid ^ " : " ^ show (cut_type? qid)) in
                    if cut_type? qid then
                      newtypeids
                    else
                      case findTheType (spc, qid) of
                        | Some typeinfo -> 
                          % let _ = writeLine("Scanning types in type: " ^ show (primaryTypeName typeinfo)) in
                          newTypesInType (typeinfo.dfn, newtypeids, type_set)
                        | None -> newtypeids)
                 new_types_in_ops
                 new_types
       in
       iterateDeps (new_ops_in_ops_or_types, new_types_in_ops_or_types, op_set, type_set, n + 1, firstDefsOnly?)
 in
 let (op_set, type_set) = iterateDeps (root_ops, root_types, emptySet, emptySet, 0, firstDefsOnly?) in
 (op_set, type_set)

%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%

op sliceSpec (spc                   : Spec, 
              root_ops              : QualifiedIds,        % include these and things they recursively mention
              root_types            : QualifiedIds,        % include these and things they recursively mention
              cut_op?               : QualifiedId -> Bool, % stop recursion at these, and do not include them
              cut_type?             : QualifiedId -> Bool, % stop recursion at these, and do not include them
              chase_terms_in_types? : Bool,                % recur through subtype predicates and quotient relations
              chase_theorems?       : Bool)                % recur through axioms and theorems that mention included types and ops
 : Spec =
 let (op_set, type_set) = sliceSpecInfo (spc, root_ops, root_types, cut_op?, cut_type?, chase_terms_in_types?, chase_theorems?, false) in
 let sliced_spc         = scrubSpec     (spc, op_set,   type_set)                                                                      in
 sliced_spc
 
op sliceSpecForCode (spc        : Spec, 
                     root_ops   : QualifiedIds,        % include these and things they recursively mention
                     root_types : QualifiedIds,        % include these and things they recursively mention
                     cut_op?    : QualifiedId -> Bool, % stop recursion at these, and do not include them
                     cut_type?  : QualifiedId -> Bool) % stop recursion at these, and do not include them
 : Spec =
 let chase_terms_in_types? = false in  % do not recur through subtype predicates and quotient relations
 let chase_theorems?       = false in  % do not recur through axioms and theorems that mention included types and ops
 sliceSpec (spc, root_ops, root_types, cut_op?, cut_type?, chase_terms_in_types?, chase_theorems?)
 
op sliceSpecForCodeM (spc        : Spec, 
                      root_ops   : QualifiedIds,        % include these and things they recursively mention
                      root_types : QualifiedIds,        % include these and things they recursively mention
                      cut_op?    : QualifiedId -> Bool, % stop recursion at these, and do not include them
                      cut_type?  : QualifiedId -> Bool, % stop recursion at these, and do not include them
                      tracing?   : Bool)
 : Env (Spec * Bool) =
 return (sliceSpecForCode (spc, root_ops, root_types, cut_op?, cut_type?), tracing?)


end-spec
