Globalize qualifying spec
{
  import /Languages/MetaSlang/Specs/Environment
  import /Languages/MetaSlang/Transformations/SliceSpec
  
  op compressWhiteSpace (s : String) : String =
   let 
     def whitespace? char = 
       char = #\s || char = #\n || char = #\t

     def compress (chars, have_whitespace?) =
       %% avoid deep recursions...
       let (chars, _) = 
           foldl (fn ((chars, have_whitespace?), char) ->
                    if whitespace? char then
                      if have_whitespace? then
                        (chars, have_whitespace?)
                      else
                        ([#\s] ++ chars, true)
                    else
                      ([char] ++ chars, false))
                 ([], true)
                 chars
       in
         reverse chars
   in
     implode (compress (explode s, true))

  op showTypeName (info : TypeInfo) : String = printQualifiedId (primaryTypeName info)
  op showOpName   (info : OpInfo)   : String = printQualifiedId (primaryOpName   info)
   
  op checkGlobalType (spc: Spec, gtype as Qualified(q,id) : TypeName) : SpecCalc.Env TypeName =
   case findTheType (spc, gtype) of
     | Some _ -> return gtype
     | _ ->
       if q = UnQualified then
         case wildFindUnQualified (spc.types, id) of
           | [_]   -> return gtype
           | []    -> raise (Fail ("Proposed type to globalize does not exist: " ^ show gtype))
           | first :: rest -> 
             let names = foldl (fn (names, info) -> names ^ ", " ^ showTypeName info) (showTypeName first) rest in
             raise (Fail ("Proposed type to globalize is ambiguous: " ^ names))
       else
         raise (Fail ("Proposed type to globalize does not exist: " ^ show gtype))
          
  op checkGlobalVar (spc: Spec, gvar as Qualified(q,id) : OpName, gtype : TypeName) : SpecCalc.Env OpName =
   let
     def verify opinfo =
       let typ = termType opinfo.dfn in
       case typ of
         | Base (qid, [], _)                 | gtype = qid -> return gvar
         | _ ->
           raise (Fail ("Global var " ^ show gvar ^ " with expected type " ^ show gtype ^ " is already defined with type " ^ printType typ))
   in
   case findTheOp (spc, gvar) of
      | Some opinfo -> verify opinfo
      | _ ->
        if q = UnQualified then
          case wildFindUnQualified (spc.ops, id) of
            | [opinfo] -> verify opinfo
            | []       -> return gvar    % Ok -- we will add the proposed var later.
            | first :: rest ->
              let names = foldl (fn (names, info) -> names ^ ", " ^ showOpName info) (showOpName first) rest in
              raise (Fail ("Proposed global var is already ambiguous among " ^ names))
        else
          % Ok -- we will add the proposed var later.
          return gvar 
          
  op checkGlobalInitOp (spc: Spec, ginit as Qualified(q,id) : OpName, gtype : TypeName) : SpecCalc.Env QualifiedId =
   let
     def removeSubtypes typ = % do not use stripSubtypes, which uses unfoldBase
       case typ of
         | Subtype (typ, _, _) -> removeSubtypes typ
         | _ -> typ

     def verify opinfo =
       let full_type = termType opinfo.dfn in
       case full_type of

         | Base (qid, [], _) | gtype = qid -> return ginit        % op foo : State

         | Subtype (typ, _, _) ->
           (let typ = removeSubtypes typ in
            case typ of

              | Base (qid, [], _) | gtype = qid -> return ginit   % op foo : (State | p?)

              | _ ->
                raise (Fail ("Op " ^ show ginit ^ " for producing initial global " ^ 
                               show gtype ^ " is defined with type " ^ printType full_type)))

         | Arrow (_, rng, _) ->
           (let rng = removeSubtypes rng in
            case rng of

              | Base (qid, [], _) | gtype = qid -> return ginit    % op foo : X -> State  %  op foo : X -> (State | p?)

              | _ ->
                raise (Fail ("Op " ^ show ginit ^ " for producing initial global " ^ 
                               show gtype ^ " is defined with type " ^ printType full_type)))

         | _ ->
           raise (Fail ("Op " ^ show ginit ^ " for producing initial global " ^ 
                          show gtype ^ " is defined with type " ^ printType full_type))
   in
   case findTheOp (spc, ginit) of
     | Some opinfo -> verify opinfo
     | _ ->
       if q = UnQualified then
         case wildFindUnQualified (spc.ops, id) of
           | [opinfo] -> verify opinfo
           | []       -> raise (Fail ("Op " ^ show ginit ^ " for producing initial global " ^ show gtype ^ " is undefined."))
           | first :: rest -> 
             let names = foldl (fn (names, qid) -> names ^ ", " ^ showOpName qid) (showOpName first) rest in
             raise (Fail ("Op " ^ show ginit ^ " for producing initial global " ^ show gtype ^ " is ambiguous among " ^ names))
       else
         raise (Fail ("Op " ^ show ginit ^ " for producing initial global " ^ show gtype ^ " is undefined."))

  op argTypeMatches? (typ : MSType, name : TypeName) : Bool =
   case typ of
     | Base    (nm, [], _) -> nm = name 
     | Subtype (typ, _, _) -> argTypeMatches? (typ, name)
     | Product (pairs,  _) -> exists? (fn (_, typ) -> argTypeMatches? (typ, name)) pairs
     | _ -> false

  op valTypeMatches? (typ : MSType, name : TypeName) : Bool =
   case typ of
     | Base    (nm, [], _) -> nm = name 
     | Subtype (typ, _, _) -> valTypeMatches? (typ, name)
     | Product (pairs,  _) -> exists? (fn (_, typ) -> valTypeMatches? (typ, name)) pairs
     | Arrow   (_, rng, _) -> valTypeMatches? (rng, name)
     | _ -> false

  op findInitOp (spc : Spec, gtype: TypeName) : SpecCalc.Env QualifiedId =
   let candidates =
       foldriAQualifierMap (fn (q, id, info, candidates) ->
                              let optype = termType info.dfn in
                              if valTypeMatches? (optype, gtype) && ~ (valTypeMatches? (optype, gtype)) then
                                (mkQualifiedId (q, id)) :: candidates 
                              else
                                candidates)
                           []
                           spc.ops
   in
   case candidates of
     | []             -> raise (Fail ("Could not find an initializer for type " ^ show gtype))
     | [init_op_name] -> return init_op_name
     | first :: rest  -> let init_ops = foldl (fn (names, init_op_name) -> 
                                                 names ^ ", " ^ show init_op_name) 
                                              (show first)
                                              rest
                         in
                         raise (Fail ("Found multiple initializers for type " ^ show gtype ^ " : " ^ init_ops))

  op globalizeSingleThreadedType (spc       : Spec, 
                                  gtype     : TypeName, 
                                  gvar      : OpName, 
                                  opt_ginit : Option OpName,
                                  tracing?  : Boolean)
   : SpecCalc.Env (Spec * Bool) =
   {
    gtype <- checkGlobalType (spc, gtype);
    gvar  <- checkGlobalVar  (spc, gvar, gtype);
    ginit <- (case opt_ginit of
                | Some ginit -> checkGlobalInitOp (spc, ginit, gtype)
                | _ -> findInitOp (spc, gtype));
    spec_with_gvar <- return (case findTheOp (spc, gvar) of
                                | Some _ -> spc
                                | _ -> spc);  % addOp (spc, gvar, type)
    replaceLocalsWithGlobalRefs (spc, gtype, gvar, ginit, tracing?)
    }

  op baseOp? (qid as Qualified(q, id) : QualifiedId) : Bool = 
   q in? ["Bool", "Char", "Compare", "Function", "Integer", "IntegerAux", "List", "List1", "Nat", "Option", "String"]

  op baseType? (qid as Qualified(q, id) : QualifiedId) : Bool = 
   q in? ["Bool", "Char", "Compare", "Function", "Integer", "IntegerAux", "List", "List1", "Nat", "Option", "String"]


  op replaceLocalsWithGlobalRefs (spc      : Spec, 
                                  gtype    : TypeName, 
                                  gvar     : OpName, 
                                  ginit    : OpName,
                                  tracing? : Boolean) 
   : SpecCalc.Env (Spec * Bool) =
   (*
    * At this point, we know:
    *  gtype names a unique existing base type in spc,
    *  gvar  names a unique existing op in spc, of type 'gtype'
    *  ginit names a unique existing op in spc, of type 'gtype' or 'X -> gtype'
    *
    * For every op f in spc, remove local vars of type gtype, and replace with references to gvar.
    * If the final returned value is constructed "on-the-fly", add an assignment of that value to gvar.
    *)
   let _ = writeLine("================================================================================") in 
   %% let ops          = opsReachableFrom xxx in
   %% let new_sigs_map = reviseSignatures ops in
   %% ...
   let chase_subtypes? = false in
   let chase_theorems? = false in
   let (root_ops, root_types) = sliceSpecInfo (spc, topLevelOps spc, topLevelTypes spc, baseOp?, baseType?, chase_subtypes?, chase_theorems?) in
   
   %% let new_sigs = mapiAQualifierMap (fn (q, id, transform?) -> ??? (spc, info, gtype, gvar, ginit)) root_ops in
   let new_ops = mapOpInfos (fn info -> 
                               let Qualified(q,id) = primaryOpName info in
                               let revise? = findAQualifierMap (root_ops, q, id) in
                               case revise? of
                                 | Some true ->
                                   let _ = writeLine("Changing " ^ q ^ "." ^ id) in
                                   reviseOpInfo (spc, info, gtype, gvar, ginit)
                                 | Some false ->
                                   let _ = writeLine("Not Revising (A) " ^ q ^ "." ^ id) in
                                   reviseOpInfo (spc, info, gtype, gvar, ginit)
                                 | _ ->
                                   let _ = writeLine("Not Revising (B) " ^ q ^ "." ^ id) in
                                   info)
                            spc.ops 
   in
   let _ = writeLine("================================================================================") in 
   return (spc << {ops = new_ops}, tracing?)

 op was_tuple? (row : List (Id * MSTerm)) : Bool =
  let (tuple?, _) =
      foldl (fn ((tuple?, n), (id, _)) ->
               if show n = id then
                 (tuple?, n + 1)
               else
                 (false, 0))
            (true, 1)
            row
  in
  tuple?

 op renumber_row (row : List (Id * MSTerm)) : List (Id * MSTerm) =
  let (new_row, _)  =
      foldl (fn ((row, n), (_, tm)) ->
               (row ++ [(show n, tm)], n+1))
            ([], 1)
            row
  in
  new_row

 op retype (tm : MSTerm, typ : MSType) : MSTerm =
  case tm of
    | Fun (x, _, pos) -> Fun (x, typ, pos)
    | _ ->
      let _ = writeLine ("Don't know how to retype : " ^ printTerm tm) in
      tm

 op reviseOpInfo (spc : Spec, info : OpInfo, gtype_name : TypeName, gvar : OpName, ginit : OpName) : OpInfo =
  let qid as Qualified(q, id) = primaryOpName info in
  if baseOp? qid then
   info
  else
  let gtype = Base (gtype_name, [], noPos) in
  % let void = Record ([], noPos) in
  let

    def remove_var id old_body =
      let 
        def aux tm =
          case tm of
            | Apply (t1, Var ((id2, _), _), pos) | id = id2 ->
              let ttype = termType tm in
              (case ttype of
                 | Arrow _ ->
                   retype (t1, ttype)
                 | Subtype(Arrow _, _, _) ->
                   retype (t1, ttype)
                 | _ ->
                   let new_fun = 
                       case t1 of
                         | Fun (Project field, _, _) ->
                           let new_typ = termType tm in
                           Fun (Op (Qualified ("Global", field), Nonfix),
                                Arrow (Product ([], noPos), new_typ, noPos),
                                noPos)
                         | _ ->
                           t1
                   in
                   let new_arg = Record ([], noPos) in
                   Apply (new_fun, new_arg, pos))

            | Record (row, a) ->
              if exists? (fn (_, trm) -> 
                            case trm of
                              | Var ((id2, _), _) | id2 = id -> true
                              | _ -> false)
                         row
                then
                  let new_row = filter (fn (_, trm) -> 
                                          case trm of
                                            | Var ((id2, _), _) | id2 = id -> false
                                            | _ -> true)
                                       row 
                  in
                  case new_row of
                    | [(_, tm)] -> tm
                    | _ ->
                      let new_row = 
                          if was_tuple? row then
                            renumber_row new_row
                          else
                            new_row
                      in 
                       Record (new_row, a)
              else
                tm
            | _ ->
              tm
      in
      mapSubTerms aux old_body

    def reviseRule (rule as (old_pat, old_cond, old_body)) = 

      let old_ptype = patternType old_pat  in
      let old_ttype = termType    old_body in

      let (new_pat, new_cond, new_body) = 
          case old_pat of
            | VarPat ((id, _), pos) ->
              if argTypeMatches? (old_ptype, gtype_name) then
                case old_body of
                  | Lambda ([(old_pat2, old_cond2, old_body2)], _) ->
                    let new_pat  = old_pat2                in
                    let new_cond = old_cond2               in
                    let new_body = remove_var id old_body2 in
                    (new_pat, new_cond, new_body)
                  | _ ->
                    let new_pat  = RecordPat ([], pos)    in
                    let new_cond = old_cond               in
                    let new_body = remove_var id old_body in
                    (new_pat, new_cond, new_body)
              else
                (old_pat, old_cond, old_body)

            | RecordPat (pairs, pos) ->
              let (new_pairs, opt_v) =
                  foldl (fn ((pairs, opt_v), pair) ->
                           let argtype = patternType pair.2 in
                           if similarType? spc (argtype, gtype) then
                             (pairs, Some pair.2)
                           else
                             (pairs ++ [pair], opt_v))
                        ([], None)
                        pairs
              in
              (case opt_v of
                 | Some (VarPat ((id, _), _)) ->
                   let new_pat  = RecordPat (new_pairs, pos) in
                   let new_cond = old_cond                   in
                   let new_body = remove_var id old_body      in
                   (new_pat, new_cond, new_body)
                 | _ ->
                   (old_pat, old_cond, old_body))

            | _ -> 
              (old_pat, old_cond, old_body)
      in
      let new_ptype = patternType new_pat  in
      let new_ttype = termType    new_body in

      let old_arg?  = argTypeMatches? (old_ptype, gtype_name) in
      let old_val?  = valTypeMatches? (old_ttype, gtype_name) in
      let x = if old_arg? then " A " else " - " in
      let y = if old_val? then " V " else " - " in
      let _ = writeLine("   " ^ x ^ y ^ " : " ^ compressWhiteSpace (printType old_ptype) ^ " \t -> " ^ compressWhiteSpace (printType old_ttype)) in
      let _ = writeLine("          : "        ^ compressWhiteSpace (printType new_ptype) ^ " \t -> " ^ compressWhiteSpace (printType new_ttype)) in
      let _ = writeLine("   old pat: "        ^ compressWhiteSpace (printPattern old_pat)) in
      let _ = writeLine("   new pat: "        ^ compressWhiteSpace (printPattern new_pat)) in
      let _ = writeLine("   old trm: "        ^ compressWhiteSpace (printTerm old_body)) in
      let _ = writeLine("   new trm: "        ^ compressWhiteSpace (printTerm new_body)) in
      % let _ = writeLine("   ---") in
      % let _ = writeLine("   old pat: "        ^ anyToString old_pat) in
      % let _ = writeLine("   new pat: "        ^ anyToString new_pat) in
      % let _ = writeLine("   old trm: "        ^ anyToString old_body) in
      % let _ = writeLine("   new trm: "        ^ anyToString new_body) in
      % let _ = writeLine("   old pty: "        ^ anyToString old_ptype) in
      % let _ = writeLine("   new pty: "        ^ anyToString new_ptype) in
      % let _ = writeLine("   old tty: "        ^ anyToString old_ttype) in
      % let _ = writeLine("   new tty: "        ^ anyToString new_ttype) in
      % let _ = writeLine("") in
      let _ = writeLine("") in

      (new_pat, new_cond, new_body)

    def reviseType typ =
      typ

    def reviseTerm tm =
      case tm of 

        | Lambda (               rules, pos) -> 
          Lambda (map reviseRule rules, pos)

        | TypedTerm (           tm,            typ, pos) -> 
          TypedTerm (reviseTerm tm, reviseType typ, pos)

        | Pi (tvs,            tm, pos) -> 
          Pi (tvs, reviseTerm tm, pos)

        | And (               tms, pos) -> 
          And (map reviseTerm tms, pos)

        | Fun _ -> tm

        | Any _ -> tm

        | _ -> 
          let _ = writeLine("?? " ^ anyToString tm) in
          tm
  in
  let _ = writeLine("-- " ^ show (primaryOpName info)) in
  let dfn = reviseTerm info.dfn in
  info << {dfn = dfn}

}


