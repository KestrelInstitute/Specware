Globalize qualifying spec
{
  import /Languages/MetaSlang/Specs/Environment
  
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

  op hasTypeAsArg?   (tm : MSTerm, typ : TypeName) : Bool = false
  op hasTypeAsValue? (tm : MSTerm, typ : TypeName) : Bool = false

  op findInitOp (spc : Spec, typ: TypeName) : SpecCalc.Env QualifiedId =
   let candidates =
       foldriAQualifierMap (fn (q, id, info, candidates) ->
                              let dfn = info.dfn in
                              if hasTypeAsValue? (dfn, typ) && ~ (hasTypeAsArg? (dfn, typ)) then
                                (mkQualifiedId (q, id)) :: candidates 
                              else
                                candidates)
                           []
                           spc.ops
   in
   case candidates of
     | []             -> raise (Fail ("Could not find an initializer for type " ^ show typ))
     | [init_op_name] -> return init_op_name
     | first :: rest  -> let init_ops = foldl (fn (names, init_op_name) -> 
                                                 names ^ ", " ^ show init_op_name) 
                                              (show first)
                                              rest
                         in
                         raise (Fail ("Found multiple initializers for type " ^ show typ ^ " : " ^ init_ops))

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
    * For ginit:
    *  Modify it to set the global gvar and then return ().
    *
    * For every op f in spc:
    *  Replace accesses to local vars of type gtype with accesses to gvar.
    *  Replace updates  to local vars of type gtype with updates  to gvar.
    *)
   let _ = writeLine("Globalization not yet implemented.") in
   return (spc, tracing?)

}
