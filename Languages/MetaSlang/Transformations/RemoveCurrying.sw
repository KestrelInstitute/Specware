%% Replace all curried functions by functions that take products
%%  op f: A -> B -> C
%% -->
%%  op f_1_1: A * B -> C
%%
%% Calls f x y --> f_1_1(x,y), f x --> (fn y -> f_1_1(x,y))
%%
%%  op f: A * (B -> C -> D) -> E
%% -->
%%  op f_2: A * (B * C -> D) -> E
%%
%%  fn x -> (fn y -> e(x,y))
%% -->
%%  fn (x,y) -> e(x,y)
%%
%%  fn x -> (e: (A -> B))
%% -->
%%  fn (x,y) e y
%%
%% Assume that pattern matching has been transformed away


RemoveCurrying qualifying spec

import CurryUtils
import /Languages/SpecCalculus/AbstractSyntax/CheckSpec

%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%

op rcPos : Position = Internal "removeCurrying"

%% Todo: Better way to do this?
 % Open up the definition of a named type (wrapped in a call of Base),
 % unless it is a co-product (which can cause loops for users of this routine).  Does not recurse.
op unfoldBaseNoCoProduct (sp : Spec, ty : MSType) : MSType =
  case ty of
    | Base (qid, tys, _) ->
      (case findTheType (sp, qid) of
	 | None -> ty %TODO Should this be an error?
	 | Some info ->
	   if definedTypeInfo? info then
	     (let (tvs, ty_def) = unpackFirstTypeDef info in
               if length tvs ~= length tys
                 then (% writeLine("Type arg# mismatch: "^printType ty);
                       %% This can arise because of inadequacy of patternType on QuotientPat
                       ty_def)
               else if coproduct? ty_def then  %% Don't do it for coproducts
                 ty
               else 
                substType (zip (tvs, tys), ty_def))
	     else %Should this be an error?
	       ty)
    | _ -> ty  %TODO: signal an error

%% Returns transformed type and whether any change was made
%% Don't look inside type definitions except to follow arrows
%% (otherwise infinitely recursive)

op uncurry_toplevel_type (old_type : MSType, spc : Spec) : Bool * MSType =
 aux_uncurry_type (old_type, spc, true)

op uncurry_var_type (old_type : MSType, spc : Spec) : Bool * MSType =
 aux_uncurry_type (old_type, spc, false)

op uncurry_type (old_type : MSType, spc : Spec) : MSType =
 let (curried?, new_type) = aux_uncurry_type (old_type, spc, false) in
 new_type

op aux_uncurry_type (old_type : MSType, spc : Spec, toplevel? : Bool) : Bool * MSType =
 let

   def uncurry_arrow (rng, accum_dom_types) =
     case stripSubtypes (spc, rng) of
       | Arrow (dom, rest_rng, _) ->
         let expanded_dom_types = accum_dom_types 
             % foldl (fn (dom_typ, dom_types) ->
             %         case productOpt (spc, dom_typ) of
             %           | Some fields -> dom_types ++ (map (fn (_, s) -> s) fields)
             %           | _ -> dom_types ++ [dom_typ])
             %       []
             %       accum_dom_types
         in
         let new_type = (uncurry_arrow (rest_rng, expanded_dom_types ++ [dom])).2 in
         (true, new_type)
       | _ ->
         let (changed?, new_rng)       = aux rng                                        in
         let (changed?, new_dom_types) = foldrPred aux changed? accum_dom_types in
         let new_type                  = mkArrow (mkProduct new_dom_types, new_rng)     in
         (changed?, new_type)

   def aux old_type =
     aux2 (old_type, false)

   def aux2 (old_type, toplevel?) =
     case old_type of

       | Subtype (old_parent, old_pred, _) ->
         let (changed?, new_parent) = aux old_parent                        in
         let new_pred               = uncurry_term (old_pred, spc)          in
         let new_type               = Subtype (new_parent, new_pred, rcPos) in
         (changed?, new_type)
         
       | Arrow (dom, rng, _) ->
         if toplevel? then
           uncurry_arrow (rng, [dom])
         else
           (false, old_type)
           
       | Product (old_fields, _) ->
         let (changed?, new_fields) = 
         foldrPred (fn (id, old_type) ->
                      let (changed?, new_type) = aux old_type in
                      (changed?, (id, new_type))) 
                   false 
                   old_fields
         in 
         let new_type = Product (new_fields, rcPos) in
         (changed?, new_type)
         
       | CoProduct (old_fields, _) ->
         let (changed?, new_fields) =
         foldrPred (fn (id, opt_type) ->
                      case opt_type of
                        | Some old_type ->
                          let (changed?, new_type) = aux old_type in
                          (changed?, (id, Some new_type))
                        | _ -> 
                          (false, (id, None)))
                   false 
                   old_fields
         in 
         (changed?, CoProduct (new_fields, rcPos))
         
      | Quotient (old_base, old_rel, _) ->
        let (changed?, new_base) = aux old_base                        in
        let new_rel              = uncurry_term (old_rel, spc)         in
        let new_type             = Quotient (new_base, new_rel, rcPos) in
        (changed?, new_type)
                          
      | Base (qid, args, ann) -> 
        let new_type = unfoldBaseNoCoProduct (spc, old_type) in 
        % This equalType? test prevents loops when unfolding did nothing 
        % (if that possible?  maybe for BaseType Bool?)
        if equalType? (new_type, old_type) then
          (false, old_type)
        else 
          aux new_type
                            
      | _ -> 
        (false, old_type)
 in
 aux2 (old_type, toplevel?)

op uncurried_op_info (spc      : Spec, 
                      old_name : OpName,
                      old_type : MSType) 
 : Option (OpName * Nat * MSType * MSType) =
 let (curried?, new_type) = uncurry_toplevel_type (old_type, spc) in
 if curried? then
   case arrowOpt (spc, new_type) of 
     | Some (new_dom, new_rng) ->
       let curry_level = curryShapeNum (spc, old_type)       in
       let new_name    = uncurryName (old_name, curry_level) in
       Some (new_name, curry_level, new_dom, new_rng)
     | _ ->
       None
 else
   None

%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%

op uncurry_pattern (pat : MSPattern, spc : Spec) : MSPattern =
  case pat of
    | RestrictedPat (pat, tm, _) -> 
      RestrictedPat (pat, uncurry_term (tm, spc), rcPos)
    | _ -> pat  %%FIXME: Add more cases!

%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%

op convert_fun (term        : MSTerm, 
                curry_level : Nat, 
                spc         : Spec) 
 : MSTerm =
 case term of

   | Fun (Op (old_name, _), old_type, _) ->
     let new_name = uncurryName (old_name, curry_level) in
     let new_type = uncurry_type (old_type, spc)        in
     mkOp (new_name, new_type)

   | _ -> term

op curried_fun_and_args (term : MSTerm) : Option (MSTerm * MSTerms) =
 let
   def aux (tm, i,  args) = 
     case tm of
       | Fun   _           -> Some (tm, args)
       | Apply (t1, t2, _) -> aux (t1, i + 1, t2::args)
       | _ -> None
 in
 aux (term, 0, [])

op mkTypedApply (f : MSTerm, arg : MSTerm, spc : Spec) : MSTerm =
 let typed_f = case f of
                 | Fun _ -> f
                 | Var _ -> f
                 | TypedTerm _ -> f
                 | _ -> 
                   let f_type  = inferType (spc, f) in
                   TypedTerm (f, f_type, rcPos) 
 in
 mkApply (typed_f, arg)

op var_name_pool : List String = ["x", "y", "z", "w", "l", "m", "n", "o", "p", "q", "r", "s"]

op mk_new_vars (types    : MSTypes, 
                used_ids : List Id, 
                spc      : Spec) 
 : MSVars =
 let
   def find_unused_name (types, used_ids, pool_id :: pool_ids) =
     case types of

       | [] -> []

       | old_type :: tail_types ->
         if pool_id in? used_ids then
           find_unused_name (types, used_ids, pool_ids)
         else 
           let new_type = uncurry_type (old_type, spc) in
           let new_var  = (pool_id, new_type)          in
           let pool_ids = case pool_ids of
                            | [] -> [pool_id ^ "x"]
                            | _ -> pool_ids
           in
           new_var |> find_unused_name (tail_types, used_ids, pool_ids)
 in 
 find_unused_name (types, used_ids, var_name_pool)

op flatten_lambda (outer_pats : MSPatterns, 
                   body       : MSTerm, 
                   body_type  : MSType, 
                   spc        : Spec) 
 : MSTerm =
 case body of

   | Lambda ([(pat, _, body)], _) ->
     flatten_lambda (outer_pats ++ [pat], 
                     body, 
                     inferType (spc, body), 
                     spc)

   | _ ->
     case arrowOpt (spc, body_type) of

       | Some (dom, _) ->
         %% !!? If dom is a product should we flatten it? No, for the moment.
         let new_vars = mk_new_vars ([dom], 
                                     map (fn (id, _)-> id) (freeVars body), 
                                     spc)
         in
         let new_pvars = map mkVarPat new_vars                       in
         let new_tvars = map mkVar    new_vars                       in
         let new_pat   = mkTuplePat (outer_pats ++ new_pvars)        in
         let new_body  = mkTypedApply (body, mkTuple new_tvars, spc) in
         let new_body  = uncurry_term (new_body, spc)                in
         mkLambda (new_pat, new_body) 

       | _ -> 
         let new_pat  = mkTuplePat outer_pats    in
         let new_body = uncurry_term (body, spc) in
         mkLambda (new_pat, new_body)

op uncurry_term (term : MSTerm, spc : Spec) : MSTerm =
 let
         
  def aux term =
    case term of

      | Apply (t1, t2, _) ->
        (case curried_fun_and_args term  of
           | Some (f, args) -> 
             let f_type      = inferType     (spc, f)      in
             let curry_level = curryShapeNum (spc, f_type) in
             let new_f =
                 if curry_level > 1 && curry_level = length args then
                   convert_fun (f, curry_level, spc) 
                 else
                   f
             in
             let new_arg = mkTuple (map aux args) in
             mkTypedApply (new_f, new_arg, spc)

           | _ ->
             let new_t1 = aux t1 in
             let new_t2 = aux t2 in
             let new_tm = Apply (new_t1, new_t2, rcPos) in
             new_tm)
        
      | Record (old_fields, _) ->
        let new_fields = map (fn (id, tm) -> (id, aux tm)) old_fields in
        if new_fields = old_fields then 
          term
        else 
          Record (new_fields, rcPos)
          
      | Var ((id, old_type), _) ->
        let (curried?, new_type) = uncurry_var_type (old_type, spc) in
        if curried? then
          Var ((id, new_type), rcPos)
        else 
          term
          
      | Fun (Op (old_name, fixity), old_type, _) ->
        (case uncurried_op_info (spc, old_name, old_type) of
           
           | Some (new_name, curry_level, new_dom, new_rng) -> 
             Fun (Op (new_name, fixity), 
                  mkArrow (new_dom, new_rng), 
                  rcPos) 
             
           | _ -> term)
        
      %% Assume multiple rules have been transformed away and predicate is true
      | Lambda ([(pat, _, old_body)], _)  ->
        let new_body = aux old_body in
        if new_body = old_body then
          term
        else 
          mkLambda (pat, new_body)
          
      | Lambda (old_rules, _) ->
        let new_rules = map (fn (old_pat, old_cond, old_body) -> 
                               let new_cond = aux old_cond in
                               let new_body = aux old_body in
                               (old_pat, new_cond, new_body))
                            old_rules
        in 
        Lambda (new_rules, rcPos)
        
      | Let (old_decls, old_body, _)  ->
        let new_decls = map (fn (pat, tm) -> (pat, aux tm)) old_decls in
        let new_body  = aux old_body                                  in
        if equalTerm? (new_body, old_body) && new_decls = old_decls then % TODO
          term
        else
          Let (new_decls, new_body, rcPos)
          
      | LetRec (old_decls, old_body, _) ->
        let new_decls = map (fn (pat, tm) -> (pat, aux tm)) old_decls in
        let new_body  = aux old_body                                  in
        if equalTerm? (new_body, old_body) && new_decls = old_decls then % TODO
          term
        else 
          LetRec (new_decls, new_body, rcPos)
          
      | The (var, old_tm, _) ->
        let new_tm = aux old_tm in
        if equalTerm? (new_tm, old_tm) then
          term
        else
          The (var, new_tm, rcPos)
          
      | IfThenElse (t1, t2, t3, _) ->
        let new_t1 = aux t1 in
        let new_t2 = aux t2 in
        let new_t3 = aux t3 in
        if equalTerm? (new_t1, t1) && equalTerm? (new_t2, t2) && equalTerm? (new_t3, t3) then 
          term
        else 
          IfThenElse (new_t1, new_t2, new_t3, rcPos)
          
      | Seq (terms, _) -> 
        Seq (map aux terms, rcPos)
        
      | Bind (binder, vars, term, _) -> 
        Bind (binder, vars, aux term, rcPos)
        
      | TypedTerm (old_term, old_type, _) ->
        let new_type = uncurry_type (old_type, spc) in 
        TypedTerm (aux old_term, new_type, rcPos)
        
      | _ -> term
 in
 aux term

%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%

op add_uncurried_ops (spc : Spec) : Spec =
 let
   def mkNewApply (f, args) = 
     case args of
       | [] -> f
       | arg :: args ->
         mkNewApply (mkTypedApply (f, arg, spc), args)

   def uncurried_name old_name =
     case findTheOp (spc, old_name) of
       | Some info ->
         let Qualified (old_q, old_id) = old_name                in
         let (old_decls, old_defs)     = opInfoDeclsAndDefs info in
         (case (old_defs ++ old_decls) of
            | old_dfn :: _ ->
              (let (old_tvs, old_type, old_tm) = unpackFirstTerm old_dfn in
               case uncurried_op_info (spc, old_name, old_type) of
                 | Some (new_name, _, _, _) ->
                   Some new_name
                 | _ -> None)
            | _ -> None)
       | _ -> None

   def add_uncurry_elements elts =
     foldl (fn (old_elts, old_elt) ->
              case old_elt of

                | Import (s_tm, imported_spec, sub_elts, _) ->
                  let new_elts = add_uncurry_elements sub_elts in
                  let new_elt  = Import (s_tm, imported_spec, new_elts, rcPos) in
                  let new_elts = old_elts <| new_elt in
                  new_elts

                | Op (name, def?, _) ->  % true means decl includes def
                  (case uncurried_name name of
                     | Some new_name ->
                       let new_elt = Op (new_name, def?, rcPos) in
                       old_elts <| old_elt <| new_elt
                     | _ ->
                       old_elts <| old_elt)

                | OpDef (name, x, y, _) ->
                  (case uncurried_name name of
                     | Some new_name ->
                       let new_elt = OpDef (new_name, x, y, rcPos) in
                       old_elts <| old_elt <| new_elt
                     | _ ->
                       old_elts <| old_elt)
                | _ -> 
                  old_elts <| old_elt)
           []
           elts
 in
 let new_ops =
     foldOpInfos (fn (info, ops) ->
                    let old_name              = primaryOpName      info in
                    let (old_decls, old_defs) = opInfoDeclsAndDefs info in
                    case old_defs ++ old_decls of
                      | old_dfn :: _ ->
                        (let (old_tvs, old_type, old_term) = unpackFirstTerm old_dfn in
                         case uncurried_op_info (spc, old_name, old_type) of
                           | Some (new_name as Qualified (new_q, new_id), curry_level, new_dom, new_rng) ->
                             let new_dfn_type = Arrow (new_dom, new_rng, rcPos) in
                             let new_dfn_body =
                                 case old_term of
                                   | Any _ -> 
                                     Any rcPos
                                   | _ -> 
                                     let 
                                       def get_arg_types dom_type =
                                         case productOpt (spc, dom_type) of
                                           | Some fields ->  map (fn (_, typ) -> typ) fields
                                           | _ -> 
                                             let _ = writeLine("Warning: RemoveCurrying saw unusual dom type: " ^ printType dom_type) in
                                             let _ = writeLine("         arrow type was: "                      ^ printType old_type) in
                                             [dom_type]
                                     in
                                     let new_arg_types   = get_arg_types new_dom                 in
                                     let new_vars        = mk_new_vars (new_arg_types, [], spc)  in
                                     let new_pvars       = map mkVarPat new_vars                 in
                                     let new_tvars       = map mkVar    new_vars                 in
                                     let new_pat         = mkTuplePat   new_pvars                in
                                     let new_f           = TypedTerm (old_term, old_type, rcPos) in
                                     let new_lambda_body = mkNewApply (new_f, new_tvars)         in
                                     let new_lambda_rule = (new_pat, trueTerm, new_lambda_body)  in
                                     Lambda ([new_lambda_rule], rcPos)
                             in
                             let new_dfn = maybePiTerm (old_tvs, TypedTerm (new_dfn_body, new_dfn_type, rcPos)) in
                             insertAQualifierMap (ops, new_q, new_id,
                                                  info << {names = [new_name],
                                                           dfn   = new_dfn})
                          | _ -> ops)
                      | _ -> ops)
                 spc.ops
                 spc.ops
 in
 let new_elts = add_uncurry_elements spc.elements in
 spc << {ops        = new_ops, 
         elements   = new_elts}

%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%

op remove_curried_refs (spc : Spec) : Spec =
 let new_ops = 
     mapOpInfos (fn old_info ->
                   if definedOpInfo? old_info then
                     %% TODO: Handle multiple defs??
                     let (old_tvs, old_type, old_term) = unpackFirstOpDef old_info in
                     let new_term = uncurry_term (old_term, spc) in
                     let new_type = uncurry_type (old_type, spc) in
                     let new_dfn  = maybePiTerm (old_tvs, TypedTerm (new_term, new_type, rcPos)) in
                     old_info << {dfn = new_dfn}
                   else
                     old_info)
                spc.ops
 in
 let new_types = 
     mapTypeInfos (fn old_info ->
                     if definedTypeInfo? old_info then
                       %% TODO: Handle multiple defs??
                       let (old_tvs, old_type) = unpackFirstTypeDef old_info in
                       let new_type = uncurry_type (old_type, spc)    in
                       let new_dfn  = maybePiType (old_tvs, new_type) in
                       old_info << {dfn = new_dfn}
                     else
                       old_info)
                  spc.types
 in
 let new_elements = 
     mapSpecElements (fn elt ->
                        case elt of
                          | Property (kind, name, tvs, old_fm, _) ->
                            let new_fm = uncurry_term (old_fm, spc) in
                            Property (kind, name, tvs, new_fm, rcPos) 
                          | _ ->
                            elt)
                     spc.elements
 in
 spc << {ops      = new_ops,
         types    = new_types,
         elements = new_elements}

%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%

op SpecTransform.removeCurrying (spc : Spec) : Spec =
 let spc = add_uncurried_ops   spc in
 let spc = remove_curried_refs spc in
 spc

end-spec
