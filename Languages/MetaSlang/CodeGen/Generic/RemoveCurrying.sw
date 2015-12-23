(* Copyright 2015 Kestrel Institute. See file LICENSE for license details *)

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

import /Languages/MetaSlang/Transformations/CurryUtils
import /Languages/SpecCalculus/AbstractSyntax/CheckSpec

op rcPos : Position = Internal "removeCurrying"

op SpecTransform.removeCurrying (spc : Spec) : Spec =
 let 
   def get_arg_types dom_type =
     case productOpt (spc, dom_type) of
       | Some fields ->  map (fn (_, typ) -> typ) fields
       | _ -> 
         let _ = writeLine("Warning: RemoveCurrying saw unusual dom type: " ^ printType dom_type) in
         [dom_type]

 in
 let (new_ops, renamings) =
     foldOpInfos (fn (info, (ops, renamings)) ->
                    let old_name              = primaryOpName      info in
                    let (old_decls, old_defs) = opInfoDeclsAndDefs info in
                    case old_defs ++ old_decls of
                      | old_dfn :: _ ->
                        (let (old_tvs, old_type, old_term) = unpackFirstTerm old_dfn in
                         case uncurry_type (old_type, spc) of
                           | (new_type, Some arity) ->
                             (case arrowOpt (spc, new_type) of 
                                | Some (new_dom, new_rng) ->
                                  let curry_level                           = curryShapeNum (spc, old_type)       in
                                  let new_name as Qualified (new_q, new_id) = uncurryName (old_name, curry_level) in

                                  % let _ = writeLine("")                                                  in
                                  % let _ = writeLine ("Uncurry: ")                                        in
                                  % let _ = let spaces = implode (repeat #\s (2 * curry_level)) in
                                  %         writeLine(show old_name ^ spaces ^ " : " ^ printType old_type) in
                                  % let _ = writeLine(show new_name ^ " : " ^ printType new_type)          in

                                  let new_dfn_type = Arrow (new_dom, new_rng, rcPos) in
                                  let new_dfn_body =
                                      case old_term of
                                        | Any _ -> 
                                          Any rcPos
                                        | _ -> 
                                          let new_arg_types   = get_arg_types new_dom in
                                          let new_vars        = case extract_vars old_term of
                                                                  | Some vars | (length vars = length new_arg_types) -> 
                                                                    vars 
                                                                  | _ -> 
                                                                    mk_new_vars (new_arg_types, [], spc)
                                          in
                                          let new_pvars       = map mkVarPat new_vars                 in
                                          let new_tvars       = map mkVar    new_vars                 in
                                          let new_pat         = mkTuplePat   new_pvars                in
                                          let new_f           = TypedTerm (old_term, old_type, rcPos) in
                                          let new_lambda_body = curried_apply (new_f, new_tvars)      in
                                          let new_lambda_rule = (new_pat, trueTerm, new_lambda_body)  in
                                          Lambda ([new_lambda_rule], rcPos)
                                  in
                                  let new_dfn = maybePiTerm (old_tvs, TypedTerm (new_dfn_body, new_dfn_type, rcPos)) in
                                  let new_ops = insertAQualifierMap (ops, new_q, new_id,
                                                                     info << {names = [new_name],
                                                                              dfn   = new_dfn})
                                  in
                                  let renamings = (old_name, new_name, arity) |> renamings in
                                  (new_ops, renamings)
                                | _ -> (ops, renamings))
                          | _ -> (ops, renamings))
                      | _ -> (ops, renamings))
                 (spc.ops, [])
                 spc.ops
 in                 
 let
   def add_uncurried_elements elements =
     foldl (fn (old_elts, old_elt) ->
              case old_elt of

                | Import (s_tm, imported_spec, sub_elts, _) ->
                  let new_elts = add_uncurried_elements sub_elts in
                  let new_elt  = Import (s_tm, imported_spec, new_elts, rcPos) in
                  let new_elts = old_elts <| new_elt in
                  new_elts

                | Op (name, def?, _) ->  % true means decl includes def
                  (case findLeftmost (fn (old_name, new_name, _) -> old_name = name) renamings of
                     | Some (_, new_name, _) ->
                       let new_elt = Op (new_name, def?, rcPos) in
                       old_elts <| old_elt <| new_elt
                     | _ ->
                       old_elts <| old_elt)

                | OpDef (name, x, y, _) ->
                  (case findLeftmost (fn (old_name, new_name, _) -> old_name = name) renamings of
                     | Some (_, new_name, _) ->
                       let new_elt = OpDef (new_name, x, y, rcPos) in
                       old_elts <| old_elt <| new_elt
                     | _ ->
                       old_elts <| old_elt)

                | _ -> 
                  old_elts <| old_elt)
           []
           elements
 in
 let new_elements = add_uncurried_elements spc.elements in
 let new_spec    = spc << {ops = new_ops,
                           elements = new_elements}
 in
 let
   def uncurry_funs_with_args term =
     case term of

      | Apply (t1, t2, _) ->
        %% don't worry here about name changes here
        (case curried_fun_and_args term  of
           | Some (old_f, args) -> 
             (let nargs = length args in
              case old_f of
                | Fun (Op (name, _), old_type, _) ->
                  (case findLeftmost (fn (old_name, _, _) -> name = old_name) renamings of
                     | Some (_, new_name, arity) -> 
                       if nargs = arity then
                         let (new_type, _) = uncurry_type (old_type, spc)                 in
                         let new_f         = Fun (Op (new_name, Nonfix), new_type, rcPos) in
                         Apply (new_f, mkTuple args, rcPos)
                       else
                         term
                     | _ -> term)
                | _ -> term)
           | _ -> term)
      | _ -> term
        

   def keep_type typ = typ
   def keep_pat  pat = pat

   def uncurry_funs_without_args term =
     case term of

       | Fun (Op (name, _), old_type, _) ->
         (case findLeftmost (fn (old_name, _, _) -> name = old_name) renamings of

            | Some (_, new_name, arity) -> 
              (let (new_type, _) = uncurry_type (old_type, spc)                 in
               let new_f         = Fun (Op (new_name, Nonfix), new_type, rcPos) in
               case arrowOpt (spc, new_type) of
                 | Some (new_dom, new_rng) ->
                   let new_arg_types = get_arg_types new_dom in
                   new_curried_lambda (new_arg_types, new_f, spc)
                 | _ -> term)
           | _ -> term)
      | _ -> term
 in
 let ttp_a = (uncurry_funs_with_args,    keep_type, keep_pat) in
 let ttp_b = (uncurry_funs_without_args, keep_type, keep_pat) in
 mapSpec ttp_b ( mapSpec ttp_a new_spec)

op new_curried_lambda (dom_types : MSTypes,
                       new_f     : MSTerm, 
                       spc       : Spec) 
 : MSTerm =
 let new_vars  = mk_new_vars (dom_types, [], spc)        in
 let new_pvars = map mkVarPat new_vars                   in
 let new_tvars = map mkVar    new_vars                   in
 let new_body  = Apply (new_f, mkTuple new_tvars, rcPos) in
 let
   def aux pvars =
     case pvars of
       | [] -> new_body
       | pvar :: pvars ->
         Lambda ([(pvar, trueTerm, aux pvars)], rcPos)
 in
 aux new_pvars 

op uncurry_type (typ : MSType, spc : Spec) : MSType * Option Nat =
 let
   def aux (rng, dom_types) =
     case rng of
       | Arrow (dom, rng, _) ->
         aux (rng, dom_types ++ [dom])

       | _ ->
         case stripSubtypes (spc, rng) of
           | Arrow (dom, rng, _) ->
             aux (rng, dom_types ++ [dom])
           | _ ->
             case dom_types of
               | []  -> (typ, None)
               | [_] -> (typ, None)
               | _ ->
                 (mkArrow (mkProduct dom_types, rng),
                  Some (length dom_types))
                  
                  
 in
 aux (typ, [])

op extract_vars (old_term : MSTerm) : Option MSVars =
 case old_term of
   | Lambda ([(pat, _, body)], _) ->
     (case pat of
        | VarPat (v, _) -> 
          (case extract_vars body of
             | Some vars -> Some (v :: vars)
             | _ -> None)
        | _ -> None)
   | _ -> Some []

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
           let new_var  = (pool_id, old_type)          in
           let pool_ids = case pool_ids of
                            | [] -> [pool_id ^ "x"]
                            | _ -> pool_ids
           in
           new_var |> find_unused_name (tail_types, used_ids, pool_ids)
 in 
 find_unused_name (types, used_ids, var_name_pool)

op curried_apply (f : MSTerm, args : MSTerms) : MSTerm =
 case args of
   | [] -> f
   | arg :: args ->
     curried_apply (Apply (f, arg, rcPos), args)

op curried_fun_and_args (term : MSTerm) : Option (MSTerm * MSTerms) =
 let
   def aux (tm, i,  args) = 
     case tm of
       | Fun   _           -> Some (tm, args)
       | Apply (t1, t2, _) -> aux (t1, i + 1, t2::args)
       | _ -> None
 in
 aux (term, 0, [])

end-spec
