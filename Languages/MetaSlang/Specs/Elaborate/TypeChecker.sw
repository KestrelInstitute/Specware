(* Copyright 2015 Kestrel Institute. See file LICENSE.text for license details *)

(* This structure adds type checking and 
   inference to the abstract syntax tree.
      - It infers types of each subterm.
      - Resolves record projection from structure accessing.
 *)

(*
   TODO:

   Syntactic well-formedness checks:
        - duplicate variables in patterns
        - distinguish recursive calls.
        - capture free variables.
        - no free variables in quotient, subtypes.
        
*)

TypeChecker qualifying spec

%% The TypeChecker function is elaboratePosSpec 

import Infix
import Utilities
import PosSpecToSpec
import /Languages/MetaSlang/Transformations/CurryUtils

%% ========================================================================

type Message  = String
type Result = | Spec Spec | Errors (List(String * Position) * Spec)

%% ========================================================================

op elaboratePosSpec           : Spec * Position.Filename -> Result

op unlinkRec                  : MSType -> MSType
op undeterminedType?          : MSType -> Bool
op elaborateType              : LocalEnv * MSType    * MSType            -> MSType
op elaborateCheckTypeForTerm  : LocalEnv * MSTerm    * MSType * MSType   -> MSType 
op elaborateTypeForTerm       : LocalEnv * MSTerm    * MSType * MSType   -> MSType
op resolveNameFromType        : LocalEnv * MSTerm*Id * MSType * Position -> MSTerm
op elaborateTerm              : LocalEnv * MSTerm    * MSType * MSTerms  -> MSTerm
op elaboratePattern           : LocalEnv * MSPattern * MSType            -> MSPattern * LocalEnv

op isCoproduct                : LocalEnv * MSType                          -> Option (List (QualifiedId * Option MSType))
op mkProject                  : LocalEnv * Id * MSType * Position          -> Option MSTerm

op undeclaredName             : LocalEnv * MSTerm      * Id * MSType * Position -> MSTerm
op ambiguousCons              : LocalEnv * MSTerm      * Id * MSType * Position -> MSTerm
op undeclaredResolving        : LocalEnv * MSTerm      * Id * MSType * Position -> MSTerm
op undeclared2                : LocalEnv * MSTerm * Id * Id * MSType * Position -> MSTerm

op pass2Error                 : LocalEnv * MSType * Message * Position -> ()

%% ========================================================================

def type_nat    = natType
def type_bool   = boolType 
def type_char   = charType
def type_string = stringType

op allowDependentSubTypes?: Bool = true

op debug?: Bool = false

%% ========================================================================
%% The main type-checking function is elaboratePosSpec.

def elaboratePosSpec (given_spec0, filename) = 
  let _ = initializeMetaTyVarCounter () in

  %% ======================================================================
  %%                           PASS ZERO  [ 0 => 1 ]
  %% ======================================================================

  %% ---------- INITIALIZE SPEC (see ast-environment.sl) ----------
  %%   AstEnvironment.init adds default imports, etc.
  %%
  %% 
  let given_spec = resolveTypeNames given_spec0 in
  let initial_env  = initialEnv (given_spec, filename) in
  let 
    def elaborate_local_op_types (ops, env) =
      let _ = if debug? then writeLine "**elaborate_local_op_types" else () in
      let def elabOpType(qid as Qualified(q, id), refine_num, ops) =
            case findAQualifierMap (ops, q, id) of
              | Some opinfo ->
                let trps = unpackTypedTerms (opinfo.dfn) in
                let (tvs, ty, tm) = nthRefinement(trps, refine_num) in
                let _ = checkTyVars (env, tvs, termAnn tm) in
                let ty1 = checkType1 (env, ty, if allowDependentSubTypes? then Some tm else None, true) in
                let _ = if debug? then writeLine("\nelos "^show refine_num^" "^show(head opinfo.names)
                                                   ^": "^printType ty^"\n -->\n"^printType ty1)
                        else () in
                let new_dfn = maybePiAndTypedTerm(replaceNthRefinement(trps, refine_num, (tvs, ty1, tm))) in
                 let _ = if debug? then writeLine(printTermWithTypes new_dfn^"\n") else () in
                insertAQualifierMap(ops, q, id, opinfo << {dfn = new_dfn})                                       
              | _ -> ops
      in
      foldl (fn (ops, el) ->
               case el of
                 | Op(qid, _, _) -> elabOpType(qid, 0, ops)
                 | OpDef(qid, refine_num, _, _) -> elabOpType(qid, refine_num, ops)
                 | _ -> ops)
        ops
        given_spec.elements

    def elaborate_local_types (types, env) =
      let _ = if debug? then writeLine "**elaborate_local_types" else () in
      if ~(hasLocalType? given_spec) then types
      else
      mapTypeInfos (fn info ->
                    if someTypeAliasIsLocal? (info.names, given_spec) then
                      let
                        def elaborate_dfn dfn =
                          let (tvs, ty) = unpackType dfn in
                          let _ = checkTyVars (env, tvs, typeAnn dfn) in
                          maybePiType (tvs, checkType (env, ty))
                      in
                      let (old_decls, old_defs) = typeInfoDeclsAndDefs info in
                      let new_defs = map elaborate_dfn old_defs in
                      let new_dfn = maybeAndType (old_decls ++ new_defs, typeAnn info.dfn) in
                      info << {dfn = new_dfn}
                    else 
                      info)
                   types 

    def elaborate_local_ops (ops, env, poly?) =
      let _ = if debug? then writeLine "\n\n**** elaborate_local_ops ****\n\n" else () in
      let def elabOpDef(qid as Qualified(q, id), refine_num, ops) =
            case findAQualifierMap (ops, q, id) of
              | Some opinfo ->
                let trps = unpackTypedTerms (opinfo.dfn) in
                let (tvs, ty, tm) = nthRefinement(trps, refine_num) in
                if poly? = (tvs ~= []) then
                  let _ = checkTyVars (env, tvs, termAnn tm) in
                  let _ = if debug? then writeLine("1: "^show(head opinfo.names)) else () in
                  let ty1 = checkType1 (env, ty, if allowDependentSubTypes? then Some tm else None, true) in
                  let _ = if debug? then writeLine("elo "^show(head opinfo.names)^": "^printType ty^"\n -->\n"^printType ty1) else () in
                  let tm1 = elaborateTerm_top (env, tm, ty1) in
                  let new_dfn = maybePiAndTypedTerm(replaceNthRefinement(trps, refine_num, (tvs, ty1, tm1))) in
                  insertAQualifierMap(ops, q, id, opinfo << {dfn = new_dfn})
                 else ops
              | _ -> ops
      in
      foldl (fn (ops, el) ->
               case el of
                 | Op(qid, _, _) -> elabOpDef(qid, 0, ops)
                 | OpDef(qid, refine_num, _, _) -> elabOpDef(qid, refine_num, ops)
                 | _ -> ops)
        ops
        given_spec.elements

    def elaborate_local_props (elts, env, last_time?) =
      let _ = if debug? then writeLine "**elaborate_local_props" else () in
      map (fn el ->
           case el of
             | Property (prop_type, name, tvs, fm, a) ->
               let elaborated_fm = elaborateTerm_top (env, fm, type_bool) in
               let _ = if last_time? then checkForUnboundMetaTyVars (fm, env) else () in
               Property(prop_type, name, tvs, elaborated_fm, a)
             | _ -> el)
          elts


    def reelaborate_local_ops (ops, env) =
      let _ = if debug? then writeLine "**reelaborate_local_ops" else () in
      foldl (fn (ops,el) ->
             case el of
               | Op(Qualified(q,id), def?, _) ->
                 let Some info = findAQualifierMap(ops,q,id) in
                 insertAQualifierMap(ops,q,id, checkOp(info, def?, 0, env))
               | OpDef(Qualified(q,id), refine_num, _, _) ->
                 let Some info = findAQualifierMap(ops,q,id) in
                 insertAQualifierMap(ops,q,id, checkOp(info, true, refine_num, env))
               | _ -> ops)
         ops given_spec.elements

  in
  %% ======================================================================
  %%                           Pass One  
  %% ======================================================================
  %% Add constructors to environment
  let env_with_constrs = addConstrsEnv (initial_env, given_spec) in


  %% Elaborate types of ops
  let elaborated_ops_0 = elaborate_local_op_types (given_spec.ops,env_with_constrs) in

  %% Elaborate types
  let elaborated_types = elaborate_local_types (given_spec.types, env_with_constrs) in
  let env_with_elaborated_types = setEnvTypes (env_with_constrs, elaborated_types) in

  %% Elaborate types of ops pass 2 so that subtypes are resolved before instantiation
  % Second pass of local op types doesn't seem needed in normal cases
  %let elaborated_ops_0a = elaborate_local_op_types(elaborated_ops_0, env_with_elaborated_types) in

  let env_with_elaborated_types = setEnvOps(env_with_elaborated_types, elaborated_ops_0) in

  %% Elaborate ops (do polymorphic definitions first)
  let elaborated_ops_a = elaborate_local_ops (elaborated_ops_0, env_with_elaborated_types, true)  in
  let elaborated_ops_b = elaborate_local_ops (elaborated_ops_a, env_with_elaborated_types, false) in
  % let _ = printIncr elaborated_ops_b in

  let second_pass_env = secondPass env_with_elaborated_types in
  let elaborated_ops_c = elaborate_local_ops (elaborated_ops_b, second_pass_env, true)  in
  let elaborated_ops   = elaborate_local_ops (elaborated_ops_c, second_pass_env, false) in
  %% Elaborate properties
  let elaborated_elts = elaborate_local_props (given_spec.elements, env_with_elaborated_types, false) in

  %% ======================================================================
  %%                           Final Pass  
  %% ======================================================================

  %% sjw: 7/17/01 Added a second pass so that order is not so important
  let final_pass_env = finalPass env_with_elaborated_types in

  % let elaborated_ops = elaborate_local_op_types (elaborated_ops, final_pass_env) in
  let final_types = elaborate_local_types (elaborated_types, final_pass_env) in
  let final_ops   = reelaborate_local_ops (elaborated_ops,   final_pass_env) in
  let final_elts  = elaborate_local_props (elaborated_elts,  final_pass_env, true) in
  let final_spec  = given_spec << {types      = final_types, 
                                   ops        = final_ops, 
                                   elements   = final_elts}
  in
  %% We no longer check that all metaTyVars have been resolved,
  %% because we don't need to know the type for _
  case checkErrors final_pass_env of
    | []   -> Spec (convertPosSpecToSpec final_spec)
    | msgs -> Errors (msgs, convertPosSpecToSpec final_spec)

(* Debugging fun
op printIncr(ops: AOpMap StandardAnnotation): () =
case findAQualifierMap (ops, "Foo", "increasingNats1?") of
  | None -> ()
  | Some info -> writeLine("increasingNats1?:\n"^printTermWithTypes info.dfn)
*)

op elaboratePosTerm(tm: MSTerm, spc: Spec, vars: MSVars): MSTerm * List (String * Position) =
  let _ = initializeMetaTyVarCounter () in
  let env  = addConstrsEnv(initialEnv (spc, "string"), spc) in
  let env = foldr (fn ((id, ty), env) -> addVariable(env, id, ty)) env vars in
  let ty = freshMetaTyVar("top_tm_ty", termAnn tm) in
  let tm = elaborateTerm(env, tm, ty, []) in
  let env = finalPass env in
  let tm = elaborateTerm(env, tm, ty, []) in
  case checkErrors env of
    | [] -> (convertPTerm spc tm, [])
    | msgs -> (tm, msgs)

% ========================================================================
%% ---- called inside TYPES : PASS 0  -----
% ========================================================================

%%% Preliminary resolution
op resolveTypeNames(spc: Spec): Spec =
  mapSpecLocals (fn tm ->
                   case tm of
                     | Fun (PChoose(qid as Qualified(qual, id)), ty, pos) | qual = UnQualified ->
                       (case findAllTypes(spc, qid) of
                          | [type_info] -> Fun (PChoose(primaryTypeName type_info), ty, pos)
                          | _ ->  Fun (PChoose(Qualified(defaultQualifier spc, id)), ty, pos))
                     | Fun (PQuotient(qid as Qualified(qual, id)), ty, pos) | qual = UnQualified ->
                       (case findAllTypes(spc, qid) of
                          | [type_info] -> Fun (PQuotient(primaryTypeName type_info), ty, pos)
                          | _ ->  Fun (PQuotient(Qualified(defaultQualifier spc, id)), ty, pos))
                     | _ -> tm,
                 fn ty ->
                   case ty of
                     | Base(qid as Qualified(qual, id), ty_args, pos) | qual = UnQualified ->
                       (case findAllTypes(spc, qid) of
                          | [type_info] -> Base(primaryTypeName type_info, ty_args, pos)
                          | _ -> Base(Qualified(defaultQualifier spc, id), ty_args, pos))
                     | _ -> ty,
                 id)
    spc

def TypeChecker.checkType (env, ty) =
  checkType1(env, ty, None, true)

op checkType0(env: LocalEnv, ty: MSType): MSType =
  checkType1(env, ty, None, true)

%% Check that ty is a valid type (has a valid kind)
%% Args:
%%   env  A local environment.
%%   ty   The type to check has a valid kind.
%%   o_tm  TODO: Document what this parameter is supposed to be.
%%   checkTerms?  TODO: Document what this parameter is supposed to be.
%% Returns:
%%  A type. TODO: Document the relationship between the result and the argument ty.
op checkType1(env: LocalEnv, ty: MSType, o_tm: Option MSTerm, checkTerms?: Bool): MSType =
  %% checkType calls elaborateTerm, which calls checkType
   let _ = if debug? then writeLine("checkType: "^printType ty) else () in
  case ty of

    | TyVar _ -> ty

    | MetaTyVar (v, _) ->
      (case ! v of
         | {link = Some other_type, uniqueId, name} -> checkType1 (env, other_type, o_tm, checkTerms?)
         | _ -> ty)

    | Boolean _ -> ty

    | Base (given_type_qid, instance_types, pos) ->
      let 
        def given_type_str () =
          (printQualifiedId given_type_qid)
          ^ (case instance_types of
               | []     -> ""    
               | hd::tl -> "("^ "??" ^ (foldl (fn (str, instance_type) ->
                                               str^", "^ "??")
                                        ""
                                        tl) 
                           ^ ")")
      in
        (case findAllTypes (env.internal, given_type_qid) of
           | [] -> 
             (error (env, 
                     "Type name "^(given_type_str ())^" has not been declared", 
                     pos);
              Base (given_type_qid, instance_types, pos))

           | info :: other_infos -> 
             let _ =
                 (%% Check for errors...
                  %% Note: If multiple candidates are returned, then given_type_qid must be unqualified,
                  %%       so if some candidate has given_type_qid as an exact alias, then that
                  %%       candidate will be first in the list (see comments for findAllTypes),
                  %%       in which case choose it.
                  if ((empty? other_infos) || exists? (fn alias -> alias = given_type_qid) info.names) then
                    let (tvs, ty) = unpackFirstTypeDef info in
                    if length tvs ~= length instance_types then
                      let found_type_str =
                          (printAliases info.names)
                          ^ (case tvs of
                               | [] -> ""    
                               | hd::tl -> 
                                 "("^ hd ^ (foldl (fn (str, tv) -> str^", "^ tv) "" tl) ^ ")")
                      in                                
                      let msg = "Type reference " ^ (given_type_str ())
                                ^" does not match declared type " ^ found_type_str
                      in
                        error (env, msg, pos)
                    else 
                      %%  Normal case goes through here:
                      %%  either there are no other infos or the first info has as unqualified
                      %%   alias, and the number of type vars equals the number of instance types.
                      ()
                  else
                    %% We know that there are multiple options 
                    %% (which implies that the given_type_qid is unqualified), 
                    %% and that none of them are unqualified, so complain.
                    let candidates_str = foldl (fn (str, other_info) -> 
                                                str ^", "^  printAliases other_info.names)
                                               (printAliases info.names)
                                               other_infos
                    in
                      error (env, 
                             "Type reference " ^ (given_type_str ())
                             ^" is ambiguous among " ^ candidates_str,
                             pos))
             in
             let new_type_qid = primaryTypeName info in
             let new_instance_types = 
                 map (fn instance_type -> checkType1 (env, instance_type, o_tm, checkTerms?))
                     instance_types
             in
               if given_type_qid = new_type_qid && instance_types = new_instance_types then 
                 ty
               else 
                 Base (new_type_qid, new_instance_types, pos))

    | CoProduct (fields, pos) ->
      let nfields = map (fn (qid, None)   -> (qid, None) 
                          | (qid, Some s) -> (qid, Some (checkType1 (env, s, None, checkTerms?))))
                     fields
      in
      if nfields = fields then 
        ty
      else 
        CoProduct (nfields, pos)

    | Product (fields, pos) ->
      let nfields = map (fn (id, s) -> (id, checkType1 (env, s, None, checkTerms?))) fields in
      if nfields = fields then 
        ty
      else 
        Product (nfields, pos)

    | Quotient (given_base_type, given_relation, pos) ->
      let new_base_type = checkType1 (env, given_base_type, None, checkTerms?) in
      let new_rel_type = Arrow (Product ([("1", new_base_type), 
                                          ("2", new_base_type)], 
                                         pos), 
                                type_bool, 
                                pos) 
      in
      let new_relation = if checkTerms?
                            then elaborateTerm (env, given_relation, new_rel_type, [])
                            else given_relation
      in
      if given_base_type = new_base_type && given_relation = new_relation then 
        ty
      else 
        Quotient (new_base_type, new_relation, pos)

    | Subtype (given_super_type, given_predicate, pos) -> 
      let new_super_type = checkType1 (env, given_super_type, o_tm, checkTerms?) in
      let new_pred_type  = Arrow (new_super_type, type_bool, pos) in
      let new_predicate  = if checkTerms?
                            then elaborateTerm (env, given_predicate, new_pred_type, [])
                            else given_predicate
      in
      let new_ty = if given_super_type = new_super_type && given_predicate = new_predicate
                     then ty
                   else Subtype (new_super_type, new_predicate, pos)
      in
      new_ty

    | Arrow (t1, t2, pos) ->
      let nt1 = checkType1 (env, t1, None, checkTerms?) in
      let (dep_env, n_o_tm) = augmentDepEnv(env, o_tm, nt1) in
      let nt2 = checkType1 (dep_env, t2, n_o_tm, checkTerms?) in
      if t1 = nt1 && t2 = nt2 then 
        ty
      else 
        Arrow (nt1, nt2, pos)

    | And (tys, pos) ->
      let (new_tys, changed?) =  
          foldl (fn ((new_tys, changed?), ty) ->
                 let new_ty = checkType1 (env, ty, o_tm, checkTerms?) in
                 (new_tys ++ [new_ty],
                  changed? || (new_ty ~= ty)))
                ([], false)
                tys
      in
      if changed? then
        maybeAndType (new_tys, pos)
      else
        ty

    | Any _ -> ty

    | mystery -> 
      let _ = toScreen ("\ncheckType, Unrecognized type: " ^ (anyToString mystery) ^ "\n") in
      mystery

% ========================================================================
%% ---- called inside OPS : PASS 0  -----
% ========================================================================

def undeterminedType? ty =
  case unlinkType ty of
    | MetaTyVar _ -> true
    | _           -> false

% ========================================================================
%% ---- called inside OPS        : PASS 1 -----
%% ---- called inside PROPERTIES : PASS 1 -----
%% ---- called inside OPS        : PASS 2 -----
%% ---- called inside AXIOMS     : PASS 2 -----
%% ---- called inside CheckType 
% ========================================================================

%op TypeChecker.resolveMetaTyVar: MSType -> MSType % see TypeToTerm
def TypeChecker.resolveMetaTyVar (ty : MSType) : MSType =
  case ty of
    | MetaTyVar(tv,_) -> 
      let {name=_,uniqueId=_,link} = ! tv in
      (case link
         of None -> ty
          | Some sty -> resolveMetaTyVar sty)
    | _ -> ty

op resolveMetaTyVars: MSTerm -> MSTerm
def resolveMetaTyVars trm =
  mapTerm (id,resolveMetaTyVar,id) trm

%% elaborateTerm calls elaborateCheckTypeForTerm, 
%% which calls elaborateTypeForTerm, 
%% which calls unifyTypes, 
%%  which side-effects links for metaTyVar's via 

def fixateOneName (id_fixity : Id * Fixity, explicit_fixity : Fixity) 
  : Id * Fixity =
  (id_fixity.1, 
   case explicit_fixity of
     | Unspecified -> id_fixity.2
     | _           -> explicit_fixity)

def fixateTwoNames (q_id_fixity : Id * Id * Fixity, explicit_fixity : Fixity) 
  : Id * Id * Fixity =
  (q_id_fixity.1, 
   q_id_fixity.2, 
   case explicit_fixity of
     | Unspecified -> q_id_fixity.3
     | _           -> explicit_fixity)

op metaFiedTypeForOp (env: LocalEnv, Qualified(q, id): QualifiedId, tm: MSTerm, ty: MSType): MSType =
  case findTheOp2(env, q, id)
    | None -> checkType0(env, ty)
    | Some info -> 
      let (tvs, d_ty, tm) = unpackFirstOpDef info in
      let (_, d_ty) = metafyType (Pi (tvs, d_ty, typeAnn d_ty)) in
      elaborateCheckTypeForOpRef(env, tm, d_ty, ty)

def resolveNameFromType(env, trm, id, ty, pos) =
  case mkEmbed0 (env, ty, id) of
    | Some qid -> Fun (Op (qid, Constructor0), metaFiedTypeForOp(env, qid, trm, ty), pos)
    | None -> 
  case mkEmbed1 (env, ty, trm, id, pos) of
    | Some term -> term
    | None ->
  case uniqueConstr (env, trm, id, ty, pos) of
    | Some term -> term
    | _ ->
  case StringMap.find (env.constrs, id) of
    | None -> undeclaredName (env, trm, id, ty, pos)
    | _    -> ambiguousCons (env, trm, id, ty, pos)

% op findConstrsWithName(env: LocalEnv, trm: MSTerm, id: Id, ty: MSType, pos: Position): MSTerms =
%   case mkEmbed0 (env, ty, id) of
%     | Some qid -> [Fun (Op (qid, Constructor0), checkType0 (env, ty), pos)]
%     | None -> 
%   case mkEmbed1 (env, ty, trm, id, pos) of
%     | Some term -> [term]
%     | None ->
%   case uniqueConstr (env, trm, id, pos) of
%     | Some term -> [term]
%     | _ ->
%   case StringMap.find (env.constrs, id) of
%     | None -> []
%     | Some constrs -> mapPartial (fn (coprod_qid, coprod_ty) -> constrTerm(env, id, coprod_qid, coprod_ty, trm, pos)) constrs


op tryResolveNameFromType(env: LocalEnv, trm:MSTerm, id: String, ty: MSType, pos: Position): Option MSTerm =
  case mkEmbed0 (env, ty, id) of
    | Some qid -> Some(Fun (Op (qid, Constructor0), metaFiedTypeForOp(env, qid, trm, ty), pos))
    | None -> mkEmbed1 (env, ty, trm, id, pos) 

op checkOp (info: OpInfo, def?: Bool, refine_num: Nat, env: LocalEnv): OpInfo =
 % let _ = if info.names = [Qualified(UnQualified, "test")] then writeLine("checkOp 0:\n"^printTermWithTypes (info.dfn)) else () in
 let _ = if debug? then writeLine("checkOp "^show (finalPass? env)^" "^show(head info.names)) else () in
 let trps = unpackTypedTerms (info.dfn) in
 let (tvs, ty0, def_tm) = nthRefinement(trps, refine_num) in

 % We need to always check the type.
 % Consider the following elements:
 %  op foo : Nat  
 %  refine def foo : {x : Nat | x = undeclared_op}
 % If fail to check the "refine def", we'll miss the reference to an undeclared op.
 let ty = checkType1 (env, ty0, if allowDependentSubTypes? then Some def_tm else None, true) in

 let elaborated_def_tm = if def? && ~(anyTerm? def_tm)
                           then elaborateTerm_top (env, def_tm, ty)
                           else def_tm
 in
 let tvs_used = collectUsedTyVars (ty, info, elaborated_def_tm, env) in
 let new_tvs =
     if empty? tvs then
       tvs_used
     else if equalTyVarSets?(tvs_used, tvs) then
       tvs  (* Probably correct ;-*)
     else 
       (error (env, 
               "mismatch between bound vars [" ^ (foldl (fn (s, tv) -> s ^ " " ^ tv) "" tvs) ^ "]"
               ^            " and free vars [" ^ (foldl (fn (s, tv) -> s ^ " " ^ tv) "" tvs_used) ^ "]"
               ^ " for op "^show(head info.names),
               termAnn def_tm);
        tvs)
 in
 let new_dfn = maybePiAndTypedTerm(replaceNthRefinement(trps, refine_num, (new_tvs, ty, elaborated_def_tm))) in
 let _ = if debug? then writeLine("resulting term\n"^printTermWithTypes new_dfn^"\n") else () in
 % let _ = if info.names = [Qualified(UnQualified, "test")]  then writeLine("checkOp test\n"^printTermWithTypes def_tm^"\n"^printTermWithTypes elaborated_def_tm) else () in
 info << {dfn = new_dfn}

op augmentDepEnv(env: LocalEnv, o_tm: Option MSTerm, dom_ty: MSType): LocalEnv * Option MSTerm =
  %% For handling dependent types in definition
  case o_tm of
    | Some(Lambda([(pat, _, bod)], pos)) ->
      let alpha = freshMetaTyVar ("Lambda_0", pos) in
      let (_, env) = elaboratePattern (env, pat, alpha) in
      (env, Some bod)
    | Some(Pi(_, tm1, _)) -> augmentDepEnv(env, Some tm1, dom_ty)
    | Some(And(tm1::_, _)) -> augmentDepEnv(env, Some tm1, dom_ty)
    | Some(Any _) ->
      (case dom_ty of
         | Subtype(_, Lambda([(pat, _, _)], _), pos) ->
           let alpha = freshMetaTyVar ("Lambda_0", pos) in
           let (_, env) = elaboratePattern (env, pat, alpha) in
           (env, None)
         | _ -> (env, None))
    | _ -> (env, None)

%%% Bound to false in swe in toplevel.lisp because not a problem with the interpreter
op complainAboutImplicitPolymorphicOps?: Bool = true

op collectUsedTyVars (ty: MSType, info: OpInfo, dfn: MSTerm, env: LocalEnv): List TyVar =
  let tv_cell = Ref [] : Ref TyVars in
  let incomplete? = Ref false in
  let 

    def insert tv = 
      tv_cell := ListUtilities.insert (tv, ! tv_cell) 

    def scan ty = 
      case ty of
        | TyVar     (tv,      _) -> insert tv
        | Product   (fields,  _) -> app (fn (_, s)      -> scan s)           fields
        | CoProduct (fields,  _) -> app (fn (_, Some s) -> scan s | _ -> ()) fields
        | Subtype   (s, _,    _) -> scan s
        | Quotient  (s, _,    _) -> scan s
        | Arrow     (s1, s2,  _) -> (scan s1; scan s2)
        | Base      (_, tys, _) -> app scan tys
        | Boolean              _ -> ()
        | MetaTyVar (mtv,     _) -> 
          (let {name = _, uniqueId, link} = ! mtv in
           case link of
             | Some s -> scan s
             | None -> incomplete? := true)
        | And (tys, _) -> app scan tys
        | Any _ -> ()

  in                        
    let _ = scan ty in
    let _ = if !incomplete? && complainAboutImplicitPolymorphicOps? then
              error (env, 
                     "Incomplete type for op " ^ (printQualifiedId (primaryOpName info)) ^ ":\n" ^(printType ty), 
                     termAnn dfn)
             else ()
    in
    ! tv_cell

(*
op collectUsedTyVars (ty: MSType, info: OpInfo, dfn: MSTerm, env: LocalEnv): List TyVar =
  let tv_cell = Ref [] : Ref TyVars in
  let incomplete? = Ref false in
  let 

    def insert tv = 
      tv_cell := ListUtilities.insert (tv, ! tv_cell) 

    def check_ty ty = 
      case ty of
        | TyVar     (tv,      _) -> insert tv
        | Boolean              _ -> ()
        | MetaTyVar (mtv,     _) -> 
          (let {name = _, uniqueId, link} = ! mtv in
           case link of
             | Some s -> ()
             | None -> incomplete? := true)
        | _ -> ()

  in                        
    let _ = appTerm (id, check_ty, id) info.dfn in
    let _ = if !incomplete? && complainAboutImplicitPolymorphicOps? then
              error (env, 
                     "Incomplete type for op " ^ (printQualifiedId (primaryOpName info)) ^ ":\n" ^(printType ty), 
                     termAnn dfn)
             else ()
    in
    ! tv_cell
*)

op checkForUnboundMetaTyVars(tm: MSTerm, env: LocalEnv): () =
  let warned? = Ref false in
  let def cType ty =
        case ty of
          | MetaTyVar (mtv,     _) -> 
            (let {name = _, uniqueId, link} = ! mtv in
               case link of
                 | None | ~ (!warned?) ->
                   (error (env, 
                           "Incomplete type for " ^ (printTerm tm) ^ ":\n" ^(printType ty), 
                           termAnn tm);
                    warned? := true)
                 | _ -> ())
          | _ -> ()
  in                        
    appTerm (fn _ -> (), cType, fn _ -> ()) tm

op ambiguousTerm?(tm: MSTerm): Bool =
  let def ambig?(tm, count) =
        if count = 0 then false
          else
            let count = count - 1 in
            case tm of
              | Fun(OneName _, _, _) -> true
              | ApplyN(tms, _) -> exists? (fn tm -> ambig?(tm, count)) tms
              | Record(id_prs, _) -> exists? (fn (_, tm) -> ambig?(tm, count)) id_prs
              | Var((nm, ty), _) -> undeterminedType? ty
              % | Lambda(matches, _) -> exists? (fn (_, _, tm) -> ambig?(tm, count)) matches
              | _ -> false
  in
  ambig?(tm, 2)

def elaborateTerm_top (env, trm, term_type) =
  let trm = elaborateTerm (env, trm, term_type, []) in
  %% Resolve now rather than later to release space
  resolveMetaTyVars trm

%% elaborateTerm typechecks and elaborates a term to the simpler core representation.
%% Arguments:
%%   env  The environment, which is a record with a bunch of fields, which
%%        TODO needs to be documented.
%%   trm  The term to be typechecked.
%%   term_type  The expected type.
%%   args       Local arguments used for their types (not sure why this is necessary).
op elaborateTerm(env:LocalEnv, trm:MSTerm, term_type:MSType, args:MSTerms):MSTerm = 
  let _ = if debug? then writeLine("tc"^show env.passNum^" "^printType term_type^"\n"^printTermWithTypes trm) else () in
  let typed_term =
        case trm of
          | Fun (Op(qid, fixity), ty, pos) ->
            let _ = elaborateCheckTypeForTerm (env, trm, ty, term_type) in
            trm
          | Fun (OneName (id, fixity), ty, pos) ->
            (let _ = elaborateCheckTypeForTerm (env, trm, ty, term_type) in
             %let _ = if id = "getBits" then writeLine("et0: getBits: "^printType ty) else () in
             %% resolve type from environment
             % let _ = writeLine("Trying to resolve name "^id^": "^printType ty) in
             case findVar(env, id, pos) of
               | Some(term as Var ((id, ty), a)) ->
                 let ty = elaborateCheckTypeForTerm (env, term, ty, term_type) in
                 Var ((id, ty), pos)
               | None ->
             case tryResolveNameFromType(env, trm, id, ty, pos) of
               | Some t -> t
               | _ ->
             case findVarOrOps (env, id, pos) % ++ findConstrsWithName (env, trm, id, ty, pos)
               of
               | terms as _::_ ->
                 %% selectTermWithConsistentType calls consistentTypeOp?, which calls unifyTypes
                 % let _ = if id = "foldable?" then (writeLine("foldable?:"); app (fn tm -> writeLine(printTerm tm)) terms) else () in
                 (case selectTermWithConsistentType (env, id, pos, terms, term_type) of
                    | None -> trm
                    | Some term ->
                      let ty = termType term in
                      % let _ = if id = "getBits" then writeLine("et1: getBits: "^printType ty) else () in
                      let ty = if hasFreeVarsInSubty? ty && args ~= []
                                 then tryInstantiateDepVars(env, term, ty, args)
                               else ty
                      in
                      let ty = elaborateCheckTypeForTerm (env, term, ty, term_type) in
                      % let _ = if id = "getBits" then writeLine("et1a: getBits: "^printType ty) else () in
                      (case term of
                         | Var ((id, _),          pos) -> Var ((id, ty),         pos)  % Now handled above
                         | Fun (OneName  idf,  _, pos) -> Fun (OneName  (fixateOneName  (idf,  fixity)), ty, pos)
                         | Fun (TwoNames qidf, _, pos) -> Fun (TwoNames (fixateTwoNames (qidf, fixity)), ty, pos)
                         | Fun (Embed _, _, _)         -> term
                         | _ -> System.fail "Variable or constant expected"))
               | [] ->
                 resolveNameFromType (env, trm, id, ty, pos))

          | Fun (TwoNames (id1, id2, fixity), ty, pos) -> 
            (let ty = elaborateCheckTypeForOpRef (env, trm, ty, term_type) in
             %% Either Qualified (id1, id2) or field selection
             case findTheOp2 (env, id1, id2) of
               | Some info -> 
                 if finalPass? env && groundType? ty && fixity = info.fixity
                   then Fun (TwoNames (id1, id2, fixity), ty, pos)
                 else
                 %% If Qualified (id1, id2) refers to an op, use the canonical name for that op.
                 let Qualified (q, id) = primaryOpName info in
                 let (tvs, d_ty, tm) = unpackFirstOpDef info in
                 let (_, d_ty) = metafyType (Pi (tvs, d_ty, typeAnn d_ty)) in
                 let term = Fun (TwoNames (q, id, info.fixity), d_ty, pos) in
                 let d_ty = if hasFreeVarsInSubty? d_ty && args ~= []
                              then tryInstantiateDepVars(env, term, d_ty, args)
                            else d_ty
                 in
                 let d_ty = elaborateCheckTypeForOpRef (env, term, d_ty, ty) in
                 (case term of
                    | Fun (TwoNames xx, _, pos) -> Fun (TwoNames xx, d_ty, pos)
                    | _ -> System.fail ("Op expected for elaboration of "^id1^"."^id2^" as resolved to "^q^"."^id))
               | None -> 
                 %% If Qualified (id1, id2) does not refer to an op, check for field selection
                 (case findVarOrOps (env, id1, pos) of
                    | [big_term] ->      % Must be a projection
                      %% unqualified id1 refers to big_term
                      % let _ = writeLine("twonames: "^id1^"."^id2^" "^printTerm big_term) in
                      let big_type = termType big_term in
                      let big_type = checkType (env, big_type) in
                      let 
                        def projectRow (big_term, big_type, row, id2) =
                          %% See if id2 is one of the field selectors for the big type.
                          case row of
                            | [] -> undeclared2 (env, trm, id1, id2, term_type, pos)
                            | (field_id, field_type) :: row -> 
                              if id2 = field_id then
                                let field_type = checkType (env, field_type) in
                                let projector = Fun (Project id2, Arrow (big_type, field_type, pos), pos) in
                                let projection = ApplyN ([projector, big_term], pos) in
                                let _ = elaborateTypeForTerm (env, projection, field_type, term_type) in
                                projection
                              else
                                projectRow (big_term, big_type, row, id2)
                        def getProduct ty : Option (List (String * MSType)) = 
                          (case unfoldType (env, ty) of
                             | Product (row,       _) -> Some row
                             | Subtype (ty, pred, _) -> getProduct ty
                             | _ -> None)
                      in          
                        %% See if big_term is a product or a subtype of a product
                        (case getProduct big_type of
                           | Some row -> projectRow (big_term, big_type, row, id2)
                           | _ ->
                             %% Specware gives up on type of field
                             %% Accord checks to see if id2 refers to a function whose domain is big_type
                             ApplyN([Fun(Project id2, Arrow (big_type, freshMetaTyVar("Field", pos), pos), pos), big_term], pos))
                    | [] -> 
                      %% both id1.id2 id1 fail to refer to anything
                      undeclared2 (env, trm, id1, id2, term_type, pos)
                    | big_terms ->
                      %% id1 is ambiguous
                      %% Specware just reports an error here
                      %% Accord checks to see if id2 (id1) typechecks
                      undeclared2 (env, trm, id1, id2, term_type, pos)))

          | Fun (Embed (qid as Qualified(_,id), _), ty, pos) -> 
            let _  (* ty *) = elaborateCheckTypeForTerm (env, trm, ty, term_type) in
            %% using term_type instead of ty in the following was cause of bug 110 : "[] read as bogus Nil"
            resolveNameFromType (env, trm, id, ty, pos) 

          | Fun (Project id,ty,pos) -> 
            let ty = elaborateCheckTypeForTerm (env, trm, ty, term_type) in
            (case mkProject (env,id,ty,pos) of
               | Some term -> term
               | None -> undeclaredResolving (env,trm,id,term_type,pos))

        % | Fun (Select id,ty,pos) -> Fun (Select id,ty,pos)      (*** Not checked ***)
          | Fun (Embedded(qid as Qualified(q, id)), ty, pos) ->
            let a = freshMetaTyVar ("Embedded", pos) in
            let ty1 = Arrow(a, type_bool, pos) in
            (elaborateTypeForTerm (env, trm, ty1, term_type);
             elaborateTypeForTerm (env, trm, ty, ty1);
             let qid =
                 case unfoldType (env, ty) of
                    | Arrow (dom, _, _) -> 
                      (case isCoproduct (env, dom) of
                         | Some fields -> 
                           if exists? (fn (qid2, _) -> qid = qid2) fields then
                             qid
                           else
                             (case findLeftmost (fn (Qualified(_, id2), _) -> id = id2 && q = UnQualified) fields of
                                | Some(qid2, _) -> qid2
                                | _ -> 
                                  (error (env, 
                                          "Name "^show qid^" is not among the constructors of "^ printType dom, 
                                          pos); qid))
                         | None -> 
                           (pass2Error (env, dom, 
                                       newLines ["Sum type with constructor "^show qid^" expected", 
                                                 "found instead "^printType dom], 
                                        pos);
                            qid))
                    | _ -> (pass2Error (env, ty, "Function type expected ", pos); qid)
             in
             Fun (Embedded qid, ty, pos))

          | Fun (PChoose qid, ty, pos) -> 
            %% Has type:  {f: base_type -> result_type | fa(m,n) equiv(m,n) => f m = f n} -> quot_type -> result_type
            %%   quot_type -- quotient type referenced by qid
            %%   equiv     -- equivalence relation in definition of quot_type
            (case findTheType (env.internal, qid) of
               | Some info ->
                 (case unpackFirstTypeDef info of
                    | (tvs, Quotient (base_body, equiv, _)) ->
                      %% In general, base_body and equiv will have free references to tvs
                      let base_type             = Pi (tvs, base_body, noPos)                      in
                      let (new_mtvs, base_type) = metafyType base_type                            in
                      let base_body             = typeInnerType base_type                         in
                      let new_type_args         = map (fn mtv -> MetaTyVar (mtv, noPos)) new_mtvs in
                      let quot_type             = Base (qid, new_type_args, noPos)                in
                      let result_type           = freshMetaTyVar ("PChoose_result", pos)          in
                      let high_arrow            = Arrow (quot_type, result_type, pos)             in
                      %% --
                      let low_arrow             = Arrow (base_type, result_type, pos)             in
                      let fvar = ("f",low_arrow) in
                      let mvar = ("m",base_type) in
                      let nvar = ("n",base_type) in
                      let lhs  = mkAppl (equiv, [mkVar mvar, mkVar nvar]) in % free refs to tvs
                      let rhs  = mkEquality (result_type, 
                                             mkApply (mkVar fvar, mkVar mvar),
                                             mkApply (mkVar fvar, mkVar nvar)) 
                      in
                      let body = mkBind (Forall,[mvar, nvar], mkImplies (lhs, rhs)) in  % free refs to tvs
                      let restricted_low_arrow  = Subtype (low_arrow, mkLambda (mkVarPat fvar, body), pos) in  % free refs to tvs
                      %% --
                      let lifting_arrow         = Arrow (restricted_low_arrow, high_arrow, pos)            in  % free refs to tvs
                      (elaborateTypeForTerm (env, trm, lifting_arrow, term_type);
                       elaborateTypeForTerm (env, trm, ty,           lifting_arrow);
                       %% now ty = term_type = lifting_arrow
                       Fun (PChoose qid, ty, pos))

                    | _ ->
                      let ss = show qid in
                      (error (env, 
                              "In choose[" ^ ss ^ "], " ^ ss ^ " refers to a type that is not a quotient",
                              pos);
                       Fun (PChoose qid, ty, pos)))
               | _ ->
                 let ss = show qid in
                 (error (env, 
                         "In choose[" ^ ss ^ "], " ^ ss ^ " does not refer to a type",
                         pos);
                  Fun (PChoose qid, ty, pos)))


          | Fun (PQuotient qid, ty, pos) ->  
            %% Has type:   base_type -> Quotient(base_type, equiv)
            %%   quot_type -- quotient type referenced by qid
            %%   equiv     -- equivalence relation in definition of quot_type
            (case findTheType (env.internal, qid) of
               | Some info ->
                 (case unpackFirstTypeDef info of
                    | (tvs, Quotient (base_body, equiv, _)) ->
                      %% In general, base_body and equiv will have free references to the tvs
                      let base_type             = Pi (tvs, base_body, noPos)                      in
                      let (new_mtvs, base_type) = metafyType base_type                            in
                      let new_type_args         = map (fn mtv -> MetaTyVar (mtv, noPos)) new_mtvs in
                      let quot_type             = Base (qid, new_type_args, noPos)                in              
                      let lifting_arrow         = Arrow (base_type, quot_type, pos)               in
                      (elaborateTypeForTerm (env, trm, lifting_arrow, term_type);
                       elaborateTypeForTerm (env, trm, ty,           lifting_arrow);
                       %% now ty = term_type = lifting_arrow
                       Fun (PQuotient qid, ty, pos))
                    | _ ->
                      let ss = show qid in
                      (error (env, 
                              "In quotient[" ^ ss ^ "], " ^ ss ^ " refers to a type that is not a quotient",
                              pos);
                       Fun (PQuotient qid, ty, pos)))
               | _ ->
                 let ss = show qid in
                 (error (env, 
                         "In quotient[" ^ ss ^ "], " ^ ss ^ " does not refer to a type",
                         pos);
                  Fun (PQuotient qid, ty, pos)))

          | Fun (Bool b, ty, pos) -> 
            (elaborateTypeForTerm (env, trm, type_bool, term_type) ; 
             elaborateCheckTypeForTerm (env, trm, ty, type_bool);
             Fun (Bool b, ty, pos))

          | Fun (Nat n, ty, pos) ->  
            (elaborateTypeForTerm (env, trm, type_nat, term_type);
             elaborateCheckTypeForTerm (env, trm, ty, type_nat);
             Fun (Nat n, ty, pos))

          | Fun (String s, ty, pos) -> 
            (elaborateTypeForTerm (env, trm, type_string, term_type);
             elaborateCheckTypeForTerm (env, trm, ty, type_string);
             Fun (String s, ty, pos))

          | Fun (Char ch, ty, pos) -> 
            (elaborateTypeForTerm (env, trm, type_char, term_type);
             elaborateCheckTypeForTerm (env, trm, ty, type_char);
             Fun (Char ch, ty, pos))

          | Var ((id, ty), pos) -> 
            let ty = elaborateCheckTypeForTerm (env, trm, ty, term_type) in
            Var ((id, ty), pos)

          | LetRec (decls, body, pos) -> 
            let 
              def declareFun (((id, ty), bdy), env) = 
                addVariable (env, id, ty)

              def elaborateDecl env ((id, ty), bdy) = 
                let terms = findVarOrOps (env, id, pos) in
                let ty = checkType(env, ty) in
                let bdy = elaborateTerm (env, bdy, ty, []) in
                ((id, ty), bdy)
            in
            let env = foldr declareFun env decls in
            let decls = map (elaborateDecl env) decls in
            let bdy = elaborateTerm (env, body, term_type, args) in
            LetRec (decls, bdy, pos)

          | Let (decls, body, pos) -> 
            let env0 = env in
            let 
              def doDeclaration ((pat, bdy), (decls, env)) = 
                let alpha = freshMetaTyVar ("Let", pos) in
                (* In case the pattern is has a type constraint, move
                   this to the body such that the type constraint is 
                   attatched to alpha.
                   *)
                let (pat, bdy) = 
                    case pat of
                      | TypedPat (pat, ty, pos) -> 
                        (pat, (TypedTerm (bdy, ty, pos)):MSTerm)
                      | _ -> (pat, bdy)
                in             
                let bdy = elaborateTerm (env0, bdy, alpha, []) in
                let (pat, env) = elaboratePattern (env, pat, alpha) in
                (Cons ((pat, bdy), decls), env)
              def maybeRedoDeclaration ((pat, bdy), decls) =
                let new_bdy = if false && ambiguousTerm? bdy
                               then elaborateTerm (env0, bdy, patternType pat, [])
                               else bdy
                in
                (pat, new_bdy) :: decls
            in         
            let (decls, body_env) = foldr doDeclaration ([], env) decls in
            let body = elaborateTerm (body_env, body, term_type, args) in
            let decls = foldr maybeRedoDeclaration [] decls in
            Let (decls, body, pos)

          | IfThenElse (test, thenTrm, elseTrm, pos) -> 
            let test = elaborateTerm (env, test, type_bool, []) in
            let thenTrm = elaborateTerm (env, thenTrm, term_type, args) in 
            let elseTrm = elaborateTerm (env, elseTrm, term_type, args) in
            IfThenElse (test, thenTrm, elseTrm, pos)

          | Record (row, pos) -> 
            let 
              def unfoldConstraint (ty) = 
                (case unfoldType (env, ty) of
                   | Product (rows, _) -> 
                     (if ~(length (row) = length (rows)) then
                        error (env, 
                               newLines [printTerm trm, "is incompatible with constraint", printType term_type], 
                               pos)
                      else 
                        ();
                      rows)
                   | MetaTyVar (mtv, _) ->
                     let row = map (fn (id, _)-> (id, freshMetaTyVar ("Record", pos))) row in
                     (linkMetaTyVar mtv ((Product (row, pos)));
                      row)

                   | Subtype (ty, term, _) -> 
                     unfoldConstraint (ty)        

                   | And (ty :: _, _) -> % TODO: be smarter about choosing among alternatives
                     unfoldConstraint ty        

                   | sv -> 
                     (pass2Error (env, 
                                  sv, 
                                  printTerm trm^" is constrained to be of an incompatible type "^newline^ printType term_type, 
                                  pos);
                      map (fn (id, _)-> (id, freshMetaTyVar ("Record_incompatible", pos))) row))
            in
            let tyrows = unfoldConstraint (term_type) in
            if length tyrows ~= length row
              then (error(env, "Mismatch in number of fields", pos);
                    Record (row, pos))
            else
            let trow = zip (row, tyrows) in 
            let row = map (fn ((id, t), (id2, ty))->
                           if id = id2 then
                             (id, elaborateTerm (env, t, ty, []))
                           else 
                             (error (env, "Field-name "^id^
                                     " is not the one imposed by type constraint.  Expected field-name is: "^
                                     id2, pos);
                              (id, t)))
                          trow
            in
              Record (row, pos)

          | Lambda (rules, pos) -> 
            let alpha = freshMetaTyVar ("Lambda_a", pos) in
            let beta  = freshMetaTyVar ("Lambda_b", pos) in
            let ty    = (Arrow (alpha, beta, pos)) in
            let _     = elaborateType (env, ty, term_type) in
            % let _ = if debug1? then writeLine("lambda term_type: "^printType term_type^"\nty: "^printType ty) else () in
            Lambda (map (fn (pat, cond, term)->
                         let (pat, env) = elaboratePattern (env, pat, alpha) in
                         let term = elaborateTerm (env, term, beta, []) in
                         let cond = elaborateTerm (env, cond, type_bool, []) in
                         (pat, cond, term)) 
                        rules,
                   pos)

          | The ((id,ty), term, pos) ->
            let ty = checkType(env, ty) in
            let env = addVariable (env,id,ty) in
            let _ = elaborateType (env, ty, term_type) in
            let term = elaborateTerm (env, term, type_bool, []) in
            The ((id,ty), term, pos)

          | Bind (bind, vars, term, pos) ->
            let _ = elaborateType (env, term_type, type_bool) in
            let (vars, env) = 
                foldl (fn ((vars, env), (id, ty)) ->
                       let ty = checkType (env, ty) in
                       (Cons ((id, ty), vars), 
                        addVariable (env, id, ty)))
                      ([], env) 
                      vars 
            in
            let vars = reverse vars in
            Bind (bind, vars, elaborateTerm (env, term, term_type, []), pos)

          | TypedTerm (term, ty, _) ->
            let ty  = elaborateType (env, ty, term_type) in
            let term = elaborateTerm (env, term, ty, args) in
            term

          | Seq (terms, pos) -> 
            let
              def elab ts = 
                case ts of
                  | [] -> []
                  | [t] -> [elaborateTerm (env, t, term_type, args)]
                  | (t::ts) -> 
                    let alpha = freshMetaTyVar ("Seq", pos) in
                    let t = elaborateTerm (env, t, alpha, []) in
                    Cons (t, elab ts)
            in
              Seq (elab terms, pos)

          | ApplyN ([t1 as Fun (Embedded _, _, _), t2], pos) -> 
            let alpha = freshMetaTyVar ("ApplyN_Embedded", pos) in
            let ty    = Arrow (alpha, term_type, pos) in
            let t2    = elaborateTerm (env, t2, alpha, []) in
            let t1    = elaborateTerm (env, t1, ty, t2::args) in
            ApplyN ([t1, t2], pos)

          | ApplyN ([t1 as Fun (Project _, _, _), t2], pos) -> 
            let alpha = freshMetaTyVar ("ApplyN_Project", pos) in
            let ty    = Arrow (alpha, term_type, pos) in
            let t2    = elaborateTerm (env, t2, alpha, []) in
            let t1    = elaborateTerm (env, t1, ty, t2::args) in
            ApplyN ([t1, t2], pos)

          | ApplyN ([t1 as Fun (f1, s1, _), t2], pos) -> 
            let (t1, t2) =
                if notFinalPass? env %&& ~(embed? Lambda t2)
                  then
                    let alpha = freshMetaTyVar ("ApplyN_Fun", pos) in
                    let ty    = Arrow (alpha, term_type, pos) in
                    % let _ = case f1 of OneName("getBits", _) -> writeLine("getBits: "^printType ty) | _ -> () in
                    let t2    = elaborateTerm (env, t2, alpha, []) in
                    let t1    = if false  %embed? Arrow (unlinkType alpha)
                                  then let term_ty = Arrow (freshMetaTyVar("ApplyN_HOFun", pos), term_type, pos) in
                                       let t1 = elaborateTerm_head (env, t1, term_ty, trm, t2::args) in
                                       let _ = elaborateTypeForTerm(env, t1, ty, term_ty) in
                                       t1
                                  else elaborateTerm_head (env, t1, ty, trm, t2::args)
                    in
                    %% Repeated for help in overload resolution once argument type is known
                    if false && ambiguousTerm? t2 then
                      let t2 = elaborateTerm (env, t2, alpha, []) in
                      % let t1  = case t1 of
                      %             | Fun(OneName _,_,_) -> elaborateTerm (env, t1, ty, t2::args)
                      %             | _ -> t1
                      % in
                      (t1, t2)
                    else (t1, t2)
                  else
                    let alpha = if notFinalPass? env
                                 then freshMetaTyVar("ApplyN_Fun", pos)
                                 else case maybeInferType (env.internal, t2) of
                                        | Some ty -> ty
                                        | None -> freshMetaTyVar("ApplyN_Fun", pos)
                    in
                    let ty    = Arrow (alpha, term_type, pos) in
                    let t1 = elaborateTerm_head (env, t1, ty, trm, t2::args) in
                    let t2 = elaborateTerm (env, t2, alpha, []) in
                    (t1, t2)
            in
            %% This is same effect as old code, but restructured
            %% so it's easier to intercept the XML references
            if notFinalPass? env then
              ApplyN ([t1, t2], pos)
            else if f1 = Equals then
              %let t1 = adjustEqualityType (env, s1, t1, t2) in
              ApplyN ([t1, t2], pos)
            else if f1 = NotEquals then
              %let t1 = adjustEqualityType (env, s1, t1, t2) in
              ApplyN ([t1, t2], pos)
            else
              ApplyN ([t1, t2], pos)

          | ApplyN ([t1, t2], pos) ->
            let alpha = freshMetaTyVar ("ApplyN_2", pos) in
            let ty    = Arrow (alpha, term_type, pos) in
            let t2    = elaborateTerm (env, t2, alpha, []) in
            let t1    = elaborateTerm (env, t1, ty, t2::args) in
            ApplyN ([t1, t2], pos)

          %% Allow for partially type-checked terms
          | Apply(t1, t2, pos) -> elaborateTerm (env, ApplyN ([t1, t2], pos), term_type, args)

          | ApplyN (terms, pos) ->
            let 
              def tagTermWithInfixInfo (term : MSTerm) : FixatedTerm =
                case term of
                  | Fun (OneName (_,  Nonfix),  _, pos) -> Nonfix term
                  | Fun (OneName (_,  Infix p), _, pos) -> Infix (term, p)
                  | Fun (OneName ("Cons",  _), _, pos) -> Infix(term, (Right, 24))
                  | Fun (OneName (id, _),       _, pos) ->
                    (case consistentTag (findVarOrOps (env, id, pos)) of
                       | (true, (Some p)) -> Infix (term, p)
                       | (true, _)      -> Nonfix term
                       | _ ->
                         (error (env, "ERROR: Inconsistent infix information for overloaded op: " ^ id,
                                 pos);
                          Nonfix term))
                  | Fun (TwoNames (_ , _, Nonfix),  _, pos) -> Nonfix term
                  | Fun (TwoNames (_ , _, Infix p), _, pos) -> Infix (term, p)
                  | Fun (TwoNames (id1, id2, _),    _, pos) ->
                    %% If, due to union semantics, findOps always returns 0 or 1 hits for Q.Id, 
                    %% then consistentTag will necessarily return (true, priority).
                    (case findTheOp2 (env, id1, id2) of
                       | Some info ->
                         (case info.fixity of
                            | Infix p -> Infix  (term, p)
                            | _ -> Nonfix term)
                       | _                    -> Nonfix term)
                  | Fun (And,       _, _) -> Infix (term, (Right, 15))
                  | Fun (Or,        _, _) -> Infix (term, (Right, 14))
                  | Fun (Implies,   _, _) -> Infix (term, (Right, 13))
                  | Fun (Iff,       _, _) -> Infix (term, (Right, 12))
                  | Fun (Equals,    _, _) -> Infix (term, (Left, 20))
                  | Fun (NotEquals, _, _) -> Infix (term, (Left, 20))
                  | Fun (RecordMerge,_,_) -> Infix (term, (Left, 25))
                  | _ -> Nonfix term
            in 
            let term = resolveInfixes (Some env, tagTermWithInfixInfo, pos, terms) in
            let new = elaborateTerm (env, term, term_type, args) in
            new

          %% These should only appear as the head of an apply (see one of the ApplyN cases above):
          | Fun (Not,       ty, pos) -> (error (env, cantuse "~",   pos); trm)
          | Fun (And,       ty, pos) -> (error (env, cantuse "&&",  pos); trm)
          | Fun (Or,        ty, pos) -> (error (env, cantuse "||",  pos); trm)
          | Fun (Implies,   ty, pos) -> (error (env, cantuse "=>",  pos); trm)
          | Fun (Iff,       ty, pos) -> (error (env, cantuse "<=>", pos); trm)
          | Fun (Equals,    ty, pos) -> (error (env, cantuse "=",   pos); trm)
          | Fun (NotEquals, ty, pos) -> (error (env, cantuse "~=",  pos); trm)

          | And (tms, pos) -> And (map (fn tm -> elaborateTerm(env, tm, term_type, args)) tms, pos)
          | term -> (%System.print term;
                     term)
  in
  let _ = if debug? then writeLine("-->\n"^printTermWithTypes typed_term) else () in
  typed_term

def cantuse inbuilt = "Can't use inbuilt operator '"^inbuilt^"' as an expression -- use '("^inbuilt^")' instead."

op elaborateTerm_head (env: LocalEnv, t1: MSTerm, ty0: MSType, trm: MSTerm, args: MSTerms): MSTerm =
  case t1 of
    | Fun (Not, ty1, pos) -> 
      (elaborateTypeForTerm (env, trm, ty1, ty0);
       Fun (Not, ty1, pos))

    | Fun (And, ty1, pos) -> 
      (elaborateTypeForTerm (env, trm, ty1, ty0);
       Fun (And, ty1, pos))

    | Fun (Or, ty1, pos) -> 
      (elaborateTypeForTerm (env, trm, ty1, ty0);
       Fun (Or, ty1, pos))

    | Fun (Implies, ty1, pos) -> 
      (elaborateTypeForTerm (env, trm, ty1, ty0);
       Fun (Implies, ty1, pos))

    | Fun (Iff, ty1, pos) -> 
      (elaborateTypeForTerm (env, trm, ty1, ty0);
       Fun (Iff, ty1, pos))

    | Fun (Equals, ty1, pos) -> 
      (elaborateTypeForTerm (env, trm, ty1, ty0);
       Fun (Equals, ty1, pos))

    | Fun (NotEquals, ty1, pos) -> 
      (elaborateTypeForTerm (env, trm, ty1, ty0);
       Fun (NotEquals, ty1, pos))

    | Fun (RecordMerge, ty1, pos) ->
      % let _ = writeLine("<< ty: "^printType ty1^"\n"^printType ty0) in
      (let a = freshMetaTyVar ("RecordMerge_a", pos) in
       let b = freshMetaTyVar ("RecordMerge_b", pos) in
       let c = freshMetaTyVar ("RecordMerge_c", pos) in
       let fresh_merge_type = Arrow(Product ([("1", a), ("2", b)], pos), c, pos) in
       (elaborateTypeForTerm(env, trm, ty1, fresh_merge_type);
        
        %elaborateTypeForTerm(env, trm, fresh_merge_type, ty0);
        let def notEnoughInfo() =
              if notFinalPass? env then 
                t1
              else 
                (error(env, "Can't determine suitable type for <<: " ^ printType ty1, pos);
                 t1)
        in
        case isArrow(env,ty1) of
          | Some (dom,rng) ->
            let _ = case isArrow(env,ty0) of
                      | Some (dom0,_) -> (elaborateTypeForTerm(env, trm, dom, dom0); ())
                      | None -> ()
            in
            (case isProduct (env,dom) of
               | Some [("1",s1),("2",s2)] ->
                 (case (isProduct(env,s1),isProduct(env,s2)) of
                    | (Some row1,Some row2) ->
                      let merged_type = Product(mergeFields(env,row1,row2,pos),pos) in
                      (elaborateTypeForTerm(env, trm, rng, merged_type);
                       elaborateTypeForTerm(env, trm, fresh_merge_type, ty0);
                       Fun(RecordMerge, ty1, pos))
                    | _ -> notEnoughInfo())
               | _ -> notEnoughInfo())
          | None -> notEnoughInfo()))

    | _ ->
      elaborateTerm (env, t1, ty0, args)

 op makeEqualityType : MSType * Position -> MSType
def makeEqualityType (ty, pos) =
  %% let a = freshMetaTyVar noPos in 
  %% parser has it's own sequence of metaTyVar's, which are distinguished
  %% from those produced by freshMetaTyVar:
  %% they will be named "#parser-xxx" instead of "#fresh-xxx"
  Arrow (Product ([("1", ty), ("2", ty)], noPos), 
         type_bool,
         pos)

% ========================================================================
op findSuperTypeDominatingTerm (env: LocalEnv) (tms: MSTerms): Option (MSTerm * MSType) =
  case filter (fn ti -> forall? (fn tj -> consistentTypes?(env, termType ti, termType tj, Ignore2)) tms) tms of
    | [dominating_term] ->
      let _ = if debug? then writeLine("Generalized type: "^printType(leastGeneral(termType(tms@0), termType(tms@1)))) else () in
      Some(dominating_term, leastGeneral(termType(tms@0), termType(tms@1)))
    | _ -> None

 op defaultQualifier?(q: Id, env: LocalEnv): Bool =
  q = defaultQualifier(env.internal)

op selectTermWithConsistentType (env: LocalEnv, id: Id, pos: Position, terms: MSTerms, ty: MSType): Option MSTerm =
  %% calls consistentTypeOp?, which calls unifyTypes
  case terms of
    | [term] -> Some term
    | _ ->
      let def findUnqualified tms =
            case tms of
              | [] -> None
              | tm::rtms ->
                (case tm of
                   | Fun (OneName  (     _,_), _, _) -> Some tm
                   | Fun (TwoNames (id1, id2,_), _, _) ->
                     % let _ = if id2 = "foldable?" then writeLine("findUnqualified: "^id1^" "^show (defaultQualifier?(id1, env))) else () in
                     if defaultQualifier?(id1, env) then
                       Some tm
                     else
                       findUnqualified rtms
                   | _ -> findUnqualified rtms)
      in
      case unlinkType ty of
        | MetaTyVar _ ->
          if notFinalPass? env then 
            None
          else
            (case findUnqualified terms of
              | Some term -> Some term
              | None ->
                (error (env,
                        "Several matches for overloaded op " ^ id ^ " of " ^
                        (printMaybeAndType ty) ^
                        (foldl (fn (str, tm) -> str ^
                                (case tm of
                                   | Fun (OneName  (     id2, _), _, _) -> " "^id2
                                   | Fun (TwoNames (id1, id2, _), _, _) -> " "^id1^"."^id2
                                   | Fun(_, ty, _) -> " "^printTerm tm^": "^printType ty
                                   | _ -> " "^printTerm tm))
                               " : "
                               terms),
                        pos);
                 None))
        | rtype ->
          let _ = if debug? then
                    (writeLine("stwct: "^printType rtype);
                     app (fn t -> writeLine(printTerm t)) terms)
                   else ()
          in
          let tyPos = typeAnn ty in
          let result = 
              (case filter (consistentTypeOp? (env, withAnnS (rtype, tyPos), Ignore)) terms of
                 | [] -> let spc = env.internal in
                         let nc_rtype = curryShapeNum(spc, rtype) in
                         let nc_term_args = foldl (fn (nc, Fun (_, ty2, _)) ->
                                                     max(nc, curryShapeNum(spc, ty2)))
                                             0 terms
                         in
                         (error (env,
                                 if nc_rtype > 1 && nc_rtype > nc_term_args
                                  then
                                    let min_n = foldl (fn (nc, Fun (_, ty2, _)) ->
                                                         min(nc, curryShapeNum(spc, ty2)))
                                                 10000 terms 
                                    in
                                    let nm_msg = if nc_term_args = min_n then ""
                                                  else "no more than "
                                    in                                              
                                    show nc_rtype^" arguments given when "^nm_msg^show nc_term_args^" expected for "^id
                                  else
                                    "No matches for op " ^ id ^ " of " ^ (printMaybeAndType ty),
                                 pos);
                          None)

                 | [term] -> Some term
                 | consistent_terms ->
                   let _ = if debugUnify? then writeLine "Looking for dominating term..." else () in
                   (case findSuperTypeDominatingTerm env consistent_terms of
                      | Some(dominating_term, gen_ty) ->
                        let _ = if debugUnify? then writeLine("Dominating term: "^printTerm dominating_term^"\n"^printType gen_ty) else () in
                        let _ = unifyTypes env Ignore gen_ty rtype in
                        let _ = if debugUnify? then writeLine("Generalized type: "^printType gen_ty) else () in
                        let consistent_terms_with_exactly_matching_subtypes = 
                        filter (consistentTypeOp? (env, withAnnS (gen_ty, tyPos), DontIgnore)) 
                          consistent_terms
                        in
                        (case consistent_terms_with_exactly_matching_subtypes of
                           %% If only one term matches including subtypes, choose it
                           | [term] ->
                             let _ = if debugUnify? then writeLine("Only plausible term: "^printTerm term) else () in
                             Some term
                           | _ :: _ | notFinalPass? env -> None
                           | _ -> Some dominating_term)
                      | None ->
                        if notFinalPass? env then
                          None
                        else
                          let consistent_terms_with_exactly_matching_subtypes = 
                          filter (consistentTypeOp? (env, withAnnS (rtype, tyPos), DontIgnore)) 
                          consistent_terms
                          in
                          case consistent_terms_with_exactly_matching_subtypes of
                            %% If only one term matches including subtypes, choose it
                            | [term] -> Some term
                            | _ ->
                              case findUnqualified consistent_terms of
                                | Some term -> Some term
                                | None ->
                                  %% Specware just reports an error here
                                  %% Accord looks to see if there is a unique most-precise term,
                                  %% preferring f : A|p -> B to f : A -> B
                                  (error (env,
                                          "Several matches for overloaded op " ^ id ^ " of " ^
                                            (printMaybeAndType ty) ^
                                            (foldl (fn (str, tm) -> str ^
                                                      (case tm of
                                                         | Fun (OneName  (     id2, _), _, _) -> " "^id2
                                                         | Fun (TwoNames (id1, id2, _), _, _) -> " "^id1^"."^id2
                                                         | Fun(_, ty, _) -> " "^printTerm tm^": "^printType ty
                                                         | _ -> " "^printTerm tm))
                                               " : "
                                               consistent_terms),
                                          pos);
                                   None)))
          in
          let _ = if debug? then
                    (case result of
                     | Some term -> writeLine(printTermWithTypes term)
                     | None -> writeLine("No term chosen!"))
                   else ()
          in
          result

def printMaybeAndType ty =
  case ty of
    | And (ty :: tys, _) ->
      foldl (fn (s, ty) -> s ^ " and type " ^ (printType ty) ^ "\n")
      ("type " ^ (printType ty) ^ "\n")
      tys
    | _ ->
      "type " ^ (printType ty) 

def consistentTypeOp? (env, ty1, subtype_mode) (tm as (Fun (_, ty2, _))) =
 %% calls unifyTypes, but then resets metatyvar links to None...
 let _ = if debugUnify? then writeLine("Consistent type? ("^showSubtypeMode subtype_mode^"): "
                                         ^printTermWithTypes tm^"\n with "^printType ty1) else () in
 let result = consistentTypes? (env, ty1, ty2, subtype_mode) in
 let _ = if debugUnify? then writeLine(show result) else () in
 result

% ========================================================================

def elaborateCheckTypeForTerm (env, term, givenType, expectedType) = 
 elaborateTypeForTerm (env, term, checkType (env, givenType), expectedType)

op elaborateCheckTypeForOpRef (env: LocalEnv, term: MSTerm, givenType: MSType, expectedType: MSType): MSType =
  if allowDependentSubTypes? && finalPass? env
    then elaborateTypeForTerm(env, term, checkType0(env, givenType), expectedType)
    else elaborateCheckTypeForTerm(env, term, givenType, expectedType)

def elaborateTypeForTerm (env, term, givenType, expectedType) = 
  %% unifyTypes has side effect of modifying metaTyVar links
  let _ = if debugUnify? then writeLine("Typing term "^printTerm term^": "^printType givenType^" with "^printType expectedType) else () in
  let success = unifyTypes env Ignore givenType expectedType in
  ((if success || notFinalPass? env then
      ()
    else
      let pos        = termAnn   term in
      let termString = printTerm term in
      let tsLen      = length termString in
      let termTyStr  = printType givenType in
      let termTyStrLen = length termTyStr in
      let expectTyStr = printType expectedType in
      let expectTyStrLen = length expectTyStr in
      let argMismatchStr = argMismatchMsg(givenType, expectedType, env.internal) in
      let mainMsg = if argMismatchStr = ""
                     then "ERROR: Could not match type constraint for "
                     else argMismatchStr
      in
      let msg =
          (if tsLen < 60
            then
              (if termTyStrLen < 100 && expectTyStrLen < 100
                then (if tsLen <= 18
                        then let prefix_len = max(tsLen+2, length "in context: ") in
                             newLines2[mainMsg, 
                                       blankString(prefix_len - tsLen - 2)^termString^": "^ termTyStr,
                                       blankString(prefix_len - length "in context: ")
                                         ^"in context: " ^ expectTyStr]
                        else newLines2[mainMsg^termString^":", 
                                       "            " ^ termTyStr,
                                       "in context: " ^ expectTyStr])
                else newLines2[mainMsg^termString^":", 
                               termTyStr,
                               "  in context:", expectTyStr])
          else
            (if termTyStrLen < 100 && expectTyStrLen < 100
              then newLines2[mainMsg, 
                             termString ^ ": ",
                             "            " ^ termTyStr,
                             "in context: " ^ expectTyStr]
            else newLines2[mainMsg, termString^":", 
                           termTyStr,
                           "  in context:", expectTyStr]))
      in
        % let _ = fail msg in
        error (env, msg, pos));
   givenType)

 % If f : A -> B, and x : C, then for f(x) we want to see
 % an error message like:
 %
 % Could not match type constraint
 %       x of type C
 %       with expected type A
 %
 % Most of the time, givenType is C (the type of the argument)
 % while expectedType is A (the domain type of the function).
 %
 % ---
 %
 % Apparently the sense of givenType and expectedType used to be 
 %  reversed for some obscure reason, but they seem ok now here.
 %  If there are problems, fix them elsewhere, and don't mangle 
 %  this code!

op argMismatchMsg(ty1: MSType, ty2: MSType, spc: Spec): String =
  let nc1 = curryShapeNum(spc, ty1) in
  let nc2 = curryShapeNum(spc, ty2) in
  if nc1 > 1
    then if nc2 > nc1
      then show nc2^" arguments given when at most "^show nc1^" expected for "
    else ""
  else if nc2 > nc1
    then if nc1 = 0
          then "Non-function given "^show nc2^" curried arguments. "
          else "Non-curried function given "^show nc2^" curried arguments. "
    else ""

op elaborateTypeForPat (env: LocalEnv, pat: MSPattern, givenType: MSType, expectedType: MSType): MSType =
  let givenTypeChecked = checkType (env, givenType) in
  %% unifyTypes has side effect of modifying metatyvar links
  let success = unifyTypes env Ignore givenTypeChecked expectedType in
  ((if success then
      ()
    else             
      let msg = newLines ["Could not match type " ^ printType givenType, 
                          "                with " ^ printType expectedType]
      in
        error (env, msg, patAnn pat));
   givenTypeChecked)

def elaborateType (env, s1, s2) = 
  let s1Checked = checkType (env, s1) in
  %% unifyTypes has side effect of modifying metatyvar links
  let success = unifyTypes env Ignore s1Checked s2 in
  ((if success then
      ()
    else             
      let msg = newLines ["Could not match type " ^ printType s1, 
                          "                with " ^ printType s2]
      in
        error (env, msg, chooseNonZeroPos (typeAnn s1, typeAnn s2)));
   s1Checked)

% ========================================================================
%% Called inside elaborateTerm 

op mkEmbed0 (env: LocalEnv, ty: MSType, id: Id): Option QualifiedId =
  case lookupEmbedId (env, id, ty) of
    | Some (None, qid) -> Some qid
    | _   -> None

op lookupEmbedId (env: LocalEnv, id: Id, ty: MSType): Option(Option MSType * QualifiedId) = 
  case unfoldTypeCoProd (env, ty) of
    | CoProduct(row, _) -> 
      let def lookup row =
            case row of
              | [] -> None
              | (found_qid as Qualified(_,found_id), entry) :: row ->  
                if id = found_id then
                  Some (case entry of
                          | None   -> (None, found_qid)
                          | Some s -> (Some (checkType (env, s)), found_qid))
                else 
                  lookup row
      in
        lookup row
    | Subtype (ty, pred, _) -> lookupEmbedId (env, id, ty)
    | _ -> None

op mkEmbed1 (env: LocalEnv, ty: MSType, trm: MSTerm, id: Id, pos: Position): Option MSTerm = 
  case isArrowCoProduct (env, ty) of
    | Some (_, _, row) ->
      let 
        %% This checks that a sum-type constructor is given the proper type
        def findId ls = 
          case ls of
            | [] -> None   % Some (undeclaredName (env, trm, id, ty, pos))
            | (constructor_qid as Qualified(_,constructor_id), Some constructor_dom_type) :: row -> 
              if id = constructor_id then
                  %let _ = writeLine ("ty:  "^printType ty) in
                  %let _ = writeLine ("dom:  "^printType (constructor_dom_type)) in
                % let constructor_dom_type = checkType (env, constructor_dom_type) in
                % let _ (* dom *) = elaborateType (env, constructor_dom_type, withAnnS (dom_type, pos)) in
                Some (Fun (Op (constructor_qid, Constructor1), metaFiedTypeForOp(env, constructor_qid, trm, ty), pos))
              else 
                findId row
            | _ :: row -> findId row
      in
        findId row
    | _ -> None

def isArrowCoProduct (env, ty) : Option (MSType * MSType * List (QualifiedId * Option MSType)) =
  case unfoldType (env, ty) of
    | Arrow (dom, rng, _) -> 
      (case isCoproduct (env, rng) of
         | Some row -> Some (dom, rng, row)
         | None -> None)
    | _ -> None

def isCoproduct (env, ty)  = 
  case unfoldTypeCoProd (env, ty) of
    | CoProduct (row, _)   -> Some row
    | Subtype   (ty, _, _) -> isCoproduct (env, ty)
    | _ -> None

op  isProduct: LocalEnv * MSType -> Option(List (Id * MSType))
def isProduct (env, ty)  = 
  case unfoldType (env, ty) of
    | Product (fields, _) -> Some fields
    | Subtype (ty, _, _) -> isProduct (env, ty)
    | _ -> None

def isArrow (env, ty): Option (MSType * MSType)  = 
  case unfoldType (env, ty) of
    | Arrow (dom, rng, _) -> Some (dom, rng)
    | Subtype(sty, _, _) -> isArrow (env, sty)
    | _ -> None

def mergeFields(env,row1,row2,pos) =
  let 
    def loop(row1,row2,merged) =
      case (row1, row2) of
        | ([], _)  -> merged ++ row2
        | (_,  []) -> merged ++ row1
        | (e1::r1, e2::r2) ->
          case compare (e1.1, e2.1) of
            | Less    -> loop (r1, row2, merged ++ [e1])
            | Greater -> loop (row1, r2, merged ++ [e2])
            | Equal   -> (elaborateType(env,
                                        Product([e1], pos),
                                        Product([e2], pos));
                          loop (r1, r2, merged ++ [e1]))   % Was e2 but e1 is better to preserve subtype info
  in 
    loop(row1,row2,[])

op constrTerm(env: LocalEnv, id: Id, coprod_qid: QualifiedId, coprod_ty: MSType, trm: MSTerm, ty: MSType, pos: Position): Option MSTerm =
  let (v_ty, c_ty) = metafyBaseType (coprod_qid, coprod_ty, termAnn trm) in
  let id_ty = case c_ty of
                 | CoProduct (fields, pos) ->
                   (case findLeftmost (fn (Qualified(_,id2), _) -> id = id2) fields of
                      | Some (_, Some dom_ty) -> Arrow (dom_ty, v_ty, pos)
                      | _ -> v_ty)
                 | _ -> v_ty
  in
  (case mkEmbed0 (env, id_ty, id) of
     | Some qid -> Some (Fun (Op (qid, Constructor0), checkType (env, id_ty), pos))
     | None -> mkEmbed1 (env, id_ty, trm, id, pos))

%% If id is the unique name of a constructor, use that constructor
def uniqueConstr (env, trm, id, ty, pos) =
  case StringMap.find (env.constrs, id) of
    | Some [(coprod_qid, coprod_ty)] -> constrTerm(env, id, coprod_qid, coprod_ty, trm, ty, pos)
      
    | _ -> None

def mkProject (env, id, ty, pos) = 
  case unfoldType (env, ty) of
    | Arrow (dom, rng, _) -> 
      (let 
         def analyzeDom dom =
           case unfoldType (env, dom) of
             | Product (row, _) -> 
               (let def findId ls = 
                      case ls of
                        | [] -> None : Option MSTerm
                        | (selector_id, selector_rng_ty) :: ids -> 
                          if id = selector_id then
                            (elaborateType (env, selector_rng_ty, withAnnS (rng, pos));
                             Some (Fun (Project id, ty, pos)))
                          else 
                            findId ids
                in
                  findId row)
             | Subtype (sty, _, _) -> analyzeDom sty
             | _ -> None
       in 
         analyzeDom dom)
    | Subtype (sty, _, _) -> mkProject (env, id, sty, pos)
    | _ -> None

def consistentTag competing_pterms =
  %% If one of the alternatives (found by findVarOrOps) has optional infix priority
  %% and the others either have the same infix priority or are not infix ops then,
  %% return (true, priority), otherwise return (false, None).
  %% In other words, we will complain if F or Foo.F is ambigous among terms that
  %% have differing infix priorities, but allow prefix versions.
  %% findVarOrOps should never return any OneName
  case competing_pterms of
    | (Fun (OneName  (_,    Infix priority), _, pos))::r -> consistentInfixMSTerms (r, Some priority)
    | (Fun (TwoNames (_, _, Infix priority), _, pos))::r -> consistentInfixMSTerms (r, Some priority) % r must be []
    | _::r                                               -> consistentInfixMSTerms (r, None)
    | _                                                  -> (true, None)

def consistentInfixMSTerms (competing_pterms, optional_priority) = 
  case competing_pterms of
    | [] -> (true, optional_priority)
    | (Fun (OneName (_, Infix element_priority), _, pos))::tail ->
      (case optional_priority of
         | None -> consistentInfixMSTerms (tail, Some element_priority)
         | Some priority -> (if element_priority = priority then
                               consistentInfixMSTerms (tail, optional_priority)
                             else 
                               (false, None)))
    | (Fun (TwoNames (_, _, Infix element_priority), _, pos))::tail ->
      (case optional_priority of
         | None -> consistentInfixMSTerms (tail, Some element_priority)
         | Some priority -> (if element_priority = priority then
                               consistentInfixMSTerms (tail, optional_priority)
                             else 
                               (false, None)))
    | _::tail -> consistentInfixMSTerms (tail, optional_priority)

 def undeclaredName (env, trm, id, ty, pos) =
  if notFinalPass? env then %&& undeterminedType? s 
    trm
  else
    (error (env, "Name "^id^" could not be identified", pos);
     % raise (TypeCheck (pos, "Name "^id^" could not be identified"));
     Fun (OneName (id, Nonfix), ty, pos))

def ambiguousCons (env, trm, id, ty, pos) =
  if notFinalPass? env then %&& undeterminedType? s 
    trm
  else
    (error (env, "Constructor "^id^" could not be disambiguated", pos);
     Fun (OneName (id, Nonfix), ty, pos))

def undeclared2 (env, trm, id1, id2, ty, pos) =
  if notFinalPass? env then %&& undeterminedType? s 
    trm
  else
    (error (env, id1^"."^id2^" has not been declared as a qualified name or as a field selection", pos);
     % raise (TypeCheck (pos, id1^"."^id2^" has not been declared as a qualified name or as a field selection"));
     Fun (TwoNames (id1, id2, Nonfix), ty, pos))

def undeclaredResolving (env, trm, id, ty, pos) = 
  if notFinalPass? env then %&& undeterminedType? s
    trm
  else
    (error (env, "Name "^id^" could not be identified; resolving with "^printType ty, pos);
     % raise (TypeCheck (pos, "Name "^id^" could not be identified; resolving with "^printType ty));
     (Fun (OneName (id, Nonfix), ty, pos)) : MSTerm)

% ========================================================================
%% Called inside elaborateTerm 
% ========================================================================

def elaboratePattern (env, p, type1) =
  let (pat, env, _) = elaboratePatternRec (env, p, type1, []) in
  (pat,env)

op  elaboratePatternRec: LocalEnv * MSPattern * MSType * List Id -> MSPattern * LocalEnv *  List Id 
def elaboratePatternRec (env, p, type1, seenVars) =
  let type1 = checkType (env, type1) in
  let 
    def addSeenVar(id, seenVars, env, pos) =
      if id in? seenVars then
        (error (env, "Variable "^id^" repeated in pattern.", pos);
         (env,seenVars))
      else 
        (env, Cons (id, seenVars))
  in
  case p of
    | WildPat (s, pos) -> (WildPat (elaborateTypeForPat (env, p, s, type1), pos), env, seenVars)
    | BoolPat   _ -> (elaborateTypeForPat (env, p, type_bool, type1);   (p, env, seenVars))
    | NatPat    _ -> (elaborateTypeForPat (env, p, type_nat, type1);    (p, env, seenVars))
    | StringPat _ -> (elaborateTypeForPat (env, p, type_string, type1); (p, env, seenVars))
    | CharPat   _ -> (elaborateTypeForPat (env, p, type_char, type1);   (p, env, seenVars))
    | VarPat ((id, ty), pos) -> 
      let ty = elaborateTypeForPat (env, p, ty, type1)  in 
      (case lookupEmbedId (env, id, ty) of
         | Some (None, qid) -> (EmbedPat (qid, None, ty, pos), env, seenVars)
         | Some _ -> 
           (error (env, "Constructor "^id^" expects an argument, but was given none", pos);
            % raise (TypeCheck (pos, "Constructor "^id^" expects an argument, but was given none"));
            (VarPat ((id, ty), pos), env, seenVars))
         | None ->
           if undeterminedType? ty then
             (case StringMap.find (env.constrs, id) of
                | None ->
                  let (env,seenVars) = addSeenVar(id,seenVars,env,pos) in
                  (VarPat ((id, ty), pos), addVariable (env, id, ty), seenVars)
                | Some [(qid, ty_info)] ->
                  let (v_ty, c_ty) = metafyBaseType (qid,ty_info,pos) in
                  (VarPat ((id, v_ty), pos), env, seenVars)
                | Some _ -> (VarPat ((id, ty), pos), env, seenVars))
           else
             let (env,seenVars) = addSeenVar(id,seenVars,env,pos) in
             (VarPat ((id, ty), pos), addVariable (env, id, ty), seenVars))
    | TypedPat (pat, ty, _) -> 
      let ty = elaborateTypeForPat (env, p, ty, type1) in
      let (p, env, seenVars) = elaboratePatternRec (env, pat, ty, seenVars) in
      (p, env, seenVars)
    | AliasPat (pat1, pat2, pos) ->
      let (pat1, env, seenVars) = elaboratePatternRec (env, pat1, type1, seenVars) in
      let (pat2, env, seenVars) = elaboratePatternRec (env, pat2, type1, seenVars) in
      (AliasPat (pat1, pat2, pos), env, seenVars)
    | EmbedPat (embedQId as Qualified(_,embedId), pattern, type0, pos) ->
      let type0 = elaborateTypeForPat (env, p, type0, type1) in
      let type0 =
          if undeterminedType? type0 then
             %% See if there is only one constructor with this name
             (case StringMap.find (env.constrs, embedId) of
                | Some [(qid,ty_info)] ->
                  let (v_ty, c_ty) = metafyBaseType (qid, ty_info, pos) in
                  elaborateTypeForPat (env, p, v_ty, type1)
                | _ -> type0)
           else
             type0
      in
        if notFinalPass? env && undeterminedType? type0 then
          let (env, epat, seenVars) =
              case pattern of
                | None -> (env,None, seenVars)
                | Some pat ->
                  let alpha = freshMetaTyVar ("EmbedPat_a", pos) in
                  let (pat, env, seenVars) = elaboratePatternRec (env, pat, alpha, seenVars) in
                  (env, Some pat, seenVars)
          in
          (EmbedPat (embedQId, epat, type0, pos), env, seenVars)
        else
          let ty_info = lookupEmbedId (env, embedId, type0) in
          let (env, embedQId, pat, seenVars) = 
              (case (ty_info, pattern) of
                 | (Some (Some ty, embedQId), Some pat) -> 
                   let (pat, env, seenVars) = elaboratePatternRec (env, pat, ty, seenVars) in
                   (env, embedQId, Some pat, seenVars)

                 | (Some (None, embedQId), None) -> (env, embedQId, None, seenVars)
                 | (None, None) -> 
                   (error (env, "Type for constructor "
                           ^ embedId
                           ^ " not found. Resolving with type "
                           ^ printType type1, pos);
                    (env, embedQId, None, seenVars))
                 | (None, Some pat) -> 
                   let alpha = freshMetaTyVar ("EmbedPat_b", pos) in
                   let (pat, env, seenVars) = elaboratePatternRec (env, pat, alpha, seenVars)
                   in
                   (error (env, "Type for constructor "
                           ^ embedId
                           ^ " not found. Resolving with type "
                           ^ printType type1, pos);
                    (env, embedQId, None, seenVars))
                 | (Some None, Some pat) -> 
                   (error (env, newLines ["Constructor "
                                          ^ embedId
                                          ^ " takes no argument", 
                                          "but was given "
                                          ^ printPattern pat], pos);
                    (env, embedQId, Some pat, seenVars))
                 | (Some (Some _, embedQId), None) -> 
                   (error (env, "Argument expected for constructor "
                           ^ embedId, pos);
                    (env, embedQId, None, seenVars)))
          in
            (EmbedPat (embedQId, pat, type1, pos), env, seenVars)
    | RecordPat (row, pos) ->
      let r = map (fn (id, ty)-> (id, freshMetaTyVar ("RecordPat", pos))) row in
      let _ = elaborateTypeForPat (env, p, (Product (r, pos)), type1) in
      let r = zip (r, row) in
      let (r, env, seenVars) = 
          foldl (fn ((row, env, seenVars), ((id, ty), (_, p))) ->
                 let (p, env, seenVars) = elaboratePatternRec (env, p, ty, seenVars) in
                 (Cons ((id, p), row), env, seenVars))
            ([], env, seenVars) r
      in
        (RecordPat (reverse r, pos), env, seenVars)

    | QuotientPat (pat, qid, param_tys, pos) ->
      (case findTheType (env.internal, qid) of
         | Some info ->
           (case unpackFirstTypeDef info of
              | (tvs, Quotient (base_body, equiv, _)) ->
                let (qp_ty, base_body) =
                    if param_tys ~= [] || tvs = []
                      then (Base(qid, param_tys, pos),
                            instantiateScheme(env, pos, param_tys, Pi(tvs, base_body, pos)))
                      else metafyBaseType(qid, Pi(tvs, base_body, pos), pos)
                in
                let _ = elaborateTypeForPat(env, p, qp_ty, type1) in
                let (pat, env, seenVars)
                   = elaboratePatternRec (env, pat, base_body, seenVars) in
                let Base(_, nparam_tys, _) = qp_ty in
                (QuotientPat (pat, qid, nparam_tys, pos), env, seenVars)
              | _ ->
                let ss = show qid in
                (error (env, 
                        "In pattern quotient[" ^ ss ^ "], " ^ ss ^ " refers to a type that is not a quotient",
                        pos);
                 (QuotientPat (pat, qid, param_tys, pos), env, seenVars)))

         | _ ->
           let ss = show qid in
           (error (env, 
                   "In pattern quotient[" ^ ss ^ "], " ^ ss ^ " does not refer to a type",
                   pos);
            (QuotientPat (pat, qid, param_tys, pos), env, seenVars)))

    | RestrictedPat (pat, term, pos) ->
      let (pat, env, seenVars) = elaboratePatternRec (env, pat, type1, seenVars) in
      let term = elaborateTerm (env, term, type_bool, []) in
      (RestrictedPat (pat, term, pos), env, seenVars)

    | p -> (System.print p; System.fail "Nonexhaustive")


% ========================================================================

def pass2Error (env, _(* s *), msg, pos) =
  if notFinalPass? env then %&& undeterminedType? s 
    ()
  else 
    error (env, msg, pos)

def blankString (n:Int) =
  if n <= 0 then 
    "" 
  else
    let oneHundredSpaces = "                                                                                                    " in
    if n < 100 then
      subFromTo (oneHundredSpaces, 0, n)
    else
      oneHundredSpaces ^ blankString (n - 100)

def newLines lines = 
  case lines of
    | [] -> ""
    | [line] -> line
    | line :: lines -> 
      line ^ show (chr 10) ^ "          " ^ (newLines lines)

op newLines2(lines: List String): String = 
  case lines of
    | [] -> ""
    | [line] -> line
    | line :: lines -> 
      line ^ "\n" ^ (newLines2 lines)

%% ---- called inside OPS : PASS 2  -----

def checkTyVars (env, tvs, pos) =
  let 
    def aux (tvs, already_seen) =
      case tvs of
        | []      -> ()
        | id::tvs ->  
          if StringSet.member (already_seen, id) then
            error (env, 
                   "Repeated type variables : " ^ (foldl (fn (str, tv) -> str ^ " " ^ tv) "" tvs),
                   pos)
          else 
            aux (tvs, StringSet.add (already_seen, id))
  in 
    aux (tvs, StringSet.empty)

op groundType?(ty: MSType): Bool =
  ~(existsInType? (fn sty ->
                   case sty of
                     | MetaTyVar(Ref{link = None, name, uniqueId}, _) -> true
                     | _ -> false)
    ty)

%% Dependent Type Utilities
op hasFreeVarsInSubty?(ty: MSType): Bool =
  existsInType? (fn sty ->
                   case sty of
                     | Subtype(_, p, _) ->
                       freeVars p ~= []
                     | _ -> false)
    ty

op makeSubstFromLambdas(tm: MSTerm, args: MSTerms): MSVarSubst =
  case args of
    | [] -> []
    | a1::r_args ->
  case tm of
    | Lambda([(pat, _, bod)], _) ->
      (case patternMatch(pat, a1, [], []) of
         | Match sb -> sb
         | _ -> [])
        ++ makeSubstFromLambdas(bod, r_args)
    | _ ->  []

op debug1?: Bool = false

op tryInstantiateDepVars(env: LocalEnv, f1: MSTerm, ty: MSType, args: MSTerms): MSType =
   let _ = if debug1? then writeLine("f1: "^printTerm f1) else () in
  let (q, nm) = case f1 of
                  | Fun (TwoNames (q, nm, _), _, _) -> (q, nm)
                  | Fun (OneName(nm, _), _, _) -> (UnQualified, nm)
                  | _ -> ("", "")       % Shouldn't happen?
  in
  case findTheOp2(env, q, nm) of
    | None -> ty
    | Some info ->
  let _ = if debug1? then writeLine(q^"."^nm^": "^printTerm info.dfn) else () in
  let (_, _, dfn) = unpackFirstOpDef info in
  let sb = makeSubstFromLambdas(dfn, args) in
  if sb = [] then ty
  else
  let new_f_ty = mapType (id,
                          fn sty ->
                            case sty of
                              | Subtype(ssty, p, a) ->
                                % let _ = if debug1? then writeLine("stp: "^anyToString p) else () in
                                let n_sty = Subtype(ssty, substitute(p, sb), a) in
                                let st_mtv as MetaTyVar (mtv, _)= freshMetaTyVar("DepType", a) in
                                (mtv := ! mtv << {link = Some n_sty};
                                 if debug1? then writeLine("Metafying Dep Type: "^printType st_mtv) else ();
                                 st_mtv)
                              | _ -> sty,
                          id)
                   ty
  in
  let _ = if debug1? then writeLine("new_f_ty: "^printType new_f_ty) else () in
  new_f_ty

end-spec
 
