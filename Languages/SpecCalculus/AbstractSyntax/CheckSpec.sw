(* Copyright 2015 Kestrel Institute. See file LICENSE.text for license details *)

%% This utility checks a spec for well-formedness.  It is available as
%% the Specware shell command 'checkspec' or as the spec
%% transformation CheckSpec (which is logically the identity
%% transformation but also prints messages about problems in specs).

%% TODO: Move this file to something under Languages/MetaSlang.
%% TODO: combine all opinfo checks into one routine
%% TODO: consistently count and report the number of errors.

CheckSpec qualifying spec 

import ShowUtils
import /Languages/MetaSlang/Specs/AnnSpec
import /Languages/MetaSlang/Specs/Utilities
import /Languages/MetaSlang/AbstractSyntax/AnnTerm
%% import /Languages/MetaSlang/Specs/Elaborate/TypeChecker

%%TTODO: Not right <- huh?
%% Strip off a call to Pi if it is the outermost construct in the term:
op [b] stripPossiblePi (tm : ATerm b) : ATerm b =
  case tm of
  | Pi(_,tm,_) -> tm
  | tm -> tm

%% walk down the list, calling compare on each pair of elements.  return true if compare returns true for all pairs.
op [a] comparePairwise? (compare : a * a -> Bool, x : List a) : Bool =
  case x of
  | [] -> true
  | [hd] -> true
  | hd::tl -> ((compare(hd, head tl)) && (comparePairwise? (compare, tl)))

op [a] badOpInfo? (opinfo : AOpInfo a, spc : Spec) : Bool =
  let name = primaryOpName opinfo in
  let dfn = opinfo.dfn in
  let triples = unpackTypedTerms dfn in % each triple is (tyvars, ty, body)
  let tyvarss = map (fn x -> x.1) triples in
  let tyvars_bad? = if ~ (allEqualElements? tyvarss) then let _ = writeLine("ERROR: Inconsistent type vars for the defintions of op " ^ show name ^ ".") in true else false in
  let tys = map (fn x -> x.2) triples in
  %% This messaage may just indicate that postcondition strengthening has been done, so it is merely a NOTE:
  let _ = if (~ (comparePairwise? (equalType?, tys))) then writeLine("NOTE: Different types for the multiple definitions of op " ^ show name ^ " (may be okay).") else () in

 %% TODO: check that Any does not appear in any argument of And?

  % let dfnNoPi = stripPossiblePi dfn in
  % %TODO: Add many more tests
  % if (existsSubTerm (fn tm -> case tm of | Pi(_,_,_) -> true | _ -> false) dfnNoPi) then
  %   let _ = writeLine ("ERROR: Pi term found not at top level in op " ^ show name ^ ".") in true
  % else
  %   false
  tyvars_bad?

%%FIXME: Consider replacing typeTyVars with this version: 
op [b] typeTyVars2 (ty : AType b) : TyVars =
  case ty of
     | Pi (tvs, _, _) -> tvs
     | And (tms, _) -> if tms = [] then [] else typeTyVars (head tms)
     | _ -> []

%% FIXME: Flesh this out.  Should take a spec as an argument?
op [b] badTerm    (accum:Bool) (tm:ATerm    b) : (ATerm    b * Bool) =
  (tm,
  case tm of
    | And([] , _) -> let _ = writeLine("ERROR: 'And' term with no conjuncts.") in true
    | And(tms, _) -> (if (exists? anyTerm? tms) then 
                         accum %% FFIXME Put this back, once these errors stop happening in HACMS!  let _ = writeLine("ERROR: 'Any' term inside of 'And' term.") in true
                       else
                         accum)
    | _ -> false)


%% FIXME: Flesh this out.  Should take a spec as an argument?
op [b] badPattern (accum:Bool) (pat:APattern b) : (APattern b * Bool) = (pat, accum)

op badType (s:Spec) (accum:Bool) (ty:AType StandardAnnotation) : (AType StandardAnnotation * Bool) =
  (ty,
   case ty of
    | Base(qid, args, _) ->
     (let argcount = length args in
      let correctargcount = 
       (let op_ty = findTheType(s,qid) in
        (case op_ty of | None -> let _ = writeLine("ERROR: Can't find type: "^(show qid)) in 0 %%FIXME error here?
                       | Some ty_info -> let dfn = ty_info.dfn in
                                         let tyvars = typeTyVars2 dfn in  %FIXME what about an And whose conjuncts have different lists of ty vars?
                                         length tyvars))
in
      (if (argcount = correctargcount) then accum else % not bad
       let _ = writeLine ("Error: Wrong arg count in Base type node applying type "^(show qid)^". Got: "^(anyToString argcount)^". Should be: "^(anyToString correctargcount)^".") in true))
       %% FIXME recur on the conjuncts!
      | And([] , _) -> let _ = writeLine("ERROR: 'And' type with no conjuncts.") in true
      | And(tys, _) -> (if (exists? anyType? tys) then 
                         let _ = writeLine("ERROR: 'Any' type inside of 'And' type.") in true
                       else 
                         accum)
      | _ -> accum % not bad
   )

op typeInfoBad? (s : Spec) (info : ATypeInfo StandardAnnotation) : Bool =
  %FIXME: make something like mapaccumterm that doesn't return the term:
  let bad? = ((mapAccumType (badTerm, badType s, badPattern) false info.dfn).2) in
  if bad? then
    let _ = writeLine ("ERROR: Found problems (listed just above) with type "^(show (primaryTypeName info))) in true
  else
   false

op typesOkay?(s : Spec) : Bool =
  (countTypeInfos (typeInfoBad? s) s.types) = 0

op opInfoBad? (s : Spec) (info : AOpInfo StandardAnnotation) : Bool =
  let bad? = ((mapAccumTerm (badTerm, badType s, badPattern) false info.dfn).2) in
  if bad? then
    let _ = writeLine ("ERROR: Found problems (listed above) with op "^(show (primaryOpName info))) in true
  else
    false

%% Better version of existsSubTerm (this one handles terms that occur inside of types, etc.).  TODO: Move this to AnnTerm.sw?
op [b] existsSubTerm3 (pred?:ATerm b -> Bool) (term:ATerm b): Bool =
  let (result_term, result) =
    (mapAccumTerm ((fn (accum) -> fn (term) -> if pred? term then (term, true) else (term, accum)),
                   (fn (accum) -> fn (ty) -> (ty, accum)),
                   (fn (accum) -> fn (pat) -> (pat, accum)))
                  false
                  term) in
  result

op call_of_undefined_op? (nm : QualifiedId) (spc: Spec) (tm:MSTerm) : Bool =
  case tm of
        | Fun (Op (qid, _), _, _) ->
          (case findTheOp (spc, qid) of
             | Some _ -> false
             | _ -> let _ = writeLine ("ERROR: op " ^ (show nm) ^ " calls " ^ (show qid) ^ ", which does not exist in the hash table.") in true)
        | _ -> false

op term_calls_undefined_op? (op_or_theorem_name : OpName) (spc: Spec) (tm:MSTerm) : Bool =
  existsSubTerm3 (call_of_undefined_op? op_or_theorem_name spc) tm

op opsOkay?(s : Spec) : Bool =
  %% For every op info in the hash table, verify that every op-reference 
  %% has a corresponding entry.  This now checks several more things.
  %% TODO: types, op-refs within types, etc.
  let ops_with_bad_definitions = countOpInfos (opInfoBad? s) s.ops in  %FIXME: make something like mapaccumterm that doesn't return the term
  %% TODO: fold this into opInfoBad?:
  let ops_that_call_non_existing_ops = countOpInfos (fn (info) -> term_calls_undefined_op? (primaryOpName info) s info.dfn) s.ops in
  %% TODO: fold this into opInfoBad?:
  let ops_with_free_vars = countOpInfos (fn (info) -> case (freeVars info.dfn) of
                                                         | [] -> false
                                                         | vars -> let _ = writeLine ("ERROR: Op " ^ show (primaryOpName info) ^ " has the following free vars in its body: " ^ (anyToString vars) ^ ".") in
                                                           true)
                                         s.ops
  in
  let other_bad_op_infos = countOpInfos (fn x -> badOpInfo?(x, s)) s.ops in
  (ops_that_call_non_existing_ops = 0 && ops_with_free_vars = 0 && ops_with_bad_definitions = 0)
                  
op propertyOkay? (prop : Property, spc : Spec) : Bool =
  let (kind, name, tyvars, term, ann) = prop in
  ~(term_calls_undefined_op? name spc term)
  %% TODO: add more tests

op specOkay? (success_msg : String) (failure_msg : String) (s : Spec) : Bool =
 %% case elaboratePosSpec(s, "") of  % TODO Stephen says this is not really the right thing to call.
 %%  | Errors errs -> let _ = writeLine( "Errors in spec:" ^ (anyToString errs)) in false
 %%  | Spec spc -> let _ = writeLine "No type checking error in spec." in
%should we use spc here?

  %% For every type info in the hash table, verify that there is a corresponding
  %% Type and/or TypeDef spec element:
  let bad_or_missing_type_elements? =
      foldTypeInfos (fn (info, err) ->
                       let names = info.names in
                       if names = [] then
                         let _ = writeLine("ERROR: No names for type!") in %% TODO Print the position?  We can't print the name since there isn't one!
                         true
                       else
                         let qid = primaryTypeName info in  %% TODO If there is more than one name, should we look up each one below?:
                         let _ = if (length names > 1) then writeLine("Warning: More than one name for type: " ^ show qid ^ ": " ^ showQIDs names) else () in
                         let typeElts = getTypeElements qid s.elements in
                         let typeDefElts = getTypeDefElements qid s.elements in
                         let typeCount    = length typeElts    in
                         let typeDefCount = length typeDefElts in
                         let _ = if typeCount    > 1 then writeLine("ERROR: " ^ show typeCount    ^ " declarations for type: " ^ show qid) else () in
                         let _ = if typeDefCount > 1 then writeLine("ERROR: " ^ show typeDefCount ^ " definitions for type: " ^ show qid) else () in
                         %% There must be at least one declaration or definition for the type:
                         let found? = (typeCount > 0 || typeDefCount > 0) in
                         let _ = if found? then () else writeLine("ERROR: No type declarations or definitions for type " ^ show qid) in

                         %% There can't be more than one declaration or more than one definition for the type:
                         let okay? = (typeCount <= 1 && typeDefCount <= 1) in
                           if found? && okay? then
                             err  %% TODO Make sure we return a failure for any of the errors above
                           else
                             true)
                   false
                    s.types
  in
  %% For every op info in the hash table, verify that there is a corresponding
  %% Op and/or OpDef spec element.
  let bad_or_missing_op_elements? =
      foldOpInfos (fn (info, err) ->
                     let names = info.names in
                     if names = [] then
                       let _ = writeLine("ERROR: No names for op!") in %% TODO Print the position?  We can't print the name since there isn't one!
                       true
                     else
                       let qid = primaryOpName info in  %% TODO If there is more than one name, should we look up each one below?:
                       let _ = if (length names = 0) then writeLine("ERROR: No names for op: " ^ show qid) else () in
                       let _ = if (length names > 1) then writeLine("Warning: More than one name for op: " ^ show qid ^ ": " ^ showQIDs names) else () in
                       let opElts = getOpElements qid s.elements in
                       let opDefElts = getOpDefElements qid s.elements in
                       let opCount    = length opElts    in
                       let opDefCount = length opDefElts in


                       %% TODO: Are these the correct rules about ops?  Some things like "add refined type" don't seem to respect these rules.
                       %% TODO: Implement all of these checks.
                       %% You can have an OpDecl with not-defined-when-declared, followed by any number of OpDefs, numbered starting from 0
                         %% What does the body in the opInfo look like?
                         %%   If there are no defs, the body is Any (possibly wrapped in TypedTerm and/or Pi?).
                         %%   If there is exactly 1 def, the body does not contain Any or And.
                         %%   If there is more than 1 def, the body is an And (possibly wrapped in Pi and maybe TypedTerm).
                       %% You can have an OpDecl with defined-when-declared, followed by any number of opDefs, numbered starting from 1
                         %% What does the body in the opInfo look like?  First, the body in the opInfo can never contains Any.
                         %%   If there is exactly 1 def, the body does not contain And.
                         %%   If there is more than 1 def, the body is an And (possibly wrapped in Pi and maybe TypedTerm).

                       let _ = if opCount = 0 then writeLine("ERROR: No declarations for op " ^ show qid ^ ", which has an entry in the hash table.") else () in
                       let _ = if opCount > 1 then writeLine("ERROR: " ^ show opCount    ^ " declarations for op: " ^ show qid) else () in
                       %let _ = if opDefCount > 1 then writeLine("ERROR: " ^ show opDefCount ^ " definitions for op: " ^ show qid) else () in
                       let found? = (opElts ~= [] || opDefElts ~= []) in %% TODO Eventually, have this check for all the errors just above here.
                         if found? then
                           err
                         else
                           true)
                 false
                  s.ops
  in
  let bad_ops? = ~ (opsOkay? s) in
  let _ = writeLine "Done testing ops." in
  let bad_types? = ~ (typesOkay? s) in
  let _ = writeLine "Done testing types." in
  %% For every Type, TypeDef, Op, or OpDef in spec elements,
  %% verify that it refers to an entry in the appropriate hash table.
  let problems_in_spec_elements? =
      foldlSpecElements (fn (err, elt) ->
                           case elt of
                             | Type    (qid, _) ->
                               (case findTheType (s, qid) of
                                  | Some _ -> err
                                  | _ -> let _ = writeLine("ERROR: Cannot find hash table entry for type:" ^ show qid) in true)
                             | TypeDef (qid, _) ->
                               (case findTheType (s, qid) of
                                  | Some _ -> err
                                  | _ -> let _ = writeLine("ERROR: Cannot find hash table entry for type:" ^ show qid) in true)
                             | Op      (qid, _, _) ->
                               (case findTheOp (s, qid) of
                                  | Some _ -> err
                                  | _ -> let _ = writeLine("ERROR: Cannot find hash table entry for op:" ^ show qid) in true)
                             | OpDef   (qid, _, _, _) ->
                               (case findTheOp (s, qid) of
                                  | Some _ -> err
                                  | _ -> let _ = writeLine("ERROR: Cannot find hash table entry for op:" ^ show qid) in true)
                             | Property prop -> if propertyOkay?(prop, s) then err else true
                             | _ -> err)
                        false
                        s.elements
  in
  case (bad_or_missing_type_elements? || bad_or_missing_op_elements? || bad_ops? || bad_types? || problems_in_spec_elements?) of
    | false ->
      let _ = writeLine success_msg in
      false
    | _ ->
      let _ = writeLine (failure_msg) in
      true

op checkSpecCore(spc : Spec, str : String) : Bool =
  let _ = writeLine ("Checking spec: " ^ str ^ ".") in
  specOkay? "Spec is okay." "ERROR: Ill-formed spec." spc

%% Evaluate the given unit and print it to a file.
%% Returns a success flag.
op checkSpec (uid_str : String) : Bool =
%let _ = writeLine ("uid_str:"^uid_str) in
case evaluateUnitId uid_str of
  | None -> let _ = writeLine("Error in checkspec: Unknown UID " ^ uid_str) in false
  | Some val ->
    case val of
    | Spec spc -> let _ = (checkSpecCore(spc, uid_str)) in true
    | Morph m -> let _ = writeLine("ERROR: Don't know how to check a morphism yet.") in true %Should these flags be true or false?
    | _ -> let _ = writeLine("ERROR: Spec checker called on unknown kind of thing.") in true

% This is the top-level function for the checkspec command.
op evaluateCheckSpec (optional_argstring : Option String, lastUnitIdLoaded : Option String, homedir : String) : Option String = 
%  let _ = writeLine "Calling evaluateCheckSpec." in
%  let _ = writeLine ("The user's home directory: "^homedir) in
%  let _ = writeLine ("arg string: "^(case optional_argstring of Some str -> enquote str | None -> "No arg string supplied.")) in
%  let _ = writeLine ("Last unit ID: "^(case lastUnitIdLoaded of | Some str -> str | None ->  "No last uid processed.")) in
  case UIDStringFromArgString(optional_argstring, lastUnitIdLoaded, homedir) of
  | None -> None % fail and don't change *last-unit-Id-_loaded*
  | Some uid_str ->
    %% Check the spec and return a new value for *last-unit-Id-_loaded* if the spec was found:
    let success? = checkSpec uid_str in
    if success? then Some uid_str else None

%% This checks the spec and prints errors if it finds any problems.
%% It does not attempt any repairs.  Logically, this is just the
%% identity transformation on specs.

%% The optional string argument allows you to name this call of check
%% spec, to support easy grepping, in case checkSpec is called many
%% times in a derivation.

op SpecTransform.checkSpec (spc : Spec, str : String) : () =
  % let str = case opt_str of | Some str -> str | None -> "" in
  let _ = checkSpecCore(spc, str) in ()

end-spec
