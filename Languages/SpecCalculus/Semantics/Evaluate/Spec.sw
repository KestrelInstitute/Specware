(* Copyright 2015 Kestrel Institute. See file LICENSE.text for license details *)

(* Evalution of a Spec form in the Spec Calculus *)

SpecCalc qualifying spec

import /Library/Legacy/DataStructures/ListUtilities % for listUnion

import /Languages/MetaSlang/Specs/Elaborate/TypeChecker
import /Languages/MetaSlang/Specs/CompressSpec
import /Languages/MetaSlang/Transformations/DefToAxiom

import Signature 
import UnitId/Utilities
import Spec/AddSpecElements
import Spec/MergeSpecs
import Spec/ComplainIfAmbiguous
import Transform
import Qualify

(*
 * To evaluate a spec we deposit the declarations in a new spec
 * (evaluating any import terms along the way), elaborate the spec
 * and then qualify the resulting spec if the spec was given a name.
 *)

op noElaboratingMessageFiles : List String = []

op evaluateSpec (spec_elements     : ExplicitSpecTerm) 
                (default_qualifier : Qualifier)
                (pos               : Position)
 : Env ValueInfo = 
 let
   def print_progress_message current_uid =
     {
      current_spec_name <- return (uidToString current_uid);
      when (current_spec_name nin? noElaboratingMessageFiles) 
        (print (";;; Elaborating spec at " ^ current_spec_name ^ "\n"))
      }

   def import? (element, _) = 
     case element of 
       | Import _ -> true 
       | _ -> false

   def any_imports? (elements : SpecElemTerms) = 
     exists? import? elements

   def base_empty_spec? ({path, hashSuffix} : UnitId) = 
     case reverse path of
       | "Empty" :: "Base" :: "Library" :: _ -> hashSuffix = None % TODO: this should be more specific
       | _ -> false

   def get_initial_spec current_uid = 
     {
      (opt_base_uid, base_spec) <- getBase;
      %% TODO: remove:
      %% return (importOfSpec (opt_base_uid, base_spec))
      %% TODO: add: [currently this induces some peculiar problems with InterpreterBase spec]
      return (if any_imports? spec_elements then
                 %% Usually at least one of the imports will import the base spec (but this is not required!).
                 emptySpec     
               else if base_empty_spec? current_uid then
                 %% The empty spec in the base library is the only spec allowed to have no implicit imports.
                 emptySpec     
               else
                 %% Other specs lacking explicit imports start by implicitly importing the base spec.
                 importOfSpec (opt_base_uid, base_spec))
      }
 in
 {
  current_uid                     <- getCurrentUID;

  print_progress_message current_uid;

  initial_spec                    <- get_initial_spec    current_uid;
  qualified_spec                  <- return (markQualified initial_spec default_qualifier);
  (raw_spec, timestamp, dep_uids) <- evaluateSpecElems   qualified_spec   spec_elements;
  elaborated_spec                 <- elaborateSpecM      raw_spec;
  disambiguated_spec              <- complainIfAmbiguous elaborated_spec pos;
  refined_spec                    <- applyOpRefinements  disambiguated_spec;
  final_value                     <- return (Spec (markQualifiedStatus (removeDuplicateImports refined_spec)) : Value);
  return (final_value, timestamp, dep_uids)
  }

(*
 * We first evaluate the imports and then the locally declared ops, types
 * axioms, etc.
 *)

op evaluateSpecElems (starting_spec : Spec) (se_terms : SpecElemTerms) 
 : Env (Spec * TimeStamp * UnitId_Dependency) =
 {
  %% Use the name starting_spec to avoid any possible confusion with the
  %% op initialSpecInCat, which refers to the initial spec in the category of specs.
  (timestamp, depUIDs, imports_info) <- foldM checkImports (0, [], []) se_terms;
  imports_spec <- foldM doImport         starting_spec (reverse imports_info);
  full_spec    <- foldM (evaluateSpecElem (multiConstructorNames? se_terms)) imports_spec  se_terms;
  return (full_spec, timestamp, depUIDs)
  }

op coProductNames (ty: MSType): Ids =
  case unpackType ty of
    | (_,  CoProduct(fields, a)) ->
      mapPartial (fn (Qualified(q, id), _) -> if q = UnQualified then Some id else None) fields
    | _ -> []

op multiConstructorNames? (se_terms : SpecElemTerms): Bool =
  exists? (fn se_tm ->
           case se_tm of
             | (Type (names, dfn), _) ->
               let nms = coProductNames dfn in
               nms ~= []
                 && exists? (fn se_tm_i ->
                              se_tm_i ~= se_tm
                             && (case se_tm_i of
                                   | (Type (names, dfn), _) ->
                                     exists? (fn nm -> nm in? nms) (coProductNames dfn)
                                   | _ -> false))
                     se_terms
             | _ -> false)
    se_terms

op checkImports (val         : (TimeStamp * UnitId_Dependency * List (SCTerm * Spec * Position)))
                ((elem, pos) : SpecElemTerm)
 : Env (TimeStamp * UnitId_Dependency * List (SCTerm * Spec * Position)) =
 case elem of
   | Import terms -> 
     foldM (fn (combined_timestamp, combined_dep_UIDs, imports_info) -> fn term ->
              {
               (value, import_timestamp, import_dep_UIDs) <- evaluateTermInfo term;
               (case coerceToSpec value of
                  | Spec spc -> 
                    return (max (combined_timestamp, import_timestamp), 
                            listUnion (combined_dep_UIDs, import_dep_UIDs),
                            (term, spc, pos) :: imports_info)
                  | InProcess _ -> 
                    (case valueOf term of
                       | UnitId (UnitId_Relative   x) -> raise (CircularDefinition x)
                       | UnitId (SpecPath_Relative x) -> raise (CircularDefinition x)
                       | _ -> raise (Fail ("Circular import")))
                    
                  | _ -> raise (Fail ("Import not a spec")))
               })
           val               
           (reverse terms) % just so result shows in same order as read
   | _ -> 
     return val

op doImport (spc : Spec) (term : SCTerm, imported_spec : Spec, pos : Position) : Env Spec =
 {(term, imported_spec) <- 
    if ~(qualifiedSpec? imported_spec) && qualifiedSpec? spc then
      let Some qual = spc.qualifier in
      % let _ = writeLine("implicit qualify: "^qual^" at "^printAll pos^"\n"^showSCTerm term^"\n"^anyToString (markQualifiedStatus imported_spec)) in 
      {impSpec <- qualifySpec imported_spec qual [] pos;
       return ((Qualify (term, qual), noPos), impSpec)}
    else 
      return (term, imported_spec);
  mergeImport term imported_spec spc pos}

op evaluateSpecElem (qualifyConstructorsWithTypeName?: Bool) (spc : Spec) ((elem, pos) : SpecElemTerm) : Env Spec =
 case elem of
   | Import  terms                            -> return spc      % Already done
   | Type    (names,       dfn)               -> addType names dfn spc pos qualifyConstructorsWithTypeName?
   | Op      (names, fxty, refine?, dfn)      -> addOp   names fxty refine? dfn spc pos

   | Claim   (Axiom,      name, tyVars, term) -> return (addAxiom      ((addQualifier spc.qualifier name, tyVars, term, pos), spc)) 
   | Claim   (Theorem,    name, tyVars, term) -> return (addTheorem    ((addQualifier spc.qualifier name, tyVars, term, pos), spc))
   | Claim   (Conjecture, name, tyVars, term) -> return (addConjecture ((addQualifier spc.qualifier name, tyVars, term, pos), spc))
   | Claim   _                                -> error "evaluateSpecElem: unsupported claim type"

   | Pragma  (prefix, body, postfix)          -> return (addPragma     ((prefix, body, postfix, pos), spc))
   | Comment str                              -> return (addComment    (str, pos, spc))

op mergeImport (spec_term     : SCTerm)
               (imported_spec : Spec) 
               (old_spec      : Spec) 
               (pos           : Position) 
 : Env Spec =
 let types = old_spec.types in
 let ops   = old_spec.ops   in
 {
  new_spec  <- return (addImport ((spec_term, imported_spec), old_spec, pos));
  new_types <- if types = emptySpec.types then 
                 return imported_spec.types
               else 
                 %% TODO: fold over just infos?
                 foldOverQualifierMap (fn (_, _, info, types) ->
                                         return (mergeTypeInfo new_spec types info)) % Which should it be: old_spec, imported_spec, or new_spec ?
                                      types 
                                      imported_spec.types;

  new_ops   <- if ops = emptySpec.ops then 
                 return imported_spec.ops
               else 
                 %% TODO: fold over just infos?
                 foldOverQualifierMap (fn (_, _, info, ops) ->
                                         return (mergeOpInfo new_spec ops info false)) % Which should it be: old_spec, imported_spec, or new_spec ?
                                      ops
                                      imported_spec.ops;

 return (new_spec << {types = new_types,
                      ops   = new_ops})
 }

(*
 * The following wraps the existing \verb+elaborateSpec+ in a monad until
 * such time as the current one can made monadic.
 *)

op elaborateSpecM (spc : Spec) : Env Spec = 
 {unitId   <- getCurrentUID;
  filename <- return ((uidToFullPath unitId) ^ ".sw");
  case elaboratePosSpec (spc, filename) of
    | Spec spc    -> return spc
    | Errors (msgs, err_spc) -> raise (TypeCheckErrors (msgs, err_spc))
  }

op explicateHiddenAxiomsM (spc : Spec) : Env Spec =
 return spc % (explicateHiddenAxioms spc)

op applyOpRefinements (spc : Spec) : Env Spec =
 foldM (fn spc -> fn elem ->
          case elem of
            | OpDef (qid, refine_num, _, _) | refine_num > 0 ->
              % let _ = writeLine("aor0: "^printQualifiedId qid^show refine_num) in
              (case findTheOp (spc, qid) of
                 | Some opinfo ->
                   let trps = unpackTypedTerms opinfo.dfn in
                   let (tvs, ty, dfn) = nthRefinement (trps, refine_num) in
                   (case transformSteps? dfn of
                      | Some refine_stmt ->
                        let (_, _, prev_tm) = nthRefinement (trps, refine_num - 1) in
                        {transfm_stmt <- makeScript spc refine_stmt;
                         % print("aor: " ^ scriptToString (Steps steps) ^ scriptToString (Steps steps1) ^ "\n");
                         (tr_term, _, info) <- interpretTerm (spc, transfm_stmt, prev_tm, ty, qid, false);
                         new_dfn <- return (maybePiAndTypedTerm (replaceNthRefinement (trps, refine_num, (tvs, ty, tr_term))));
                         return (setOpInfo (spc, qid, opinfo << {dfn = new_dfn}))}
                      | _ -> return spc)
                 | _ -> return spc)
            | _ -> return spc)
      spc spc.elements

end-spec
