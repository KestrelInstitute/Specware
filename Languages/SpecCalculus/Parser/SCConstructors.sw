(* Copyright 2015 Kestrel Institute. See file LICENSE for license details *)

SCParser qualifying spec

 import /Languages/SpecCalculus/AbstractSyntax/Types

 %% =============================================================================
 %%  Hacks to interface to lisp code used by parser.
 %%  The lisp code may return the lisp atom :unspecified in some contexts,
 %%  which we may interpret as None, [], etc. depending on context.
 %%  That may also affect how we interpret a specified value (e.g. as Some x).
 %% =============================================================================

 type ParserOptional a  % to indicate that value might be non-MetaSlang value of :unspecified

 op [a] Parser4.parser_unspecified? : ParserOptional a -> Bool % primitive defined in semantics.lisp
 op [a] Parser4.parser_id           : ParserOptional a -> a    % primitive defined in semantics.lisp
 op     Parser4.makeRegion          : LCB * LCB -> Position    % primitive defined in semantics.lisp

 op [a] defaultToNull (x : ParserOptional (List a)) : List a =
   if Parser4.parser_unspecified? x then
     []
   else
     Parser4.parser_id x

 op [a] defaultToNone (x : ParserOptional a) : Option a =
   if Parser4.parser_unspecified? x then
     None
   else
     Some (Parser4.parser_id x)

 %% =============================================================================
 %%  Convenient local names for imported types.
 %%  TODO: propagate these back to source file
 %% =============================================================================

 type LCB         = LineColumnByte
 type MSTypeVars  = TyVars
 type MSTypeNames = MetaSlang.TypeNames
 type MSOpNames   = MetaSlang.OpNames

 %% =============================================================================

 op mkRegion (left : LCB) (right : LCB) : Position =
   Parser4.makeRegion (left, right)

 op mkImportSpecElem (tms : SCTerms, pos : Position) : SpecElemTerm = 
  (Import tms, pos)

 op SpecCalc.mkSCDecl (name : String, term : SCTerm, left : LCB, right : LCB) : SCDecl = 
  % TODO: don't ignore left and right
  (name, term)

 op mkSpecTerm (elements : SpecElemTerms, left : LCB, right : LCB) : SCTerm =
  SpecCalc.mkSpec (elements, mkRegion left right)

 op mkToplevelTerm  (tm : SCTerm, left : LCB, right : LCB) : SpecTerm = 
  SpecCalc.mkTerm (tm, mkRegion left right)

 op mkToplevelDecls (decls : SCDecls, left : LCB, right : LCB) : SpecTerm =
  SpecCalc.mkDecls (decls, mkRegion left right)
 
 op mkPrint (term : SCTerm, left : LCB, right : LCB) : SCTerm = 
  SpecCalc.mkPrint (term, mkRegion left right)

 op parseUnitId (str : String, left : LCB, right : LCB) : SCTerm =
  %% We assume str is a sequence of non-whitespace chars.
  %% If the first char is a slash, this is SpecPath_Relative, else UnitId_Relative.
  %% The string is split at slashes, and then the final element is split at the first 
  %% hash mark (if any).
  %% Examples:
  %% "a/b/c"        ==>  UnitId_Relative   {path = ["a", "b",   "c"], suffix = None}
  %% "/a/b/c"       ==>  SpecPath_Relative {path = ["a", "b",   "c"], suffix = None}
  %% "/a/b#c/x#y#z" ==>  SpecPath_Relative {path = ["a", "b#c", "x"], suffix = Some "y#z"}

  let region = mkRegion left right in
  let chars  = explode str         in
  let (absolute?, chars) = 
      case chars of
        | #/ :: tail -> (true,  tail)
        | _ ->          (false, chars)
  in
  let
    def split_at_slashes chars =
      case splitAtLeftmost (fn c -> c = #/) chars of
        | Some (x, _, tail) -> x |> (split_at_slashes tail)
        | _ -> [chars]
  in
  let lists_of_chars = split_at_slashes chars in
  let all_but_last   = butLast lists_of_chars in 
  let final          = last    lists_of_chars in 
  let (final, suffix) =
      case splitAtRightmost (fn c -> c = #\#) final of
        | Some (x, _, y) -> (x,     Some (implode y))
        | _              -> (final, None)
  in
  let path_and_suffix = {path       = map implode (all_but_last <| final),
                         hashSuffix = suffix}  
  in
  let uid = 
      if absolute? then
        SpecPath_Relative path_and_suffix % relative to SPECPATH
      else
        UnitId_Relative   path_and_suffix % relative to current unit id
  in
  SpecCalc.mkUnitId (uid, mkRegion left right)
             
 op mkAbsoluteUnitId (path               : List String, 
                      parsed_fragment_id : ParserOptional String,
                      left               : LCB, 
                      right              : LCB) 
  : SCTerm = 
  let suffix : Option String = defaultToNone parsed_fragment_id in
  let uid = SpecPath_Relative {path = path, hashSuffix = suffix} in % relative to SPECPATH
  SpecCalc.mkUnitId (uid, mkRegion left right)

 op mkRelativeUnitId (path               : List String, 
                      parsed_fragment_id : ParserOptional String,
                      left               : LCB, 
                      right              : LCB) 
  : SCTerm = 
  let suffix : Option String = defaultToNone parsed_fragment_id in
  let uid = UnitId_Relative {path = path, hashSuffix = suffix} in  % relative to current unit id
  SpecCalc.mkUnitId (uid, mkRegion left right)

 type AmbigRef = QualifiedId 
 type TypeRef  = QualifiedId 
 type OpRef    = QualifiedId * Option MSType

 op mkLet              (decls     : SCDecls,     trm : SCTerm,        left : LCB, right : LCB) : SCTerm = SpecCalc.mkLet       (decls, trm,     mkRegion left right)
 op mkWhere            (decls     : SCDecls,     trm : SCTerm,        left : LCB, right : LCB) : SCTerm = SpecCalc.mkWhere     (decls, trm,     mkRegion left right)
 op mkQualify	        (qualifier : Qualifier,   trm : SCTerm,        left : LCB, right : LCB) : SCTerm = SpecCalc.mkQualify   (trm, qualifier, mkRegion left right)
 op mkTranslate        (trm       : SCTerm,      renaming : Renaming, left : LCB, right : LCB) : SCTerm = SpecCalc.mkTranslate (trm, renaming,  mkRegion left right)

 op mkUnannotatedOpRef      (opRef : QualifiedId,                      left : LCB, right : LCB) : QualifiedId * Option MSType = (opRef, None)      % TODO: use left and right
 op mkAnnotatedOpRef        (opRef : QualifiedId, typ : MSType,        left : LCB, right : LCB) : QualifiedId * Option MSType = (opRef, Some typ)  % TODO: use left and right
 op mkRenaming              (rules : RenamingRules,                    left : LCB, right : LCB) : Renaming     = (rules,                            mkRegion left right)
 op mkTypeRenamingRule      (lref  : TypeRef,     rref : TypeRef,      left : LCB, right : LCB) : RenamingRule = (Type      (lref, rref, [rref]),   mkRegion left right)
 op mkOpRenamingRule        (lref  : OpRef,       rref : OpRef,        left : LCB, right : LCB) : RenamingRule = (Op        (lref, rref, [rref.1]), mkRegion left right)
 op mkAmbiguousRenamingRule (lref  : AmbigRef,    rref : AmbigRef,     left : LCB, right : LCB) : RenamingRule = (Ambiguous (lref, rref, [rref]),   mkRegion left right)

 op mkSpecMorphismTerm      (dom : SCTerm, cod : SCTerm, rules : SpecMorphRules, pragmas : ParserOptional SM_Pragmas) 
  : SpecMorphismTerm = 
  (dom, cod, rules, defaultToNull pragmas)

 op mkDiagramTerm      (elements : DiagElems) : DiagramTerm = elements
 op mkNode	        (node_id  : Id,                           trm : SCTerm, left : LCB, right : LCB) : DiagElemBody = Node (node_id,                 trm) % TODO: mkRegion left right
 op mkEdge             (edge_id  : Id, dom_id : Id, cod_id : Id, trm : SCTerm, left : LCB, right : LCB) : DiagElemBody = Edge (edge_id, dom_id, cod_id, trm) % TODO: mkRegion left right
 op mkColimitTerm	(diag     : SCTerm,                                     left : LCB, right : LCB) : SCTerm = mkColimit (diag, mkRegion left right)

 op mkSubstitute       (spec_term : SCTerm, sm_term : SCTerm, pragmas : ParserOptional SM_Pragmas, left : LCB, right : LCB) : SCTerm =
   SpecCalc.mkSubst     (spec_term, sm_term, defaultToNull pragmas, mkRegion left right)
 op mkOpRefine 	(spec_term : SCTerm, elements : SpecElemTerms,  left : LCB, right : LCB) : SCTerm = SpecCalc.mkOpRefine  (spec_term, elements,   mkRegion left right)
 op mkTransform 	(spec_term : SCTerm, transfm : TransformExpr, left : LCB, right : LCB) : SCTerm =
    SpecCalc.mkTransform (spec_term, transfm, [], mkRegion left right)

 op mkTransformName   (name  : Id,         left : LCB, right : LCB) : TransformExpr = SpecCalc.mkTransformName(name,  mkRegion left right)
 op mkTransformNumber (num   : Nat,        left : LCB, right : LCB) : TransformExpr = SpecCalc.mkTransformNumber(num, mkRegion left right)
 op mkTransformString (str   : String,     left : LCB, right : LCB) : TransformExpr = SpecCalc.mkTransformString(str, mkRegion left right)
%op mkTransformBool   (b     : Bool,       left : LCB, right : LCB) : TransformExpr = SpecCalc.mkTransformBool(b, mkRegion left right)
 op mkTransformSCTerm (uid   : SCTerm,     left : LCB, right : LCB) : TransformExpr = SpecCalc.mkTransformSCTerm(uid, mkRegion left right)
 op mkTransformQuotedTerm (tm: MSTerm,     left : LCB, right : LCB) : TransformExpr = SpecCalc.mkTransformQuotedTerm(tm, mkRegion left right)
 op mkTransformQual (q: Qualifier, id: Id, left : LCB, right : LCB) : TransformExpr = SpecCalc.mkTransformQual(q, id, mkRegion left right)
 op mkTransformItem(mod: String, expr: TransformExpr, left : LCB, right : LCB) : TransformExpr =
    SpecCalc.mkTransformItem(mod,  expr, mkRegion left right)
 op mkTransformRecord  (recpairs: List (String * TransformExpr), left : LCB, right : LCB) : TransformExpr =
    SpecCalc.mkTransformRecord  (recpairs, mkRegion left right)
 op mkTransformOptions (args : TransformExprs,  left : LCB, right : LCB) : TransformExpr =
    SpecCalc.mkTransformOptions (args, mkRegion left right)
 op mkTransformTuple   (items : TransformExprs, left : LCB, right : LCB) : TransformExpr =
    SpecCalc.mkTransformTuple   (items, mkRegion left right)
 op mkTransformCommand (head: String, args: TransformExprs, left : LCB, right : LCB) : TransformExpr =
    SpecCalc.mkTransformCommand (head, args, mkRegion left right)

 op mkObligations 	     (term  : SCTerm,                                   left : LCB, right : LCB) : SCTerm        = SpecCalc.mkObligations (term, mkRegion left right)

 op mkGenerate (target_language : String, 
                         sc_term         : SCTerm, 
                         filename        : ParserOptional Filename,
                         left            : LCB,
                         right           : LCB) 
  : SCTerm = 
  SpecCalc.mkGenerate (target_language, sc_term, defaultToNone filename, mkRegion left right)

 op mkProve (claim_name  : QualifiedId,
             sc_term     : SCTerm,
             prover_name : ProverName,
             assertions  : ParserOptional ClaimNames,
             opts        : ParserOptional ProverOptions,
             answer_var  : ParserOptional AnswerVar,
             left        : LCB,
             right       : LCB)
  : SCTerm =
  
  let _ = if prover_name in? ["Snark", "PVS", "FourierM", "Checker"] then
            ()
          else
            writeLine ("Unrecognized prover: " ^ prover_name ^ ", not Snark, PVS, FourierM, or Checker")
  in
  let assertions = if parser_unspecified? assertions then All             else Explicit (parser_id assertions) in
  let opts       = if parser_unspecified? opts       then OptionString [] else parser_id opts                  in
  let answer_var = if parser_unspecified? answer_var then None            else parser_id answer_var            in
  let here       = mkRegion left right                                                   in

  if claim_name = Qualified (UnQualified, "WellFormed") then
    SpecCalc.mkProofCheck (WellFormed,       sc_term, prover_name, assertions, opts, ProverBase,             here)
  else if prover_name = "Checker" then
    SpecCalc.mkProofCheck (Claim claim_name, sc_term, prover_name, assertions, opts, ProverBase,             here)
  else    
    SpecCalc.mkProve      (claim_name,       sc_term, prover_name, assertions, opts, ProverBase, answer_var, here)
    
 op mkAnswerVar     (annvar : MSVar)    : AnswerVar     = Some annvar

 op mkExpand 	     (sc_term : SCTerm,                      left : LCB, right : LCB) : SCTerm = SpecCalc.mkExpand      (sc_term,          mkRegion left right)
 op mkReduce 	     (ms_term : MSTerm,    sc_term : SCTerm, left : LCB, right : LCB) : SCTerm = SpecCalc.mkReduce      (ms_term, sc_term, mkRegion left right)
%% op mkExtend 	     (sc_term : SCTerm,                      left : LCB, right : LCB) : SCTerm = SpecCalc.mkExtendMorph (sc_term,          mkRegion left right)
 op mkHide 	     (names   : NameExprs, sc_term : SCTerm, left : LCB, right : LCB) : SCTerm = SpecCalc.mkHide        (names, sc_term,   mkRegion left right)
 op mkExport 	     (names   : NameExprs, sc_term : SCTerm, left : LCB, right : LCB) : SCTerm = SpecCalc.mkExport      (names, sc_term,   mkRegion left right)

 op mkAmbiguousRef  (ref : QualifiedId,                   left : LCB, right : LCB) : NameExpr = Ambiguous ref  % TODO: use left, right
 op mkTypeRef       (ref : QualifiedId,                   left : LCB, right : LCB) : NameExpr = Type      ref  % TODO: use left, right
 op mkOpRef 	     (ref : QualifiedId * Option MSType,   left : LCB, right : LCB) : NameExpr = Op        ref  % TODO: use left, right
 op mkClaimRef      (claim_type, claimref : QualifiedId,  left : LCB, right : LCB) : NameExpr = case claim_type of
                                                                                                                      | "Axiom"      -> Axiom      claimref
                                                                                                                      | "Theorem"    -> Theorem    claimref
                                                                                                                      | "Conjecture" -> Conjecture claimref

 op mkFragmentId (char  : Char, 
                           num   : ParserOptional Nat, 
                           sym   : ParserOptional String, 
                           left  : LCB, 
                           right : LCB)
  : String = 
  let s1 = if char in? [#S, #T] then "" else show char in
  let s2 = if parser_unspecified? num  then "" else show (parser_id num) in 
  let s3 = if parser_unspecified? sym  then "" else parser_id sym        in
  let id = s1 ^ s2 ^ s3 in  
  let _ = if isNum char then writeLine ("Fragment identifiers must be simple names, hence must not begin with digits: " ^ id) else () in
  let _ = if id = ""    then writeLine "Fragment identifier is missing"                                                       else () in
  %% TODO: use left, right
  id 

 op mkImportDeclaration (tms : SCTerms, left : LCB, right : LCB) 
  : SpecElemTerm = 
  mkImportSpecElem (tms, mkRegion left right)

 op mkTypeDeclaration (names : MSTypeNames, 
                                tvs   : MSTypeVars,
                                left  : LCB,
                                right : LCB) 
  : SpecElemTerm = 
  SpecCalc.mkTypeSpecElem (names, tvs, [], mkRegion left right)

 op mkTypeDefinition (names : MSTypeNames, 
                               tvs   : MSTypeVars, 
                               defs  : MSTypes, 
                               left  : LCB, 
                               right : LCB) 
  : SpecElemTerm = 
  SpecCalc.mkTypeSpecElem (names, tvs, defs, mkRegion left right)

(*
 op mkOpSpecElem (names    : MSOpNames,  
                           fixity   : Fixity,
                           pre_tvs  : MSTypeVars,
                           post_tvs : MSTypeVars,
                           opt_type : MSType,
                           params   : MSPatterns,
                           dfn      : MSTerm,
                           refn     : Bool,
                           trans    : MSTransformExpr,
                           left     : LCB,
                           right    : LCB)
  : SpecElemTerm =
  mkOpSpecElem (names, fixity, tvs, typ, dfn, refine?, mkRegion left right)
*)

 op mkPragma 	       (prefix : String, body : String, postfix : String,                     left : LCB, right : LCB) : SpecElemTerm = SpecCalc.mkPragma (prefix, body, postfix, mkRegion left right)

 op mkClaimDefinition (kind : PropertyType, label : PropertyName, claim : Id, term : MSTerm, left : LCB, right : LCB) : SpecElemTerm = (Claim (kind, label, [], term), mkRegion left right)

 op mkSMPragma        (prefix : String, body : String, postfix : String,                     left : LCB, right : LCB) : SM_Pragma    = ((prefix, body, postfix),          mkRegion left right)

end-spec
