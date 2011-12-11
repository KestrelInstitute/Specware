spec
{

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

 op SCParser.mkSpecTerm (elements : SpecElemTerms, left : LCB, right : LCB) : SCTerm =
  SpecCalc.mkSpec (elements, mkRegion left right)

 op SCParser.mkToplevelTerm  (tm : SCTerm, left : LCB, right : LCB) : SpecTerm = 
  SpecCalc.mkTerm (tm, mkRegion left right)

 op SCParser.mkToplevelDecls (decls : SCDecls, left : LCB, right : LCB) : SpecTerm =
  SpecCalc.mkDecls (decls, mkRegion left right)
 
 op SCParser.mkPrint (term : SCTerm, left : LCB, right : LCB) : SCTerm = 
  SpecCalc.mkPrint (term, mkRegion left right)

 op SCParser.mkAbsoluteUnitId (path               : List String, 
                               parsed_fragment_id : ParserOptional String,
                               left               : LCB, 
                               right              : LCB) 
  : SCTerm = 
  let suffix : Option String = defaultToNone parsed_fragment_id in
  let uid = SpecPath_Relative {path = path, hashSuffix = suffix} in % relative to SPECPATH
  SpecCalc.mkUnitId (uid, mkRegion left right)

 op SCParser.mkRelativeUnitId (path               : List String, 
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

 op SCParser.mkLet              (decls     : SCDecls,     trm : SCTerm,        left : LCB, right : LCB) : SCTerm = SpecCalc.mkLet       (decls, trm,     mkRegion left right)
 op SCParser.mkWhere            (decls     : SCDecls,     trm : SCTerm,        left : LCB, right : LCB) : SCTerm = SpecCalc.mkWhere     (decls, trm,     mkRegion left right)
 op SCParser.mkQualify	        (qualifier : Qualifier,   trm : SCTerm,        left : LCB, right : LCB) : SCTerm = SpecCalc.mkQualify   (trm, qualifier, mkRegion left right)
 op SCParser.mkTranslate        (trm       : SCTerm,      renaming : Renaming, left : LCB, right : LCB) : SCTerm = SpecCalc.mkTranslate (trm, renaming,  mkRegion left right)

 op SCParser.mkUnannotatedOpRef      (opRef : QualifiedId,                      left : LCB, right : LCB) : QualifiedId * Option MSType = (opRef, None)      % TODO: use left and right
 op SCParser.mkAnnotatedOpRef        (opRef : QualifiedId, typ : MSType,        left : LCB, right : LCB) : QualifiedId * Option MSType = (opRef, Some typ)  % TODO: use left and right
 op SCParser.mkRenaming              (rules : RenamingRules,                    left : LCB, right : LCB) : Renaming     = (rules,                            mkRegion left right)
 op SCParser.mkTypeRenamingRule      (lref  : TypeRef,     rref : TypeRef,      left : LCB, right : LCB) : RenamingRule = (Type      (lref, rref, [rref]),   mkRegion left right)
 op SCParser.mkOpRenamingRule        (lref  : OpRef,       rref : OpRef,        left : LCB, right : LCB) : RenamingRule = (Op        (lref, rref, [rref.1]), mkRegion left right)
 op SCParser.mkAmbiguousRenamingRule (lref  : AmbigRef,    rref : AmbigRef,     left : LCB, right : LCB) : RenamingRule = (Ambiguous (lref, rref, [rref]),   mkRegion left right)

 op SCParser.mkSpecMorphismTerm      (dom : SCTerm, cod : SCTerm, rules : SpecMorphRules, pragmas : ParserOptional SM_Pragmas) 
  : SpecMorphismTerm = 
  (dom, cod, rules, defaultToNull pragmas)

 op SCParser.mkDiagramTerm      (elements : DiagElems) : DiagramTerm = elements
 op SCParser.mkNode	        (node_id  : Id,                           trm : SCTerm, left : LCB, right : LCB) : DiagElemBody = Node (node_id,                 trm) % TODO: mkRegion left right
 op SCParser.mkEdge             (edge_id  : Id, dom_id : Id, cod_id : Id, trm : SCTerm, left : LCB, right : LCB) : DiagElemBody = Edge (edge_id, dom_id, cod_id, trm) % TODO: mkRegion left right
 op SCParser.mkColimitTerm	(diag     : SCTerm,                                     left : LCB, right : LCB) : SCTerm = mkColimit (diag, mkRegion left right)

 op SCParser.mkSubstitute       (spec_term : SCTerm, sm_term    : SCTerm,         left : LCB, right : LCB) : SCTerm = SpecCalc.mkSubst     (spec_term, sm_term,    mkRegion left right)
 op SCParser.mkOpRefine 	(spec_term : SCTerm, elements   : SpecElemTerms,  left : LCB, right : LCB) : SCTerm = SpecCalc.mkOpRefine  (spec_term, elements,   mkRegion left right)
 op SCParser.mkTransform 	(spec_term : SCTerm, transforms : TransformExprs, left : LCB, right : LCB) : SCTerm = SpecCalc.mkTransform (spec_term, transforms, mkRegion left right)

 op SCParser.mkTransformName	     (name  : Id,                                       left : LCB, right : LCB) : TransformExpr = SpecCalc.mkTransformName         (name,            mkRegion left right)
 op SCParser.mkTransformNumber	     (num   : Nat,                                      left : LCB, right : LCB) : TransformExpr = SpecCalc.mkTransformNumber       (num,             mkRegion left right)
 op SCParser.mkTransformString	     (str   : String,                                   left : LCB, right : LCB) : TransformExpr = SpecCalc.mkTransformString       (str,             mkRegion left right)
%op SCParser.mkTransformBool 	     (b     : Bool,                                     left : LCB, right : LCB) : TransformExpr = SpecCalc.mkTransformBool         (b,               mkRegion left right)
 op SCParser.mkTransformSCTerm	     (uid   : SCTerm,                                   left : LCB, right : LCB) : TransformExpr = SpecCalc.mkTransformSCTerm       (uid,             mkRegion left right)
 op SCParser.mkTransformQual	     (q     : Qualifier,     id       : Id,             left : LCB, right : LCB) : TransformExpr = SpecCalc.mkTransformQual         (q, id,           mkRegion left right)
 op SCParser.mkTransformItem         (mod   : String,        expr     : TransformExpr,  left : LCB, right : LCB) : TransformExpr = SpecCalc.mkTransformItem         (mod,  expr,      mkRegion left right)
 op SCParser.mkTransformGlobalize    (typ   : TypeName, gvar : OpName, init : Option OpName,   
                                                                                        left : LCB, right : LCB) : TransformExpr = SpecCalc.mkTransformGlobalize    (typ, gvar, init, mkRegion left right)
 op SCParser.mkTransformApply        (head  : TransformExpr, args     : TransformExprs, left : LCB, right : LCB) : TransformExpr = SpecCalc.mkTransformApply        (head, args,      mkRegion left right)
 op SCParser.mkTransformApplyRecord  (head  : TransformExpr, recpairs : TransformExprs, left : LCB, right : LCB) : TransformExpr = SpecCalc.mkTransformApply        (head, recpairs,  mkRegion left right)
 op SCParser.mkTransformApplyOptions (head  : TransformExpr, args     : TransformExprs, left : LCB, right : LCB) : TransformExpr = SpecCalc.mkTransformApplyOptions (head, args,      mkRegion left right)
 op SCParser.mkTransformTuple        (items : TransformExprs,                           left : LCB, right : LCB) : TransformExpr = SpecCalc.mkTransformTuple        (items,           mkRegion left right)

 op SCParser.mkObligations 	     (term  : SCTerm,                                   left : LCB, right : LCB) : SCTerm        = SpecCalc.mkObligations (term, mkRegion left right)

 op SCParser.mkGenerate (target_language : String, 
                         sc_term         : SCTerm, 
                         filename        : ParserOptional Filename,
                         left            : LCB,
                         right           : LCB) 
  : SCTerm = 
  SpecCalc.mkGenerate (target_language, sc_term, defaultToNone filename, mkRegion left right)

 op SCParser.mkProve  		      (claim_name  : QualifiedId,
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
    
 op SCParser.mkAnswerVar     (annvar : Var)    : AnswerVar     = Some annvar

 op SCParser.mkExpand 	     (sc_term : SCTerm,                      left : LCB, right : LCB) : SCTerm = SpecCalc.mkExpand      (sc_term,          mkRegion left right)
 op SCParser.mkReduce 	     (ms_term : MSTerm,    sc_term : SCTerm, left : LCB, right : LCB) : SCTerm = SpecCalc.mkReduce      (ms_term, sc_term, mkRegion left right)
 op SCParser.mkExtend 	     (sc_term : SCTerm,                      left : LCB, right : LCB) : SCTerm = SpecCalc.mkExtendMorph (sc_term,          mkRegion left right)
 op SCParser.mkHide 	     (names   : NameExprs, sc_term : SCTerm, left : LCB, right : LCB) : SCTerm = SpecCalc.mkHide        (names, sc_term,   mkRegion left right)
 op SCParser.mkExport 	     (names   : NameExprs, sc_term : SCTerm, left : LCB, right : LCB) : SCTerm = SpecCalc.mkExport      (names, sc_term,   mkRegion left right)

 op SCParser.mkAmbiguousRef  (ref : QualifiedId,                   left : LCB, right : LCB) : NameExpr = Ambiguous ref  % TODO: use left, right
 op SCParser.mkTypeRef       (ref : QualifiedId,                   left : LCB, right : LCB) : NameExpr = Type      ref  % TODO: use left, right
 op SCParser.mkOpRef 	     (ref : QualifiedId * Option MSType,   left : LCB, right : LCB) : NameExpr = Op        ref  % TODO: use left, right
 op SCParser.mkClaimRef      (claim_type, claimref : QualifiedId,  left : LCB, right : LCB) : NameExpr = case claim_type of
                                                                                                                      | "Axiom"      -> Axiom      claimref
                                                                                                                      | "Theorem"    -> Theorem    claimref
                                                                                                                      | "Conjecture" -> Conjecture claimref

 op SCParser.mkFragmentId (char  : Char, 
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

 op SCParser.mkImportDeclaration (tms : SCTerms, left : LCB, right : LCB) 
  : SpecElemTerm = 
  mkImportSpecElem (tms, mkRegion left right)

 op SCParser.mkTypeDeclaration (names : MSTypeNames, 
                                tvs   : MSTypeVars,
                                left  : LCB,
                                right : LCB) 
  : SpecElemTerm = 
  SpecCalc.mkTypeSpecElem (names, tvs, [], mkRegion left right)

 op SCParser.mkTypeDefinition (names : MSTypeNames, 
                               tvs   : MSTypeVars, 
                               defs  : MSTypes, 
                               left  : LCB, 
                               right : LCB) 
  : SpecElemTerm = 
  SpecCalc.mkTypeSpecElem (names, tvs, defs, mkRegion left right)

(*
 op SCParser.mkOpSpecElem (names    : MSOpNames,  
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

 op SCParser.mkPragma 	       (prefix : String, body : String, postfix : String,                     left : LCB, right : LCB) : SpecElemTerm = SpecCalc.mkPragma (prefix, body, postfix, mkRegion left right)

 op SCParser.mkClaimDefinition (kind : PropertyType, label : PropertyName, claim : Id, term : MSTerm, left : LCB, right : LCB) : SpecElemTerm = (Claim (kind, label, [], term), mkRegion left right)

 op SCParser.mkSMPragma        (prefix : String, body : String, postfix : String,                     left : LCB, right : LCB) : SM_Pragma    = ((prefix, body, postfix),          mkRegion left right)

}
