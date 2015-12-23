(* Copyright 2015 Kestrel Institute. See file LICENSE for license details *)

%%% Spec Calculus Abstract Syntax

SpecCalc qualifying spec

 %% We import PosSpec for Position, QualifiedId, ATypeScheme etc.  This is a
 %% bit of a shame as AnnSpec would like to import this spec so as to insert
 %% a spec calculus term in the import of a spec. This would create a cyclic
 %% dependency between specs. At present, this is addressed in AnnSpec by
 %% defining an abstract type SCTerm, which is refined below.

 %% Value.sw indirectly imports Types.sw

 import /Languages/MetaSlang/Specs/StandardSpec    % Position, QualifiedId, Var, etc.
 import /Library/Legacy/Utilities/Lisp             % LispCell (see ProverOptions)
 import /Languages/SpecCalculus/Semantics/ValueSig % ValueInfo
 import UnitId                                     % UnitId, RelativeUnitId
 import SCTerm                                     % SCTerm

 %% All the objects in the abstract syntax are polymorphic and defined at
 %% two levels.  The first level pairs the type the type parameter. 
 %% The second level defines the constructors for the type.
 %% In this way, every type is annotated. The annotation is typically 
 %% information about the position of the term in the file. 
 %% It is not clear that there is any benefit in making this polymorphic. 
 %% Might might be enough to pair it with the Position type and then 
 %% refine that type.  Using two levels ensures that for all objects in the 
 %% abstract syntax tree, the position information is always the second component.

 %%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%

 %% The type Name is used everywhere that one can expect a non-structured identifier. 
 %% This includes for instance, the names of vertices and edges in the shape of a diagram. 
 %% It also includes the qualifiers on op and type names.
 %% 
 %% In the near term, it also includes the identifiers bound by declarations.
 %% These are either let bound or bound by specs listed in a file. Later, we might allow
 %% bound identifiers to be UIDs thus enabling one to override an existing definition.

 type Name = String

 %%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%

 %% The following is the toplevel returned by the parser. 
 %% A file may contain a list of name = term or contain a single term. 
 %% This should not be polymorphic.
 %% The type parameter should be instantiated with the type Position.

 type SpecTerm       = SpecTermBody * Position

 type SpecTermBody   = | Term  SCTerm 
                       | Decls SCDecls

 op mkTerm (term  : SCTerm, pos : Position) 
  : SpecTerm = 
  (Term term, pos)

 op mkDecls (decls : SCDecls, pos : Position) 
  : SpecTerm = 
  (Decls decls, pos)

 %%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%
 %% The following is the type given to us by the parser.
 %%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%

 type SCTerm = SCTermBody * Position
 type SCTermBody = 
   | UnitId       RelativeUID
   | Print        PrintTerm            
   | Prove        ProveTerm           
   | ProofCheck   ProofCheckTerm      
   | Spec         ExplicitSpecTerm        
   | Diag         DiagramTerm          
   | Colimit      ColimitTerm         
   | SpecMorph    SpecMorphismTerm    
   | SpecInterp   SpecInterpTerm      
   | SpecPrism    SpecPrismTerm       
   | DiagMorph    DiagramMorphismTerm 
%%   | ExtendMorph  ExtendMorphismTerm  
   | Qualify      QualifyTerm          
   | Translate    TranslateTerm        
   | Let          LetTerm              
   | Where        WhereTerm           
   | Hide         HideTerm              % Control visibilty of names outside a spec.
   | Export       ExportTerm            % Control visibilty of names outside a spec.
   | Generate     GenerateTerm        
   | Subst        SubstTerm           
   | OpRefine     OpRefineTerm         
   | Transform    TransformTerm       
   | Obligations  ObligationsTerm     
   | Expand       ExpandTerm          
   | Reduce       ReduceTerm           
   | Other        (OtherTerm Position)  % A hook for for creating applications that are extensions to Specware.
                                        % If more than one new term is needed, OtherTerm can be a coproduct of desired terms.
   | Quote        ValueInfo             % Used to capture an internally created value and turn it into a Term when needed.

 %%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%

 op mkUnitId (uid : RelativeUID, pos : Position) 
  : SCTerm = 
  (UnitId uid, pos)

 %%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%

 type PrintTerm = SCTerm 

 op mkPrint (term : SCTerm, pos : Position) : SCTerm = 
  (Print term, pos)

 %%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%

 type ProveTerm = ClaimName * SCTerm * ProverName * Assertions * ProverOptions * ProverBaseOptions * AnswerVar

 type ProverName = Name

 type Assertions = 
   | All
   | Explicit ClaimNames

 type ProverOptions = 
   | OptionString LispCells
   | OptionName   QualifiedId
   | Error        (String * String)  % error msg, problematic string

 type ProverBaseOptions = | ProverBase | Base | AllBase | NoBase
  
 type AnswerVar = Option MSVar

 op mkProve (claim_name     : ClaimName, 
             term           : SCTerm,
             prover_name    : ProverName,
             assertions     : Assertions,
             prover_options : ProverOptions,
             includeBase?   : ProverBaseOptions,
             answer_var     : AnswerVar,
             pos            : Position)
  : SCTerm = 
  (Prove (claim_name, term, prover_name, assertions, prover_options, includeBase?, answer_var), pos)

 %%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%

 type ProofCheckTerm = PCClaimName * SCTerm * ProverName * Assertions * ProverOptions * ProverBaseOptions

 type PCClaimName = | WellFormed | Claim QualifiedId
 type ClaimNames  = List ClaimName
 type ClaimName   = QualifiedId

 op mkProofCheck  (claim_name     : PCClaimName,
                   term           : SCTerm,
                   prover_name    : ProverName,
                   assertions     : Assertions,
                   prover_options : ProverOptions,
                   includeBase?   : ProverBaseOptions,
                   pos            : Position)
  : SCTerm =
  (ProofCheck (claim_name, term, prover_name, assertions, prover_options, includeBase?), pos) 

 %%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%


 %% A SpecElemTerm is a declaration within a spec -- the ops types etc.

 type SpecElemTerm  = SpecElemBody * Position
 type SpecElemTerms = List SpecElemTerm
 type ExplicitSpecTerm = SpecElemTerms

 type SpecElemBody =
   | Import  SCTerms
   | Type    Aliases * MSType
   | Op      Aliases * Fixity * Bool * MSTerm
   | Claim   PropertyType * PropertyName * TyVars * MSTerm
   | Pragma  String * String * String
   | Comment String

 %% These are used by the parser to create SpecElemTerm's
 %% They can be changed to adapt to new structures for SpecElemTerm's
 %% without altering the parser code in semantics.lisp

 op mkPragma (prefix  : String, 
              body    : String, 
              postfix : String, 
              pos     : Position) 
  : SpecElemTerm =
  (Pragma (prefix, body, postfix), pos)

 %% The following two functions are defined using hand-written lisp code in 
 %%  Languages/SpecCalculus/Parser/Handwritten/Lisp/semantics.lisp
 %% They store and retrieve information in a hash-table not visisble to
 %%  Specware execpt through this interface:

 %% Note: The alphabetized field_names value passed to setOrginalFieldOrders 
 %%       is replaced by the original alphabetized list before being saved,
 %%       using transient information available to the parser code.
 %%       (See Languages/SpecCalculus/Parser/Handwritten/Lisp/semantics.lisp)

 op setOrginalFieldOrders (name : TypeName, field_names : List Id) : () % ad hoc
 op getOrginalFieldOrders (name : TypeName) : List Id                   % ad hoc

 op rememberOrginalFieldOrdersForCGen (name : TypeName, dfn : MSType) : () =
  let inner_dfn =
      case dfn of
        | Pi  (_, dfn,   _) -> dfn
        | And (dfn :: _, _) -> dfn
        | _                 -> dfn
  in
  case inner_dfn of
    | Product (fields, _) ->
      let field_names = map (fn (field_name, _) -> field_name) fields in
      %% let _ = writeLine("Save order for " ^ anyToString name) in
      %% let _ = writeLine("fields: " ^ anyToString field_names) in
      setOrginalFieldOrders (name, field_names)
    | _ ->
      ()

 op mkTypeSpecElem (names : TypeNames, 
                    tvs   : TyVars, 
                    defs  : MSTypes,
                    pos   : Position) 
  : SpecElemTerm =
  let dfn = 
      case defs of
        | []    -> maybePiType (tvs, Any pos)
        | [dfn] -> maybePiType (tvs, dfn)
        | _     -> And (map (fn srt -> maybePiType (tvs, srt)) defs, 
                        pos)
  in
  let _ = map (fn name -> 
                 rememberOrginalFieldOrdersForCGen (name, dfn)) 
              names 
  in
  (Type (names, dfn), pos)

 op mkOpSpecElem (names   : OpNames, 
                  fixity  : Fixity, 
                  tvs     : TyVars, 
                  srt     : MSType,
                  defs    : MSTerms,
                  refine? : Bool, 
                  pos     : Position) 
  : SpecElemTerm =
  %% We potentially could be smarter if srt is just a meta type var
  %% and use just a normal term instead of a typed term, but that's
  %% a complication we don't need now (or perhaps ever).
  let dfn =
      case defs of
	| []   -> TypedTerm (Any pos, srt, pos) % op decl
        | [tm] -> tm
  in
  let dfn = maybePiTerm (tvs, dfn) in
  (Op (names, fixity, refine?, dfn), pos)

 op mkSpec (elements : SpecElemTerms, pos : Position) : SCTerm = 
  (Spec elements, pos)

 %%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%

 type DiagramTerm = DiagElems

 %% A diagram is defined by a list of elements. An element may be a labeled
 %% vertex or edge.
 %% 
 %% In the current form, the names of vertices and edges are simply Names.
 %% This may change in the future. In particular, one can construct limits and 
 %% colimits of diagram in which case, vertices and edges in the resulting 
 %% shape may be tuples and equivalence classes. It remains to be seen whether 
 %% we need a concrete syntax for this.

 type DiagElems    = List DiagElem
 type DiagElem     = DiagElemBody * Position
 type DiagElemBody = | Node NodeId * SCTerm
                     | Edge EdgeId * NodeId * NodeId * SCTerm
 type NodeId = Name
 type EdgeId = Name

 op mkDiag (elements : DiagElems, pos : Position) : SCTerm = 
  (Diag elements, pos)

 %%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%

 type ColimitTerm = SCTerm 
 op mkColimit (diag : SCTerm, pos : Position) : SCTerm = 
  (Colimit diag, pos)

 %%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%

 type SpecMorphismTerm = SCTerm * SCTerm * SpecMorphRules * SM_Pragmas 
 %% The calculus supports two types of morphisms: morphisms between specs and
 %% morphisms between diagrams.  Right now spec morphism are distinguished
 %% from diagram morphisms in both the concrete and abstract syntax.
 %% The first two elements in the morphism products are terms that evaluate
 %% to the domain and codomain of the morphisms.

 type SpecMorphRules    = List SpecMorphRule
 type SpecMorphRule     = SpecMorphRuleBody * Position
 type SpecMorphRuleBody = 
   | Ambiguous QualifiedId                   * QualifiedId 
   | Type      QualifiedId                   * QualifiedId
   | Op        (QualifiedId * Option MSType) * (QualifiedId * Option MSType)

 type SM_Pragmas = List SM_Pragma 
 type SM_Pragma  = (String * String * String) * Position

 op mkSpecMorph (dom_term : SCTerm, 
                 cod_term : SCTerm, 
                 rules    : SpecMorphRules, 
                 pragmas  : SM_Pragmas, 
                 pos      : Position) 
  : SCTerm =
  (SpecMorph (dom_term, cod_term, rules, pragmas), pos)

 %%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%

 type SpecInterpTerm      = SCTerm * SCTerm * SpecInterpRules
 type SpecInterpRules     = SpecInterpRulesBody * Position
 type SpecInterpRulesBody = 
   %% This is the form used by Specware 2 -- a cospan, where the codomain-to-mediator.
   %% morphism is presumably a definitional extension.
   %% Alternatively, this could be expressed as symbol to term mappings,
   %% or as a quotient of morphisms (where an interpretation is viewed as a morphism
   %% from a quotient of isomorphic specs to a quotient of isomorphic specs).
   {med : SCTerm,
    d2m : SCTerm,
    c2m : SCTerm}

 op mkSpecInterpRules (med : SCTerm, 
                       d2m : SCTerm, 
                       c2m : SCTerm, 
                       pos : Position) 
  : SpecInterpRules =
  ({med = med, d2m = d2m, c2m = c2m}, pos)

 op mkSpecInterp  (dom_term : SCTerm, 
                   cod_term : SCTerm, 
                   rules    : SpecInterpRules, 
                   pos      : Position) 
  : SCTerm =
  (SpecInterp (dom_term, cod_term, rules), pos)

 %%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%

 %% In Uniform mode, we may choose a fixed specific morphism (Nth i),
 %% a fixed random morphism, or iterative though all different morphisms.

 %% In per instance mode, we choose a morphism at random for each
 %% occurence of each op, using the provided additional morphisms
 %% or interpretations to translate as necessary when the resulting
 %% types would otherwise not match.

 type SpecPrismTerm = SCTerm * SCTerms * PrismModeTerm 
   %% The first  arg denotes a shared domain spec.
   %% The second arg denotes a list of morphisms, all with the same domain spec.
   %% The third  arg gives the rules for choosing among the morphism.

 type PrismModeTerm = 
   | Uniform      PrismSelection
   | PerInstance  SCTerms     % sms or interps

 type PrismSelection = | Nth Nat | Random | Generative

 op mkSpecPrism (dom_term : SCTerm, 
                 sm_terms : SCTerms, 
                 pmode    : PrismModeTerm, 
                 pos      : Position) 
  : SCTerm =
  (SpecPrism (dom_term, sm_terms, pmode), pos)

 op mkPrismPerInstance (interps : SCTerms) : PrismModeTerm =
  PerInstance interps

 op mkPrismUniform (s : PrismSelection) : PrismModeTerm =
  Uniform s

 %%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%

 %% Note that the term associated with a node must evaluate to a spec or diagram. 
 %% The term for an edge must evaluate to a spec morphism or diagram morphism.
 %% 
 %% The syntax for spec morphisms accommodates mapping names to terms but
 %% the interpreter handles only name to name maps for now.
 %% 
 %% The tagging in the types below may be excessive given the ATerm is already tagged.
 
 %% The current syntax allows one to write morphisms mapping names to terms
 %% but only name/name mappings will be handled by the interpreter in the
 %% near term.
 %% 
 %% A diagram morphism has two types of elements: components of the shape map
 %% and components of the natural transformation. The current syntax allows
 %% them to be presented in any order. 

 %% A NatTranComp element is a component in a natural transformation between diagrams. 
 %% The components are indexed by vertices in the shape.
 %% The term in the component must evaluate to a morphism.

 type DiagramMorphismTerm = SCTerm * SCTerm * DiagMorphRules
 type DiagMorphRules      = List DiagMorphRule
 type DiagMorphRule       = DiagMorphRuleBody * Position
 type DiagMorphRuleBody   = | ShapeMap    Name * Name
                            | NatTranComp Name * SCTerm 

 op mkDiagMorph (dom_term : SCTerm, 
                 cod_term : SCTerm, 
                 rules    : DiagMorphRules,
                 pos      : Position) 
  : SCTerm =
  (DiagMorph (dom_term, cod_term, rules), pos)

 %%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%

 %% type ExtendMorphismTerm = SCTerm

 %% op  mkExtendMorph (term : SCTerm, pos : Position) : SCTerm = 
 %%  (ExtendMorph term, pos)

 %%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%

 type QualifyTerm = SCTerm * Name

 op  mkQualify (term : SCTerm, name : Name, pos : Position) : SCTerm = 
  (Qualify (term, name), pos)

 %%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%

 type TranslateTerm = SCTerm * Renaming

 %% A Renaming denotes some mappings of names, e.g. for types, ops,
 %% and possibly other entities.
 %% Some mappings may be ambiguous until placed in some context.

 type Renaming      = RenamingRules * Position
 type RenamingRules = List RenamingRule
 type RenamingRule  = RenamingRuleBody * Position
 type RenamingRuleBody =
   | Ambiguous QualifiedId                   * QualifiedId                   * Aliases   % last field is all aliases, including name in second field
   | Type      QualifiedId                   * QualifiedId                   * TypeNames % last field is all aliases, including name in second field
   | Op        (QualifiedId * Option MSType) * (QualifiedId * Option MSType) * OpNames   % last field is all aliases, including name in second field
   | Other     OtherRenamingRule

 op  mkTranslate (term : SCTerm, renaming : Renaming, pos : Position) 
  : SCTerm = 
  (Translate (term, renaming), pos)

 %%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%

 type LetTerm = SCDecls * SCTerm

 op mkLet (decls : SCDecls, term : SCTerm, pos : Position) : SCTerm = 
  (Let (decls, term), pos)

 %%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%

 type WhereTerm = SCDecls * SCTerm
   %% The intention is that 'let {decls} in term' is the same as 'term where {decls}. 
   %% The where construct is experimental.

 op  mkWhere (decls : SCDecls, term : SCTerm, pos : Position) : SCTerm = 
  (Where (decls, term), pos)

 %%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%

 type HideTerm = NameExprs * SCTerm

 %% A NameExpr denotes the name of an op, type or claim. Lists of such
 %% expressions are used in hide and export terms to either
 %% exclude names from being export or dually, to specify exactly what names
 %% are to be exported.  Presumably the syntax will borrow ideas from the
 %% syntax used for qualifiying names. In particular we might want to allow
 %% patterns with wildcards to stand for a collection of names. For now,
 %% one must explicitly list them.
 %% 
 %% There is some inconsistency here as NameExpr is not annotated with 
 %% a position as in Renaming above.

 type NameExprs = List NameExpr
 type NameExpr  = 
   | Type       QualifiedId
   | Op         QualifiedId * Option MSType
   | Axiom      QualifiedId
   | Theorem    QualifiedId
   | Conjecture QualifiedId
   | Ambiguous  QualifiedId

 op  mkHide (names : NameExprs, term : SCTerm, pos : Position) : SCTerm = 
  (Hide (names, term), pos)

 %%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%

 type ExportTerm = NameExprs * SCTerm
 op mkExport (names : NameExprs, term : SCTerm, pos : Position) : SCTerm = 
  (Export (names, term), pos)

 %%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%

 %% This is an initial attempt at code generation. The first string is the
 %% name of the target language. Perhaps it should be a constructor.
 %% Also perhaps we should say where to put the output. The idea is that
 %% is should go in the file with the same root name as the UnitId calling
 %% compiler (but with a .lisp suffix) .. but the term may not have a UnitId.
 %% The third argument is an optional file name to store the result.

 type GenerateTerm = String * SCTerm * Option String
 op mkGenerate (lang : String,
                term : SCTerm, 
                file : Option String, 
                pos  : Position) 
  : SCTerm = 
  (Generate (lang, term, file), pos)

 %%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%

 %% Subsitution. The first term should be spec valued and the second should be
 %% morphism valued. Remains to be seen what will happen if/when we have diagrams.

 type SubstTerm = SCTerm * SCTerm * SM_Pragmas

 op  mkSubst (spec_term : SCTerm, 
              sm_term   : SCTerm,
              pragmas   : SM_Pragmas,
              pos       : Position) 
  : SCTerm = 
  (Subst (spec_term, sm_term, pragmas), pos)

 %%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%
 %% Op refinement. 
 %% The first term should be spec valued and the second should be op spec element valued.

 type OpRefineTerm = SCTerm * SpecElemTerms

 op mkOpRefine (spec_term : SCTerm,   
                elements  : SpecElemTerms, 
                pos       : Position)
  : SCTerm = 
  (OpRefine (spec_term, elements), pos)

 %%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%
 %% Spec transformation. Takes a spec and a transformation script.

 type TransformTerm = SCTerm * TransformExpr * SM_Pragmas

 op mkTransform (spec_term  : SCTerm, 
                 transfm    : TransformExpr,
                 pragmas    : SM_Pragmas, 
                 pos        : Position) 
  : SCTerm = 
  (Transform (spec_term, transfm, pragmas), pos)

 %% --------------------

 type TransformExprs = List TransformExpr
 type TransformExpr  = ATransformExpr Position

 op mkTransformName    (name:  String,                    pos: Position) : TransformExpr = Name   (name,    pos)
 op mkTransformNumber  (n:     Nat,                       pos: Position) : TransformExpr = Number (n,       pos)
 op mkTransformString  (s:     String,                    pos: Position) : TransformExpr = Str    (s,       pos)
 op mkTransformSCTerm  (sc_tm: SCTerm,                    pos: Position) : TransformExpr = SCTerm (sc_tm,   pos)
 op mkTransformQuotedTerm (tm: MSTerm,                    pos: Position) : TransformExpr = QuotedTerm(tm,   pos)
 op mkTransformQual    (q:     String, name: String,      pos: Position) : TransformExpr = Qual   (q, name, pos)
 op mkTransformItem    (mod:   String, te: TransformExpr, pos: Position) : TransformExpr = Item   (mod, te, pos)
 op mkTransformSlice   (root_ops: OpNames, root_types: TypeNames, cut_op?: OpName -> Bool, cut_type?: TypeName -> Bool, pos: Position): TransformExpr =
    Slice (root_ops, root_types, cut_op?, cut_type?, pos)
 op mkTransformRepeat  (cnt: Nat, transfm: TransformExpr, pos: Position): TransformExpr = Repeat (cnt, transfm, pos)
 op mkTransformOptions (args: TransformExprs,             pos: Position) : TransformExpr = Options(args,       pos)
 op mkTransformTuple   (itms: TransformExprs,             pos: Position) : TransformExpr = Tuple  (itms,       pos)
 op mkTransformBlock   (comms: TransformExprs,            pos: Position) : TransformExpr = Block  (comms,      pos)
 op mkTransformRecord  (fld_val_prs: List (String * TransformExpr), pos: Position) : TransformExpr = Record (fld_val_prs,    pos)
 op mkTransformAt      (qids: QualifiedIds, comm: TransformExpr,  pos: Position)   : TransformExpr = At     (qids, comm,    pos)
 op mkTransformCommand (name:  String, args: TransformExprs,        pos: Position) : TransformExpr = Command(name, args,     pos)

 %%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%
 %% Obligations takes a spec or a a morphism and returns a spec including
 %% the proof obligations as conjectures.

 type ObligationsTerm = SCTerm

 op mkObligations (term : SCTerm, pos : Position) 
  : SCTerm = 
  (Obligations term, pos)

 %%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%
 %% Expand takes a spec and returns a transformed spec that has lambdas
 %% lifted nad HO functions instantiated and defintions expanded into
 %% axioms.  It is essentially the input to the Snark prover interface.

 type ExpandTerm = SCTerm

 op mkExpand (term : SCTerm, pos : Position) 
  : SCTerm = 
  (Expand term, pos)

 %%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%
 %% Reduce will rewrite the given term in the context of the given spec
 %% using the definitions and axioms of the spec as rules.

 type ReduceTerm = MSTerm * SCTerm

 %% The following are declarations that appear in a file or listed
 %% within a 'let'. As noted above, at present the identifiers
 %% bound by a let or listed in a file are unstructured.

 op mkReduce (term_a : MSTerm, 
              term_b : SCTerm,  
              pos    : Position) 
  : SCTerm = 
  (Reduce (term_a, term_b), pos)

 %%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%

 type OtherRenamingRule % hook for extensions

 %% In a basic Specware image, OtherTerm is unspecified, but in an extension such as PSL or
 %% Planware, it might be refined to an application-specific erm, or a coproduct of such terms.

 type OtherTerm a % hook for extensions

 op mkOther (other : OtherTerm Position, pos : Position) 
  : SCTerm = 
  (Other other, pos)

 %%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%

 type SCDecls = List SCDecl
 type SCDecl  = Name * SCTerm 

 %%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%

 op hasHashSuffix? (unitId : RelativeUID) : Bool =
  case unitId of
    | UnitId_Relative  ({path,hashSuffix=Some _}) -> true
    | SpecPath_Relative({path,hashSuffix=Some _}) -> true
    | _ -> false

%% Tests whether s is anything followed by a colon.
op deviceString? (s : String) : Bool =
  let len = length s in
  len > 1 && s@(len - 1) = #:

 op [a] valueOf    (value : a, _   : Position) : a        = value
 op [a] positionOf (_     : a, pos : Position) : Position = pos


endspec
