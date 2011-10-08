%%% Spec Calculus Abstract Syntax

SpecCalc qualifying spec

 %% We import PosSpec for Position, QualifiedId, ASortScheme etc.  This is a
 %% bit of a shame as AnnSpec would like to import this spec so as to insert
 %% a spec calculus term in the import of a spec. This would create a cyclic
 %% dependency between specs. At present, this is addressed in AnnSpec by
 %% defining an abstract type SpecCalc.Term a, which is refined below.

 %% Value.sw indirectly imports Types.sw

 import ../../MetaSlang/Specs/StandardSpec % for Position
 import /Library/Legacy/Utilities/Lisp     % for LispCell (see ProverOptions)

 %% All the objects in the abstract syntax are polymorphic and defined at
 %% two levels.  The first level pairs the type the type parameter. 
 %% The second level defines the constructors for the sort.
 %% In this way, every sort is annotated. The annotation is typically 
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

 type SpecCalc.ValueInfo  % Defined in ../Semantics/Value

 type SpecCalc.SCTerm = SpecCalc.Term Position

 %% The following is the toplevel returned by the parser. 
 %% A file may contain a list of name = term or contain a single term. 
 %% This should not be polymorphic.
 %% The type parameter should be instantiated with the type Position.

 type SpecTerm     a = (SpecTermBody a) * a

 type SpecTermBody a = | Term  (SpecCalc.Term a)
                       | Decls (List (Decl a))

 op [a] mkTerm (term  : SpecCalc.Term a, pos : a) 
  : SpecTerm a  = 
  (Term term, pos)

 op [a] mkDecls (decls : List (Decl a), pos : a) 
  : SpecTerm a = 
  (Decls decls, pos)

 %%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%
 %% The following is the type given to us by the parser.
 %%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%

 type SpecCalc.Term a = (TermBody a) * a
 type TermBody a = 
   | UnitId       RelativeUID
   | Print        PrintTerm           a 
   | Prove        ProveTerm           a
   | ProofCheck   ProofCheckTerm      a
   | Spec         ExplicitSpecTerm    a    
   | Diag         DiagramTerm         a 
   | Colimit      ColimitTerm         a
   | SpecMorph    SpecMorphismTerm    a
   | SpecInterp   SpecInterpTerm      a
   | SpecPrism    SpecPrismTerm       a
   | DiagMorph    DiagramMorphismTerm a
   | ExtendMorph  ExtendMorphismTerm  a
   | Qualify      QualifyTerm         a 
   | Translate    TranslateTerm       a 
   | Let          LetTerm             a 
   | Where        WhereTerm           a
   | Hide         HideTerm            a  % Control visibilty of names outside a spec.
   | Export       ExportTerm          a  % Control visibilty of names outside a spec.
   | Generate     GenerateTerm        a
   | Subst        SubstTerm           a
   | OpRefine     OpRefineTerm        a 
   | Transform    TransformTerm       a
   | Obligations  ObligationsTerm     a
   | Expand       ExpandTerm          a
   | Reduce       ReduceTerm          a 
   | Other        OtherTerm           a  % A hook for for creating applications that are extensions to Specware.
                                         % If more than one new term is needed, OtherTerm can be a coproduct of desired terms.
   | Quote        ValueInfo              % Used to capture an internally created value and turn it into a Term when needed.


 %%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%

 %% The support for UnitId's is somewhat simplistic but hopefully sufficient
 %% for now.  A user may specify a unitId that is relative to the current unitId
 %% (ie relative to the object making the reference) or relative to a path
 %% in the SPECPATH environment variable. In the current syntax, the
 %% latter are indicated by an opening "/". In additon, each unitId evaluates
 %% to a full canonical system path. The latter cannot be directly entered
 %% by the user. My apologies for the long constructor names. A relative UnitId
 %% resolves to a canonical UnitId. The latter in turn resolves to an absolute
 %% path in the file system. Recall that file may contain a single anonymous
 %% term or a list of bindings. Thus a canonical UnitId may resolve to two
 %% possible path names. Later we may want to have UIDs with network addresses.

 type UnitId = {
		path       : List   String,
		hashSuffix : Option String
	       }

 type SpecCalc.RelativeUID =
   | UnitId_Relative   UnitId
   | SpecPath_Relative UnitId

 op [a] mkUnitId (uid : RelativeUID, pos : a) 
  : SpecCalc.Term a = 
  (UnitId uid, pos)

 %%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%

 type PrintTerm a = SpecCalc.Term a

 op [a] mkPrint (term : SpecCalc.Term a, pos : a) : SpecCalc.Term a = 
  (Print term, pos)

 %%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%

 type ProveTerm a = ClaimName * SpecCalc.Term a * ProverName * Assertions * ProverOptions * ProverBaseOptions * AnswerVar

 type ProverName = Name

 type Assertions = 
   | All
   | Explicit (List ClaimName)

 type ProverOptions = 
   | OptionString (List LispCell)
   | OptionName   QualifiedId
   | Error        (String * String)  % error msg, problematic string

 type ProverBaseOptions = | ProverBase | Base | AllBase | NoBase
  
 type AnswerVar = Option Var

 op [a] mkProve (claim_name     : ClaimName, 
                 term           : SpecCalc.Term a,
                 prover_name    : ProverName,
                 assertions     : Assertions,
                 prover_options : ProverOptions,
                 includeBase?   : ProverBaseOptions,
                 answer_var     : AnswerVar,
                 pos            : a)
  : SpecCalc.Term a = 
  (Prove (claim_name, term, prover_name, assertions, prover_options, includeBase?, answer_var), pos)

 %%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%

 type ProofCheckTerm a = PCClaimName * SpecCalc.Term a * ProverName * Assertions * ProverOptions * ProverBaseOptions

 type PCClaimName = | WellFormed | Claim QualifiedId
 type ClaimName   = QualifiedId

 op [a] mkProofCheck  (claim_name     : PCClaimName,
                       term           : SpecCalc.Term a,
                       prover_name    : ProverName,
                       assertions     : Assertions,
                       prover_options : ProverOptions,
                       includeBase?   : ProverBaseOptions,
                       pos            : a)
  : SpecCalc.Term a =
  (ProofCheck (claim_name, term, prover_name, assertions, prover_options, includeBase?), pos) 

 %%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%

 type ExplicitSpecTerm a = List (SpecElem a)

 %% A SpecElem is a declaration within a spec -- the ops types etc.

 type SpecElem a = (SpecElemBody a) * a

 type SpecElemBody a =
   | Import  List (SpecCalc.Term a)
   | Sort    List QualifiedId          * ASort a
   | Op      List QualifiedId * Fixity * Bool * ATerm a
   | Claim   (PropertyType * PropertyName * TyVars * ATerm a)
   | Pragma  String * String * String
   | Comment String

 %% These are used by the parser to create SpecElem's
 %% They can be changed to adapt to new structures for SpecElem's
 %% without altering the parser code in semantics.lisp

 op [a] mkPragma (prefix  : String, 
                  body    : String, 
                  postfix : String, 
                  pos     : a) 
  : SpecElem a =
  (Pragma (prefix, body, postfix), pos)

 op [a] mkSortSpecElem (names : SortNames, 
                        tvs   : TyVars, 
                        defs  : List (ASort a), 
                        pos   : a) 
  : SpecElem a =
  let dfn = 
      case defs of
        | []    -> maybePiSort (tvs, Any pos)
        | [dfn] -> maybePiSort (tvs, dfn)
        | _     -> And (map (fn srt -> maybePiSort (tvs, srt)) defs, 
                        pos)
  in
  (Sort (names, dfn), pos)

 op [a] mkOpSpecElem (names   : OpNames, 
                      fixity  : Fixity, 
                      tvs     : TyVars, 
                      srt     : ASort a, 
                      defs    : List (ATerm a), 
                      refine? : Bool, 
                      pos     : a) 
  : SpecElem a =
   %% We potentially could be smarter if srt is just a meta type var
   %% and use just a normal term instead of a typed term, but that's
   %% a complication we don't need now (or perhaps ever).
   let dfn =
       case defs of
	 | []   -> SortedTerm (Any pos, srt, pos) % op decl
	 | [tm] -> tm
   in
   let dfn = maybePiTerm (tvs, dfn) in
   (Op (names, fixity, refine?, dfn), pos)

 op [a] mkSpec (elements : List (SpecElem a), pos : a) : SpecCalc.Term a = 
  (Spec elements, pos)

 %%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%

 type DiagramTerm a = List (DiagElem a)

 %% A diagram is defined by a list of elements. An element may be a labeled
 %% vertex or edge.
 %% 
 %% In the current form, the names of vertices and edges are simply Names.
 %% This may change in the future. In particular, one can construct limits and 
 %% colimits of diagram in which case, vertices and edges in the resulting 
 %% shape may be tuples and equivalence classes. It remains to be seen whether 
 %% we need a concrete syntax for this.

 type DiagElem     a = (DiagElemBody a) * a
 type DiagElemBody a = | Node NodeId * (SpecCalc.Term a)
                       | Edge EdgeId * NodeId * NodeId * (SpecCalc.Term a)
 type NodeId = Name
 type EdgeId = Name

 op [a] mkDiag (elements : List (DiagElem a), pos : a) : SpecCalc.Term a = 
  (Diag elements, pos)

 %%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%

 type Colimit a = SpecCalc.Term a
 op [a] mkColimit (diag : SpecCalc.Term a, pos : a) : SpecCalc.Term a = 
  (Colimit diag, pos)

 %%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%

 type SpecMorphismTerm a = (SpecCalc.Term a) * (SpecCalc.Term a) * (List (SpecMorphRule a)) * SM_Pragmas a
   %% The calculus supports two types of morphisms: morphisms between specs and
   %% morphisms between diagrams.  Right now spec morphism are distinguished
   %% from diagram morphisms in both the concrete and abstract syntax.
   %% The first two elements in the morphism products are terms that evaluate
   %% to the domain and codomain of the morphisms.

 type SpecMorphRule a = (SpecMorphRuleBody a) * a
 type SpecMorphRuleBody a = 
   | Ambiguous QualifiedId                 * QualifiedId 
   | Sort      QualifiedId                 * QualifiedId
   | Op        (QualifiedId * Option Sort) * (QualifiedId * Option Sort)

 type SM_Pragma  a = (String * String * String) * a
 type SM_Pragmas a = List (SM_Pragma a)

 op [a] mkSpecMorph (dom_term : SpecCalc.Term a, 
                     cod_term : SpecCalc.Term a, 
                     rules    : List (SpecMorphRule a), 
                     pragmas  : SM_Pragmas a, 
                     pos : a) 
  : SpecCalc.Term a =
  (SpecMorph (dom_term, cod_term, rules, pragmas), pos)

 %%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%

 type SpecInterpTerm      a = (SpecCalc.Term a) * (SpecCalc.Term a) * (SpecInterpRules a)
 type SpecInterpRules     a = (SpecInterpRulesBody a) * a
 type SpecInterpRulesBody a = 
   %% This is the form used by Specware 2 -- a cospan, where the codomain-to-mediator.
   %% morphism is presumably a definitional extension.
   %% Alternatively, this could be expressed as symbol to term mappings,
   %% or as a quotient of morphisms (where an interpretation is viewed as a morphism
   %% from a quotient of isomorphic specs to a quotient of isomorphic specs).
   {med : SpecCalc.Term a,
    d2m : SpecCalc.Term a,
    c2m : SpecCalc.Term a}

 op [a] mkSpecInterpRules (med : SpecCalc.Term a, 
                           d2m : SpecCalc.Term a, 
                           c2m : SpecCalc.Term a, 
                           pos : a) 
  : SpecInterpRules a =
  ({med = med, d2m = d2m, c2m = c2m}, pos)

 op [a] mkSpecInterp  (dom_term : SpecCalc.Term a, 
                       cod_term : SpecCalc.Term a, 
                       rules    : SpecInterpRules a, 
                       pos      : a) 
  : SpecCalc.Term a =
  (SpecInterp (dom_term, cod_term, rules), pos)

 %%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%

 %% In Uniform mode, we may choose a fixed specific morphism (Nth i),
 %% a fixed random morphism, or iterative though all different morphisms.

 %% In per instance mode, we choose a morphism at random for each
 %% occurence of each op, using the provided additional morphisms
 %% or interpretations to translate as necessary when the resulting
 %% types would otherwise not match.

 type SpecPrismTerm a = (SpecCalc.Term a) * List (SpecCalc.Term a) * PrismModeTerm a
   %% The first  arg denotes a shared domain spec.
   %% The second arg denotes a list of morphisms, all with the same domain spec.
   %% The third  arg gives the rules for choosing among the morphism.

 type PrismModeTerm a = 
   | Uniform      PrismSelection
   | PerInstance  List (SpecCalc.Term a)     % sms or interps

 type PrismSelection = | Nth Nat | Random | Generative

 op [a] mkSpecPrism (dom_term : SpecCalc.Term a, 
                     sm_terms : List (SpecCalc.Term a), 
                     pmode    : PrismModeTerm a, 
                     pos      : a) 
  : SpecCalc.Term a =
  (SpecPrism (dom_term, sm_terms, pmode), pos)

 op [a] mkPrismPerInstance (interps : List (SpecCalc.Term a)) : PrismModeTerm a =
  PerInstance interps

 op [a] mkPrismUniform (s : PrismSelection) : PrismModeTerm a =
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

 type DiagramMorphismTerm a = (SpecCalc.Term a) * (SpecCalc.Term a) * (List (DiagMorphRule a))
 type DiagMorphRule       a = (DiagMorphRuleBody a) * a
 type DiagMorphRuleBody   a = | ShapeMap    Name * Name
                              | NatTranComp Name * (SpecCalc.Term a) 

 op [a] mkDiagMorph (dom_term : SpecCalc.Term a, 
                     cod_term : SpecCalc.Term a, 
                     rules    : List (DiagMorphRule a), 
                     pos      : a) 
  : SpecCalc.Term a =
  (DiagMorph (dom_term, cod_term, rules), pos)

 %%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%

 type ExtendMorphismTerm  a = (SpecCalc.Term a)

 op [a] mkExtendMorph (term : SpecCalc.Term a, pos : a) 
  : SpecCalc.Term a = 
  (ExtendMorph term, pos)

 %%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%

 type QualifyTerm a = (SpecCalc.Term a) * Name

 op [a] mkQualify (term : SpecCalc.Term a, name : Name, pos : a) 
  : SpecCalc.Term a = 
  (Qualify (term, name), pos)

 %%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%

 type TranslateTerm a = (SpecCalc.Term a) * Renaming

 %% A Renaming denotes some mappings of names, e.g. for sorts, ops,
 %% and possibly other entities.
 %% Some mappings may be ambiguous until placed in some context.

 type Renaming      = RenamingRules * Position
 type RenamingRules = List RenamingRule
 type RenamingRule  = RenamingRuleBody * Position
 type RenamingRuleBody =
   | Ambiguous QualifiedId                 * QualifiedId                 * Aliases   % last field is all aliases, including name in second field
   | Sort      QualifiedId                 * QualifiedId                 * SortNames % last field is all aliases, including name in second field
   | Op        (QualifiedId * Option Sort) * (QualifiedId * Option Sort) * OpNames   % last field is all aliases, including name in second field
   | Other     OtherRenamingRule

 op [a] mkTranslate (term : SpecCalc.Term a, renaming : Renaming, pos : a) 
  : SpecCalc.Term a = 
  (Translate (term, renaming), pos)

 %%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%

 type LetTerm a = (List (Decl a)) * (SpecCalc.Term a)

 op [a] mkLet (decls : List (Decl a), term : SpecCalc.Term a, pos : a) 
  : SpecCalc.Term a = 
  (Let (decls, term), pos)

 %%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%

 type WhereTerm a = (List (Decl a)) * (SpecCalc.Term a)
   %% The intention is that 'let {decls} in term' is the same as 'term where {decls}. 
   %% The where construct is experimental.

 op [a] mkWhere (decls : List (Decl a), term : SpecCalc.Term a, pos : a) 
  : SpecCalc.Term a = 
  (Where (decls, term), pos)

 %%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%

 type HideTerm a = (List (NameExpr a)) * (SpecCalc.Term a)

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

 type NameExpr a = 
   | Sort       QualifiedId
   | Op         QualifiedId * Option Sort
   | Axiom      QualifiedId
   | Theorem    QualifiedId
   | Conjecture QualifiedId
   | Ambiguous  QualifiedId

 op [a] mkHide (names : List (NameExpr a), term : SpecCalc.Term a, pos : a) 
  : SpecCalc.Term a = 
  (Hide (names, term), pos)

 %%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%

 type ExportTerm a = (List (NameExpr a)) * (SpecCalc.Term a)
 op [a] mkExport (names : List (NameExpr a), term : SpecCalc.Term a, pos : a) 
  : SpecCalc.Term a = 
  (Export (names, term), pos)

 %%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%

 %% This is an initial attempt at code generation. The first string is the
 %% name of the target language. Perhaps it should be a constructor.
 %% Also perhaps we should say where to put the output. The idea is that
 %% is should go in the file with the same root name as the UnitId calling
 %% compiler (but with a .lisp suffix) .. but the term may not have a UnitId.
 %% The third argument is an optional file name to store the result.

 type GenerateTerm a = String * (SpecCalc.Term a) * Option String
 op [a] mkGenerate (lang : String,
                    term : SpecCalc.Term a, 
                    file : Option String, 
                    pos  : a) 
  : SpecCalc.Term a = 
  (Generate (lang, term, file), pos)

 %%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%

 %% Subsitution. The first term should be spec valued and the second should be
 %% morphism valued. Remains to be seen what will happen if/when we have diagrams.

 type SubstTerm a = (SpecCalc.Term a) * (SpecCalc.Term a)

 op [a] mkSubst (spec_term : SpecCalc.Term a, 
                 sm_term   : SpecCalc.Term a, 
                 pos       : a) 
  : SpecCalc.Term a = 
  (Subst (spec_term, sm_term), pos)

 %%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%
 %% Op refinement. 
 %% The first term should be spec valued and the second should be op spec element valued.

 type OpRefineTerm a = (SpecCalc.Term a) * List (SpecElem a)

 op [a] mkOpRefine (spec_term : SpecCalc.Term a,   
                    elements  : List (SpecElem a), 
                    pos       : a)
  : SpecCalc.Term a = 
  (OpRefine (spec_term, elements), pos)

 %%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%
 %% Spec transformation. Takes a spec and a transformation script.

 type TransformTerm a = (SpecCalc.Term a) * List TransformExpr

 op [a] mkTransform (spec_term  : SpecCalc.Term a, 
                     transforms : List TransformExpr,
                     pos        : a) 
  : SpecCalc.Term a = 
  (Transform (spec_term, transforms), pos)

 %% --------------------

 type TransformExpr = ATransformExpr Position

 op mkTransformName         (name:  String,                                  pos: Position) : TransformExpr = Name         (name,        pos)
 op mkTransformNumber       (n:     Nat,                                     pos: Position) : TransformExpr = Number       (n,           pos)
 op mkTransformString       (s:     String,                                  pos: Position) : TransformExpr = Str          (s,           pos)
 op mkTransformSCTerm       (sc_tm: SCTerm,                                  pos: Position) : TransformExpr = SCTerm       (sc_tm,       pos)
 op mkTransformQual         (q:     String,        name: String,             pos: Position) : TransformExpr = Qual         (q,    name,  pos)
 op mkTransformItem         (mod:   String,        te:   TransformExpr,      pos: Position) : TransformExpr = Item         (mod,  te,    pos)
 op mkTransformApply        (head:  TransformExpr, args: List TransformExpr, pos: Position) : TransformExpr = Apply        (head, args,  pos)
 op mkTransformApplyOptions (head:  TransformExpr, args: List TransformExpr, pos: Position) : TransformExpr = ApplyOptions (head, args,  pos)
 op mkTransformTuple        (itms:  List TransformExpr,                      pos: Position) : TransformExpr = Tuple        (itms,        pos)
 op mkRecord                (fld_val_prs: List (String * TransformExpr),     pos: Position) : TransformExpr = Record       (fld_val_prs, pos)

 %%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%
 %% Obligations takes a spec or a a morphism and returns a spec including
 %% the proof obligations as conjectures.

 type ObligationsTerm a = SpecCalc.Term a

 op [a] mkObligations (term : SpecCalc.Term a, pos : a) 
  : SpecCalc.Term a = 
  (Obligations term, pos)

 %%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%
 %% Expand takes a spec and returns a transformed spec that has lambdas
 %% lifted nad HO functions instantiated and defintions expanded into
 %% axioms.  It is essentially the input to the Snark prover interface.

 type ExpandTerm a = SpecCalc.Term a

 op [a] mkExpand (term : SpecCalc.Term a, pos : a) 
  : SpecCalc.Term a = 
  (Expand term, pos)

 %%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%
 %% Reduce will rewrite the given term in the context of the given spec
 %% using the definitions and axioms of the spec as rules.

 type ReduceTerm a = ATerm a * SpecCalc.Term a

 %% The following are declarations that appear in a file or listed
 %% within a 'let'. As noted above, at present the identifiers
 %% bound by a let or listed in a file are unstructured.

 op [a] mkReduce (term_a : ATerm a, 
                  term_b : SpecCalc.Term a,  
                  pos    : a) 
  : SpecCalc.Term a = 
  (Reduce (term_a, term_b), pos)

 %%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%

 type OtherRenamingRule % hook for extensions

 %% In a basic Specware image, OtherTerm is unspecified, but in an extension such as PSL or
 %% Planware, it might be refined to an application-specific erm, or a coproduct of such terms.

 type OtherTerm a  % hook for extensions

 op [a] mkOther (other : OtherTerm a, pos : a) 
  : SpecCalc.Term a = 
  (Other other, pos)

 %%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%

 type Decl a = Name * (SpecCalc.Term a)

 %%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%

 op hasHashSuffix? (unitId : RelativeUID) : Bool =
  case unitId of
    | UnitId_Relative  ({path,hashSuffix=Some _}) -> true
    | SpecPath_Relative({path,hashSuffix=Some _}) -> true
    | _ -> false

 op deviceString? (s : String) : Bool =
  let len = length s in
  len > 1 && s@(len - 1) = #:

 op [a] valueOf    (value : a, _   : Position) : a        = value
 op [a] positionOf (_     : a, pos : Position) : Position = pos


endspec
