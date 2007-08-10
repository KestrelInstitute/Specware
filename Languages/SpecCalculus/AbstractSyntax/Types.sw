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
 %% Might might be enough to pair it with the \verb+Position+ type and then 
 %% refine that type.  Using two levels ensures that for all objects in the 
 %% abstract syntax tree, the position information is always the second component.

 type SpecCalc.ValueInfo  % Defined in ../Semantics/Value

 type SCTerm = SpecCalc.Term Position

 op valueOf    : [a] a * Position -> a
 op positionOf : [a] a * Position -> Position

 def valueOf    (value, _       ) = value
 def positionOf (_,     position) = position

 %% The following is the toplevel returned by the parser. 
 %% A file may contain a list of $\mathit{name} =
 %% \mathit{term}$ or contain a single term. This should not be polymorphic.
 %% The type parameter should be instantiated with the type \verb+Position+.

 type SpecTerm  a = (SpecTermBody a) * a
 type SpecTermBody a =
   | Term  (SpecCalc.Term a)
   | Decls (List (Decl a))

 %% The support for UnitId's is somewhat simplistic but hopefully sufficient
 %% for now.  A user may specify a unitId that is relative to the current unitId
 %% (ie relative to the object making the reference) or relative to a path
 %% in the \verb+SPECPATH+ environment variable. In the current syntax, the
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

 type RelativeUID =
   | UnitId_Relative UnitId
   | SpecPath_Relative UnitId


 %% The type \verb+Name+ is used everywhere that one can expect a
 %% non-structured identifier.  This includes for instance, the names of
 %% vertices and edges in the shape of a diagram. It also includes the
 %% qualifiers on op and type names.
 %% 
 %% In the near term, it also includes the identifiers bound by declarations.
 %% These are either \verb+let+ bound or bound by specs listed in a
 %% file. Later, we might allow bound identifiers to be UIDs thus enabling
 %% one to override an existing definition.

 type Name       = String
 type ProverName = Name
 type PCClaimName  = | WellFormed | Claim QualifiedId
 type ClaimName  = QualifiedId

  type TransformExpr =
    | Name String * Position
    | Number Nat * Position
    | Qual String * String * Position
    | Item String * TransformExpr * Position       % e.g. unfold map
    | Tuple List TransformExpr * Position
    | ApplyOptions TransformExpr * List TransformExpr * Position
    | Apply TransformExpr * List TransformExpr * Position

 %% In a basic Specware image, OtherTerm is unspecified, but in an extension
 %% such as PSL or Planware, it might be refined to an application-specific 
 %% term, or a coproduct of such terms.

 type OtherTerm a  % hook for extensions

 %% The following is the type given to us by the parser.

 type SpecCalc.Term a = (TermBody a) * a
 type TermBody a = 
   | Print        (SpecCalc.Term a)
   | Prove        ClaimName   * SpecCalc.Term a * ProverName * Assertions * ProverOptions * ProverBaseOptions * AnswerVar
   | ProofCheck   PCClaimName * SpecCalc.Term a * ProverName * Assertions * ProverOptions * ProverBaseOptions
   | UnitId       RelativeUID
   | Spec         List (SpecElem a)
   | Diag         List (DiagElem a)
   | Colimit      (SpecCalc.Term a)

   %% The calculus supports two types of morphisms: morphisms between specs and
   %% morphisms between diagrams.  Right now spec morphism are distinguished
   %% from diagram morphisms in both the concrete and abstract syntax.
   %% The first two elements in the morphism products are terms that evaluate
   %% to the domain and codomain of the morphisms.

   | SpecMorph    (SpecCalc.Term a) * (SpecCalc.Term a) * (List (SpecMorphRule a)) * SM_Pragmas a
   | SpecInterp   (SpecCalc.Term a) * (SpecCalc.Term a) * (SpecInterpRules a)

   | SpecPrism    (SpecCalc.Term a) * List (SpecCalc.Term a) * PrismModeTerm a
     %% The first  arg denotes a shared domain spec.
     %% The second arg denotes a list of morphisms, all with the same domain spec.
     %% The third  arg gives the rules for choosing among the morphism.

   | DiagMorph    (SpecCalc.Term a) * (SpecCalc.Term a) * (List (DiagMorphRule a))
   | ExtendMorph  (SpecCalc.Term a)
   | Qualify      (SpecCalc.Term a) * Name
   | Translate    (SpecCalc.Term a) * Renaming
%  | Renaming     Renaming

   %% The intention is that \verb+let+ \emph{decls} \verb+in+ \emph{term}
   %% is the same as \emph{term} \verb+where+ \emph{decls}. The \verb+where+
   %% construct is experimental.

   | Let          (List (Decl a)) * (SpecCalc.Term a)
   | Where        (List (Decl a)) * (SpecCalc.Term a)

   %% The next two control the visibilty of names outside a spec.

   | Hide         (List (NameExpr a)) * (SpecCalc.Term a)
   | Export       (List (NameExpr a)) * (SpecCalc.Term a)

   %% This is an initial attempt at code generation. The first string is the
   %% name of the target language. Perhaps it should be a constructor.
   %% Also perhaps we should say where to put the output. The idea is that
   %% is should go in the file with the same root name as the UnitId calling
   %% compiler (but with a .lisp suffix) .. but the term may not have a UnitId.
   %% The third argument is an optional file name to store the result.

   | Generate     (String * (SpecCalc.Term a) * Option String)

   %% Subsitution. The first term should be spec valued and the second should
   %% be morphism valued. Remains to be seen what will happen if/when we
   %% have diagrams.

   | Subst        (SpecCalc.Term a) * (SpecCalc.Term a)

   %% Op refinement. The first term should be spec valued and the second should
   %% be op spec element valued.

   | OpRefine     (SpecCalc.Term a) * (List (SpecElem a))

   %% Spec transformation. Takes a spec and a transformation script.

   | Transform    (SpecCalc.Term a) * (List TransformExpr)

   %% Obligations takes a spec or a a morphism and returns a spec including
   %% the proof obligations as conjectures.

   | Obligations  (SpecCalc.Term a)

   %% Expand takes a spec and returns a transformed spec that has lambdas
   %% lifted nad HO functions instantiated and defintions expanded into
   %% axioms.  It is essentially the input to the Snark prover interface.

   | Expand       (SpecCalc.Term a)

   %% Reduce will rewrite the given term in the context of the given spec
   %% using the definitions and axioms of the spec as rules.

   | Reduce       (ATerm a * SpecCalc.Term a)

   %% Quote is used to capture an internally created value and turn it
   %% into a Term when needed.

   | Quote        ValueInfo

   %% The following is a hook for creating applications that are 
   %% extensions to Specware.  If more than one new term is needed,
   %% you can make OtherTerm a coproduct of the desired terms.

   | Other        (OtherTerm a)



 %% The following are declarations that appear in a file or listed
 %% within a \verb+let+. As noted above, at present the identifiers
 %% bound by a let or listed in a file are unstructured.

 type PrismModeTerm a = 
   | Uniform      PrismSelection
   | PerInstance  List (SpecCalc.Term a)     % sms or interps

 op  mkPrismPerInstance : [a] List (SpecCalc.Term a) -> PrismModeTerm a
 def mkPrismPerInstance interps = PerInstance interps

 op  mkPrismUniform : [a] PrismSelection -> PrismModeTerm a
 def mkPrismUniform s = Uniform s

 %% In Uniform mode, we may choose a fixed specific morphism (Nth i),
 %% a fixed random morphism, or iterative though all different morphisms.

 %% In per instance mode, we choose a morphism at random for each
 %% occurence of each op, using the provided additional morphisms
 %% or interpretations to translate as necessary when the resulting
 %% types would otherwise not match.

 type PrismSelection = | Nth Nat | Random | Generative

 type Decl a = Name * (SpecCalc.Term a)

 %% A \verb+Renaming+ denotes some mappings of names, e.g. for sorts, ops,
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

 type OtherRenamingRule % hook for extensions

 %% TODO: phase this out...
 type SpecMorphRule a = (SpecMorphRuleBody a) * a
 type SpecMorphRuleBody a = 
   | Ambiguous QualifiedId                 * QualifiedId 
   | Sort      QualifiedId                 * QualifiedId
   | Op        (QualifiedId * Option Sort) * (QualifiedId * Option Sort)

 type SM_Pragma  a = (String * String * String) * a
 type SM_Pragmas a = List (SM_Pragma a)

 %% A \verb+NameExpr+ denote the name of an op, type or claim. Lists of such
 %% expressions are used in \verb+hide+ and \verb+export+ terms to either
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

 %% A \verb+SpecElem+ is a declaration within a spec, \emph{i.e.} the ops types etc.

 type SpecElem a = (SpecElemBody a) * a

 type SpecElemBody a =
   | Import  List (SpecCalc.Term a)
   | Sort    List QualifiedId          * ASort a
   | Op      List QualifiedId * Fixity * ATerm a
   | Claim   (PropertyType * PropertyName * TyVars * ATerm a)
   | Pragma  String * String * String
   | Comment String

 %% These are used by the parser to create SpecElem's
 %% They can be changed to adapt to new structures for SpecElem's
 %% without altering the parser code in semantics.lisp

 op  mkPragma : [a] String * String * String * a -> SpecElem a
 def mkPragma (prefix, body, postfix, pos) = 
   (Pragma (prefix, body, postfix), pos)

 op  mkSortSpecElem : [a] SortNames * TyVars * List (ASort a) * a -> SpecElem a
 def [a] mkSortSpecElem (names, tvs, defs, pos) =
   let dfn = 
       case defs of
	 | []    -> maybePiSort (tvs, Any pos)
	 | [dfn] -> maybePiSort (tvs, dfn)
	 | _     -> And (map (fn srt -> maybePiSort (tvs, srt)) defs, 
			 pos)
   in
     (Sort (names, dfn), pos)

 op  mkOpSpecElem : [a] OpNames * Fixity * TyVars * ASort a * List (ATerm a) * a -> SpecElem a
 def [a] mkOpSpecElem (names, fixity, tvs, srt, defs, pos) =
   %% We potentially could be smarter if srt is just a meta type var
   %% and use just a normal term instead of a typed term, but that's
   %% a complication we don't need now (or perhaps ever).
   let dfn =
       case defs of
	 | []   -> SortedTerm (Any pos, srt, pos) % op decl
	 | [tm] -> tm
   in
   let dfn = maybePiTerm (tvs, dfn) in
   (Op (names, fixity, dfn), pos)

 %% A diagram is defined by a list of elements. An element may be a labeled
 %% vertex or edge.
 %% 
 %% In the current form, the names of vertices and edges are simply
 %% \verb{Name}s. This may change in the future. In particular, one can
 %% construct limits and colimits of diagram in which case, vertices and
 %% edges in the resulting shape may be tuples and equivalence classes. It
 %% remains to be seen whether we need a concrete syntax for this.

 type DiagElem a = (DiagElemBody a) * a
 type DiagElemBody a =
   | Node NodeId * (SpecCalc.Term a)
   | Edge EdgeId * NodeId * NodeId * (SpecCalc.Term a)
 type NodeId = Name
 type EdgeId = Name

 %% Note that the term associated with a node must evaluate to a spec
 %% or diagram. The term for an edge must evaluate to a spec morphism or
 %% diagram morphism.
 %% 
 %% The syntax for spec morphisms accommodates mapping names to terms but
 %% the interpreter handles only name to name maps for now.
 %% 
 %% The tagging in the types below may be excessive given the \verb+ATerm+
 %% is already tagged.
 
 %% The current syntax allows one to write morphisms mapping names to terms
 %% but only name/name mappings will be handled by the interpreter in the
 %% near term.
 %% 
 %% A diagram morphism has two types of elements: components of the shape map
 %% and components of the natural transformation. The current syntax allows
 %% them to be presented in any order. 
 %% 
 %% A \verb+NatTranComp+ element is a component in a natural transformation
 %% between diagrams. The components are indexed by vertices in the shape.
 %% The term in the component must evaluate to a morphism.

 type DiagMorphRule  a = (DiagMorphRuleBody a) * a
 type DiagMorphRuleBody a =
   | ShapeMap    Name * Name
   | NatTranComp Name * (SpecCalc.Term a) 

 type Assertions = 
   | All
   | Explicit (List ClaimName)

 type ProverOptions = 
   | OptionString (List LispCell)
   | OptionName   QualifiedId
   | Error        (String * String)  % error msg, problematic string

 type ProverBaseOptions = | ProverBase | Base | AllBase | NoBase
  
 type AnswerVar = Option Var

 type  SpecInterpRules     a = (SpecInterpRulesBody a) * a
 type  SpecInterpRulesBody a = 
   %% This is the form used by Specware 2 -- a cospan, where the codomain-to-mediator.
   %% morphism is presumably a definitional extension.
   %% Alternatively, this could be expressed as symbol to term mappings,
   %% or as a quotient of morphisms (where an interpretation is viewed as a morphism
   %% from a quotient of isomorphic specs to a quotient of isomorphic specs).
   {med : SpecCalc.Term a,
    d2m : SpecCalc.Term a,
    c2m : SpecCalc.Term a}

 op  mkSpecInterpRules  : [a] (SpecCalc.Term a) * (SpecCalc.Term a) * (SpecCalc.Term a) * a -> SpecInterpRules a
 def mkSpecInterpRules (med, d2m, c2m, pos) = 
   ({med = med, 
     d2m = d2m, 
     c2m = c2m}, 
    pos)

 %% The following are invoked from the parser:

 op mkTerm        : [a] (SpecCalc.Term a)                            * a -> SpecTerm a
 op mkDecls       : [a] (List (Decl a))                              * a -> SpecTerm a

 op mkPrint       : [a] (SpecCalc.Term a)                            * a -> SpecCalc.Term a

 op mkProve       : [a] ClaimName   * SpecCalc.Term a * ProverName * Assertions * ProverOptions * ProverBaseOptions * AnswerVar * a -> SpecCalc.Term a
 op mkProofCheck  : [a] PCClaimName * SpecCalc.Term a * ProverName * Assertions * ProverOptions * ProverBaseOptions             * a -> SpecCalc.Term a

 op mkUnitId      : [a] RelativeUID                                  * a -> SpecCalc.Term a
 op mkSpec        : [a] (List (SpecElem a))                          * a -> SpecCalc.Term a
 op mkDiag        : [a] (List (DiagElem a))                          * a -> SpecCalc.Term a
 op mkColimit     : [a] (SpecCalc.Term a)                            * a -> SpecCalc.Term a

 op mkSpecMorph   : [a] (SpecCalc.Term a) * (SpecCalc.Term a)        * (List (SpecMorphRule a)) * (SM_Pragmas a) * a -> SpecCalc.Term a
 op mkSpecInterp  : [a] (SpecCalc.Term a) * (SpecCalc.Term a)        * (SpecInterpRules a)                       * a -> SpecCalc.Term a
 op mkSpecPrism   : [a] (SpecCalc.Term a) * (List (SpecCalc.Term a)) * PrismModeTerm a                           * a -> SpecCalc.Term a
 op mkDiagMorph   : [a] (SpecCalc.Term a) * (SpecCalc.Term a)        * (List (DiagMorphRule a))                  * a -> SpecCalc.Term a

 op mkExtendMorph : [a] (SpecCalc.Term a)                            * a -> SpecCalc.Term a
 op mkQualify     : [a] (SpecCalc.Term a) * Name                     * a -> SpecCalc.Term a
 op mkTranslate   : [a] (SpecCalc.Term a) * Renaming                 * a -> SpecCalc.Term a
%op mkRenaming    : [a] Renaming                                     * a -> SpecCalc.Term a
 op mkLet         : [a] (List (Decl a))     * (SpecCalc.Term a)      * a -> SpecCalc.Term a
 op mkWhere       : [a] (List (Decl a))     * (SpecCalc.Term a)      * a -> SpecCalc.Term a
 op mkHide        : [a] (List (NameExpr a)) * (SpecCalc.Term a)      * a -> SpecCalc.Term a
 op mkExport      : [a] (List (NameExpr a)) * (SpecCalc.Term a)      * a -> SpecCalc.Term a
 op mkGenerate    : [a] String * (SpecCalc.Term a) * (Option String) * a -> SpecCalc.Term a
 op mkSubst       : [a] (SpecCalc.Term a)   * (SpecCalc.Term a)      * a -> SpecCalc.Term a
 op mkOpRefine    : [a] (SpecCalc.Term a)   * (List (SpecElem a))    * a -> SpecCalc.Term a
 op mkTransform   : [a] (SpecCalc.Term a)   * (List TransformExpr)   * a -> SpecCalc.Term a
 op mkObligations : [a] (SpecCalc.Term a)                            * a -> SpecCalc.Term a
 op mkExpand      : [a] (SpecCalc.Term a)                            * a -> SpecCalc.Term a
 op mkReduce      : [a] (ATerm a)           * (SpecCalc.Term a)      * a -> SpecCalc.Term a
 op mkOther       : [a] (OtherTerm a)                                * a -> SpecCalc.Term a

 %% SpecTerm's    

 def mkTerm        (term,                      pos) = (Term        term,                        pos)
 def mkDecls       (decls,                     pos) = (Decls       decls,                       pos)

 %% Term's

 def mkPrint       (term,                      pos) = (Print       term,                        pos)

 def mkProve       (claim_name, term, prover_name, assertions, prover_options, includeBase?, answer_var, pos) =
   (Prove       (claim_name, term, prover_name, assertions, prover_options, includeBase?, answer_var), 
    pos)

 def mkProofCheck  (claim_name, term, prover_name, assertions, prover_options, includeBase?, pos) =
   (ProofCheck  (claim_name, term, prover_name, assertions, prover_options, includeBase?), 
    pos) 

 def mkUnitId      (uid,                       pos) = (UnitId      uid,                         pos)
 def mkSpec        (elements,                  pos) = (Spec        elements,                    pos)
 def mkDiag        (elements,                  pos) = (Diag        elements,                    pos)
 def mkColimit     (diag,                      pos) = (Colimit     diag,                        pos)

 def mkSpecMorph   (dom_term, cod_term, rules, pragmas, pos) = (SpecMorph   (dom_term, cod_term, rules, pragmas), pos)
 def mkSpecInterp  (dom_term, cod_term, rules,          pos) = (SpecInterp  (dom_term, cod_term, rules),          pos)
 def mkDiagMorph   (dom_term, cod_term, rules,          pos) = (DiagMorph   (dom_term, cod_term, rules),          pos)
 def mkSpecPrism   (dom_term, sm_terms, pmode,          pos) = (SpecPrism   (dom_term, sm_terms, pmode),          pos)

 def mkExtendMorph (term,                      pos) = (ExtendMorph term,                        pos)
 def mkQualify     (term, name,                pos) = (Qualify     (term, name),                pos)
 def mkTranslate   (term, renaming_expr,       pos) = (Translate   (term, renaming_expr),       pos)
%def mkRenaming    (translate_expr,            pos) = (Renaming    translate_expr,              pos)
 def mkLet         (decls, term,               pos) = (Let         (decls, term),               pos)
 def mkWhere       (decls, term,               pos) = (Where       (decls, term),               pos)
 def mkHide        (name_exprs, term,          pos) = (Hide        (name_exprs, term),          pos)
 def mkExport      (name_exprs, term,          pos) = (Export      (name_exprs, term),          pos)
 def mkGenerate    (lang, term, opt_file,      pos) = (Generate    (lang, term, opt_file),      pos)
 def mkSubst       (spec_term, sm_term,        pos) = (Subst       (spec_term, sm_term),        pos)
 def mkOpRefine    (spec_term, elements,       pos) = (OpRefine    (spec_term, elements),       pos)
 def mkTransform   (spec_term, transforms,     pos) = (Transform   (spec_term, transforms),     pos)
 def mkObligations (term,                      pos) = (Obligations (term),                      pos)
 def mkExpand      (term,                      pos) = (Expand      (term),                      pos)
 def mkReduce      (term_a, term_b,            pos) = (Reduce      (term_a, term_b),            pos)
 def mkOther       (other,                     pos) = (Other       other,                       pos)

 def mkTransformName(name: String, pos: Position)                  : TransformExpr = Name(name, pos)
 def mkTransformNumber(n: Nat, pos: Position)                      : TransformExpr = Number(n, pos)
 def mkTransformQual(q: String, name: String, pos: Position)       : TransformExpr = Qual(q, name, pos)
 def mkTransformItem(mod: String, te: TransformExpr, pos: Position): TransformExpr = Item(mod, te, pos)
 def mkTransformApply(head: TransformExpr, args: List TransformExpr, pos: Position): TransformExpr
   = Apply(head, args, pos)
 def mkTransformApplyOptions(head: TransformExpr, args: List TransformExpr, pos: Position): TransformExpr
   = ApplyOptions(head, args, pos)
 def mkTransformTuple(itms: List TransformExpr, pos: Position): TransformExpr = Tuple(itms, pos)

 op  hasHashSuffix?: RelativeUID -> Boolean
 def hasHashSuffix? unitId =
   case unitId of
     | UnitId_Relative  ({path,hashSuffix=Some _}) -> true
     | SpecPath_Relative({path,hashSuffix=Some _}) -> true
     | _ -> false

 op  deviceString?: String -> Boolean
 def deviceString? s =
   let len = length s in
   len > 1 && sub(s,len - 1) = #:

endspec
