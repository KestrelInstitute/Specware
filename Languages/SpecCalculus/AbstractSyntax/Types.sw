\section{Spec Calculus Abstract Syntax}

\begin{spec}
SpecCalc qualifying spec
\end{spec}

We import PosSpec for Position, QualifiedId, ASortScheme etc.  This is a
bit of a shame as AnnSpec would like to import this spec so as to insert
a spec calculus term in the import of a spec. This would create a cyclic
dependency between specs. At present, this is addressed in AnnSpec by
defining an abstract sort SpecCalc.Term a, which is refined below.

\begin{spec}
  import ../../MetaSlang/Specs/StandardSpec 
  import /Library/Legacy/Utilities/Lisp % for LispCell
\end{spec}

All the objects in the abstract syntax are polymorphic and defined at
two levels.  The first level pairs the sort the type paramerter. The
second level defines the constructors for the sort. In this way, every
sort is annotated. The annotation is typically information about the
position of the term in the file. It is not clear that there is any
benefit in making this polymorphic. Might might be enough to pair it
with the \verb+Position+ sort and then refine that sort.  Using two
levels ensures that for all objects in the abstract syntax tree, the
position information is always the second component.

\begin{spec}
  op valueOf    : fa (a) a * Position -> a
  op positionOf : fa (a) a * Position -> Position

  def valueOf    (value, _       ) = value
  def positionOf (_,     position) = position
\end{spec}

The following is the toplevel returned by the parser. I don't like
the name of this sort. A file may contain a list of $\mathit{name} =
\mathit{term}$ or contain a single term. This should not be polymorphic.
The type parameter should be instantiated with the type \verb+Position+.

\begin{spec}
  sort SpecFile  a = (SpecFile_ a) * a
  sort SpecFile_ a =
    | Term  (Term a)
    | Decls (List (Decl a))
\end{spec}

The support for UnitId's is somewhat simplistic but hopefully sufficient
for now.  A user may specify a unitId that is relative to the current unitId
(ie relative to the object making the reference) or relative to a path
in the \verb+SPECPATH+ environment variable. In the current syntax, the
latter are indicated by an opening "/". In additon, each unitId evaluates
to a full canonical system path. The latter cannot be directly entered
by the user. My apologies for the long constructor names. A relative UnitId
resolves to a canonical UnitId. The latter in turn resolves to an absolute
path in the file system. Recall that file may contain a single anonymous
term or a list of bindings. Thus a canonical UnitId may resolve to two
possible path names. Later we may want to have UIDs with network addresses.

\begin{spec}
  sort UnitId = {
      path : List String,
      hashSuffix : Option String
   }

  sort RelativeUID =
    | UnitId_Relative UnitId
    | SpecPath_Relative UnitId

  sort RelativeUnitId = RelativeUID
\end{spec}

The sort \verb+Name+ is used everywhere that one can expect a
non-structured identifier.  This includes for instance, the names of
vertices and edges in the shape of a diagram. It also includes the
qualifiers on op and sort names.

In the near term, it also includes the identifiers bound by declarations.
These are either \verb+let+ bound or bound by specs listed in a
file. Later, we might allow bound identifiers to be UIDs thus enabling
one to override an existing definition.

\begin{spec}
  sort Name = String
  sort ProverName = Name
  sort ClaimName = QualifiedId
\end{spec}

In a basic Specware image, OtherTerm is unspecified, but in an extension
such as PSL or Planware, it might be refined to an application-specific 
term, or a coproduct of such terms.

\begin{spec}
  sort OtherTerm a  % hook for extensions
\end{spec}

The following is the sort given to us by the parser.

\begin{spec}
  sort Term a = (Term_ a) * a
  sort Term_ a = 
    | Print   (Term a)
    | Prove   ClaimName * Term a * ProverName * Assertions * ProverOptions * AnswerVar
    | UnitId     RelativeUID
    | Spec    List (SpecElem a)
    | Diag    List (DiagElem a)
    | Colimit (Term a)
\end{spec}

The calculus supports two types of morphisms: morphisms between specs and
morphisms between diagrams.  Right now spec morphism are distinguished
from diagram morphisms in both the concrete and abstract syntax.
The first two elements in the morphism products are terms that evaluate
to the domain and codomain of the morphisms.

\begin{spec}
    | SpecMorph (Term a) * (Term a) * (List (SpecMorphRule a))
    | DiagMorph (Term a) * (Term a) * (List (DiagMorphRule a))
    | ExtendMorph  (Term a)
\end{spec}

\begin{spec}
    | Qualify   (Term a) * Name
    | Translate (Term a) * (TranslateExpr a)
\end{spec}

The intention is that \verb+let+ \emph{decls} \verb+in+ \emph{term}
is the same as \emph{term} \verb+where+ \emph{decls}. The \verb+where+
construct is experimental.

\begin{spec}
    | Let   (List (Decl a)) * (Term a)
    | Where (List (Decl a)) * (Term a)
\end{spec}

The next two control the visibilty of names outside a spec.

\begin{spec}
    | Hide   (List (NameExpr a)) * (Term a)
    | Export (List (NameExpr a)) * (Term a)
\end{spec}

This is an initial attempt at code generation. The first string is the
name of the target language. Perhaps it should be a constructor.
Also perhaps we should say where to put the output. The idea is that
is should go in the file with the same root name as the UnitId calling
compiler (but with a .lisp suffix) .. but the term may not have a UnitId.
The third argument is an optional file name to store the result.

\begin{spec}
    | Generate (String * (Term a) * Option String)
\end{spec}

Subsitution. The first term should be spec valued and the second should
be morphism valued. Remains to be seen what will happen if/when we
have diagrams.

\begin{spec}
    | Subst (Term a) * (Term a)
\end{spec}

Obligations takes a spec or a a morphism and returns a spec including
the proof obligations as conjectures.

\begin{spec}
    | Obligations (Term a)
\end{spec}

Expand takes a spec and returns a transformed spec that has lambdas
lifted nad HO functions instantiated and defintions expanded into
axioms.  It is essentially the input to the Snark prover interface.

\begin{spec}
    | Expand (Term a)
\end{spec}

Reduce will rewrite the given term in the context of the given spec
using the definitions and axioms of the spec as rules.

\begin{spec}
    | Reduce (ATerm a * Term a)
\end{spec}

The following is a hook for creating applications that are 
extensions to Specware.  If more than one new term is needed,
you can make OtherTerm a coproduct of the desired terms.

\begin{spec}
    | Other (OtherTerm a)
\end{spec}

The following are declarations that appear in a file or listed
within a \verb+let+. As noted above, at present the identifiers
bound by a let or listed in a file are unstructured.

\begin{spec}
  sort Decl a = Name * (Term a)
\end{spec}

A \verb+TranslateExpr+ denotes a mapping on the op and sort names in a
spec. Presumably, in the longer term there will a pattern matching syntax
to simplify the task of uniformly renaming a collection of operators
and sorts or for requalifying things. For now, a translation is just a
mapping from names to names, annotated with the full list of aliases
to be used in the target info.

Recall the sort \verb+IdInfo+ is just a list of identifiers (names).

\begin{spec}
  sort TranslateExpr  a = List (TranslateRule a) * a
  sort TranslateRule  a = (TranslateRule_ a) * a
  sort TranslateRule_ a =
    | Sort      QualifiedId                 * QualifiedId                 * SortNames % last field is all aliases
    | Op        (QualifiedId * Option Sort) * (QualifiedId * Option Sort) * OpNames   % last field is all aliases
    | Ambiguous QualifiedId                 * QualifiedId                 * Aliases   % last field is all aliases
\end{spec}

A \verb+NameExpr+ denote the name of an op, sort or claim. Lists of such
expressions are used in \verb+hide+ and \verb+export+ terms to either
exclude names from being export or dually, to specify exactly what names
are to be exported.  Presumably the syntax will borrow ideas from the
syntax used for qualifiying names. In particular we might want to allow
patterns with wildcards to stand for a collection of names. For now,
one must explicitly list them.

There is some inconsistency here as NameExpr is not annotated with 
a position as in TranslateExpr above.

\begin{spec}
  sort NameExpr a = | Sort       QualifiedId
                    | Op         QualifiedId * Option Sort
                    | Axiom      QualifiedId
                    | Theorem    QualifiedId
                    | Conjecture QualifiedId
                    | Ambiguous  QualifiedId
\end{spec}

A \verb+SpecElem+ is a declaration within a spec, \emph{i.e.} the ops sorts etc.

\begin{spec}
  sort SpecElem a = (SpecElem_ a) * a

  sort SpecElem_ a =
    | Import List (Term a)
    | Sort   List QualifiedId * (TyVars * List (ASortScheme a))
    | Op     List QualifiedId * (Fixity * ASortScheme a * List (ATermScheme a))
    | Claim  (AProperty a)
\end{spec}

A diagram is defined by a list of elements. An element may be a labeled
vertex or edge.

In the current form, the names of vertices and edges are simply
\verb{Name}s. This may change in the future. In particular, one can
construct limits and colimits of diagram in which case, vertices and
edges in the resulting shape may be tuples and equivalence classes. It
remains to be seen whether we need a concrete syntax for this.

\begin{spec}
  sort DiagElem a = (DiagElem_ a) * a
  sort DiagElem_ a =
    | Node NodeId * (Term a)
    | Edge EdgeId * NodeId * NodeId * (Term a)
  sort NodeId = Name
  sort EdgeId = Name
\end{spec}

Note that the term associated with a node must evaluate to a spec
or diagram. The term for an edge must evaluate to a spec morphism or
diagram morphism.

The syntax for spec morphisms accommodates mapping names to terms but
the interpreter handles only name to name maps for now.

The tagging in the sorts below may be excessive given the \verb+ATerm+
is already tagged.

\begin{spec}
  sort SpecMorphRule a = (SpecMorphRule_ a) * a
  sort SpecMorphRule_ a = 
    | Sort      QualifiedId * QualifiedId
    | Op        (QualifiedId * Option Sort) * (QualifiedId * Option Sort)
    | Ambiguous QualifiedId * QualifiedId 
\end{spec}

The current syntax allows one to write morphisms mapping names to terms
but only name/name mappings will be handled by the interpreter in the
near term.

A diagram morphism has two types of elements: components of the shape map
and components of the natural transformation. The current syntax allows
them to be presented in any order. 

A \verb+NatTranComp+ element is a component in a natural transformation
between diagrams. The components are indexed by vertices in the shape.
The term in the component must evaluate to a morphism.

\begin{spec}
  sort DiagMorphRule a = (DiagMorphRule_ a) * a
  sort DiagMorphRule_ a =
    | ShapeMap    Name * Name
    | NatTranComp Name * (Term a) 
\end{spec}

\begin{spec}
  sort Assertions = | All
                    | Explicit List ClaimName

  sort ProverOptions = | OptionString (List LispCell)
                       | OptionName QualifiedId
                       | Error   (String * String)  % error msg, problematic string

  sort AnswerVar = Option Var
\end{spec}

The following are invoked from the parser:

\begin{spec}

  op mkTerm        : fa (a) (Term a)                                                        * a -> SpecFile a
  op mkDecls       : fa (a) (List (Decl a))                                                 * a -> SpecFile a

  op mkPrint       : fa (a) (Term a)                                                        * a -> Term a
  op mkProve       : fa (a) ClaimName * Term a * ProverName * Assertions * ProverOptions * AnswerVar   * a -> Term a
  op mkUnitId      : fa (a) RelativeUID                                                     * a -> Term a
  op mkSpec        : fa (a) (List (SpecElem a))                                             * a -> Term a
  op mkDiag        : fa (a) (List (DiagElem a))                                             * a -> Term a
  op mkColimit     : fa (a) (Term a)                                                        * a -> Term a
  op mkSpecMorph   : fa (a) (Term a) * (Term a) * (List (SpecMorphRule a))                  * a -> Term a
  op mkDiagMorph   : fa (a) (Term a) * (Term a) * (List (DiagMorphRule a))                  * a -> Term a
  op mkExtendMorph : fa (a) (Term a)                                                        * a -> Term a
  op mkQualify     : fa (a) (Term a) * Name                                                 * a -> Term a
  op mkTranslate   : fa (a) (Term a) * (TranslateExpr a)                                    * a -> Term a
  op mkLet         : fa (a) (List (Decl a)) * (Term a)                                      * a -> Term a
  op mkWhere       : fa (a) (List (Decl a)) * (Term a)                                      * a -> Term a
  op mkHide        : fa (a) (List (NameExpr a)) * (Term a)                                  * a -> Term a
  op mkExport      : fa (a) (List (NameExpr a)) * (Term a)                                  * a -> Term a
  op mkGenerate    : fa (a) String * (Term a) * (Option String)                             * a -> Term a
  op mkSubst       : fa (a) (Term a) * (Term a)                                             * a -> Term a
  op mkObligations : fa (a) (Term a)                                                        * a -> Term a
  op mkExpand      : fa (a) (Term a)                                                        * a -> Term a
  op mkReduce      : fa (a) (ATerm a) * (Term a)                                            * a -> Term a
  op mkOther       : fa (a) (OtherTerm a)                                                   * a -> Term a

  %% SpecFile's    

  def mkTerm        (term,                      pos) = (Term        term,                        pos)
  def mkDecls       (decls,                     pos) = (Decls       decls,                       pos)

  %% Term's

  def mkPrint       (term,                      pos) = (Print       term,                        pos)
  def mkProve       (claim_name, term, prover_name, assertions, prover_options, answer_var, pos) 
                                                     = (Prove       (claim_name, term, prover_name, assertions, prover_options, answer_var), pos) 
  def mkUnitId      (uid,                       pos) = (UnitId      uid,                         pos)
  def mkSpec        (elements,                  pos) = (Spec        elements,                    pos)
  def mkDiag        (elements,                  pos) = (Diag        elements,                    pos)
  def mkColimit     (diag,                      pos) = (Colimit     diag,                        pos)
  def mkSpecMorph   (dom_term, cod_term, rules, pos) = (SpecMorph   (dom_term, cod_term, rules), pos)
  def mkDiagMorph   (dom_term, cod_term, rules, pos) = (DiagMorph   (dom_term, cod_term, rules), pos)
  def mkExtendMorph (term,                      pos) = (ExtendMorph term,                        pos)
  def mkQualify     (term, name,                pos) = (Qualify     (term, name),                pos)
  def mkTranslate   (term, translate_expr,      pos) = (Translate   (term, translate_expr),      pos)
  def mkLet         (decls, term,               pos) = (Let         (decls, term),               pos)
  def mkWhere       (decls, term,               pos) = (Where       (decls, term),               pos)
  def mkHide        (name_exprs, term,          pos) = (Hide        (name_exprs, term),          pos)
  def mkExport      (name_exprs, term,          pos) = (Export      (name_exprs, term),          pos)
  def mkGenerate    (lang, term, opt_file,      pos) = (Generate    (lang, term, opt_file),      pos)
  def mkSubst       (spec_term, sm_term,        pos) = (Subst       (spec_term, sm_term),        pos)
  def mkObligations (term,                      pos) = (Obligations (term),                      pos)
  def mkExpand      (term,                      pos) = (Expand      (term),                      pos)
  def mkReduce      (term_a, term_b,            pos) = (Reduce      (term_a, term_b),            pos)
  def mkOther       (other,                     pos) = (Other       other,                       pos)

  op  hasHashSuffix?: RelativeUID -> Boolean
  def hasHashSuffix? unitId =
    case unitId of
      | UnitId_Relative  ({path,hashSuffix=Some _}) -> true
      | SpecPath_Relative({path,hashSuffix=Some _}) -> true
      | _ -> false
endspec
\end{spec}
