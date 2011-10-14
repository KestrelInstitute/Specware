\section{Spec Calculus Abstract Syntax}

\begin{spec}
OscarAbsSyn qualifying spec
  import /Languages/MetaSlang/Specs/StandardSpec % For Position
  import /Languages/MetaSlang/AbstractSyntax/AnnTerm % For PSL, but not Specware4
  import /Languages/SpecCalculus/AbstractSyntax/Types
\end{spec}

This defines the abstract syntax of a simple procedural specification
language. It is built on top of MetaSlang. We import the spec defining the
abstract syntax of MetaSlang.

This is a general type for an annotated syntax tree for the procedural
specification language. The annotations give rise to the polymorphism of
the types defined below. Thus, one can associate positional information,
types, etc. with fragments of code. At present, only the type Command
is annotated. Annotated versions of the other types may be needed later.

Declarations are MetaSlang \verb+type+, \verb+op+, \verb+def+, and
\verb+axiom+ declarations plus \verb+var+ (variable) and \verb+proc+
(procedure) declarations. Bear in mind that \verb+def+s in the concrete
syntax appear as \verb+op+s in the abstract syntax with an associated
defining term.

### The name of the procedure should be a qualified id.

\begin{spec}
  type OscarSpecElem a = (OscarSpecElemBody a) * a

  type Ident = String
  type OscarSpecElemBody a =
    | Import (List (SpecCalc.Term a))
    | Type   List QualifiedId * (TyVars * List (ATypeScheme a))
    | Op     List QualifiedId * (Fixity * ATypeScheme a * List (ATermScheme a))
    | Claim  (Claim a)
    | Var    List QualifiedId * (Fixity * ATypeScheme a * List (ATermScheme a))
    | Def    List QualifiedId * (Fixity * ATypeScheme a * List (ATermScheme a))
    | Proc   Ident * (ProcInfo a)

  type Claim a = ClaimType * PropertyName * TyVars * ATerm a
  type ClaimType = | Axiom | Theorem | Invariant | Conjecture

  type ProcInfo a = {
    formalArgs : List (AVar a),
    returnType : AType a,
    command : Command a
  }

  op formalArgs : fa(a) ProcInfo a -> List (AVar a)
  def formalArgs procInfo = procInfo.formalArgs

  op returnType : fa(a) ProcInfo a -> AType a
  def returnType procInfo = procInfo.returnType

  op command : fa(a) ProcInfo a -> Command a
  def command procInfo = procInfo.command
\end{spec}

\begin{spec}
  op mkImport : (List (SpecCalc.Term Position)) * Position -> OscarSpecElem Position
  def mkImport (terms,position) = (Import terms, position)

  op mkType : List QualifiedId * TyVars * List (ATypeScheme Position) * Position -> OscarSpecElem Position
  def mkType (ids,tyVars,typeSchemes,position) = (Type (ids, (tyVars,typeSchemes)),position) 

  op mkProc : Ident * (ProcInfo Position) * Position -> OscarSpecElem Position
  def mkProc (ident,procInfo,position) = (Proc (ident,procInfo),position)

  op mkProcInfo : List (AVar Position) * (AType Position) * Command Position -> ProcInfo Position
  def mkProcInfo (formalArgs,returnType,command) =
    {formalArgs = formalArgs, returnType = returnType, command = command}

  op mkVar : (List QualifiedId) * (ATypeScheme Position) * Position -> OscarSpecElem Position
  def mkVar (ids,typeScheme,position) = (Var (ids, (Nonfix,typeScheme,[])),position)

  op mkDef : (List QualifiedId) * (Option Fixity) * (ATypeScheme Position) * List (ATermScheme Position) * Position -> OscarSpecElem Position
  def mkDef (ids,optFixity,typeScheme,termSchemes,position) = 
    case optFixity of
      | None -> (Def (ids, (Nonfix,typeScheme,termSchemes)),position)
      | Some fixity -> (Def (ids, (fixity,typeScheme,termSchemes)),position)

  op mkOp : (List QualifiedId) * (Option Fixity) * (ATypeScheme Position) * List (ATermScheme Position) * Position -> OscarSpecElem Position
  def mkOp (ids,optFixity,typeScheme,termSchemes,position) = 
    case optFixity of
      | None -> (Op (ids, (Nonfix,typeScheme,termSchemes)),position)
      | Some fixity -> (Op (ids, (fixity,typeScheme,termSchemes)),position)
\end{spec}

The abstract syntax for commands is modeled after Dijkstra's guarded
command language.  Thus, rather than \verb+if+/\verb+then+/\verb+else+
and \verb+while+ we have guarded commands (or alternatives) wrapped in
\verb+if+ or \verb+do+. This form is appealing since the branching of
alternatives corresponds roughly with the branching in diagrams. Also,
the nondeterminism may prove useful later. A conventional syntax can be
used if preferred and easily mapped to this representation.

The intention is that the \verb+let+ commands behave like recursive
\verb+let+s. Order of declarations is not significant and declarations
may be mutually recursive (but guarded). It is unforunate that there is
both a \verb+let+ command and a MetaSlang \verb+let+ expression. This
needs some thought.

\begin{spec}
  type Command a = (CommandBody a) * a
  type CommandBody a = 
    | If         List (Alternative a)
    | Case       (ATerm a) * (List (Case a))
    | Do         List (Alternative a)
    | Assign     (ATerm a) * (ATerm a)
    | Let        List (OscarSpecElem a) * (Command a)
    | Seq        List (Command a)
    | Relation   (ATerm a)
    | Return     Option (ATerm a)
    | Continue   
    | Abort      Option (ATerm a)
    | Break
    | Exec       (ATerm a)
    | Skip
\end{spec}

\begin{spec}
  op mkIf : List (Alternative Position) * Position -> Command Position
  def mkIf (alts,position) = (If alts,position)

  op mkCase : ATerm Position * List (Case Position) * Position -> Command Position
  def mkCase (term,branches,position) = (Case (term,branches),position)

  op mkSeq : List (Command Position) * Position -> Command Position
  def mkSeq (commands,position) = (Seq commands, position)

  op mkDo : List (Alternative Position) * Position -> Command Position
  def mkDo (alts,position) = (Do alts,position)

  op mkAssign : ATerm Position * ATerm Position * Position -> Command Position
  def mkAssign (lhs,rhs,position) = (Assign (lhs,rhs),position)

  op mkLet : List (OscarSpecElem Position) * (Command Position) * Position -> Command Position
  def mkLet (decls,body,position) = (Let (decls,body),position)

  op mkReturn : Option (ATerm Position) * Position -> Command Position
  def mkReturn (optTerm,position) = (Return optTerm,position)

  op mkRelation : (ATerm Position) * Position -> Command Position
  def mkRelation (term,position) = (Relation term,position)

  op mkExec : (ATerm Position) * Position -> Command Position
  def mkExec (term,position) = (Exec term,position)

  op mkSkip : Position -> Command Position
  def mkSkip position = (Skip, position)

  op mkBreak : Position -> Command Position
  def mkBreak position = (Break, position)

  op mkContinue : Position -> Command Position
  def mkContinue position = (Continue, position)
\end{spec}

An \emph{alternative} is a guarded command in the sense of Dijkstra.
A \emph{case} is a pattern, a boolean valued guard, and a command.
In the near term, there is no support for the guard. In the longer term,
we may want to dispense with the \verb+if+ in the abstract syntax
since, with guards, the case statement subsumes it.

Perhaps the guard term in the case should be made \verb+Option+al.

\begin{spec}
  type Alternative a = (AlternativeBody a) * a
  type AlternativeBody a = (ATerm a) * (Command a)
  type Case a = (CaseBody a) * a
  type CaseBody a = (List (AVar a)) * (APattern a) * (ATerm a) * (Command a)

  op mkCaseBranch : (List (AVar Position)) * (APattern Position) * (Command Position) * Position -> Case Position
  def mkCaseBranch (vars,pat,cmd,pos) = ((vars,pat,mkTrueA pos,cmd),pos)

  op mkAlternative : (ATerm Position) * (Command Position) * Position -> Alternative Position
  def mkAlternative (term,command,position) = ((term,command),position)
\end{spec}

One could argue that the lists above should be sets.

We need a way to specify actions/commands that are relations (rather
than just assignments). Also, we need a way to assert local invariants.

There should be more consistency (or some convention) with respect to
using records (with field names) vs tuples.

The language is a first-order in the sense that one cannot pass
procedures as arguments. Perhaps this should be changed. Some options
include variants of Idealized Algol or John Reynold's language Forsythe.
This would also address the possible confusion arising from having
imperative and functional \verb+let+s, \verb+if+s, \verb+case+s etc.
Also, Reynolds has defined an effective encoding of object oriented
concepts into such languages.

Note that there are specific commands for procedure calls. The first one
calls the procedure, discarding the returned value. The second one calls
the procedure and assigns the returned value to the left-hand-side term.

Operators and procedures share the same name space. This is not ideal. It
precludes, for example, defining an operator for \emph{sqrt} which is
later implemented by a procedure with the same name. The distinction
between procedures and functions is also resolved in a nice way in both
Idealized Algol and Forsythe.

\begin{spec}

(*
  type SpecCalc.OtherTerm a =
    | Specialize MS.Term * SpecCalc.Term a
    | Inline String * SpecCalc.Term a
    | OscarDecls List (OscarSpecElem a)
    | Project String * (SpecCalc.Term a) * String

  op mkSpecialize : MS.Term * (SpecCalc.Term Position) * Position -> SpecCalc.Term Position
  def mkSpecialize (metaSlangTerm,unit,position) =
    mkOther (Specialize (metaSlangTerm,unit),position)

  op mkInline : String * (SpecCalc.Term Position) * Position -> SpecCalc.Term Position
  def mkInline (name,unit,position) =
    mkOther (Inline (name,unit),position)

  op mkProject : String * (SpecCalc.Term Position) * String * Position -> SpecCalc.Term Position
  def mkProject (name,unit,fileName,position) =
    mkOther (Project (name,unit,fileName),position)

  op mkDecls : List (OscarSpecElem Position) * Position -> SpecCalc.Term Position
  def mkDecls (specElems,position) = mkOther (OscarDecls specElems, position)
*)
\end{spec}

\begin{spec}
endspec
\end{spec}
