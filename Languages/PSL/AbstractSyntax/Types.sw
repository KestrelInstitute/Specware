\section{Spec Calculus Abstract Syntax}

\begin{spec}
OscarAbsSyn qualifying spec
  import ../../MetaSlang/Specs/StandardSpec % For Position
  import ../../MetaSlang/AbstractSyntax/AnnTerm % For PSL, but not Specware4
  import ../../SpecCalculus/AbstractSyntax/Types
\end{spec}

This defines the abstract syntax of a simple procedural specification
language. It is built on top of MetaSlang. We import the spec defining the
abstract syntax of MetaSlang.

This is a general sort for an annotated syntax tree for the procedural
specification language. The annotations give rise to the polymorphism of
the sorts defined below. Thus, one can associate positional information,
types, etc. with fragments of code. At present, only the sort Command
is annotated. Annotated versions of the other sorts may be needed later.

Declarations are MetaSlang \verb+sort+, \verb+op+, \verb+def+, and
\verb+axiom+ declarations plus \verb+var+ (variable) and \verb+proc+
(procedure) declarations. Bear in mind that \verb+def+s in the concrete
syntax appear as \verb+op+s in the abstract syntax with an associated
defining term.

\begin{spec}
  sort OscarSpecElem a = (OscarSpecElem_ a) * a

  sort Ident = String
  sort OscarSpecElem_ a =
    | Import (SpecCalc.Term a)
    | Sort   List QualifiedId * (TyVars * List (ASortScheme a))
    | Op     List QualifiedId * (Fixity * ASortScheme a * List (ATermScheme a))
    | Claim  (AProperty a)
    | Var    List QualifiedId * (Fixity * ASortScheme a * List (ATermScheme a))
    | Def    List QualifiedId * (Fixity * ASortScheme a * List (ATermScheme a))
    | Proc   Ident * (ProcInfo a)

  sort ProcInfo a = {
    formalArgs : List (AVar a),
    returnSort : ASort a,
    command : Command a
  }

  op formalArgs : fa(a) ProcInfo a -> List (AVar a)
  def formalArgs procInfo = procInfo.formalArgs

  op returnSort : fa(a) ProcInfo a -> ASort a
  def returnSort procInfo = procInfo.returnSort

  op command : fa(a) ProcInfo a -> Command a
  def command procInfo = procInfo.command
\end{spec}

\begin{spec}
  op mkImport : SpecCalc.Term Position * Position -> OscarSpecElem Position
  def mkImport (term,position) = (Import term, position)

  op mkSort : List QualifiedId * TyVars * List (ASortScheme Position) * Position -> OscarSpecElem Position
  def mkSort (ids,tyVars,sortSchemes,position) = (Sort (ids, (tyVars,sortSchemes)),position) 

  op mkProc : Ident * (ProcInfo Position) * Position -> OscarSpecElem Position
  def mkProc (ident,procInfo,position) = (Proc (ident,procInfo),position)

  op mkProcInfo : List (AVar Position) * (ASort Position) * Command Position -> ProcInfo Position
  def mkProcInfo (formalArgs,returnSort,command) =
    {formalArgs = formalArgs, returnSort = returnSort, command = command}
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
  sort Command a = (Command_ a) * a
  sort Command_ a = 
    | If         List (Alternative a)
    | Case       (ATerm a) * (List (Case a))
    | Do         List (Alternative a)
    | Assign     (ATerm a) * (ATerm a)
    | Let        List (OscarSpecElem a) * (Command a)
    | Seq        List (Command a)
    | Relation   (ATerm a)
    | Return     Option (ATerm a)
    | Continue   
    | Break
    | Exec       (ATerm a)
    | Skip
\end{spec}

\begin{spec}
  op mkIf : List (Alternative Position) * Position -> Command Position
  def mkIf (alts,position) = (If alts,position)

  op mkSeq : List (Command Position) * Position -> Command Position
  def mkSeq (commands,position) = (Seq commands, position)
\end{spec}

An \emph{alternative} is a guarded command in the sense of Dijkstra.
A \emph{case} is a pattern, a boolean valued guard, and a command.
In the near term, there is no support for the guard. In the longer term,
we may want to dispense with the \verb+if+ in the abstract syntax
since, with guards, the case statement subsumes it.

Perhaps the guard term in the case should be made \verb+Option+al.

\begin{spec}
  sort Alternative a = (Alternative_ a) * a
  sort Alternative_ a = (ATerm a) * (Command a)
  sort Case a = (Case_ a) * a
  sort Case_ a = (APattern a) * (ATerm a) * (Command a)

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
endspec
\end{spec}
