\section{Abstract sort For Procedures}

This is a prototype implementation for \PSL\. This spec defines
the sort corresponding to the semantic representation of a PSL procedure.

Bipointed predicative \BSpecs\ are those where the morphisms in
a diagram are all imports and where each \BSpec\ has two \emph{points};
corresponding to initial and final states.

\begin{spec}
SpecCalc qualifying spec {
  % import SpecCalc qualifying /Languages/BSpecs/Predicative/Multipointed
  import SpecCalc qualifying /Languages/BSpecs/Predicative/BetterPrinter
  % import BSpecs qualifying /Languages/BSpecs/Predicative/Multipointed

  sort Procedure = {
    parameters : List String,
    return : Option String,
    staticSpec : Spec, % why are these here?
    dynamicSpec : Spec,
    code : BSpec
  }

  op makeProcedure : List String -> Option String -> Spec -> Spec -> BSpec -> Procedure
  def makeProcedure args ret static dynamic bSpec = {
    parameters = args,
    return = ret,
    staticSpec = static,
    dynamicSpec = dynamic,
    code = bSpec
  }
\end{spec}

The field \verb+paramaters+ lists the names of the formal parameters
of the procedure. Rather than strings, it might be better if this were
sort \verb+var+ from the MetaSlang abstract syntax as this includes
the identifier name together with its sort. String may be sufficient,
however, since once we have a semantic representation, we don't need
the types anymore. Parameters are call by value.

The field \verb+return+ holds the name of the identifier within the
procedure to be passed back to the caller.  There might be a better
way. We return different terms from different places in the procedure. The
assumption here is that before returning, the procedure will make
a transition to the final state of the \BSpec\ and that along that
transition, it will assign a return value to the given identifier. This
final state has no successor transitions.

The field \verb+staticSpec+ gives the sorts, operators and axioms which, while
not part of the machine state, are available to the procedure being
defined and to the procedures within its scope. To that end, the static spec
is imported into every spec in the \BSpec\ defining the procedure and
into the static spec for the procedures defined within its scope.

The static spec also includes an operator declaration mirroring the
procedure being defined and each procedure in scope. See Compile.spec
for details.

The field \verb+dynamicSpec+ gives the operators representing the variables
in scope when the procedure was declared (but defined outside the
procedure). These are in scope and can be modified within the procedure
even though they are not passed as parameters. The current scheme is
sufficient in the short term, but proper scoping of variables remains
a problem requiring thought. The current scheme, for example, will not
handle name clashes properly.

This isn't the final answer since it doesn't allow us to introduce new
ops and axioms along a transition \ldots only when we introduce procedures.

\begin{spec}
  op ppProcedureLess : Procedure -> Spec -> Pretty
  def ppProcedureLess proc spc =
    ppConcat [
      ppString "params=(",
      ppSep (ppString ",") (map ppString proc.parameters),
      ppString "), return=",
      case proc.return of
          None -> ppNil
        | Some name -> ppString name,
      % ppNewline,
      % ppString "staticSpec=",
      % ppNewline,
      % ppString "  ",
      % ppIndent (ppSpec proc.staticSpec),
      ppNewline,
      ppString "bspec=",
      ppNewline,
      ppString "  ",
      ppIndent (ppBSpecShort proc.code proc.dynamicSpec)
    ]

  op ppProcedure : Procedure -> Pretty
  def ppProcedure proc =
    ppConcat [
      ppString "params=(",
      ppSep (ppString ",") (map ppString proc.parameters),
      ppString "), return=",
      case proc.return of
          None -> ppNil
        | Some name -> ppString name,
      % ppNewline,
      % ppString "staticSpec=",
      % ppNewline,
      % ppString "  ",
      % ppIndent (ppSpec proc.staticSpec),
      ppNewline,
      ppString "bspec=",
      ppNewline,
      ppString "  ",
      ppIndent (ppBSpec proc.code)
    ]

  op showProcedure : Procedure -> String
  def showProcedure proc =
      "params=("
      ^ (List.show "," proc.parameters)   %%% Why do we need the qualifier?
      ^ "), return="
      ^ (case proc.return of
          None -> ""
        | Some name -> name)
      ^ "\nbspec=\n"
      ^ (ppFormat (ppBSpec proc.code))
}
\end{spec}
