\section{Abstract sort for procedures}

This spec defines the sort corresponding to the semantic value
of a PSL procedure.

The list of strings, \verb+parameters+, gives the formal parameters to
the procedure.  These are strings but an alternative might be to uses
sort \verb+var+ from the MetaSlang abstract syntax as this includes
the identifier name together with its sort. Strings may be sufficient,
however, since once we have a semantic representation, we don't need
the types anymore. Parameters are call by value.

The field \verb+dynamicSpec+ records the variables in scope at the
point where the procedure is declared. It does not include the formal
parameters of the procedure. This might later be renamed "variables".

Similarly the fields \verb+staticSpec+ is a static context containing
the constants in scope where the procedure is declared. This includes
a static operator defining a predicate that encapsulates the effect
of the procedure. This operator has the same name as the procedure.
This spec might later be renamed "constants".

The field \verb+bSpec+ holds the ``flow graph'' for the procedure
represented as a \emph{predicative multipointed bspec}.  Multipointed
means that the graph has a single start state but possibly many final
states.

\begin{spec}
SpecCalc qualifying spec {
  import SpecCalc qualifying /Languages/BSpecs/Predicative/BetterPrinter

  sort ReturnInfo = Option {returnName : String, returnSort : ASort Position}

  sort Procedure = {
    parameters : List String,
    returnInfo : ReturnInfo,
    dynamicSpec : Spec,
    staticSpec : Spec,
    bSpec : BSpec
  }

  op makeProcedure : List String -> ReturnInfo -> Spec -> Spec -> BSpec -> Procedure
  def makeProcedure args returnInfo static dynamic bSpec = {
    parameters = args,
    returnInfo = returnInfo,
    dynamicSpec = dynamic,
    staticSpec = static,
    bSpec = bSpec
  }
\end{spec}

The field \verb+returnName+ holds the name of the identifier within the
procedure to be assigned the return value. Right now, this is the name of
the procedure prefixed by the string "return#".  There might be a better
way. The assumption here is that before returning, the procedure will
make a transition to the final state of the \BSpec\ and that along that
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

\begin{spec}
  op ppProcedureLess : Procedure -> Spec -> WadlerLindig.Pretty
  def ppProcedureLess proc spc =
    ppConcat [
      ppString "params=(",
      ppSep (ppString ",") (map ppString proc.parameters),
      ppString "), return=",
      case proc.returnInfo of
        | None -> ppNil
        | Some {returnName,returnSort} -> ppString returnName,
      % ppNewline,
      % ppString "staticSpec=",
      % ppNewline,
      % ppString "  ",
      % ppIndent (ppSpec proc.staticSpec),
      ppNewline,
      ppString "bspec=",
      ppNewline,
      ppString "  ",
      ppIndent (ppBSpecShort proc.bSpec proc.dynamicSpec)
    ]

  op ppProcedure : Procedure -> WadlerLindig.Pretty
  def ppProcedure proc =
    ppConcat [
      ppString "params=(",
      ppSep (ppString ",") (map ppString proc.parameters),
      ppString "), return=",
      case proc.returnInfo of
        | None -> ppNil
        | Some {returnName,returnSort} -> ppString returnName,
      % ppNewline,
      % ppString "staticSpec=",
      % ppNewline,
      % ppString "  ",
      % ppIndent (ppSpec proc.staticSpec),
      ppNewline,
      ppString "bspec=",
      ppNewline,
      ppString "  ",
      ppIndent (ppBSpec proc.bSpec)
    ]

  op showProcedure : Procedure -> String
  def showProcedure proc =
      "params=("
      ^ (List.show "," proc.parameters)   %%% Why do we need the qualifier?
      ^ "), return="
      ^ (case proc.returnInfo of
          | None -> ""
          | Some {returnName,returnSort} -> returnName)
      ^ "\nbspec=\n"
      ^ (ppFormat (ppBSpec proc.bSpec))
}
\end{spec}
