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
Procedure qualifying spec {
  import ModeSpec

  import SpecCalc qualifying /Languages/BSpecs/Predicative/Multipointed/Monomorphic

  sort ReturnInfo = Option {returnName : String, returnSort : ASort Position}

  sort Procedure = {
    parameters : List String,
    returnInfo : ReturnInfo,
    modeSpec : ModeSpec,
    bSpec : BSpec
  }

  op make : List String -> ReturnInfo -> ModeSpec -> BSpec -> Procedure
  def make args returnInfo modeSpec bSpec = {
    parameters = args,
    returnInfo = returnInfo,
    modeSpec = modeSpec,
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

The field \verb+modeSpec+ gives the sorts, operators variables and axioms
that are in scope within the procedure. This does not include the formal
parameters to the procedure.  It also includes an operator declaration
mirroring the procedure being defined and each procedure in scope. See
Compile.spec for details.

Proper scoping of variables requires thought.
problem requiring thought. The current scheme, for example, will not
handle name clashes properly.

\begin{spec}
  op pp : Procedure -> Doc
  def pp proc =
    ppConcat [
      pp "params=(",
      ppSep (pp ",") (map pp proc.parameters),
      pp "), return=",
      case proc.returnInfo of
        | None -> ppNil
        | Some {returnName,returnSort} -> pp returnName,
      ppNewline,
      pp "bspec=",
      ppNewline,
      pp "  ",
      ppIndent (pp (bSpec proc))
    ]

  op show : Procedure -> String
  def show proc =
      "params=("
      ^ (List.show "," proc.parameters)   %%% Why do we need the qualifier?
      ^ "), return="
      ^ (case proc.returnInfo of
          | None -> ""
          | Some {returnName,returnSort} -> returnName)
      ^ "\nbspec=\n"
      ^ (ppFormat (pp (bSpec proc)))
}
\end{spec}
