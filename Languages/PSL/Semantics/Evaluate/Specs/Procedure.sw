\section{Abstract sort for procedures}

This spec defines the sort corresponding to the semantic value of a PSL /
Oscar procedure.

The list of strings, \verb+parameters+, gives the formal parameters to
the procedure.  These are strings but an alternative might be to also
include the sort for the variables.  Parameters are call by value.

The field \verb+modeSpec+ records the ops, sorts and variables in scope
at the point where the procedure is declared. It does not include the
formal parameters of the procedure.

The ops include a static operator defining a predicate that encapsulates
the effect of the procedure. This operator has the same name as the
procedure.

The field \verb+bSpec+ holds the ``flow graph'' for the procedure
represented as a \emph{predicative multipointed bspec}.  Multipointed
means that the graph has a single start state but possibly many final
states.

\begin{spec}
Proc qualifying spec {
  import ModeSpec
  import translate /Languages/BSpecs/Predicative/Multipointed by {
      Cat.Object +-> ModeSpec.ModeSpec,
      Cat.Arrow +-> ModeSpec.Morphism
    }

  sort ReturnInfo = Option {returnId : Id, returnType : Type}

  op ReturnInfo.make : Id -> Type -> ReturnInfo
  def ReturnInfo.make id type = Some {returnId = id, returnType = type}

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

  op parameters : Procedure -> List String
  def parameters proc = proc.parameters

  op bSpec : Procedure -> BSpec
  def bSpec proc = proc.bSpec

  op returnInfo : Procedure -> ReturnInfo
  def returnInfo proc = proc.returnInfo

  op modeSpec : Procedure -> ModeSpec
  def modeSpec proc = proc.modeSpec
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
      ppSep (pp ",") (map pp (parameters proc)),
      pp "), returnInfo=[",
      pp (returnInfo proc),
      pp "]",
      ppNewline,
      pp "bSpec=",
      ppNewline,
      pp "  ",
      ppIndent (pp (bSpec proc))
    ]

  op ReturnInfo.pp : ReturnInfo -> Doc
  def ReturnInfo.pp info =
    case info of
      | None -> pp "None"
      | Some {returnId,returnType} ->
          ppConcat [
            pp "returnId=",
            pp returnId,
            pp " returnType=",
            pp returnType
          ]

   op show : Procedure -> String 
   def show proc = ppFormat (pp proc)
}
\end{spec}
