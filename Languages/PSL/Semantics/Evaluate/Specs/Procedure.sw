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
Proc qualifying spec
  import BSpec
  % import EdgeSets

%   import translate (translate /Languages/BSpecs/Predicative/Coalgebra
%     by {Cat.Object +-> ModeSpec.ModeSpec, Cat.Arrow +-> SpecMorph.Morphism})
%     by {CatObject._ +-> ModeSpec._, CatArrow._ +-> SpecMorph._, Cat._ +-> ModeSpecCat._,
%         Vertex._ +-> Vrtx._, Edge._ +-> Edg._,
%         VertexSet._ +-> VrtxSet._, EdgeSet._ +-> EdgSet._}
% 
  sort ReturnInfo = Option Op.Ref

  op ReturnInfo.make : Op.Ref -> ReturnInfo
  def ReturnInfo.make ref = Some ref

  sort Procedure = {
    parameters : List Op.Ref,
    varsInScope : List Op.Ref,
    returnInfo : ReturnInfo,
    modeSpec : ModeSpec,
    bSpec : BSpec
  }

  op makeProcedure : List Op.Ref -> List Op.Ref -> ReturnInfo -> ModeSpec -> BSpec -> Procedure
  def makeProcedure params varsInScope returnInfo modeSpec bSpec = {
    parameters = params,
    varsInScope = varsInScope,
    returnInfo = returnInfo,
    modeSpec = modeSpec,
    bSpec = bSpec
  }

  op ProcEnv.makeProcedure : List Op.Ref -> List Op.Ref -> ReturnInfo -> ModeSpec -> BSpec -> Env Procedure
  def ProcEnv.makeProcedure params varsInScope returnInfo modeSpec bSpec =
    return (makeProcedure params varsInScope returnInfo modeSpec bSpec)

  op parameters : Procedure -> List Op.Ref
  def parameters procedure = procedure.parameters

  op varsInScope : Procedure -> List Op.Ref
  def varsInScope procedure = procedure.varsInScope

  op bSpec : Procedure -> BSpec
  def bSpec procedure = procedure.bSpec

  op withBSpec infixl 17 : Procedure * BSpec -> Procedure
  def withBSpec (procedure,newBSpec) = {
    parameters = procedure.parameters,
    varsInScope = procedure.varsInScope,
    returnInfo = procedure.returnInfo,
    modeSpec = procedure.modeSpec,
    bSpec = newBSpec
  }

  op returnInfo : Procedure -> ReturnInfo
  def returnInfo procedure = procedure.returnInfo

  op modeSpec : Procedure -> ModeSpec
  def modeSpec procedure = procedure.modeSpec

  op withModeSpec infixl 17 : Procedure * ModeSpec -> Procedure
  def withModeSpec (procedure,newModeSpec) = {
    parameters = procedure.parameters,
    varsInScope = procedure.varsInScope,
    returnInfo = procedure.returnInfo,
    modeSpec = newModeSpec,
    bSpec = procedure.bSpec
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

begin{spec}
  op pp : Procedure -> Doc
  def pp procedure =
    ppConcat [
      pp "params=(",
      ppSep (pp ",") (map pp (parameters procedure)),
      pp "), returnInfo=",
      pp (returnInfo procedure),
      pp ", bSpec=",
      ppNewline,
      pp "  ",
      ppIndent (pp (bSpec procedure))
    ]

  op ppLess : Procedure -> ModeSpec -> Doc
  def ppLess procedure ms =
    let
      procShort =
        makeProcedure (parameters procedure)
                      (varsInScope procedure)
                      (returnInfo procedure)
                      (subtract (modeSpec procedure) ms)
                      (map (bSpec procedure) (fn ms -> ModeSpec.subtract ms (modeSpec procedure)) (fn x -> x))
    in
      pp procShort

\begin{spec}
  op ReturnInfo.pp : ReturnInfo -> Doc
  def ReturnInfo.pp info =
    case info of
      | None -> String.pp "None"
      | Some ref -> Id.pp ref
\end{spec}

   op show : Procedure -> String 
   def show procedure = ppFormat (pp procedure)

\begin{spec}
  op ProcEnv.pp : Id.Id -> Procedure -> Env Doc
  def ProcEnv.pp procId procedure = {
    doc <- pp procedure.bSpec (modeSpec procedure);
    return 
     (ppConcat [
        String.pp "proc ",
        Id.pp procId,
        String.pp " params=(",
        ppSep (String.pp ",") (map Id.pp (parameters procedure)),
        String.pp "), returnInfo=",
        pp (returnInfo procedure),
        String.pp ", bSpec=",
        doc
     ])
    }
endspec
\end{spec}
