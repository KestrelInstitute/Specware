\section{Spec of labelling the BSpec states (modes) and transitions.}

This is still under development.

As in ASMs we had previously distinguished static and dynamic
specs. Static specs contain names whose meaning is fixed in all worlds.
Dynamic spec reflects things that can change.  The ops in the dynamic spec
are variables. The static spec is imported into the dynamic spec. Thus
static operators cannot refer to dynamic variables.

This is problematic as one might start, for example, with sets in
the static spec (a functional data structure), and then refine it to
something that, while still functional, is implemented, for example,
with linked lists.  The latter is defined only in the dynamic spec.

If the above separation is adhered to, then such a refinement is not
possible as ops in the static spec cannot be defined in terms of names
in the dynamic spec.

Also, one might want to define auxilliary functions that have a fixed
meaning but defined in terms of the dynamic variables. An invariant on
a heap might be one example. Such a function would by dynamic as it is
defined in terms of variables and yet it makes no sense to call it a
variable and it makes no sense that such a function appear on the left
side of an assignment.

The alternative is to make a different distinction. There is only one spec
plus additional information that describes whether something is assignable
or not (whether or not it can appear on the left side of an assignment).

The spec below experiments with the latter idea. We define a category of
BSpecs labelled with conventional specs and information describing what
operators in each spec constitute the variables that make up the store.

\begin{spec}
ModeSpec qualifying spec {
  import Spec
  import Morphism

  sort ModeSpec = {
      spc : Spec,
      variables : OpRefSet.Set
    }

  op specOf : ModeSpec -> Spec
  def specOf modeSpec = modeSpec.spc

  op variables : ModeSpec -> OpRefSet.Set
  def variables modeSpec = modeSpec.variables

  op empty : ModeSpec
  def empty = make Spec.empty OpRefSet.empty

  op make : Spec -> OpRefSet.Set -> ModeSpec
  def make spc variables = {
      spc = spc,
      variables = variables
    }

  % This is not used
  op withVariables infixl 18 : ModeSpec * OpRefSet.Set -> ModeSpec
  def withVariables (modeSpec,variables) = {
      spc = specOf modeSpec,
      variables = variables
    }

  op withSpec infixl 18 : ModeSpec * Spec -> ModeSpec
  def withSpec (modeSpec,spc) = {
      spc = spc,
      variables = variables modeSpec
    }

  op addConstant : ModeSpec -> OpInfo -> Position -> Env ModeSpec
  def addConstant modeSpec opInfo position = {
      newSpec <- addOp (specOf modeSpec) opInfo position;
      return (modeSpec withSpec newSpec)
    }

  op addVariable : ModeSpec -> OpInfo -> Position -> Env ModeSpec
  def addVariable modeSpec opInfo position = {
      newSpec <- addOp (specOf modeSpec) opInfo position;
      ref <- refOf (specOf modeSpec) opInfo;
      return (make newSpec (OpRefSet.insert (variables modeSpec) ref))
    }

  op findTheOp : ModeSpec -> Id.Id -> Env OpInfo
  def findTheOp modeSpec id = findTheOp (specOf modeSpec) id

  op findTheVariable : ModeSpec -> Id.Id -> Env OpInfo
  def findTheVariable modeSpec id = {
      opInfo <- findTheOp (specOf modeSpec) id;
      ref <- refOf (specOf modeSpec) opInfo;
      if (member? (variables modeSpec) ref) then
        return opInfo
      else
        specError ("Id is an op but not a variable: " ^ (show id))
    }

  op ModeSpecEnv.foldOps : fa(a) (a -> OpInfo -> Env a) -> a -> ModeSpec -> Env a
  def ModeSpecEnv.foldOps f unit modeSpec = SpecEnv.foldOps f unit (specOf modeSpec)

  op ModeSpec.foldVariables : fa(a) (a -> OpInfo -> a) -> a -> ModeSpec -> a
  def ModeSpec.foldVariables f unit modeSpec = Spec.foldOps
    (fn x -> fn opInfo ->
        if member? (variables modeSpec) (refOf (specOf modeSpec) opInfo) then
          f x opInfo
        else
          x) unit (specOf modeSpec)
 
  op ModeSpecEnv.foldVariables : fa(a) (a -> OpInfo -> Env a) -> a -> ModeSpec -> Env a
  def ModeSpecEnv.foldVariables f unit modeSpec = SpecEnv.foldOps
    (fn x -> fn opInfo -> {
        ref <- refOf (specOf modeSpec) opInfo;
        if member? (variables modeSpec) ref then
          f x opInfo
        else
          return x
      }) unit (specOf modeSpec)
 

  op addProperty : ModeSpec -> Property -> Position -> Env ModeSpec
  def addProperty modeSpec property position = {
      newSpec <- addProperty (specOf modeSpec) property position;
      return (modeSpec withSpec newSpec)
    }

  op elaborate : ModeSpec -> Env ModeSpec
  def elaborate modeSpec = {
      elabSpec <- Spec.elaborate (specOf modeSpec);
      return (modeSpec withSpec elabSpec)
    }

  op pp : ModeSpec -> Doc
  def pp modeSpec =
    ppConcat [
      pp "spec=",
      pp (specOf modeSpec),
      ppNewline,
      pp "variables=",
      pp (variables modeSpec)
    ]
}
\end{spec}
