\section{Spec of labelling the BSpec states (modes) and transitions.}

This is still under development.

The issue is as follows. As in ASMs we had previously distinguished
static and dynamic specs. Static specs contain names whose meaning is
fixed in all worlds.  Dynamic spec reflects things that can change.
The ops in the dynamic spec are variables. The static spec
is imported into the dynamic spec. Thus static operators cannot
refer to dynamic variables.

This is problematic as one might start, for example, with sets
in the static spec (a functional data structure), and then refine it
to something that, while still functional, is implemented, for example,
with linked lists.  The latter is defined only in the dynamic spec.

Also, one might want to define auxilliary functions that have a fixed
meaning but defined in terms of the dynamic variables. Thus the
functions cannot appear on the left side, but nevertheless, they are
dynamic.

The alternative is to make a different distinction. There is only one spec
plus additional information that describes whether something is assignable
or not (whether or not it can appear on the left side of an assignment).

The spec below experiments with the latter idea. We define a category of
BSpecs labelled with conventional specs and information describing what
operators in each spec constitute the variables that make up the store.

\begin{spec}
spec {
  import translate Spec by {
      Monad.Monad +-> SpecCalc.Env
    }

  sort Morphism

  sort ModeSpec = {
      spc : Spec,
      variables : Id.Set
    }

  sort BSpec.Object = ModeSpec

  op specOf : ModeSpec -> Spec
  def specOf modeSpec = modeSpec.spc

  op variables : ModeSpec -> Id.Set
  def variables modeSpec = modeSpec.variables

  op make : Spec -> Id.Set -> ModeSpec
  def make spc variables = {
      spc = spc,
      variables = variables
    }

  op withVariables infixl 18 : ModeSpec * Id.Set -> ModeSpec
  def withVariables (modeSpec,variables) = {
      spc = specOf modeSpec,
      variables = variables
    }

  op withSpec infixl 18 : ModeSpec * Spec -> ModeSpec
  def withSpec (modeSpec,spc) = {
      spc = spc,
      variables = variables modeSpec
    }

  sort BSpec.Arrow = Morphism

  op addConstant : ModeSpec -> OpInfo -> SpecCalc.Env ModeSpec
  def addConstant modeSpec opInfo = {
      newSpec <- insert (specOf modeSpec) opInfo;
      return (modeSpec withSpec newSpec)
    }

  op addVariable : ModeSpec -> OpInfo -> SpecCalc.Env ModeSpec
  def addVariable modeSpec opInfo = {
      newSpec <- insert (specOf modeSpec) opInfo;
      return (make newSpec (Id.insert (variables modeSpec) (name opInfo)))
    }

  op addProperty : ModeSpec -> Property -> SpecCalc.Env ModeSpec
  def addProperty modeSpec property =
    return (modeSpec withSpec (insert (specOf modeSpec) property))

  op elaborate : ModeSpec -> SpecCalc.Env ModeSpec
  def elaborate modeSpec = {
      elabSpec <- Spec.elaborate (specOf modeSpec);
      return (modeSpec withSpec elabSpec)
    }
}
\end{spec}
