\section{Transition Specs}

This is experimental as, for better or worse, the labelling of transitions is forced
by the theory to consist of a pair of morphisms and a mode spec. Thus, it is not clear
whether defining an abstract sort for transition specification is a win.

I suppose there is a win if we say that a transition spec is isomorphic
to a triple but is implemented in some other way. For instance, it might
be augmented with other information which, while redundant with respect
to the product, might improve efficiency. 

\begin{spec}
TransSpec qualifying spec
  import ModeSpec
  import SimpleMorph
  import Subst
  import Constraints

  sort TransSpec = SpecMorph.Morphism * ModeSpec.ModeSpec * SpecMorph.Morphism

  op forwMorph : TransSpec -> SpecMorph.Morphism
  op backMorph : TransSpec -> SpecMorph.Morphism
  op modeSpec : TransSpec -> ModeSpec.ModeSpec
  op addVariable : TransSpec -> Op.OpInfo -> Position -> Env TransSpec

  op make : ModeSpec -> OpRefSet.Set -> TransSpec

  op elaborate : TransSpec -> Env TransSpec

  op applySubst : TransSpec * Subst -> Env TransSpec
  op applyConstraints : TransSpec * Constraints -> Env TransSpec
  op simplifyVariants : ModeSpec -> TransSpec -> Env TransSpec
  op projectPostSubst : TransSpec -> Env Subst

  op hideVariables : TransSpec -> Subst -> Subst -> Env TransSpec
  op provablyInconsistent? : TransSpec -> Boolean

  op withClaim infixl 18 : TransSpec * Claim -> TransSpec

  op makePrimedId : Id.Id -> Id.Id
  op removePrime : Id.Id -> Id.Id
endspec
\end{spec}
