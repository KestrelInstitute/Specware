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
ModeSpec qualifying spec
  import Spec
  import Subst

  sort ModeSpec 

  op specOf : ModeSpec -> Spec.Spec
  op variables : ModeSpec -> OpRefSet.Set
  op invariants : ModeSpec -> ClaimRefSet.Set

  op empty : ModeSpec

  op make : Spec.Spec -> OpRefSet.Set -> ClaimRefSet.Set -> ModeSpec

  op addSort : ModeSpec -> Sort.SortInfo -> Position -> Env ModeSpec

  op addOp : ModeSpec -> Op.OpInfo -> Position -> Env ModeSpec
  op addVariable : ModeSpec -> Op.OpInfo -> Position -> Env ModeSpec

  op hideOp : ModeSpec -> Op.OpInfo -> Env ModeSpec
  op hideVariable : ModeSpec -> Op.OpInfo -> Env ModeSpec
  op hideVariables : ModeSpec -> Subst -> Env ModeSpec
  op addClaim : ModeSpec -> Claim.Claim -> Position -> Env ModeSpec
  op addInvariant : ModeSpec -> Claim.Claim -> Position -> Env ModeSpec

  op findTheOp : ModeSpec -> Id.Id -> Env Op.OpInfo
  op findTheVariable : ModeSpec -> Id.Id -> Env Op.OpInfo

  op ModeSpecEnv.foldOps : fa(a) (a -> Op.OpInfo -> Env a) -> a -> ModeSpec -> Env a
  op ModeSpec.foldVariables : fa(a) (a -> Op.OpInfo -> a) -> a -> ModeSpec -> a
  op ModeSpecEnv.foldVariables : fa(a) (a -> Op.OpInfo -> Env a) -> a -> ModeSpec -> Env a

  op ModeSpecEnv.foldVariants : fa(a) (a -> Claim -> Env a) -> a -> ModeSpec -> Env a

  % op ModeSpecEnv.mapOps : ModeSpec -> (Op.OpInfo -> Env Op.OpInfo) -> Env ModeSpec
  % op ModeSpecEnv.mapVariables : ModeSpec -> (Op.OpInfo -> Env Op.OpInfo) -> Env ModeSpec

  % op ModeSpecEnv.mapClaim : ModeSpec -> (Claim.Claim -> Env Claim.Claim) -> Env ModeSpec
  % op ModeSpecEnv.mapInvariant : ModeSpec -> (Claim.Claim -> Env Claim.Claim) -> Env ModeSpec

  op elaborate : ModeSpec -> Env ModeSpec

  op subtract : ModeSpec -> ModeSpec -> ModeSpec
  op union : ModeSpec -> ModeSpec -> Env ModeSpec
    
  op applySubst : ModeSpec * Subst -> Env ModeSpec

  op simplifyVariable : ModeSpec * Op.Ref -> Env ModeSpec
  op simplifyInvariant : ModeSpec * Claim.Ref -> Env ModeSpec
  op simplifyInvariants : ModeSpec -> Env ModeSpec

  op pp : ModeSpec -> Doc
  op show : ModeSpec -> String
endspec
\end{spec}

Does it make sense to do a map over the variables or ops? What is the
constraint on the opInfo function that ensures that the final spec is
well formed.

I suppose you toss one op out but put another op in. But what happens
to references to terms that refer to ops that get tossed.

Perhaps require that the map operation doesn't change the name.

Same issue applies to map over set.

Need some rationale for deciding when the parameter should be an
op or an opInfo? For example hyde is wrong.
