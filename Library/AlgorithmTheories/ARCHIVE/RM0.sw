(*  
   Rehof-Mogenson Fixpoint Iteration Algorithm Theory 

  Assumption1:  O has the form of a conjunction of definite constraints
               in quantified form:
                    fa(x)(P(x,s) => x<=s)
	       or
                    fa(i,x)(P(i,x,s) => x<=s(i))
               where P is monotone in s
	       or
                    fa(i)(f(i,s)<=s(i))
               where f is monotone in s

  Assumption 2: Output type is a map from Variables to partially-ordered Values
                    State = Map(Variable, Value)
*)

RMTheory = spec
  import ProblemTheory#DROfPartial

  type Variable
  import translate ../Math/PartialOrder by
      {A      +-> Value,
       <=     +-> RefinesTo}   % binop  +-> Join  for semilattice

  type State = Map(Variable,Value)
  op InitialState : D -> State

  type ConstraintRep
  op Constraints : D -> List ConstraintRep
  op EvalConstraint: ConstraintRep * State -> Boolean
  op EvalVariable(v:Variable, vm:State | v in domain(vm)):Value =
      TMApply(vm,v)

  op violatedConstraints(crs:List ConstraintRep, vm:State): List ConstraintRep =
     case crs of
      | Nil -> Nil
      | cr::tl -> if EvalConstraint(cr,vm)
      	            then Cons(cr, violatedConstraints(tl,vm))
		    else violatedConstraints (tl,vm)

   axiom xi_is_increasing_initially is
     fa(x:D,s:State)(s = InitialState(x) => RefinesTo(s, xi(s)))  

  (* Phi is a pruning test.  It is defined as ... *)

   op Phi : State -> Boolean
%   axiom characterization_of_necessary_pruning_test_phi is
%     fa(x:D,z:R,s:State)(Satisfies(z,s) & O(x,z) => Phi(s))

 end-spec


(*****************   RM Scheme without pruning   ************************)

RM = spec 
  import RMTheory

  (* This is the top level of the RM iteration algorithm.  *)

  def f(x:D): Option R = 
    let init:State = InitialState(x) in
    RM(x,violatedConstraints(Constraints(x),init),init)

  (* RM iterates xi to a fixpoint.  *)

  def RM(x:D, workset:List ConstraintRep, vm:State | true ) : R = 
    if empty workset then vm
    else let new:State = RefineBy(vm, first(workset)) in
         RM(x, 
	    ListAppend(tail(workset),TMApply(dependsOn, rhs(cr))), 
	    new)

  theorem correcness_of_RM is
   fa(x:D) (case f(x) of 
              | Some z -> O(x,z) 
              | None -> ~(ex(z)O(x,z)))

(*****************   RM Scheme with pruning   ************************)

RM = spec 
  import RMTheory

  (* This is the top level of the RM iteration algorithm.  *)

  def f(x:D): Option R = 
    if Phi(InitialState(x))
    then RM(x,InitialState(x))
    else None

  (* RM iterates xi to a fixpoint.  *)

  def RM(x:D, s:State | Phi(s) ) : Option R = 
    let newr:State = xi(r) in
    if newr = r
    then Some r
    else if Phi(newr)
         then RM(x, newr)
	 else None

  theorem correcness_of_RM is
   fa(x:D) (case f(x) of 
              | Some z -> O(x,z) 
              | None -> ~(ex(z)O(x,z)))

end-spec
