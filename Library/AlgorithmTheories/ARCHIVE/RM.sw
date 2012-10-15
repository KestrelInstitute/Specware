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

  Assumption 2: Homogeneous Variables
                Output type is a map from Variables to partially-ordered Values
                    State = Map(Variable, Value)
  Issues:
   - this should be a refinement of fixpoint iteration theory

*)

RMTheory = spec
  import translate ProblemTheory#DROfPartial by {R +-> State}, 
         ../DataTypes/Maps

  type Variable
  import translate ../Math/Semilattice by
      {A      +-> Value,
       <=     +-> RefinesTo,
       binop  +-> Join}
  type VarMap =  Map(Variable,Value)

  type ConstraintRep   % = {LHS: , RHS:}
  op getLHSVars: ConstraintRep -> Set Variable
  op getRHSVar:  ConstraintRep -> Option Variable
  op evalLHS: ConstraintRep * VarMap -> Value
  op evalRHS: ConstraintRep * VarMap -> Value

  op Constraints : D -> List ConstraintRep
  op evalConstraint(cr:ConstraintRep, vm:VarMap):Boolean =
     RefinesTo(evalLHS(cr,vm),evalRHS(cr,vm))

  op violatedConstraints(crs:List ConstraintRep, 
		         vm:Map(Variable,Value)): List ConstraintRep =
     case crs of
      | Nil    -> Nil
      | cr::tl -> if evalConstraint(cr,vm)
      	            then violatedConstraints(tl,vm)
		    else Cons(cr, violatedConstraints(tl,vm))

  type State = ({vars        : Set Variable,
                 varMap      : VarMap,
                 constraints : List ConstraintRep,
                 workset     : List ConstraintRep,
                 dependencies: Map(Variable, List ConstraintRep)}
                | fn(vars,varMap,constraints,workset,dependencies)->
                  vars = domain(varMap)
                  && workset = violatedConstraints(constraints,varMap)
                  && dependencies = mkDependencies(vars,constraints)
                  )
  op InitialState : D -> State

% design this so that it is O(n) vs O(n^2)
  op mkDependencies(vars: Set Variable, crs:List ConstraintRep): Map(Variable, List ConstraintRep) =
    mapFrom(vars, fn(v)-> (filter (fn(cr)-> v in? getLHSVars(cr)) (crs)))

  axiom initial_value_of_constraints is
    fa(x:D,s:State)(s = InitialState(x) => s.constraints = Constraints(x))

%   axiom xi_is_increasing_initially is
%     fa(x:D,s:State)(s = InitialState(x) => RefinesTo(s, xi(s)))  

 end-spec


(*****************   RM Scheme without pruning   ************************)

RM = spec 
  import RMTheory

  op RefineBy(s:State, cr:ConstraintRep): Option State =
     let lval: Value = evalLHS(cr,s.varMap) in
     let rval: Value = evalRHS(cr,s.varMap) in
     if RefinesTo(lval, rval) then Some s
     else (case getRHSVar(cr) of
           | None -> None 
	   | Some v -> let newval:Value = Join(lval, rval) in
	               let newVM:VarMap = (update s.varMap v newval) in
                       Some {vars = s.vars,
                             varMap = newVM,
                             constraints = s.constraints,
                             % only add in the violated constraints	
                             workset = concat(tl(s.workset), 
                                              violatedConstraints(TMApply(s.dependencies,v),newVM)),
                             dependencies = s.dependencies
                             })

  (* This is the top level of the RM iteration algorithm.  *)

  def f(x:D): Option State = 
    let init:State = InitialState(x) in
    RM(x,init)

  (* RM iterates xi to a fixpoint.  *)

  def RM(x:D, vm:State | true ) : Option State = 
    if vm.workset = [] then Some vm
    else case RefineBy(vm, hd(vm.workset)) of
         | None       -> None
         | Some newst -> RM(x, newst)

  theorem correcness_of_RM is
   fa(x:D) (case f(x) of 
              | Some z -> O(x,z) 
              | None -> ~(ex(z)O(x,z)))

end-spec

(*****************   RM Scheme with pruning   ************************)

