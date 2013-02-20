(*  
          Tarksi Fixpoint Iteration Algorithm Theory 

  Assumption:  We are given a monotone function xi over 
	       the partial order <State,RefinesTo>
*)

TKTheory = spec
  import ProblemTheory#DROfPartial
  type State
  op InitialState : D -> State

  import translate ../Math/PartialOrder by
      {A    +-> State,
       <=   +-> RefinesTo}   % binop  +-> Join  for semilattice

  (* F is the monotone function that we iterate. *)

   op F : State -> Boolean
   axiom F_is_monotone is
     fa(x:D,s1:State,s2:State)(RefinesTo(s1,s2) => RefinesTo(F(s1),F(s2)))  

   axiom F_is_increasing_initially is
     fa(x:D,s:State)(s = InitialState(x) => RefinesTo(s, F(s)))  

 end-spec


(*****************   TK Scheme without pruning   ************************)

TK = spec 
  import TKTheory

  (* This is the top level of the TK iteration algorithm.  *)

  def f(x:D): Option R = 
    TK(x,InitialState(x))

  (* TK iterates F to a fixpoint.  *)

  def TK(x:D, s:State ) : Option R = 
    let newr:State = F(r) in
    if newr = r
    then Some r
    else TK(x, newr)

  theorem correcness_of_TK is
   fa(x:D) (case f(x) of 
              | Some z -> O(x,z) 
              | None -> ~(ex(z)O(x,z)))

end-spec

(*****************   TK Scheme with pruning   ************************)

TKwp = spec 
  import TKTheory

  (* Phi is a pruning test.  It is defined as ... *)

   op Phi : State -> Boolean
%   axiom characterization_of_necessary_pruning_test_phi is
%     fa(x:D,z:R,s:State)(Satisfies(z,s) && O(x,z) => Phi(s))

  (* This is the top level of the TK iteration algorithm.  *)

  def f(x:D): Option R = 
    if Phi(InitialState(x))
    then TK(x,InitialState(x))
    else None

  (* TK iterates F to a fixpoint.  *)

  def TK(x:D, s:State | Phi(s) ) : Option R = 
    let newr:State = F(r) in
    if newr = r
    then Some r
    else if Phi(newr)
         then TK(x, newr)
	 else None

  theorem correctness_of_TK is
   fa(x:D) (case f(x) of 
              | Some z -> O(x,z) 
              | None -> ~(ex(z)O(x,z)))

end-spec
