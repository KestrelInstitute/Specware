(* Copyright 2015 Kestrel Institute. See file LICENSE for license details *)

% Some useful definitions and theorems for approximation orderings,
% from domain theory. Intuitively, these are preorders that capture
% when one value / computation is an approximation of, i.e., a
% possibly less-defined version of, another

DomainTheory = DomainTheory qualifying spec
  import /Library/General/Order

  % lift a preorder to an Option type
  op [a] approx_option (r_a: PreOrder a) : PreOrder (Option a) =
    fn (x,y) -> fa (a) x = Some a => (ex (a') r_a (a,a') && y = Some a')

  % lift a preorder on the codomain type to a preorder on a function type
  op [a,b] approx_fun (r_b : PreOrder b) : PreOrder (a -> b) =
    fn (f1,f2) -> fa (a) r_b (f1 a, f2 a)

  % the equivalence relation derived from an ordering
  op [a] approx_equiv (r_a: PreOrder a) : Equivalence a =
    fn (a1, a2) -> r_a (a1, a2) && r_a (a2, a1)

  % specify that f is monotonic w.r.t. input order r_a and output order r_b
  op [a,b] monotonic? (r_a : PreOrder a, r_b : PreOrder b) (f : a -> b) : Bool =
    fa (a1, a2) r_a (a1, a2) => r_b (f a1, f a2)


  % FIXME: proofs
end-spec


