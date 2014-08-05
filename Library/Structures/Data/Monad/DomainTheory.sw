% Some useful definitions and theorems for approximation orderings,
% from domain theory. Intuitively, these are preorders that capture
% when one value / computation is an approximation of, i.e., a
% possibly less-defined version of, another

DomainTheory = DomainTheory qualifying spec
  import /Library/General/Order

  op [a] approx_option : EndoRelation (Option a) =
    fn (x,y) -> fa (a) x = Some a => y = Some a

  op [a,b] approx_fun (r_b : EndoRelation b) : EndoRelation (a -> b) =
    fn (f1,f2) -> fa (a) r_b (f1 a, f2 a)

  op [a,b] monotonic? (r_a : EndoRelation a, r_b : EndoRelation b) (f : a -> b) : Bool =
    fa (a1, a2) r_a (a1, a2) => r_b (f a1, f a2)

  theorem approx_option_preorder is [a]
    preOrder? (approx_option : EndoRelation (Option a))

  theorem approx_fun_preorder is [a,b]
    fa (appr) preOrder? appr =>
      preOrder? (approx_fun appr : EndoRelation (a -> b))

  % FIXME: proofs
end-spec


