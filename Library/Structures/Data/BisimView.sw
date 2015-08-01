BisimView qualifying spec
  import ISet
  import Lens

  (* We say relation R is a good-only bisimulation between preorders leq1 and
  leq2 iff the following forall-exists diagrams hold (where "solid" lines are
  universals and dotted lines are existentials):

    *------leq1----->*          * . . .leq1. . .>*
    |                .\         |                .
    |                . R        |                .   *
    R                R  \       R                R  /
    |                .   *      |                . R 
    |                .          |                ./
    * . . .leq2 . . >*          *------leq2----->*

  Intuitively, this means that R is a bisimulation between the restrictions of
  leq1 and leq2 to the "good" transitions, that is, the transitions that
  preserve R-ness to something. The R relation is used to "view" type a at type
  b, while the leq1 and leq2 relations are used to describe the updates to
  element of these types that the view "allows". The diagrams above mean that,
  although the updates allowed by a view might mess the view itself up, by going
  to a state that is not "good", when an update via leq1 does go to a good
  state, then it is equivalent to a leq2 update, and vice-versa. *)
  op [a,b] good_only_bisim_at_point? (leq1:PreOrder a, leq2:PreOrder b,
                                      R:Relation (a,b)) (a:a,b:b) : Bool =
    (fa (a')
       R (a,b) && leq1 (a,a') && (ex (b') R (a',b')) =>
       (ex (b') R (a',b') && leq2 (b,b'))) &&
    (fa (b')
       R (a,b) && leq2 (b,b') && (ex (a') R (a',b')) =>
       (ex (a') R (a',b') && leq1 (a,a')))
  op [a,b] good_only_bisim? (leq1:PreOrder a, leq2:PreOrder b,
                             R:Relation (a,b)) : Bool =
    fa (a,b) good_only_bisim_at_point? (leq1,leq2,R) (a,b)

  (* In the below, we use the shortened term "bisimilarity view" or just
  "biview" for tuples (R,leq1,leq2) where R is a good-only bisimulation between
  preorders leq1 and leq2 *)
  type RawBisimView (a,b) = {biview: Relation (a,b),
                             bv_leq1: PreOrder a,
                             bv_leq2: PreOrder b}
  type BisimView (a,b) = {bv: RawBisimView (a,b) |
                            good_only_bisim? (bv.bv_leq1, bv.bv_leq2, bv.biview)}


  (***
   *** The Category of Bisimilarity Views
   ***)

  (* The identitiy bi-view; (almost) nothing is separate from it *)
  op [a] identity_biview : BisimView (a,a) =
    {biview = (=),
     bv_leq1 = fn _ -> true,
     bv_leq2 = fn _ -> true}

  (* Compose two bi-views. Elements of the domain type (a) are considered bv_leq
  iff they are bv_leq by sbv1 and sbv1 maps them to sets of elements of the
  intermediate type (b) that are considered bv_leq by sbv2; similarly with
  elements of the co-domain type (c). *)
  op [a,b,c] compose_biviews (sbv1: BisimView (a,b),
                              sbv2: BisimView (b,c)) : BisimView (a,c) =
    {biview = relCompose (sbv1.biview, sbv2.biview),
     bv_leq1 = fn (a1,a2) ->
       sbv1.bv_leq1 (a1,a2) &&
       (fa (b1) sbv1.biview (a1,b1) =>
          (ex (b2) sbv1.biview (a2,b2) && sbv2.bv_leq1 (b1,b2))) &&
       (fa (b2) sbv1.biview (a2,b2) =>
          (ex (b1) sbv1.biview (a1,b1) && sbv2.bv_leq1 (b1,b2))),
     bv_leq2 = fn (c1,c2) ->
       sbv2.bv_leq2 (c1,c2) &&
       (fa (b1) sbv2.biview (b1,c1) =>
          (ex (b2) sbv2.biview (b2,c2) && sbv1.bv_leq2 (b1,b2))) &&
       (fa (b2) sbv2.biview (b2,c2) =>
          (ex (b1) sbv2.biview (b1,c1) && sbv1.bv_leq2 (b1,b2)))}

  theorem compose_identity_biview_l is [a,b]
    fa (sbv:BisimView(a,b))
      compose_biviews (identity_biview, sbv) = sbv
  theorem compose_identity_biview_r is [a,b]
    fa (sbv:BisimView(a,b))
      compose_biviews (sbv, identity_biview) = sbv
  theorem compose_biviews_assoc is [a,b,c,d]
    fa (sbv1:BisimView(a,b),sbv2:BisimView(b,c),sbv3:BisimView(c,d))
      compose_biviews (compose_biviews (sbv1, sbv2), sbv3) =
      compose_biviews (sbv1, compose_biviews (sbv2, sbv3))


  (***
   *** Inverting Bisimilarity Views
   ***)

  (* Invert a bi-view, turning it around *)
  op [a,b] invert_biview (sbv: BisimView (a,b)) : BisimView (b,a) =
    {biview = fn (b,a) -> sbv.biview (a,b),
     bv_leq1 = sbv.bv_leq2,
     bv_leq2 = sbv.bv_leq1}

  (* FIXME: theorems stating that invert_biview is an involution *)


  (***
   *** Conjunction of Bisimilarity Views
   ***)

  (* States that any leq1 update on a and any leq2 update on b preserves R *)
  op [a,b] preorders_preserve_R_at_point? (leq1:PreOrder a, leq2:PreOrder b,
                                           R:Relation (a,b)) (a:a,b:b) : Bool =
    (fa (a',b')
       leq1 (a,a') && leq2 (b,b') && R (a,b) => R (a',b'))

  (* States that all leq1 and leq2 updates preserve R *)
  op [a,b] preorders_preserve_R? (leq1:PreOrder a, leq2:PreOrder b,
                                  R:Relation (a,b)) : Bool =
    (fa (a,b) preorders_preserve_R_at_point? (leq1,leq2,R) (a,b))

  (* States that any number of leq1 and leq2 steps starting at x can be
  decomposed into leq1 steps followed by leq2 steps or vice-versa *)
  op [a] preorders_decompose_at_point? (leq1: PreOrder a, leq2: PreOrder a)
                                       (x: a) : Bool =
    (fa (y)
       rt_closure (relCompose (leq1,leq2)) (x,y) =>
       relCompose (leq1,leq2) (x,y) && relCompose (leq2,leq1) (x,y))

  (* Conjoin two bisimilarity views, intuitively building the bisimilarity view
  that allows updates using sbv1 and/or sbv2. *)
  (* FIXME: explain the biview relation better... *)
  op [a,b] conjoin_biviews2 (sbv1: BisimView (a,b),
                             sbv2: BisimView (a,b)) : BisimView (a,b) =
    {biview = fn (a,b) ->
       sbv1.biview (a,b) && sbv2.biview (a,b) &&
       preorders_preserve_R_at_point? (sbv1.bv_leq1,sbv1.bv_leq2,
                                       sbv2.biview) (a,b) &&
       preorders_preserve_R_at_point? (sbv2.bv_leq1,sbv2.bv_leq2,
                                       sbv1.biview) (a,b) &&
       preorders_decompose_at_point? (sbv1.bv_leq1,sbv2.bv_leq1) a &&
       preorders_decompose_at_point? (sbv1.bv_leq2,sbv2.bv_leq2) b,
     bv_leq1 = rt_closure (relCompose (sbv1.bv_leq1, sbv2.bv_leq1)),
     bv_leq2 = rt_closure (relCompose (sbv1.bv_leq2, sbv2.bv_leq2))}

  (* The trivial biview, that relates everything and provides no permissions *)
  op [a,b] trivial_biview : BisimView (a,b) =
    {biview = fn _ -> true, bv_leq1 = (=), bv_leq2 = (=)}

  (* Conjoin a list of bi-views *)
  op [a,b] conjoin_biviews (sbvs: List (BisimView (a,b))) : BisimView (a,b) =
    foldr conjoin_biviews2 trivial_biview sbvs

  (* Conjunction with the constant view forms a commutative monoid *)
  theorem conjoin_biviews_assoc is [a,b]
    fa (sbv1,sbv2,sbv3:BisimView(a,b))
      conjoin_biviews2 (sbv1, conjoin_biviews2 (sbv2, sbv3)) =
      conjoin_biviews2 (conjoin_biviews2 (sbv1, sbv2), sbv3)
  theorem conjoin_biviews_comm is [a,b]
    fa (sbv1,sbv2:BisimView(a,b))
      conjoin_biviews2 (sbv1, sbv2) =
      conjoin_biviews2 (sbv2, sbv1)
  theorem conjoin_biviews_constant is [a,b]
    fa (sbv:BisimView (a,b))
      conjoin_biviews2 (sbv,trivial_biview) = sbv


  (***
   *** Separation of Bisimilarity Views
   ***)

  (* Two bisimilarity views are separate iff each biview is preserved by the
  other's preorder and the respective preorders commute. Intutively, this means
  that the updates allowed by one biview do not interfere with the other. *)
  op [a,b] separate_biviews? (sbv1: BisimView (a,b), sbv2: BisimView (a,b)) : Bool =
    preorders_preserve_R? (sbv1.bv_leq1, sbv1.bv_leq2, sbv2.biview) &&
    preorders_preserve_R? (sbv2.bv_leq1, sbv2.bv_leq2, sbv1.biview) &&
    relations_commute? (sbv1.bv_leq1, sbv2.bv_leq1) &&
    relations_commute? (sbv1.bv_leq2, sbv2.bv_leq2)

  (* Separation is commutative *)
  theorem separation_commutative is [a,b]
    fa (sbv1,sbv2: BisimView (a,b))
      separate_biviews? (sbv1,sbv2) => separate_biviews? (sbv2,sbv1)

  (* Good-only bisimulation is closed under composition with preorders that
  preserve R and that commute with the original preorders *)
  theorem good_only_bisim_compose is [a,b]
    fa (leq1,leq1',leq2,leq2',R:Relation (a,b))
      good_only_bisim? (leq1,leq2,R) &&
      preorders_preserve_R? (leq1',leq2',R) &&
      relations_commute? (leq1,leq1') &&
      relations_commute? (leq2,leq2') =>
      good_only_bisim? (rt_closure (relCompose (leq1,leq1')),
                        rt_closure (relCompose (leq2,leq2')),
                        R)

  (* Conjoining separate biviews yields the intersection for biview and the
  composition for the two equalities *)
  theorem conjoin_separate_biviews is [a,b]
    fa (sbv1,sbv2: BisimView (a,b))
      separate_biviews? (sbv1,sbv2) =>
      conjoin_biviews2 (sbv1,sbv2) =
      {biview = iSetInter (sbv1.biview, sbv2.biview),
       bv_leq1 = relCompose (sbv1.bv_leq1, sbv2.bv_leq1),
       bv_leq2 = relCompose (sbv1.bv_leq2, sbv2.bv_leq2)}

  (* Separation from two bi-views implies separation from their conjunction *)
  theorem biview_separate_from_conjunction is [a,b]
    fa (sbv1,sbv2,sbv: BisimView (a,b))
      separate_biviews? (sbv1, sbv) && separate_biviews? (sbv2, sbv) =>
      separate_biviews? (conjoin_biviews2 (sbv1, sbv2), sbv)

  (* Separation from the conjunction of separate biviews implies separation from
  the individual biviews themselves *)
  theorem biview_separation_un_conjoin is [a,b]
    fa (sbv1,sbv2,sbv:BisimView (a,b))
      separate_biviews? (sbv1, sbv2) &&
      separate_biviews? (conjoin_biviews2 (sbv1, sbv2), sbv) =>
       separate_biviews?(sbv1, sbv)

  (* Separation commutes with composition (FIXME: should this be an iff?) *)
  theorem compose_biviews_separate is [a,b,c]
    fa (sbv1:BisimView(a,b),sbv2:BisimView(b,c),sbv1',sbv2')
      separate_biviews? (sbv1,sbv1') && separate_biviews? (sbv2,sbv2') =>
      separate_biviews? (compose_biviews (sbv1,sbv2),
                         compose_biviews (sbv1',sbv2'))

  (* The constant bi-view is separate from all other bi-views *)
  theorem trivial_biview_separate is [a,b]
    fa (sbv:BisimView (a, b)) separate_biviews? (trivial_biview, sbv)


  (***
   *** More Examples of Bisimilarity Views
   ***)

  (* Create a bi-view from a lens *)
  op [a,b] biview_of_lens (l: Lens(a,b)) : BisimView(a,b) =
    {biview = fn (a,b) -> l.lens_get a = b,
     bv_leq1 = fn (a1,a2) -> l.lens_set a1 (l.lens_get a2) = a2,
     bv_leq2 = fn (b1,b2) -> true}

  (* The biview for viewing the first element of a pair *)
  op [a,b] proj1_biview : BisimView (a*b, a) =
    biview_of_lens proj1_lens

  (* The biview for viewing the second element of a pair *)
  op [a,b] proj2_biview : BisimView (a*b, b) =
    biview_of_lens proj2_lens

  (* Combine a view of a and a view of b to a view of a*b *)
  op [a,b,c] tensor_biviews_l (sbv1: BisimView (a,c),
                               sbv2: BisimView (b,c)) : BisimView (a*b,c) =
    conjoin_biviews2 (compose_biviews (proj1_biview, sbv1),
                      compose_biviews (proj2_biview, sbv2))

  (* Combine a view of a at b and a view of a at c to a view of a at b*c *)
  op [a,b,c] tensor_biviews_r (sbv1: BisimView (a,b),
                               sbv2: BisimView (a,c)) : BisimView (a,b*c) =
    conjoin_biviews2 (compose_biviews (sbv1, invert_biview proj1_biview),
                      compose_biviews (sbv2, invert_biview proj2_biview))


  (***
   *** Implicational Bisimilarity Views
   ***)

  (* An implicational bisimilarity view intuitively allows some updates, called
  the succedent updates, iff some other set of updates, called the antecedent
  updates, are already allowed. In general, there could be multiple pairs of
  antecedent and succedent updates, which is represented as a list. For
  simplicity, the updates are always on the a / left-hand type, and
  implicational bisimilarity views are like the constant view for the b /
  right-hand type and the biview relation. *)
  type ImplBisimView1 a =
    {implview_ant: PreOrder a,
     implview_succ: PreOrder a}
  type ImplBisimView a = List (ImplBisimView1 a)

  (* Build a bisimilarity view that allows a-updates as per leq1 *)
  op [a,b] biview_of_leq1 (leq1: PreOrder a) : BisimView (a,b) =
    {biview = fn _ -> true,
     bv_leq1 = leq1,
     bv_leq2 = (=)}

  (* Compose all succ preorders in an implview *)
  op [a] compose_impl_succ_preorders (implview: ImplBisimView a) : PreOrder a =
    foldr relCompose (=) (map (fn impl -> impl.implview_succ) implview)

  (* The succedent biview of implview *)
  op [a,b] impl_succ_biview (implview: ImplBisimView a) : BisimView (a,b) =
    biview_of_leq1 (compose_impl_succ_preorders implview)

  (* Map an impl bisim view backwards using a function *)
  op [a,b] impl_biview_map (f: a -> b) (implview: ImplBisimView b) : ImplBisimView a =
    map
      (fn impl1 ->
         {implview_ant = map_endo f impl1.implview_ant,
          implview_succ = map_endo f impl1.implview_succ})
      implview

  (* Compose a relation R with an implview *)
  op [a,b] compose_rel_impl_biview (R: Relation (a,b))
                                   (implview: ImplBisimView b) : ImplBisimView a =
    map
      (fn impl1 ->
         {implview_ant =
            (fn (a1,a2) ->
               a1 = a2 ||
               (ex (b1) R (a1,b1)) &&
               (fa (b1)
                  R (a1,b1) =>
                  (ex (b2) R (a2,b2) && impl1.implview_ant (b1,b2)))),
          implview_succ =
            (fn (a1,a2) ->
               a1 = a2 ||
               (ex (b1) R (a1,b1)) &&
               (fa (b1)
                  R (a1,b1) =>
                  (ex (b2) R (a2,b2) && impl1.implview_succ (b1,b2))))})
      implview

  (* Compose a single implicational view with leq, allowing the succedent
  preorder to be used only at points where leq satisfies the antecedent *)
  op [a] rel_compose_impl1 (implview1: ImplBisimView1 a,
                            leq: PreOrder a) : PreOrder a =
    rt_closure (fn (a1,a2) ->
                  leq (a1,a2) ||
                  ((fa (a3) implview1.implview_ant (a1,a3) => leq (a1,a3)) &&
                     implview1.implview_succ (a1,a2)))

  (* Compose a list of implicational views with a relation; this allows the
  individual implicational views to be composed with leq in any order, because,
  e.g., one might add to leq in a way that satisfies another's antecedent *)
  op [a] rel_compose_impl (implview: ImplBisimView a,
                           leq: PreOrder a) : PreOrder a =
    fn (a1,a2) ->
      (ex (l)
         (forall? (fn impl1 -> impl1 in? implview) l) &&
         foldr rel_compose_impl1 leq l (a1,a2))

  (* Conjoin a biview with an implicational biview *)
  op [a,b] conjoin_biview_impl (bv: BisimView (a,b),
                                implview: ImplBisimView a) : BisimView (a,b) =
    {biview = fn (a,b) ->
       bv.biview (a,b) &&
       good_only_bisim_at_point? (rel_compose_impl (implview, bv.bv_leq1),
                                  bv.bv_leq2,bv.biview) (a,b),
     bv_leq1 = rel_compose_impl (implview, bv.bv_leq1),
     bv_leq2 = bv.bv_leq2}

  (* This separation requires that adding all the succ preorders of an implview
  to bv does not mess with the good-only bisimulation property of bv *)
  op [a,b] biview_impl_separate? (bv: BisimView (a,b),
                                  implview: ImplBisimView a) : Bool =
    good_only_bisim? (rt_closure
                        (relCompose (bv.bv_leq1,
                                     compose_impl_succ_preorders implview)),
                      bv.bv_leq2, bv.biview)

  (* Conjunction does not change biview when bv is separate from implview *)
  theorem conjoin_biview_impl_separate is [a,b]
    fa (bv:BisimView (a,b),implview)
      biview_impl_separate? (bv, implview) =>
      (conjoin_biview_impl (bv,implview)).biview = bv.biview

  (* If bv is separate from the succedent biview of implview, then it is
  separate from implview *)
  theorem separate_succ_biview_separate_impl is [a,b]
    fa (bv:BisimView (a,b),implview)
      separate_biviews? (bv,impl_succ_biview implview) =>
      biview_impl_separate? (bv, implview)

  (* If the succedent relation of implview always leads to a "bad" state of bv,
  and if it commutes with the leq1 of bv, then implview is separate from bv *)
  theorem succ_bad_separate_biview_impl is [a,b]
    fa (bv:BisimView (a,b),implview)
      (fa (a1,a2)
         implview.implview_succ (a1,a2) =>
         a1 = a2 || (fa (b) ~(bv.biview (a2,b)))) &&
      relations_commute? (bv.bv_leq1, implview.implview_succ) =>
      biview_impl_separate? (bv, [implview])

  (* Whether all of the individual succedent relations in one implicational
  biview commute with all those in another *)
  op [a] impl_biviews_commute? (impl1:ImplBisimView a,
                                impl2:ImplBisimView a) : Bool =
    forall? (fn impl1_1 ->
               forall? (fn impl1_2 ->
                          relations_commute? (impl1_1.implview_succ,
                                              impl1_2.implview_succ))
                 impl1) impl2

  (* Whether all of the individual succedent relations in an implicational
  biview commute with each other *)
  op [a] impl_biview_self_commutes? (impl:ImplBisimView a) : Bool =
    impl_biviews_commute? (impl,impl)

  (* If bv is separate from two impl biviews that commute then it is separate
  from the combination of the two impl biviews *)
  theorem separate_biview_impl_append is [a,b]
    fa (bv:BisimView (a,b),impl1,impl2)
      biview_impl_separate? (bv, impl1) &&
      biview_impl_separate? (bv, impl2) &&
      impl_biviews_commute? (impl1,impl2) =>
      biview_impl_separate? (bv, impl1 ++ impl2)

  (* The implicational bisimilarity view with the given succedent that is always
  allowed to be used, i.e., whose antecedent is always satisfied. This works
  because = is the smallest preorder on any type. *)
  op [a] always_impl_biview (succ: PreOrder a) : ImplBisimView a =
    [{implview_ant = (=), implview_succ = succ}]

  (* The always implicational view acts like its succedent view *)
  theorem conjoin_always_impl_biview is [a,b]
    fa (bv:BisimView (a,b),succ)
      conjoin_biview_impl (bv, always_impl_biview succ) =
      conjoin_biviews2 (bv, impl_succ_biview (always_impl_biview succ))

end-spec
