BisimView qualifying spec
  import ISet
  import Lens, OptLens

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

  (* Compose two bi-views. The allowed updates on the domain type, type a, must
  be allowed by the first bisimilarity view, bv1, restricted so that all related
  updates on the intermediate type, type b, are allowed by the second
  bisimilarity view, bv2. The allowed updates on the co-domain type, type c, are
  defined similarly. *)
  op [a,b,c] compose_biviews (bv1: BisimView (a,b),
                              bv2: BisimView (b,c)) : BisimView (a,c) =
    {biview = relCompose (bv1.biview, bv2.biview),
     bv_leq1 = fn (a1,a2) ->
       bv1.bv_leq1 (a1,a2) &&
       (fa (b1,b2) bv1.biview (a1,b1) && bv1.biview (a2,b2) =>
          bv2.bv_leq1 (b1,b2)),
     bv_leq2 = fn (c1,c2) ->
       bv2.bv_leq2 (c1,c2) &&
       (fa (b1,b2) bv2.biview (b1,c1) && bv2.biview (b2,c2) =>
          bv1.bv_leq2 (b1,b2))}

  theorem compose_identity_biview_l is [a,b]
    fa (bv:BisimView(a,b))
      compose_biviews (identity_biview, bv) = bv
  theorem compose_identity_biview_r is [a,b]
    fa (bv:BisimView(a,b))
      compose_biviews (bv, identity_biview) = bv
  theorem compose_biviews_assoc is [a,b,c,d]
    fa (bv1:BisimView(a,b),bv2:BisimView(b,c),bv3:BisimView(c,d))
      compose_biviews (compose_biviews (bv1, bv2), bv3) =
      compose_biviews (bv1, compose_biviews (bv2, bv3))


  (***
   *** Inverting Bisimilarity Views
   ***)

  (* Invert a bi-view, turning it around *)
  op [a,b] invert_biview (bv: BisimView (a,b)) : BisimView (b,a) =
    {biview = fn (b,a) -> bv.biview (a,b),
     bv_leq1 = bv.bv_leq2,
     bv_leq2 = bv.bv_leq1}

  (* FIXME: theorems stating that invert_biview is an involution *)


  (***
   *** Conjunction of Bisimilarity Views
   ***)

  (* States that any leq1 update on a and any leq2 update on b preserves R *)
  op [a,b] preorders_preserve_R_at_point? (leq1:PreOrder a, leq2:PreOrder b,
                                           R:Relation (a,b)) (a:a,b:b) : Bool =
    (fa (a',b')
       leq1 (a,a') && leq2 (b,b') && R (a,b) => R (a',b'))

  (* States that leq1 and leq2 updates preserve R at all points *)
  op [a,b] preorders_preserve_R? (leq1:PreOrder a, leq2:PreOrder b,
                                  R:Relation (a,b)) : Bool =
    (fa (a,b) preorders_preserve_R_at_point? (leq1,leq2,R) (a,b))

  (* States that any number of leq1 and leq2 steps starting at x can be
  decomposed into leq1 steps followed by leq2 steps *)
  op [a] preorders_decompose_at_point? (leq1: PreOrder a, leq2: PreOrder a)
                                       (x: a) : Bool =
    (fa (y)
       rt_closure (relCompose (leq1,leq2)) (x,y) =>
       relCompose (leq1,leq2) (x,y) && relCompose (leq2,leq1) (x,y))

  (* Conjoin two bisimilarity views, intuitively building the bisimilarity view
  that allows updates using bv1 and/or bv2. *)
  (* FIXME: explain the biview relation better... *)
  op [a,b] conjoin_biviews (bv1: BisimView (a,b),
                            bv2: BisimView (a,b)) : BisimView (a,b) =
    {biview = fn (a,b) ->
       bv1.biview (a,b) && bv2.biview (a,b) &&
       (preorders_preserve_R_at_point? (bv1.bv_leq1,bv1.bv_leq2,
                                        bv2.biview) (a,b) &&
        preorders_decompose_at_point? (bv1.bv_leq1,bv2.bv_leq1) a &&
        preorders_decompose_at_point? (bv1.bv_leq2,bv2.bv_leq2) b)
       ||
       (preorders_preserve_R_at_point? (bv2.bv_leq1,bv2.bv_leq2,
                                        bv1.biview) (a,b) &&
        preorders_decompose_at_point? (bv2.bv_leq1,bv1.bv_leq1) a &&
        preorders_decompose_at_point? (bv2.bv_leq2,bv1.bv_leq2) b),
     bv_leq1 = rt_closure (relCompose (bv1.bv_leq1, bv2.bv_leq1)),
     bv_leq2 = rt_closure (relCompose (bv1.bv_leq2, bv2.bv_leq2))}

  (* The trivial biview, that relates everything and provides no permissions *)
  op [a,b] trivial_biview : BisimView (a,b) =
    {biview = fn _ -> true, bv_leq1 = (=), bv_leq2 = (=)}

  (* FIXME HERE: understand this better... *)
  op [a,b] half_trivial_biview : BisimView (a,b) =
    {biview = (fn _ -> true),
     bv_leq1 = (=),
     bv_leq2 = (fn _ -> true)}

  (* Conjoin a list of bi-views *)
  op [a,b] conjoin_biviewsN (bvs: List (BisimView (a,b))) : BisimView (a,b) =
    foldr conjoin_biviews trivial_biview bvs

  (* Conjunction with the trivial view forms a commutative monoid *)
  theorem conjoin_biviews_assoc is [a,b]
    fa (bv1,bv2,bv3:BisimView(a,b))
      conjoin_biviews (bv1, conjoin_biviews (bv2, bv3)) =
      conjoin_biviews (conjoin_biviews (bv1, bv2), bv3)
  theorem conjoin_biviews_comm is [a,b]
    fa (bv1,bv2:BisimView(a,b))
      conjoin_biviews (bv1, bv2) =
      conjoin_biviews (bv2, bv1)
  theorem conjoin_biviews_trivial is [a,b]
    fa (bv:BisimView (a,b))
      conjoin_biviews (bv,trivial_biview) = bv

  (* Intuitively, one bisimilarity view is stronger than another iff it is the
  conjunction of the other with some other bisimilarity view *)
  (* FIXME: there should be some way to define this before conjunction... *)
  op [a,b] biview_weaker? : PreOrder (BisimView (a,b)) =
    fn (bv1,bv2) -> (ex (bv) bv2 = conjoin_biviews (bv1, bv))


  (***
   *** Separation of Bisimilarity Views
   ***)

  (* Two bisimilarity views are separate iff each biview is preserved by the
  other's preorder and the respective preorders commute. Intutively, this means
  that the updates allowed by one biview do not interfere with the other. *)
  op [a,b] separate_biviews? (bv1: BisimView (a,b), bv2: BisimView (a,b)) : Bool =
    preorders_preserve_R? (bv1.bv_leq1, bv1.bv_leq2, bv2.biview) &&
    preorders_preserve_R? (bv2.bv_leq1, bv2.bv_leq2, bv1.biview) &&
    relations_commute? (bv1.bv_leq1, bv2.bv_leq1) &&
    relations_commute? (bv1.bv_leq2, bv2.bv_leq2)

  (* Separation is commutative *)
  theorem separation_commutative is [a,b]
    fa (bv1,bv2: BisimView (a,b))
      separate_biviews? (bv1,bv2) => separate_biviews? (bv2,bv1)

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
    fa (bv1,bv2: BisimView (a,b))
      separate_biviews? (bv1,bv2) =>
      conjoin_biviews (bv1,bv2) =
      {biview = iSetInter (bv1.biview, bv2.biview),
       bv_leq1 = relCompose (bv1.bv_leq1, bv2.bv_leq1),
       bv_leq2 = relCompose (bv1.bv_leq2, bv2.bv_leq2)}

  (* Separation from two bi-views implies separation from their conjunction *)
  theorem biview_separate_from_conjunction is [a,b]
    fa (bv1,bv2,bv: BisimView (a,b))
      separate_biviews? (bv1, bv) && separate_biviews? (bv2, bv) =>
      separate_biviews? (conjoin_biviews (bv1, bv2), bv)

  (* Separation from the conjunction of separate biviews implies separation from
  the individual biviews themselves *)
  theorem biview_separation_un_conjoin is [a,b]
    fa (bv1,bv2,bv:BisimView (a,b))
      separate_biviews? (bv1, bv2) &&
      separate_biviews? (conjoin_biviews (bv1, bv2), bv) =>
      separate_biviews? (bv1, bv)

  (* Separation commutes with composition (FIXME: should this be an iff?) *)
  theorem compose_biviews_separate is [a,b,c]
    fa (bv1:BisimView(a,b),bv2:BisimView(b,c),bv1',bv2')
      separate_biviews? (bv1,bv1') && separate_biviews? (bv2,bv2') =>
      separate_biviews? (compose_biviews (bv1,bv2),
                         compose_biviews (bv1',bv2'))

  (* The trivial bi-view is separate from all other bi-views *)
  theorem trivial_biview_separate is [a,b]
    fa (bv:BisimView (a, b)) separate_biviews? (trivial_biview, bv)


  (***
   *** Pseudo-Monic Bisimilarity Views
   ***)

  (* We call a biview "pseudo-monic" iff every domain element is related to some
  co-domain element and if the relation is one-to-one for domain elements
  related by the bv_leq1 relation. Stated differently, this latter condition
  says that, if the biview allows a1 to be updated to some unequal a2, then a2
  will be related to different b's. Pseudo-monic-ness intuitively captures the
  condition that a biview is lens-like, where the first condition says that
  there is always some b corresponding to a given a, and the second condition is
  like the get-put lens law, saying that if we update an a to have the same b
  that it already has, then we get the same a. *)
  op [a,b] pseudo_monic? (bv: BisimView (a,b)) : Bool =
    (fa (a) ex (b) bv.biview (a,b)) &&
    (fa (a1,a2,b)
       bv.biview (a1,b) && bv.biview (a2,b) &&
       bv.bv_leq1 (a1,a2) => a1 = a2)

  (* The pseudo-monic condition is precisely what is needed to prove that
  composing a view with the trivial biview yields the trivial biview *)
  theorem compose_trivial_iff_pseudo_monic is [a,b,c]
    fa (bv:BisimView (a,b))
      pseudo_monic? bv <=>
      compose_biviews (bv, trivial_biview: BisimView (b,c)) = trivial_biview

  (* The trivial biview is pseudo-monic *)
  theorem trivial_pseudo_monic is [a,b]
    pseudo_monic? (trivial_biview: BisimView (a,b))

  (* The identity biview is pseudo-monic *)
  theorem identity_pseudo_monic is [a]
    pseudo_monic? (identity_biview: BisimView (a,a))

  (* Composition preserves pseudo-monic-ness *)
  theorem pseudo_monic_compose is [a,b,c]
    fa (bv1:BisimView (a,b), bv2:BisimView (b,c))
      pseudo_monic? (bv1) && pseudo_monic? (bv2) =>
      pseudo_monic? (compose_biviews (bv1, bv2))

  (* Conjunction of separate biviews preserves pseudo-monic-ness *)
  theorem pseudo_monic_conjoin is [a,b]
    fa (bv1, bv2:BisimView (a,b))
      pseudo_monic? (bv1) && pseudo_monic? (bv2) &&
      separate_biviews? (bv1,bv2) =>
      pseudo_monic? (conjoin_biviews (bv1, bv2))


  (***
   *** Biviews Built from Lenses
   ***)

  (* Build the biview corresponding to a lens *)
  op [a,b] biview_of_lens (l: Lens(a,b)) : BisimView(a,b) =
    {biview = fn (a,b) -> l.lens_get a = b,
     bv_leq1 = fn (a1,a2) -> l.lens_set a1 (l.lens_get a2) = a2,
     bv_leq2 = fn (b1,b2) -> true}

  (* Composition of lens biviews = the composed lens biview *)
  theorem biview_of_lens_compose is [a,b,c]
    fa (lens1:Lens (a,b), lens2:Lens (b,c))
      compose_biviews (biview_of_lens lens1, biview_of_lens lens2) =
      biview_of_lens (lens_compose (lens1,lens2))

  (* Lens biviews are pseudo-monic, as discussed above *)
  theorem lens_biview_pseudo_monic is [a,b]
    fa (lens: Lens (a,b))
      pseudo_monic? (biview_of_lens lens)

  (* Inverse lenses are also pseudo-monic, provided the domain is non-empty *)
  theorem lens_biview_inverse_pseudo_monic is [a,b]
    fa (lens: Lens (a,b))
      (ex (a:a) true) =>
      pseudo_monic? (invert_biview (biview_of_lens lens))

  (* Build a biview out of two lenses to the same type; intuitively, two objects
  are related iff each lens maps its object to the same result *)
  op [a,b,c] biview_of_lens_pair (lens1: Lens (a,b),
                                  lens2: Lens (c,b)) : BisimView (a,c) =
    compose_biviews (biview_of_lens lens1,
                     invert_biview (biview_of_lens lens2))

  (* A lens pair biview is pseudo-monic iff its co-domain type is non-empty *)
  theorem lens_pair_biview_pseudo_monic is [a,b,c]
    fa (lens1: Lens (a,b),lens2: Lens (c,b))
      (ex (c:c) true) =>
      pseudo_monic? (biview_of_lens_pair (lens1,lens2))


  (***
   *** More Examples of Bisimilarity Views
   ***)

  (* The biview for viewing the first element of a pair *)
  op [a,b] proj1_biview : BisimView (a*b, a) =
    biview_of_lens proj1_lens

  (* The biview for viewing the second element of a pair *)
  op [a,b] proj2_biview : BisimView (a*b, b) =
    biview_of_lens proj2_lens

  (* Combine a view of a and a view of b to a view of a*b *)
  op [a,b,c] tensor_biviews_l (bv1: BisimView (a,c),
                               bv2: BisimView (b,c)) : BisimView (a*b,c) =
    conjoin_biviews (compose_biviews (proj1_biview, bv1),
                     compose_biviews (proj2_biview, bv2))

  (* Combine a view of a at b and a view of a at c to a view of a at b*c *)
  op [a,b,c] tensor_biviews_r (bv1: BisimView (a,b),
                               bv2: BisimView (a,c)) : BisimView (a,b*c) =
    conjoin_biviews (compose_biviews (bv1, invert_biview proj1_biview),
                     compose_biviews (bv2, invert_biview proj2_biview))

  (* Build the biview corresponding to an option lens; this biview allows an a
  to be updated to one that does not satisfy the relation, but not vice-versa *)
  op [a,b] biview_of_opt_lens (optlens: OptLens(a,b)) : BisimView(a,b) =
    {biview = fn (a,b) -> optlens.optlens_get a = Some b,
     bv_leq1 = (fn (a1,a2) ->
                  case (optlens.optlens_get a1, optlens.optlens_get a2) of
                    | (None, None) -> true
                    | (Some _, None) -> true
                    | (None, Some _) -> false
                    | (Some _, Some b2) ->
                      optlens.optlens_set a1 b2 = Some a2),
     bv_leq2 = fn (b1,b2) -> true}

  (* Intersect the relation of a biview with another relation *)
  op [a,b] biview_intersect (R: Relation (a,b),
                             bv: BisimView (a,b)) : BisimView (a,b) =
    {biview = iSetInter (R, bv.biview),
     bv_leq1 = bv.bv_leq1,
     bv_leq2 = bv.bv_leq2}


  (***
   *** Implicational Bisimilarity Views
   ***)

  (* An implicational bisimilarity view intuitively allows some updates, called
  the succedent updates, iff some other set of updates, called the antecedent
  updates, are already allowed. In general, there could be multiple pairs of
  antecedent and succedent updates, which is represented as a list. For
  simplicity, the updates are always on the a / left-hand type, and
  implicational bisimilarity views are like the trivial view for the b /
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

  (* An impl biview is stronger than another iff any composition with a preorder
  always yields a superset *)
  (* FIXME: I don't think this does what we want... *)
  (*
  op [a] impl_biview_weaker? (implview1: ImplBisimView a,
                              implview2: ImplBisimView a) : Bool =
    fa (leq)
      subset? (rel_compose_impl (implview1, leq),
               rel_compose_impl (implview2, leq))
   *)

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
      conjoin_biviews (bv, impl_succ_biview (always_impl_biview succ))

end-spec
