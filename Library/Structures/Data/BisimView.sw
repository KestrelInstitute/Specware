BisimView qualifying spec
  import ISet
  import Lens

  (* Whether a relation from type a to type b commutes with equivalences on a
  and b, forming the following commutative square:

    * ---- eq1 ---- *
    |               |
    R               R
    |               |
    * ---- eq2 ---- *

  Such squares are used to describe, at a high level, permitted ways that state
  can be updated: a particular triple (R,eq1,eq2) "allows" state of type a to be
  updated in any way that preserves eq1, and the commutativity states that this
  is equivalent to an update of the related state type b that eq2 allows. *)
  op [a,b] commutes_with_eqs (eq1:Equivalence a, eq2:Equivalence b,
                              R:Relation (a,b)) : Bool =
    fa (a,b)
      (ex (a') eq1 (a,a') && R (a',b)) <=> (ex (b') eq2 (b,b') && R (a,b'))

  (* A bisimilarity view of type a at type b is a relation R that forms a
  bisimulation between two given equivalences, one on a and one on b *)
  type RawBisimView (a,b) = {biview: Relation (a,b),
                             bv_eq1: Equivalence a,
                             bv_eq2: Equivalence b}
  type BisimView (a,b) = {bv: RawBisimView (a,b) |
                            commutes_with_eqs (bv.bv_eq1, bv.bv_eq2, bv.biview)}


  (***
   *** The Category of Bisimilarity Views
   ***)

  (* The identitiy bi-view; (almost) nothing is separate from it *)
  op [a] identity_biview : BisimView (a,a) =
    {biview = (=),
     bv_eq1 = fn _ -> true,
     bv_eq2 = fn _ -> true}

  (* Compose two bi-views. Elements of the domain type (a) are considered bv_eq
  iff they are bv_eq by sbv1 and sbv1 maps them to sets of elements of the
  intermediate type (b) that are considered bv_eq by sbv2; similarly with
  elements of the co-domain type (c). *)
  op [a,b,c] compose_biviews (sbv1: BisimView (a,b),
                              sbv2: BisimView (b,c)) : BisimView (a,c) =
    {biview = relCompose (sbv1.biview, sbv2.biview),
     bv_eq1 = fn (a1,a2) ->
       sbv1.bv_eq1 (a1,a2) &&
       (fa (b1) sbv1.biview (a1,b1) =>
          (ex (b2) sbv1.biview (a2,b2) && sbv2.bv_eq1 (b1,b2))) &&
       (fa (b2) sbv1.biview (a2,b2) =>
          (ex (b1) sbv1.biview (a1,b1) && sbv2.bv_eq1 (b1,b2))),
     bv_eq2 = fn (c1,c2) ->
       sbv2.bv_eq2 (c1,c2) &&
       (fa (b1) sbv2.biview (b1,c1) =>
          (ex (b2) sbv2.biview (b2,c2) && sbv1.bv_eq2 (b1,b2))) &&
       (fa (b2) sbv2.biview (b2,c2) =>
          (ex (b1) sbv2.biview (b1,c1) && sbv1.bv_eq2 (b1,b2)))}

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
     bv_eq1 = sbv.bv_eq2,
     bv_eq2 = sbv.bv_eq1}

  (* FIXME: theorems stating that invert_biview is an involution *)


  (***
   *** Conjunction of Bisimilarity Views
   ***)

  (* Conjoin two bisimilarity views, intuitively building the bisimilarity view
  that allows updates using sbv1 and/or sbv2. *)
  (* FIXME: explain the biview relation better... *)
  op [a,b] conjoin_biviews2 (sbv1: BisimView (a,b),
                             sbv2: BisimView (a,b)) : BisimView (a,b) =
    {biview = fn (a,b) ->
       (fa (a',b') sbv2.bv_eq1 (a,a') && sbv2.bv_eq2 (b,b') =>
          sbv1.biview (a',b')) &&
       (fa (a',b') sbv1.bv_eq1 (a,a') && sbv1.bv_eq2 (b,b') =>
          sbv2.biview (a',b')),
     bv_eq1 = rst_closure (relCompose (sbv1.bv_eq1, sbv2.bv_eq1)),
     bv_eq2 = rst_closure (relCompose (sbv1.bv_eq2, sbv2.bv_eq2))}

  (* Conjoin a list of bi-views *)
  op [a,b] conjoin_biviews (sbvs: List (BisimView (a,b))) : BisimView (a,b) =
    foldr conjoin_biviews2 constant_biview sbvs

  (* The constant bi-view that allows no changes to anything *)
  op [a,b] constant_biview : BisimView (a,b) =
    {biview = fn _ -> true, bv_eq1 = (=), bv_eq2 = (=)}

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
      conjoin_biviews2 (sbv,constant_biview) = sbv


  (***
   *** Separation of Bisimilarity Views
   ***)

  (* Two bisimilarity views are separate iff each biview is preserved by the
  other's equivalences and the respectively equivalences commute. Intutively,
  this means that the state updates allowed by each biview do not interfere with
  each other. *)
  op [a,b] separate_biviews? (sbv1: BisimView (a,b), sbv2: BisimView (a,b)) : Bool =
    (fa (a1,a2,b1,b2)
       sbv1.bv_eq1 (a1,a2) && sbv1.bv_eq2 (b1,b2) && sbv2.biview (a1,b1) =>
       sbv2.biview (a2,b2)) &&
    (fa (a1,a2,b1,b2)
       sbv2.bv_eq1 (a1,a2) && sbv2.bv_eq2 (b1,b2) && sbv1.biview (a1,b1) =>
       sbv1.biview (a2,b2)) &&
    (commutes_with_eqs (sbv1.bv_eq1, sbv1.bv_eq1, sbv2.bv_eq1)) &&
    (commutes_with_eqs (sbv1.bv_eq2, sbv1.bv_eq2, sbv2.bv_eq2))

  (* Separation is commutative *)
  theorem separation_commutative is [a,b]
    fa (sbv1,sbv2: BisimView (a,b))
      separate_biviews? (sbv1,sbv2) => separate_biviews? (sbv2,sbv1)

  (* Conjoining separate biviews yields the intersection for biview and the
  composition for the two equalities *)
  theorem conjoin_separate_biviews is [a,b]
    fa (sbv1,sbv2: BisimView (a,b))
      separate_biviews? (sbv1,sbv2) =>
      conjoin_biviews2 (sbv1,sbv2) =
      {biview = iSetInter (sbv1.biview, sbv2.biview),
       bv_eq1 = relCompose (sbv1.bv_eq1, sbv2.bv_eq1),
       bv_eq2 = relCompose (sbv1.bv_eq2, sbv2.bv_eq2)}

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
  theorem constant_biview_separate is [a,b]
    fa (sbv:BisimView (a, b)) separate_biviews? (constant_biview, sbv)


  (***
   *** More Examples of Bisimilarity Views
   ***)

  (* Create a bi-view from a lens *)
  op [a,b] biview_of_lens (l: Lens(a,b)) : BisimView(a,b) =
    {biview = fn (a,b) -> l.lens_get a = b,
     bv_eq1 = fn (a1,a2) -> l.lens_set a1 (l.lens_get a2) = a2,
     bv_eq2 = fn (b1,b2) -> true}

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


end-spec
