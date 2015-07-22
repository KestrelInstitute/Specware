SeparableView qualifying spec
  import ISet
  import Lens

  (* A separable view of type a at type b is a "view" of a at type b, along with
  an equivalence relation stating when elements of type a are equal except for
  that view. This equivalence allows us to define whether two views can be
  considered "separate", an so makes such a view "separable". *)
  type SeparableView (a,b) = { view: Relation (a,b), sep_eq: Equivalence a }

  (* Whether two separable views are separate *)
  op [a,b,c] separate_views? (sv1: SeparableView(a,b), sv2: SeparableView(a,c)) : Bool =
    (fa (a1, a2, b) sv1.view (a1, b) && sv2.sep_eq (a1, a2) => sv1.view (a2, b)) &&
    (fa (a1, a2, c) sv2.view (a1, c) && sv1.sep_eq (a1, a2) => sv2.view (a2, c)) &&
    (relations_commute? (sv1.sep_eq, sv2.sep_eq))

  (* Tensor two separable views that are separate *)
  op [a,b,c] tensor_separate_views (sv1: SeparableView(a,b), sv2: SeparableView(a,c) |
                                      separate_views? (sv1, sv2))
  : SeparableView (a, b*c) =
    { view = relCross2 (sv1.view, sv2.view),
      sep_eq = relCompose (sv1.sep_eq, sv2.sep_eq) }

  (* Create a separable view from a lens *)
  op [a,b] separable_view_of_lens (l: Lens(a,b)) : SeparableView(a,b) =
    { view = fn (a,b) -> l.lens_get a = b,
      sep_eq = fn (a1,a2) -> l.lens_set a1 (l.lens_get a2) = a2 }


  (*** Separable Bi-Views ****)

  (* A separable bi-view is a view that is separable in both directions *)
  type SeparableBiView (a,b) = {biview: Relation (a,b),
                                sep_eq1: Equivalence a,
                                sep_eq2: Equivalence b}

  (* The trivial bi-view that is separate from everything *)
  op [a,b] trivial_biview : SeparableBiView (a,b) =
    {biview = fn _ -> true, sep_eq1 = (=), sep_eq2 = (=)}

  (* The trivial bi-view is separate from all other bi-views *)
  theorem trivial_biview_separate is [a,b]
    fa (sbv:SeparableBiView (a, b)) separate_biviews? (trivial_biview, sbv)

  (* Make a bi-view of a relation where (almost) nothing is separate from it *)
  op [a,b] biview_of_relation (R: Relation (a,b)) : SeparableBiView(a,b) =
    {biview = R,
     sep_eq1 = fn _ -> true,
     sep_eq2 = fn _ -> true}

  (* Make a bi-view of a function *)
  op [a,b] biview_of_function (f: a -> b) : SeparableBiView(a,b) =
    biview_of_relation (fn (a,b) -> f a = b)

  (* The identitiy bi-view; (almost) nothing is separate from it *)
  op [a] identity_biview : SeparableBiView (a,a) =
    biview_of_function (fn x -> x)

  (* Make a separable bi-view between a and b from separable views of a and b at
  some intermediate type c *)
  op [a,b,c] bivew_of_views (sv1: SeparableView (a,c), sv2: SeparableView (b,c)) : SeparableBiView (a,b) =
    {biview = relCompose (sv1.view, relInvert sv2.view),
     sep_eq1 = sv1.sep_eq, sep_eq2 = sv2.sep_eq}

  (* Extract a separable view from a separable bi-view *)
  op [a,b] view_of_biview (sbv: SeparableBiView (a,b)) : SeparableView (a,b) =
    {view = sbv.biview, sep_eq = sbv.sep_eq1}

  (* Extract the inverse separable view from a separable bi-view *)
  op [a,b] inv_view_of_biview (sbv: SeparableBiView (a,b)) : SeparableView (b,a) =
    {view = relInvert sbv.biview, sep_eq = sbv.sep_eq2}

  (* Two biviews are separate iff both of their views are *)
  op [a,b] separate_biviews? (sbv1: SeparableBiView (a,b), sbv2: SeparableBiView (a,b)) : Bool =
    separate_views? (view_of_biview sbv1, view_of_biview sbv2) &&
    separate_views? (inv_view_of_biview sbv1, inv_view_of_biview sbv2)

  (* Invert a bi-view, turning it around *)
  op [a,b] invert_biview (sbv: SeparableBiView (a,b)) : SeparableBiView (b,a) =
    {biview = fn (b,a) -> sbv.biview (a,b),
     sep_eq1 = sbv.sep_eq2,
     sep_eq2 = sbv.sep_eq1}

  (* Conjoin two bi-views, only allowing the view to work if the two bi-views
  are separate. We use the rst_closure for the sep_eq relations to make sure
  they are equivalences even if sbv1 and sbv2 are not separate, but this is
  equivalent to relCompose (sbv1.sep_eq, sbv1.sep_eq) if they are. *)
  op [a,b] conjoin_biviews2 (sbv1: SeparableBiView (a,b),
                             sbv2: SeparableBiView (a,b)) : SeparableBiView (a,b) =
    {biview = fn (a,b) ->
       separate_biviews? (sbv1, sbv2) &&
       iSetInter (sbv1.biview, sbv2.biview) (a,b),
     sep_eq1 = rst_closure (relCompose (sbv1.sep_eq1, sbv2.sep_eq1)),
     sep_eq2 = rst_closure (relCompose (sbv1.sep_eq2, sbv2.sep_eq2))}

  (* Conjoining with the trivial bi-view is a no-op *)
  theorem conjoin_trivial_biview is [a,b]
    fa (sbv:SeparableBiView (a,b))
      conjoin_biviews2 (sbv,trivial_biview) = sbv

  (* Separation from two bi-views implies separation from their conjunction *)
  theorem conjoin_biviews_separate is [a,b]
    fa (sbv1,sbv2,sbv: SeparableBiView (a,b))
      separate_biviews? (sbv1, sbv) && separate_biviews? (sbv2, sbv) =>
      separate_biviews? (conjoin_biviews2 (sbv1, sbv2), sbv)

  (* Conjoin a list of bi-views *)
  op [a,b] conjoin_biviews (sbvs: List (SeparableBiView (a,b))) : SeparableBiView (a,b) =
    foldr conjoin_biviews2 trivial_biview sbvs

  (* Compose two bi-views. Elements of the domain type (a) are considered sep_eq
  iff they are sep_eq by sbv1 and sbv1 maps them to sets of elements of the
  intermediate type (b) that are considered sep_eq by sbv2; similarly with
  elements of the co-domain type (c). *)
  op [a,b,c] compose_biviews (sbv1: SeparableBiView (a,b),
                              sbv2: SeparableBiView (b,c)) : SeparableBiView (a,c) =
    {biview = relCompose (sbv1.biview, sbv2.biview),
     sep_eq1 = fn (a1,a2) ->
       sbv1.sep_eq1 (a1,a2) &&
       (fa (b1) sbv1.biview (a1,b1) =>
          (ex (b2) sbv1.biview (a2,b2) && sbv2.sep_eq1 (b1,b2))) &&
       (fa (b2) sbv1.biview (a2,b2) =>
          (ex (b1) sbv1.biview (a1,b1) && sbv2.sep_eq1 (b1,b2))),
     sep_eq2 = fn (c1,c2) ->
       sbv2.sep_eq2 (c1,c2) &&
       (fa (b1) sbv2.biview (b1,c1) =>
          (ex (b2) sbv2.biview (b2,c2) && sbv1.sep_eq2 (b1,b2))) &&
       (fa (b2) sbv2.biview (b2,c2) =>
          (ex (b1) sbv2.biview (b1,c1) && sbv1.sep_eq2 (b1,b2)))}

  theorem compose_identity_biview_l is [a,b]
    fa (sbv:SeparableBiView(a,b))
      compose_biviews (identity_biview, sbv) = sbv

  theorem compose_identity_biview_r is [a,b]
    fa (sbv:SeparableBiView(a,b))
      compose_biviews (sbv, identity_biview) = sbv

  theorem compose_biviews_assoc is [a,b,c,d]
    fa (sbv1:SeparableBiView(a,b),sbv2:SeparableBiView(b,c),sbv3:SeparableBiView(c,d))
      compose_biviews (compose_biviews (sbv1, sbv2), sbv3) =
      compose_biviews (sbv1, compose_biviews (sbv2, sbv3))

  theorem compose_biviews_separate is [a,b,c]
    fa (sbv1:SeparableBiView(a,b),sbv2:SeparableBiView(b,c),sbv1',sbv2')
      separate_biviews? (sbv1,sbv1') && separate_biviews? (sbv2,sbv2') =>
      separate_biviews? (compose_biviews (sbv1,sbv2),
                         compose_biviews (sbv1',sbv2'))

  (* The biview for viewing the first element of a pair *)
  op [a,b] proj1_biview : SeparableBiView (a*b, a) =
    {biview = fn ((a,b),a') -> a = a',
     sep_eq1 = fn ((a1,b1),(a2,b2)) -> b1 = b2,
     sep_eq2 = fn (a1,a2) -> true}

  (* The biview for viewing the second element of a pair *)
  op [a,b] proj2_biview : SeparableBiView (a*b, b) =
    {biview = fn ((a,b),b') -> b = b',
     sep_eq1 = fn ((a1,b1),(a2,b2)) -> a1 = a2,
     sep_eq2 = fn (b1,b2) -> true}

  (* Combine a view of a and a view of b to a view of a*b *)
  op [a,b,c] tensor_biviews_l (sbv1: SeparableBiView (a,c),
                               sbv2: SeparableBiView (b,c)) : SeparableBiView (a*b,c) =
    conjoin_biviews2 (compose_biviews (proj1_biview, sbv1),
                      compose_biviews (proj2_biview, sbv2))

  (* Combine a view of a at b and a view of a at c to a view of a at b*c *)
  op [a,b,c] tensor_biviews_r (sbv1: SeparableBiView (a,b),
                               sbv2: SeparableBiView (a,c)) : SeparableBiView (a,b*c) =
    conjoin_biviews2 (compose_biviews (sbv1, invert_biview proj1_biview),
                      compose_biviews (sbv2, invert_biview proj2_biview))


end-spec
