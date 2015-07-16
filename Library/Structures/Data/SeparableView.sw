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

  (* Combine two separable views that are separate *)
  op [a,b,c] combine_separate_views (sv1: SeparableView(a,b), sv2: SeparableView(a,c) |
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

end-spec
