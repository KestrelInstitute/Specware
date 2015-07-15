SeparableView qualifying spec
  import ISet
  import Lens

  (* A separable view of type a at type b is a "view" of a at type b, along with
  an equivalence relation stating when element of type a are equal except for
  that view. *)
  type SeparableView (a,b) = { view: Relation (a,b), sep_eq: Equivalence a }

  (* Whether two separable views are separate *)
  op [a,b,c] separate_views? (sv1: SeparableView(a,b), sv2: SeparableView(a,c)) : Bool =
    (fa (a1, a2, b) sv1.view (a1, b) && sv2.sep_eq (a1, a2) => sv1.view (a2, b)) &&
    (fa (a1, a2, c) sv2.view (a1, c) && sv1.sep_eq (a1, a2) => sv2.view (a2, c)) &&
    (fa (a1, a3)
       (ex (a2) sv1.sep_eq (a1, a2) && sv2.sep_eq (a2, a3))
       <=>
       (ex (a2) sv2.sep_eq (a1, a2) && sv1.sep_eq (a2, a3)))

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

end-spec
