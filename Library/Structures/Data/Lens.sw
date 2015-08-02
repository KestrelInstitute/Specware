(* The getter/setter form of lenses *)

Lens qualifying spec

  (* A lens from a to b is a pair of a "getter" function that projects an a to a
     "component" of type b, along with a "setter" function that sets the b
     component of an a. *)
  type RawLens (a,b) = {lens_get : a -> b, lens_set: a -> b -> a}

  (* To be valid, a lens also has to satisfy the following laws, which
     intuitively state that get and set behave like real accessors *)
  op [a,b] satisfies_get_put (l:RawLens (a,b)) : Bool =
    fa (a) l.lens_set a (l.lens_get a) = a
  op [a,b] satisfies_put_get (l:RawLens (a,b)) : Bool =
    fa (a,b) l.lens_get (l.lens_set a b) = b
  op [a,b] satisfies_put_put (l:RawLens (a,b)) : Bool =
    fa (a,b1,b2) l.lens_set (l.lens_set a b1) b2 = l.lens_set a b2

  (* The bundled type of lenses *)
  type Lens (a,b) =
    { l : RawLens (a,b) |
       satisfies_get_put l && satisfies_put_get l && satisfies_put_put l }

  (* Lenses compose, in the expected way *)
  op [a,b,c] lens_compose (l1:Lens(a,b), l2:Lens(b,c)) : Lens(a,c) =
    {lens_get = (fn a -> l2.lens_get (l1.lens_get a)),
     lens_set = (fn a -> fn c ->
                   l1.lens_set a (l2.lens_set (l1.lens_get a) c))}

  (* Whether two lenses on the same type are separate *)
  op [a,b1,b2] separate_lenses? (l1:Lens(a,b1), l2:Lens(a,b2)) : Bool =
    (* l1's sets do not affect l2's gets *)
    (fa (a,b1) l2.lens_get a = l2.lens_get (l1.lens_set a b1)) &&
    (* l2's sets do not affect l1's gets *)
    (fa (a,b2) l1.lens_get a = l1.lens_get (l2.lens_set a b2)) &&
    (* the two sets commute *)
    (fa (a,b1,b2)
     l2.lens_set (l1.lens_set a b1) b2 = l1.lens_set (l2.lens_set a b2) b1)

proof Isa lens_compose_Obligation_subtype
  by (auto simp add: Lens__Lens__subtype_pred_def Lens__satisfies_get_put_def
                     Lens__satisfies_put_get_def Lens__satisfies_put_put_def)
end-proof

  (* The identity lens *)
  op [a] id_lens : Lens (a,a) =
    {lens_get = fn a -> a, lens_set = fn a -> fn a' -> a'}

  (* The unit lens *)
  op [a] unit_lens : Lens (a,()) =
    {lens_get = fn a -> (), lens_set = fn a -> fn () -> a}

  (* The lens for the first projection of a pair *)
  op [a,b] proj1_lens : Lens (a*b,a) =
    {lens_get = fn (a,b) -> a, lens_set = fn (a,b) -> fn a' -> (a',b)}
  (* The lens for the second projection of a pair *)
  op [a,b] proj2_lens : Lens (a*b,b) =
    {lens_get = fn (a,b) -> b, lens_set = fn (a,b) -> fn b' -> (a,b')}


  (***
   *** Lenses for Triples, Quadruples, etc.
   ***)

  (* Lenses for projecting a component of a tuple. The naming convention is that
  tuple_lens_i_j projects the jth element of an i-tuple. *)

  op [a,b,c] tuple_lens_3_1 : Lens (a*b*c,a) =
    {lens_get = fn (a,b,c) -> a, lens_set = fn (a,b,c) -> fn a' -> (a',b,c)}
  op [a,b,c] tuple_lens_3_2 : Lens (a*b*c,b) =
    {lens_get = fn (a,b,c) -> b, lens_set = fn (a,b,c) -> fn b' -> (a,b',c)}
  op [a,b,c] tuple_lens_3_3 : Lens (a*b*c,c) =
    {lens_get = fn (a,b,c) -> c, lens_set = fn (a,b,c) -> fn c' -> (a,b,c')}

  op [a,b,c,d] tuple_lens_4_1 : Lens (a*b*c*d,a) =
    {lens_get = fn (a,b,c,d) -> a, lens_set = fn (a,b,c,d) -> fn a' -> (a',b,c,d)}
  op [a,b,c,d] tuple_lens_4_2 : Lens (a*b*c*d,b) =
    {lens_get = fn (a,b,c,d) -> b, lens_set = fn (a,b,c,d) -> fn b' -> (a,b',c,d)}
  op [a,b,c,d] tuple_lens_4_3 : Lens (a*b*c*d,c) =
    {lens_get = fn (a,b,c,d) -> c, lens_set = fn (a,b,c,d) -> fn c' -> (a,b,c',d)}
  op [a,b,c,d] tuple_lens_4_4 : Lens (a*b*c*d,d) =
    {lens_get = fn (a,b,c,d) -> d, lens_set = fn (a,b,c,d) -> fn d' -> (a,b,c,d')}

  op [a,b,c,d,e] tuple_lens_5_1 : Lens (a*b*c*d*e,a) =
    {lens_get = fn (a,b,c,d,e) -> a, lens_set = fn (a,b,c,d,e) -> fn a' -> (a',b,c,d,e)}
  op [a,b,c,d,e] tuple_lens_5_2 : Lens (a*b*c*d*e,b) =
    {lens_get = fn (a,b,c,d,e) -> b, lens_set = fn (a,b,c,d,e) -> fn b' -> (a,b',c,d,e)}
  op [a,b,c,d,e] tuple_lens_5_3 : Lens (a*b*c*d*e,c) =
    {lens_get = fn (a,b,c,d,e) -> c, lens_set = fn (a,b,c,d,e) -> fn c' -> (a,b,c',d,e)}
  op [a,b,c,d,e] tuple_lens_5_4 : Lens (a*b*c*d*e,d) =
    {lens_get = fn (a,b,c,d,e) -> d, lens_set = fn (a,b,c,d,e) -> fn d' -> (a,b,c,d',e)}
  op [a,b,c,d,e] tuple_lens_5_5 : Lens (a*b*c*d*e,e) =
    {lens_get = fn (a,b,c,d,e) -> e, lens_set = fn (a,b,c,d,e) -> fn e' -> (a,b,c,d,e')}

  (* Lenses for projecting a sub-tuple from a larger tuple. The naming
  convention is that subtuple_lens_i projects the first i-1 elements, as an
  i-1-tuple, of an i-tuple. *)

  op [a,b,c] subtuple_lens_3 : Lens (a*b*c, a*b) =
    {lens_get = fn (a,b,c) -> (a,b),
     lens_set = fn (a,b,c) -> fn (a',b') -> (a',b',c)}
  op [a,b,c,d] subtuple_lens_4 : Lens (a*b*c*d, a*b*c) =
    {lens_get = fn (a,b,c,d) -> (a,b,c),
     lens_set = fn (a,b,c,d) -> fn (a',b',c') -> (a',b',c',d)}
  op [a,b,c,d,e] subtuple_lens_5 : Lens (a*b*c*d*e, a*b*c*d) =
    {lens_get = fn (a,b,c,d,e) -> (a,b,c,d),
     lens_set = fn (a,b,c,d,e) -> fn (a',b',c',d') -> (a',b',c',d',e)}

end-spec
