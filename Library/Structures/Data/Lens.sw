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
  type Lens (a,b) = { l : RawLens (a,b) |
                       satisfies_get_put l && satisfies_put_get l && satisfies_put_put l }


  (* Lenses compose, in the expected way *)
  op [a,b,c] lens_compose (l1:Lens(a,b), l2:Lens(b,c)) : Lens(a,c) =
    {lens_get = (fn a -> l2.lens_get (l1.lens_get a)),
     lens_set = (fn a -> fn c ->
                   l1.lens_set a (l2.lens_set (l1.lens_get a) c))}

  (* FIXME: prove the subtyping constraints! *)


  (* We can even compose lenses that return option types *)
  op [a,b,c] lens_compose_opt (l1:Lens(a,Option b), l2:Lens(b,Option c)) : Lens(a,Option c) =
    {lens_get = (fn a -> l2.lens_get (l1.lens_get a)),
     lens_set = (fn a -> fn c ->
                   l1.lens_set a (l2.lens_set (l1.lens_get a) c))}
end-spec
