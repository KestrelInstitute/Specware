(* Copyright 2015 Kestrel Institute. See file LICENSE for license details *)


S1 = spec
    op f : Integer -> Integer
end-spec

S1p = spec
    op f (x : Integer) : Integer =
      x + 1
end-spec


S2 = spec
    op f : Integer * Integer -> Integer
end-spec

S3 = spec
    import S1
    op g (x : Integer) : Integer =
      f x
end-spec


S1_Ref = morphism S1 -> S1p { }

S3p = S3 [S1_Ref]

S2p = S2 [S1_Ref]


(*
Test = S4 qualifying spec
  op h (x : Integer) : Integer = x + 2
end-spec
*)

Test = spec
  % import /Library/Base/Empty
  type t
  type u
  type mine.u = Bool
  op f : t -> u
  op g : u -> t

  axiom f_g_inv is
    fa (x:t) g (f x) = x

  axiom g_f_inv is
    fa (y:u) f (g y) = y
end-spec

(*
Test = fun (type u, type t, op f, op g) ->
   record {
      t := t; u := u; mine.u := Bool; f := f; g := g
   }
*)

Test2 = spec
  import Test (* <---- u in for t *)
  type t = u
  (* ERROR: type mine.u = Integer *)
end-spec

(*
Test2 = fun (type u, op f, op g) ->
  Test (u, u, f, g)
*)

Test3 = spec
  import Test
  type r
  type t = r
end-spec

(*
Test3 = fun (type u, op f, op g, type r) ->
  Test (u, r, f, g) extend { r := r }
*)

Test4 = spec
  import Test
  type r = r_ctor t
  type t = t_ctor r
end-spec

(*
Test4 = fun (type u, op f, op g) ->
  let rec t = r_ctor r
             r = t_ctor t in
  Test (u, t, f, g) extend { r := r }
*)


(*
Test2 = spec
  type u'
  op f'
  axiom ...

  apply Test (u', List Integer, f', g', ...)

  import translate Test by { t |-> List Integer, u |-> u', f |-> f' }
  type t = List Integer
end-spec
*)

(*
Test = spec
  import /Library/Base/Boolean
  op h (x : Bool) : Bool = ~x
end-spec
*)

(*
S5 = spec
  % test: are top-level names visible in specs?
  op f (x : Integer) : Integer = S1 x
end-spec
*)


S6 = spec
  type t
end-spec

S7 = spec
  import S6
  op g (x : t) : t = x
end-spec

S8 = spec
  import S7
  op h (x : t) (y : t) : t = y
end-spec
