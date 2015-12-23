(* Copyright 2015 Kestrel Institute. See file LICENSE.text for license details *)

RelLens qualifying spec
  import /Library/General/OptionExt

(* Relational lenses are like lenses (see Lens.sw), but where the getter and
   setter are relations instead of functions. Stated differently, relational
   lenses are like monadic lenses (see MLens.sw) where the monad is the set
   monad, i.e., Monad a is a -> Bool. (Note, however, that law 2 here is
   actually weaker than law 2 for monadic lenses with the set monad, since set
   a1 b a2 here allows get a2 b' for b' other than b.) The relational lens laws
   are:

     get a b                      => set a b a
     set a1 b a2                  => get a2 b
     set a1 b1 a2 && set a2 b2 a3 => set a1 b2 a3

   These are the relational versions of the normal lens laws, where get a b
   holds iff b is a possible component value for a, and set a1 b a2 holds iff a2
   is a possible way to update a1 using component value b. Law 1 says that, if a
   has component b, then we can set the component value of a to b to get a
   again. Law 2 says that, if we can set the component value of a1 to b to get
   a2, then b must be a valid component value of a2. Finally, law 3 says that if
   we set the component value to b1 and then to b2, we can short-circuit this by
   just setting the component value to b2. *)

(* The "raw" type of relational lenses, without the laws *)
type RawRelLens (a,b) = {rellens_get : a -> b -> Bool,
                         rellens_set : a -> b -> a -> Bool }

(* The monadic lens laws *)
op [a,b] satisfies_get_put_rel (l:RawRelLens (a,b)) : Bool =
  fa (a,b) l.rellens_get a b => l.rellens_set a b a
op [a,b] satisfies_put_get_rel (l:RawRelLens (a,b)) : Bool =
  fa (a1,b,a2) l.rellens_set a1 b a2 => l.rellens_get a2 b
op [a,b] satisfies_put_put_rel (l:RawRelLens (a,b)) : Bool =
  fa (a1,b1,a2,b2,a3)
    l.rellens_set a1 b1 a2 && l.rellens_set a2 b2 a3 => l.rellens_set a1 b2 a3

(* The complete type of monadic lenses *)
type RelLens (a,b) =
  { l : RawRelLens (a,b) |
     satisfies_get_put_rel l && satisfies_put_get_rel l && satisfies_put_put_rel l }

(* Compose two monadic lenses *)
op [a,b,c] rellens_compose (l1 : RelLens (a,b), l2 : RelLens (b,c)) : RelLens (a,c) =
   {rellens_get = (fn a -> fn c -> ex (b) l1.rellens_get a b && l2.rellens_get b c),
    rellens_set = (fn a1 -> fn c -> fn a2 ->
                     ex (b1,b2)
                       l1.rellens_get a1 b1 && l2.rellens_set b1 c b2 &&
                       l1.rellens_set a1 b2 a2)}

(* Separation of lenses: each write commutes with the other lens's operations *)
op [a,b,c] rellens_separate? (l1: RelLens (a,b), l2: RelLens (a,c)) : Bool =
  (* l1's get commutes with l2's set *)
  (fa (a1,b,c,a2)
     l1.rellens_get a1 b && l2.rellens_set a1 c a2 => l1.rellens_get a2 b) &&
  (* l2's get commutes with l1's set *)
  (fa (a1,b,c,a2)
     l2.rellens_get a1 c && l1.rellens_set a1 b a2 => l2.rellens_get a2 c) &&
  (* The two sets commute *)
  (fa (a1,b,c,a3)
     (ex (a2) l1.rellens_set a1 b a2 && l2.rellens_set a2 c a3)
     <=>
     (ex (a2) l2.rellens_set a1 c a2 && l1.rellens_set a2 b a3))


(*** Examples of relational lenses ***)

(* The constant RelLens *)
op [a,b] rellens_const (b:b) : RelLens (a,b) =
  {rellens_get = fn a -> fn b' -> b = b',
   rellens_set = fn a -> fn b' -> fn a' -> a = a' && b = b'}


end-spec
