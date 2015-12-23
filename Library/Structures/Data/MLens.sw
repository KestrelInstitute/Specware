(* Copyright 2015 Kestrel Institute. See file LICENSE for license details *)

MLens qualifying spec
import Monad

(* Monadic lenses are like lenses (see Lens.sw), but where the getter
   and setter functions are monadic. The monadic lens laws are:

     {b <- get a; set a b}       = {get a; return a}
     {a' <- set a b; get a'}     = {set a b; return b}
     {a' <- set a b1; set a' b2} = set a b2

   These are almost the same as the normal lens laws: rule 1 says that
   getting the value of a and then setting this value to itself is a
   essentially no-op; however, the read itself could have a
   side-effect, so it remains in the simpler right-hand side.
   Similarly, rule 2 says that setting a value and then reading it
   again just returns the value set; again, the set remains on the
   right-hand side, since it could have side-effects. Finally, rule 3
   says that any set erases any previous sets.
*)

(* The "raw" type of monadic lenses, without the laws *)
type RawMLens (a,b) = { mlens_get : a -> Monad b,
                        mlens_set : a -> b -> Monad a }

(* The monadic lens laws *)
op [a,b] satisfies_get_put_m (l:RawMLens (a,b)) : Bool =
  fa (a) {b <- l.mlens_get a; l.mlens_set a b} = {l.mlens_get a; return a}
op [a,b] satisfies_put_get_m (l:RawMLens (a,b)) : Bool =
  fa (a,b)
    {a' <- l.mlens_set a b; l.mlens_get a'} =
    {a' <- l.mlens_set a b; return b}
op [a,b] satisfies_put_put_m (l:RawMLens (a,b)) : Bool =
  fa (a,b1,b2)
    {a' <- l.mlens_set a b1; l.mlens_set a' b2} = l.mlens_set a b2

(* The complete type of monadic lenses *)
type MLens (a,b) =
  { l : RawMLens (a,b) |
     satisfies_get_put_m l && satisfies_put_get_m l && satisfies_put_put_m l }

(* Compose two monadic lenses *)
op [a,b,c] mlens_compose (l1 : MLens (a,b), l2 : MLens (b,c)) : MLens (a,c) =
   {mlens_get = (fn a -> {b <- l1.mlens_get a; l2.mlens_get b}),
    mlens_set = (fn a -> fn c ->
                   {b <- l1.mlens_get a;
                    b_new <- l2.mlens_set b c;
                    l1.mlens_set a b_new})}

(* FIXME: axiom about mlens_compose forming a category, i.e., it is associative
   and has an identity *)

(* FIXME: can combine lenses MLens(a,b1) and MLens(a,b2) into an MLens(a,b1*b2),
   but only if the gets and sets commute; i.e., only if they are *separable* *)

(* The monadic lens for getting / setting a specific key in a map. It
   is an error to get or set a key not already in the map; the error
   computations are passed in as arguments so that we don't have to
   import MonadError (which makes it easier to use Option instead) *)
op [a,b] mlens_of_key (key:a, getErr:Monad b, setErr:Monad (a -> Option b)) : MLens ((a -> Option b),b) =
   {mlens_get = (fn m -> mapOptionDefault return getErr (m key)),
    mlens_set = (fn m -> fn b ->
                   case m key of
                     | None -> setErr
                     | Some _ ->
                       return (fn a -> if a = key then Some b else m a)) }


(* Look up a value in an alist *)
(* FIXME HERE: this should be in a library somewhere... *)
op [a,b] assoc (l:List (a * b)) (key : a) : Option b =
  case l of
    | [] -> None
    | (x,y)::l' -> if key = x then Some y else assoc l' key

(* Set the value for a key in an alist, returning None if the key is not already
in the alist *)
op [a,b] alist_set (l:List (a * b)) (key : a) (val : b) : Option (List (a * b)) =
   case l of
     | [] -> None
     | (key',val')::l' ->
       if key = key' then Some ((key,val)::l') else
         case alist_set l' key val of
           | Some res_l ->
             Some ((key',val')::res_l)
           | None -> None

(* Similar to the above, but using an alist instead of a map. *)
op [a,b] mlens_of_alist_key (key:a, getErr:Monad b, setErr:Monad (List (a * b))) : MLens (List (a * b),b) =
   {mlens_get = (fn alist -> mapOptionDefault return getErr (assoc alist key)),
    mlens_set = (fn alist -> fn b ->
                   case alist_set alist key b of
                     | None -> setErr
                     | Some alist' -> return alist') }

(* The monadic lens for the ith element of a list. As with
   mlens_of_key, it is an error in both the get and the set if a list
   does not have an ith element. *)
op [a] mlens_of_list_index (i:Nat, getErr:Monad a, setErr:Monad (List a)) : MLens (List a, a) =
    {mlens_get = (fn l -> if i < length l then return (l @ i) else getErr),
     mlens_set = (fn l -> fn a ->
                    if i < length l then return (update (l,i,a)) else setErr)}

(* The monadic lens for the ith element from the end of a list. As with
   mlens_of_key and mlens_of_list_index, it is an error in both the get and the
   set if a list does not have an ith element from the end. *)
op [a] mlens_of_list_rindex (i:Nat, getErr:Monad a, setErr:Monad (List a)) : MLens (List a, a) =
    {mlens_get = (fn l -> if i < length l then return (l @ (length l - i)) else getErr),
     mlens_set = (fn l -> fn a ->
                    if i < length l then return (update (l,length l - i,a)) else setErr)}

(* The monadic lens for the first element of a pair. Note that this is a
standard lens, so there are no errors. *)
op [a,b] mlens_for_proj1 : MLens (a * b, a) =
    {mlens_get = (fn tup -> return tup.1),
     mlens_set = (fn tup -> fn a -> return (a, tup.2))}

(* The monadic lens for an Option type; it is an error to get or set a "None" *)
op [a] mlens_for_option (getErr : Monad a, setErr : Monad (Option a)) : MLens (Option a, a) =
    {mlens_get = (fn opt ->
                    case opt of
                      | Some a -> return a
                      | None -> getErr),
     mlens_set = (fn opt -> fn a ->
                    case opt of
                      | Some _ -> return (Some a)
                      | None -> setErr)}

(* Turn a computation that returns a monadic lens into a monadic lens, where the
   "get" and "set" functions first perform the computation and then apply the
   corresponding function in the returned monadic lens *)
op [a,b] mlens_of_computation (m: Monad (MLens (a, b))) : MLens (a,b) =
  {mlens_get = fn a -> {l <- m; l.mlens_get a},
   mlens_set = fn b -> fn a -> {l <- m; l.mlens_set b a}}


(* FIXME: prove the subtyping constraints! *)

end-spec
