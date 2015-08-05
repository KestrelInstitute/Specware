OptLens qualifying spec
  import /Library/General/OptionExt
  import Lens

(* Option lenses are like lenses (see Lens.sw), but where the getter and setter
   functions can fail, returning None. Stated differently, option lenses are
   monadic lenses (see MLens.sw) where the monad is Option. The option lens laws
   are:

     {b <- get a; set a b}       = {get a; Some a}
     {a' <- set a b; get a'}     = {set a b; Some b}
     {a' <- set a b1; set a' b2} = set a b2

   These are almost the same as the normal lens laws: rule 1 says that getting
   the value of a and then setting this value to itself is a essentially no-op;
   however, the read itself could fail, so it remains in the simpler right-hand
   side. Similarly, rule 2 says that setting a value and then getting it again
   just returns the value that was set; again, the setting remains on the
   right-hand side, since it could fail. Finally, rule 3 says that setting
   erases any previous setting. *)

(* The "raw" type of monadic lenses, without the laws *)
type RawOptLens (a,b) = {optlens_get : a -> Option b,
                         optlens_set : a -> b -> Option a }

(* The monadic lens laws *)
op [a,b] satisfies_get_put_opt (l:RawOptLens (a,b)) : Bool =
  fa (a) {b <- l.optlens_get a; l.optlens_set a b} = {l.optlens_get a; Some a}
op [a,b] satisfies_put_get_opt (l:RawOptLens (a,b)) : Bool =
  fa (a,b)
    {a' <- l.optlens_set a b; l.optlens_get a'} =
    {a' <- l.optlens_set a b; Some b}
op [a,b] satisfies_put_put_opt (l:RawOptLens (a,b)) : Bool =
  fa (a,b1,b2)
    {a' <- l.optlens_set a b1; l.optlens_set a' b2} = l.optlens_set a b2

(* The complete type of monadic lenses *)
type OptLens (a,b) =
  { l : RawOptLens (a,b) |
     satisfies_get_put_opt l && satisfies_put_get_opt l && satisfies_put_put_opt l }

(* Compose two monadic lenses *)
op [a,b,c] optlens_compose (l1 : OptLens (a,b), l2 : OptLens (b,c)) : OptLens (a,c) =
   {optlens_get = (fn a -> {b <- l1.optlens_get a; l2.optlens_get b}),
    optlens_set = (fn a -> fn c ->
                   {b <- l1.optlens_get a;
                    b_new <- l2.optlens_set b c;
                    l1.optlens_set a b_new})}

(* Separation of lenses: each write commutes with the other lens's operations *)
op [a,b,c] optlens_separate? (l1: OptLens (a,b), l2: OptLens (a,c)) : Bool =
  (* l1's get commutes with l2's set *)
  (fa (a,c)
     {b <- l1.optlens_get a; l2.optlens_set a c; Some b} =
     {a' <- l2.optlens_set a c; l1.optlens_get a'}) &&
  (* l2's get commutes with l1's set *)
  (fa (a,b)
     {c <- l2.optlens_get a; l1.optlens_set a b; Some c} =
     {a' <- l1.optlens_set a b; l2.optlens_get a'}) &&
  (* The two sets commute *)
  (fa (a,b,c)
     {a' <- l1.optlens_set a b; l2.optlens_set a c} =
     {a' <- l2.optlens_set a c; l1.optlens_set a b})

  (* Build an option lens out of a lens *)
  op [a,b] opt_lens_of_lens (l: Lens (a,b)) : OptLens (a,b) =
    {optlens_get = fn a -> Some (l.lens_get a),
     optlens_set = fn a -> fn b -> Some (l.lens_set a b)}

  (* The option lens for an option type *)
  op [a] option_opt_lens : OptLens (Option a, a) =
    {optlens_get = fn opt -> opt,
     optlens_set = fn opt -> fn a -> Some (Some a)}

  (* The option lenses that look at the head and the tail, respectively, of a
  non-empty list. Both fail for empty lists. *)
  op [a] list_head_opt_lens : OptLens (List a, a) =
    {optlens_get = (fn l ->
                      case l of
                        | [] -> None
                        | x::_ -> Some x),
     optlens_set = (fn l -> fn x' ->
                      case l of
                        | [] -> None
                        | x::l' -> Some (x'::l'))}
  op [a] list_tail_opt_lens : OptLens (List a, List a) =
    {optlens_get = (fn l ->
                      case l of
                        | [] -> None
                        | _::l' -> Some l'),
     optlens_set = (fn l -> fn l' ->
                      case l of
                        | [] -> None
                        | x::_ -> Some (x::l'))}

end-spec
