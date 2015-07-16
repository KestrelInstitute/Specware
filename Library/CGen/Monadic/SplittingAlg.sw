(* Splitting Algebras (FIXME: documentation) *)

SplittingAlg qualifying spec
  import /Library/Structures/Data/Monad/CPO

  (***
   *** Splittings
   ***)

  (* A splitting is an abstract representation of a portion of an entity that
  can be "split" in two, zero or more times. The entire entity (with no
  splitting) is represented by the empty list, and if w represents some portion
  of the entity then SplitL :: w and SplitR:: w, respectively, represent the
  "left half" and the "right half" of the result of splitting the w portion. *)
  (* FIXME: make a metaphor with binary space partitions *)
  type SplittingLetter = | SplitL | SplitR
  type Splitting = List SplittingLetter

  (* We order splitting spl1 before spl2 iff spl1 represents a sub-portion of
  what spl2 represents. This can be decided by testing whether spl2 is a suffix
  of spl1 *)
  op splitting_leq : PartialOrder Splitting =
  (fn (spl1, spl2) ->
     spl1 = spl2 ||
     (case spl1 of
        | [] -> false
        | _ :: spl1' -> splitting_leq (spl1', spl2)))

  (* The splitting that represents all of an entity *)
  op splitting_unity : Splitting = []

  (* Any splitting is a sub-portion of unity *)
  theorem leq_splitting_unity is
    fa (spl) splitting_leq (spl, splitting_unity)

  (* Two splittings are compatible iff they represent non-overlapping portions;
  i.e., iff they are incomparable w.r.t. the above partial order *)
  op splittings_compatible? (spl1: Splitting, spl2: Splitting) : Bool =
    ~(splitting_leq (spl1, spl2)) && ~(splitting_leq (spl2, spl1))

  (* Two splittings are combinable iff their two portions can be combined into a
  whole; i.e., iff they are the left and right splits of the same splitting *)
  op splittings_combinable? (spl1: Splitting, spl2: Splitting) : Bool =
    case (spl1, spl2) of
      | (SplitL :: spl1', SplitR :: spl2') -> spl1' = spl2'
      | (SplitR :: spl1', SplitL :: spl2') -> spl1' = spl2'
      | _ -> false

  (* Combine two combinable splittings *)
  op combine_splittings (spl1: Splitting, spl2: Splitting |
                           splittings_combinable? (spl1,spl2)) : Splitting =
    case (spl1, spl2) of
      | (SplitL :: spl1', SplitR :: spl2') -> spl1'
      | (SplitR :: spl1', SplitL :: spl2') -> spl1'
      | _ -> []


  (***
   *** Lists of Splittings
   ***)

  (* A splitting is compatible with a list iff it is compatible with each
  element of the list *)
  op splitting_compatible_with_list? (spl: Splitting,
                                      spls: List Splitting) : Bool =
    forall? (fn spl' -> splittings_compatible? (spl, spl')) spls

  (* Whether a splitting can be combined with some element of a list *)
  op splitting_combinable_with_list? (spl: Splitting,
                                      spls: List Splitting) : Bool =
  exists? (fn spl' -> splittings_combinable? (spl, spl')) spls

  (* Combine a splitting with a list of splittings *)
  op combine_splitting_with_list (spl: Splitting, spls: List Splitting |
                                  splitting_combinable_with_list? (spl, spls)) : List Splitting =
    case spls of
      | [] -> [] (* This case cannot actually happen *)
      | spl'::spls' ->
        if splittings_combinable? (spl, spl') then
          combine_splittings (spl, spl') :: spls'
        else
          spl' :: combine_splitting_with_list (spl, spls')

  (* combine_splitting_with_list yields a list of the same size as the input *)
  theorem combine_splitting_with_list_length is
    fa (spl,spls)
      splitting_combinable_with_list? (spl, spls) =>
      length (combine_splitting_with_list (spl, spls)) = length spls

  (* A splitting is "in" a splitting set iff the portion of an entity
  represented by the splitting is contained in the portion represented by the
  splitting set. This is essentially an extension of the splitting_leq partial
  order. *)
  op splitting_in? (spl: Splitting, spls: List Splitting) : Bool =
    exists? (fn spl' -> splitting_leq (spl, spl')) spls

  (* Combining a splitting with a list preserves splitting_in *)
  theorem combine_splitting_in? is
    fa (spl,spl',spls)
      splitting_combinable_with_list? (spl',spls) =>
      splitting_in? (spl, spl'::spls) <=>
        splitting_in? (spl, combine_splitting_with_list (spl', spls))


  (***
   *** Splitting Sets
   ***)

  (* A splitting multiset is a list of zero or more splittings that is in
  canonical form, meaning the list cannot be simplified by combining two
  splittings. We call such a structure a splitting multiset rather than a
  splitting set because the splittings in a splitting multiset are not required
  to be compatible with each other, meaning that, intuitively, a splitting
  multiset could represent some duplication of the portions of a splittable
  entity. For example, a splitting multiset could contain two copies of the
  "left half" of an entity. Splitting multisets that do not contain such
  duplication are "consistent", and are called splitting sets. *)
  op canonical_splitting_list? (spls : List Splitting) : Bool =
    case spls of
      | [] -> true
      | spl :: spls' ->
        ~(splitting_combinable_with_list? (spl, spls')) &&
        canonical_splitting_list? spls'
  type SplittingMultiSet = { l : List Splitting | canonical_splitting_list? l }

  (* Canonicalize a splitting set; this is inductive in the size of the list *)
  op canonicalize_splitting_list (spls : List Splitting) : SplittingMultiSet =
    case spls of
      | [] -> []
      | spl::spls' ->
        let spls'' = canonicalize_splitting_list spls' in
        if splitting_combinable_with_list? (spl, spls'') then
          canonicalize_splitting_list (combine_splitting_with_list (spl, spls'))
        else
          spl::spls''

  (* Add a splitting to a splitting set, maintaining canonicity *)
  op splitting_set_add (spl: Splitting, splset: SplittingMultiSet) : SplittingMultiSet =
    canonicalize_splitting_list (spl::splset)

  (* Combine two splitting sets *)
  op combine_splitting_sets (splset1: SplittingMultiSet,
                             splset2: SplittingMultiSet) : SplittingMultiSet =
    case splset1 of
      | [] -> splset2
      | spl1 :: splset1' ->
        splitting_set_add (spl1, combine_splitting_sets (splset1', splset2))

  (* The splitting set partial order intuitively is the notion of sub-portion *)
  op splitting_set_leq : PartialOrder SplittingMultiSet =
  (fn (splset1, splset2) ->
   forall? (fn spl1 -> splitting_in? (spl1, splset2)) splset1)

  (* The splitting set representing all of an entity *)
  op splitting_set_unity : SplittingMultiSet = []

  (* A splitting set is consistent iff it is no greater than unity *)
  op splitting_set_consistent? (splset: SplittingMultiSet) : Bool =
    splitting_set_leq (splset, splitting_set_unity)

  (* The type of consistent splitting sets *)
  type SplittingSet = { s: SplittingMultiSet | splitting_set_consistent? s }


  (***
   *** Splitting Expressions
   ***)

  (* A splitting expression is a splitting with an optional variable,
  represented as a natural number, that quantifies over suffixes *)
  type SplExpr = Splitting * Option Nat

  (* We can only compare splitting expressions with the same suffix, since
  variables could be instantiated to anything. The only exception is unity,
  which is always greater than anything else. *)
  op splexpr_leq : PartialOrder SplExpr =
    fn (sexpr1, sexpr2) ->
      sexpr2 = (splitting_unity, None) ||
      (splitting_leq (sexpr1.1, sexpr2.1) && sexpr1.2 = sexpr2.2)

  (* A variable assignment assigns a splitting to each variable *)
  type SplAssign = Nat -> Splitting

  (* Instantiate a splitting expression using a variable assignment *)
  op instantiate_splexpr (asgn: SplAssign) (sexpr: SplExpr) : Splitting =
    sexpr.1 ++ (case sexpr.2 of
                  | None -> []
                  | Some n -> asgn n)

  (* splexpr_leq holds iff all instantiations satisfy splitting_leq *)
  theorem splexpr_leq_instantiate is
    fa (sexpr1,sexpr2)
      splexpr_leq (sexpr1,sexpr2) <=>
        (fa (asgn) splitting_leq (instantiate_splexpr asgn sexpr1,
                                  instantiate_splexpr asgn sexpr2))

  (* Two splitting expressions are combinable iff their splittings are
  combinable and their suffixes are equal *)
  op splexprs_combinable? (sexpr1: SplExpr, sexpr2: SplExpr) : Bool =
    (splittings_combinable? (sexpr1.1, sexpr2.1) && sexpr1.2 = sexpr2.2)

  (* Two splitting exprs are combinable iff all instantiations are *)
  theorem splexpr_combinable_instantiate is
    fa (sexpr1,sexpr2)
      splexprs_combinable? (sexpr1,sexpr2) <=>
        (fa (asgn) splittings_combinable?
           (instantiate_splexpr asgn sexpr1,
            instantiate_splexpr asgn sexpr2))

  (* Combine two combinable splittings *)
  op combine_splexprs (sexpr1: SplExpr, sexpr2: SplExpr |
                         splexprs_combinable? (sexpr1,sexpr2)) : SplExpr =
    (combine_splittings (sexpr1.1, sexpr2.1), sexpr1.2)

  (* Combining splitting expressions commutes with instantiation *)
  theorem splexpr_leq_instantiate is
    fa (sexpr1,sexpr2)
      splexprs_combinable? (sexpr1,sexpr2) =>
      (fa (asgn)
         instantiate_splexpr asgn (combine_splexprs (sexpr1, sexpr2))
         =
         combine_splittings (instantiate_splexpr asgn sexpr1,
                             instantiate_splexpr asgn sexpr2))


  (***
   *** Lists of Splitting Expressions
   ***)

  (* Whether a splitting expr can be combined with some element of a list *)
  op splexpr_combinable_with_list? (spl: SplExpr, spls: List SplExpr) : Bool =
  exists? (fn spl' -> splexprs_combinable? (spl, spl')) spls

  (* Combine a splitting expr with a list of splitting exprs *)
  op combine_splexpr_with_list (spl: SplExpr, spls: List SplExpr |
                                  splexpr_combinable_with_list? (spl, spls)) : List SplExpr =
    case spls of
      | [] -> [] (* This case cannot actually happen *)
      | spl'::spls' ->
        if splexprs_combinable? (spl, spl') then
          combine_splexprs (spl, spl') :: spls'
        else
          spl' :: combine_splexpr_with_list (spl, spls')

  (* combine_splexpr_with_list yields a list of the same size as the input *)
  theorem combine_splexpr_with_list_length is
    fa (spl,spls)
      splexpr_combinable_with_list? (spl, spls) =>
      length (combine_splexpr_with_list (spl, spls)) = length spls

  (* Whether a splitting expression is "in" a list of splitting expressions *)
  op splexpr_in? (spl: SplExpr, spls: List SplExpr) : Bool =
    exists? (fn spl' -> splexpr_leq (spl, spl')) spls

  (* Combining a splitting with a list preserves splitting_in *)
  theorem combine_splexpr_in? is
    fa (spl,spl',spls)
      splexpr_combinable_with_list? (spl',spls) =>
      splexpr_in? (spl, spl'::spls) <=>
        splexpr_in? (spl, combine_splexpr_with_list (spl', spls))


  (***
   *** Splitting Set Expressions
   ***)

  (* A splitting set expression is a canonical list of splitting expressions *)
  op canonical_splexpr_set? (spls : List SplExpr) : Bool =
    case spls of
      | [] -> true
      | spl :: spls' ->
        ~(splexpr_combinable_with_list? (spl, spls')) &&
        canonical_splexpr_set? spls'
  type SplSetExpr = { l : List SplExpr | canonical_splexpr_set? l }

  (* Canonicalize a splitting expression set *)
  op canonicalize_splexpr_list (spls : List SplExpr) : SplSetExpr =
    case spls of
      | [] -> []
      | spl::spls' ->
        let spls'' = canonicalize_splexpr_list spls' in
        if splexpr_combinable_with_list? (spl, spls'') then
          canonicalize_splexpr_list (combine_splexpr_with_list (spl, spls'))
        else
          spl::spls''

  (* Add a splitting expression to a set, maintaining canonicity *)
  op splexpr_set_add (spl: SplExpr, splset: SplSetExpr) : SplSetExpr =
    canonicalize_splexpr_list (spl::splset)

  (* Combine two splitting expression sets *)
  op combine_splexpr_sets (splset1: SplSetExpr,
                             splset2: SplSetExpr) : SplSetExpr =
    case splset1 of
      | [] -> splset2
      | spl1 :: splset1' ->
        splexpr_set_add (spl1, combine_splexpr_sets (splset1', splset2))

  (* The splitting expression set partial order *)
  op splexpr_set_leq : PartialOrder SplSetExpr =
  (fn (splset1, splset2) ->
   forall? (fn spl1 -> splexpr_in? (spl1, splset2)) splset1)

  (* The splitting expression set representing all of an entity *)
  op splexpr_set_unity : SplSetExpr = []

  (* A splitting expression set is consistent iff it is no greater than unity *)
  op splexpr_set_consistent? (splset: SplSetExpr) : Bool =
    splexpr_set_leq (splset, splexpr_set_unity)


end-spec
