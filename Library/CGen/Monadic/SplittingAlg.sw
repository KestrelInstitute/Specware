(* Splitting Algebras (FIXME: documentation) *)

S = SplittingAlg qualifying spec
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
  op splitting_leq : CPO.PartialOrder Splitting =
  (fn (spl1, spl2) ->
     spl1 = spl2 ||
     (case spl1 of
        | [] -> false
        | _ :: spl1' -> splitting_leq (spl1', spl2)))

  (* Two splittings are compatible iff they represent non-overlapping portions;
  i.e., iff they are incomparable w.r.t. the above partial order *)
  op splittings_compatible? (spl1: Splitting, spl2: Splitting) : Bool =
    ~(splitting_leq (spl1, spl2)) && ~(splitting_leq (spl2, spl1))

  (* A splitting is compatible with a list iff it is compatible with each
  element of the list *)
  op splitting_compatible_with_list? (spl: Splitting,
                                      spls: List Splitting) : Bool =
    forall? (fn spl' -> splittings_compatible? (spl, spl')) spls

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

  (* Whether a splitting can be combined with some element of a list *)
  op splitting_combinable_with_list? (spl: Splitting,
                                      spls: List Splitting) : Bool =
  exists? (fn spl' -> splittings_combinable? (spl, spl')) spls


  (***
   *** Fragments
   ***)

  (* A fragment represents some portion of a splittable entity; e.g., a fragment
  might contain the left split and also the right split of the right split of an
  entity. Fragments are represented as lists of splitting words which are all
  compatible, since a portion of an object cannot contain the same sub-portion
  multiple times. Additionally, we require fragments to be in a canonical form,
  where any sub-portions that could potentially be combined are. *)
  op valid_fragment? (spls : List Splitting) : Bool =
    case spls of
      | [] -> true
      | spl :: spls' ->
        splitting_compatible_with_list? (spl, spls') &&
        ~(splitting_combinable_with_list? (spl, spls')) &&
        valid_fragment? spls'
  type Fragment = { l : List Splitting | valid_fragment? l }

  (* A splitting is "in" a fragment iff the portion of an entity represented by
  the splitting is contained in the portion represented by the fragment. This is
  essentially an extension of the splitting_leq partial order. *)
  op splitting_in_fragment? (spl: Splitting, frag: Fragment) : Bool =
    exists? (fn spl' -> splitting_leq (spl, spl')) frag

  (* The fragment partial order intuitively is the notion of sub-portion *)
  op fragment_leq : CPO.PartialOrder Fragment =
  (fn (frag1, frag2) ->
   forall? (fn spl1 -> splitting_in_fragment? (spl1, frag2)) frag1)

  (* Combine a splitting with a fragment *)
  op combine_splitting_with_fragment (spl: Splitting, frag: Fragment |
                                        splitting_compatible_with_list? (spl, frag)) : Fragment =
  case frag of
    | [] -> [spl]
    | spl' :: frag' ->
      if splittings_combinable? (spl, spl') then
        combine_splittings (spl, spl') :: frag'
      else
        spl' :: combine_splitting_with_fragment (spl, frag')

  (* Two fragments are compatible iff they are pointwise compatible *)
  op fragments_compatible? (frag1: Fragment, frag2: Fragment) : Bool =
    forall? (fn spl1 -> splitting_compatible_with_list? (spl1, frag2)) frag1

  (* Combine two compatible fragments *)
  op combine_fragments (frag1: Fragment, frag2: Fragment |
                          fragments_compatible? (frag1, frag2)) : Fragment =
    case frag1 of
      | [] -> frag2
      | spl1 :: frag1' ->
        combine_splitting_with_fragment (spl1,
                                         combine_fragments (frag1', frag2))


  (***
   *** Fragment Terms
   ***)

  type RawFragmentTerm =
      | FragmentTermNone
      | FragmentTermSplitting Splitting
      | FragmentTermCombine RawFragmentTerm * RawFragmentTerm

end-spec
