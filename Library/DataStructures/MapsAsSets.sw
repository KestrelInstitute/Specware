% refinement of (finite) maps in terms of (finite) sets
Map qualifying
spec

  % we refine maps by means of sets: a map can be represented by a set of
  % pairs of type (a,b) such that no two pairs in the set have the same first
  % component but different second components (this is essentially the usual
  % set-theoretic definition)

  % clearly, there exist other ways to refine sets

  % first, we import sets

  import Sets

  % a map is a set of pairs (i.e., a binary relation) satisfying the
  % "functional requirement" (i.e., no element is mapped to different
  % elements)

  type Map(a,b) = {s : Set(a * b) |
                   fa(x,y1,y2) (x,y1) in? s & (x,y2) in? s => y1 = y2}

  % we (re-)define the operations on maps to operate on the
  % sets just defined and to be constructive

  % apply is defined by going through the set (by means of set_fold),
  % and looking for a pair whose first component is the given argument:
  % if one is found, the second component is returned (wrapped with
  % Some); if not, None is returned

  op [a,b] apply (m: Map(a,b)) (x:a) : Option b = 
    set_fold None
             (fn (result, (x1,y1)) -> if x = x1 then Some y1 else result)
             m

  op [a,b] map_apply (m : Map(a,b)) (b_default : b) (x : a) : b =
    set_fold b_default
             (fn (result, (x1,y1)) -> if x = x1 then y1 else result)
             m

  % the empty map is represented by the empty set of pairs
  op [a,b] empty_map : Map(a,b) = empty_set

  % there are two cases for updating a map: if a pair with the given
  % first component does not belong to the map, a suitable pair is inserted
  % into the set; otherwise, we go though the set (by means of set_fold)
  % reconstructing it the way it was, except for the pair with the given
  % first component

  op [a,b] update (m: Map(a,b)) (x:a) (y:b) : Map(a,b) =
    if (apply m x = None) then
      set_insert((x,y),m)
    else
      set_fold empty_map
               (fn (result_map,(x1,y1)) ->
                 if x1 = x then
                   set_insert((x,y),result_map)
                 else
                   set_insert((x1,y1),result_map))
               m

  % Remove the binding for key (if any).
  op [a,b] remove (m:Map(a,b)) (x:a) : Map(a,b) = 
    if (apply m x = None) then
      m  % No binding, so do nothing (could drop this case, but it may be faster to keep it)
    else
      set_fold empty_map
               (fn (result_map,(x1,y1)) ->
                  if x1 = x then
                    result_map % This is the pair to be removed.  Skip it.
                  else
                    set_insert((x1,y1),result_map)) % Copy everything else.
               m

  op [a,b] singletonMap (x:a) (y:b) : Map(a,b) = (update (empty_map) x y)

  op [a,b] domain (m : Map(a,b)) : Set a =
    set_fold empty_set 
             (fn (dom,(x1,y1))-> set_insert(x1, dom))
             m

  op [a,b] range (m:Map(a,b)) : Set b =
    set_fold empty_set
             (fn (range,(x1,x2))-> set_insert(x2, range))
             m

  % TODO: This doesn't seem well-formed (see the restrictions on
  % set_fold).  In particular, in what order should the elements of
  % the domain list appear?
  op [a,b] domainToList(m: Map(a,b)): List a =
    set_fold [] 
             (fn (dom, (x1,x2))-> x1 :: dom)
             m

  % TODO: This doesn't seem well-formed (see the restrictions on
  % set_fold).  In particular, in what order should the elements of
  % the range list appear?
  op [a,b] rangeToList (m: Map(a,b)): List b =
    set_fold []
             (fn (range, (x1,x2))-> x2 :: range)
             m

  op [a,b] size (m : Map(a,b)) : Nat = size (domain m)

  op [a,b] total? (s:Set a, m:Map(a,b)): Boolean = (s subset domain m)

  op [a,b] TMApply(m:Map(a,b), x:a | x in? domain(m)): b =
    (case apply m x of
      | Some z -> z)

  op [a,b] mapFrom(s: Set a, f: a -> b): Map(a,b) =
    set_fold empty_map (fn (m, x) -> update m x (f x)) s

  op [a,b] mapUpdateSet(m: Map(a,b), s: Set a, f: a -> b): Map(a,b) =
     set_fold m (fn (m, x) -> update m x (f x)) s

  op [Dom,Cod,a] foldi (f : (Dom * Cod * a -> a)) (acc:a) (m : Map (Dom,Cod)) : a =
    set_fold acc
             (fn (acc,(x,y)) -> f(x,y,acc))
             m

%TODO The Isabelle obligations don't seem to include the crucial information from the type Map.
proof Isa Map__apply_Obligation_subtype
  sorry
end-proof

%TODO The Isabelle obligations don't seem to include the crucial information from the type Map.
proof Isa Map__map_apply_Obligation_subtype
  sorry
end-proof

proof Isa Map__empty_map_Obligation_subtype
  apply(simp add: Map__Map__subtype_pred_def  Set__empty_set)
end-proof

proof Isa Map__update_Obligation_subtype
  sorry
end-proof

proof Isa Map__update_Obligation_subtype0
  sorry
end-proof

proof Isa Map__update_Obligation_subtype1
  sorry
end-proof

proof Isa Map__update_Obligation_subtype2
  sorry
end-proof

proof Isa Map__remove_Obligation_subtype
  sorry
end-proof

proof Isa Map__remove_Obligation_subtype0
  sorry
end-proof

proof Isa Map__domain_Obligation_subtype
  sorry
end-proof

proof Isa Map__range_Obligation_subtype
  sorry
end-proof

proof Isa Map__domainToList_Obligation_subtype
  sorry
end-proof

proof Isa Map__rangeToList_Obligation_subtype
  sorry
end-proof

proof Isa Map__mapFrom_Obligation_subtype
  sorry
end-proof

proof Isa Map__mapUpdateSet_Obligation_subtype
  sorry
end-proof

proof Isa Map__foldi_Obligation_subtype
  sorry
end-proof


end-spec

