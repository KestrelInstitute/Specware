(* Copyright 2015 Kestrel Institute. See file LICENSE for license details *)

% TODO can we replace this with something in Library/Structures/Data/Maps?  Maybe Simple.sw?

(*
                    Specification of Finite Maps

    empty_map and update could be constructors,
    but we want implementations that do destructive update
    to keep the size linear in the domain.
*)

Maps = Map qualifying spec
  import Sets
  type Map(a,b)

  % a map from a to b yields, when applied to an element of type a,
  % an element of type b if defined on it, otherwise no element:
  % this is modeled by means of the Option polymorphic type

  % if two maps return the same result on each element of type a,
  % they are the same map

  op [a,b] apply : Map(a,b) -> a -> Option b
  axiom map_equality is [a,b]
        fa(m1:Map(a,b), m2:Map(a,b)) (fa(x) apply m1 x = apply m2 x) => m1 = m2

  % the empty map is undefined over all elements of type a

  op [a,b] empty_map :  Map(a,b)
  axiom empty_map is [a,b]
        fa(x:a) apply (empty_map: Map(a,b)) x = None

 % This one is like apply but does not return an option.  Instead, it returns the given default element to indicate no match.
 % TODO map_apply is not a good name for this (maybe apply_present or apply_default?).
 % This op previously was given meaning by the axiom map_apply_def.  I changed it to just be a definition. -Eric
  op [a,b] map_apply (m: Map(a,b)) (null_elt:b) (x:a) : b =
    case (apply m x) of
    | Some y -> y
    | None   -> null_elt

  % update is used to define the map to return a certain element of
  % type b when applied over a certain element of type a; if the map
  % was undefined on that element of type a, now it is defined; if
  % instead it was already defined, the previous element of type b
  % is "overwritten"

  op [a,b] update : Map(a,b) -> a -> b -> Map(a,b)
  axiom update is
        fa(m,x,y,z) apply (update m x y) z =
                    (if z = x then Some y else apply m z)

  op [a,b] remove (m : Map (a,b)) (key : a) : Map (a,b)
  axiom remove is [a,b]
    fa(m: Map(a,b), key1 : a, key2 : a)
      apply (remove m key1) key2 =
      (if key1 = key2 then None else apply m key2)

  theorem update_of_remove_same is [a,b]
    fa(m: Map(a,b), key : a, val: b)
      update (remove m key) key val = update m key val

  theorem remove_of_update_same is [a,b]
    fa(m: Map(a,b), key : a, val: b)
      (remove (update m key val) key) = (remove m key)

  theorem remove_of_empty is [a,b]
    fa(key : a)
      (remove (empty_map : Map(a,b)) key) = empty_map

  theorem remove_of_update_both is [a,b]
    fa(m: Map(a,b), key1 : a, key2 : a, val: b)
      remove (update m key1 val) key2 = (if key1 = key2 then (remove m key2) else (update (remove m key2) key1 val))

  theorem update_of_update_both is [a,b]
    fa(m: Map(a,b), keyone : a, keytwo : a, val1: b, val2 : b)
      update (update m keyone val1) keytwo val2 = (if keyone = keytwo then (update m keytwo val2) else (update (update m keytwo val2) keyone val1))

  %% TODO: why can't I do cut_tac if the vars in the theorem are key1 and key2?
  theorem remove_of_remove_both is [a,b]
    fa(m: Map(a,b), keyone : a, keytwo : a)
      remove (remove m keyone) keytwo = remove (remove m keytwo) keyone

    

  op [a,b] singletonMap (x:a) (y:b) : Map(a,b) = update (empty_map) x y

  % this induction axiom constrains maps to be finite: any finite map can be
  % obtained by suitable successive applications of update to empty_map

  axiom map_induction is [a,b]
    fa (p : Map(a,b) -> Bool)
      p empty_map &&
      (fa(m,x,y) p m => p (update m x y))
      =>
      (fa(m) p m)

% TODO could use a definedOn? helper predicate
%TODO define using a fold?
  op [a,b] domain: Map(a,b) -> Set a
  axiom map_domain is
     [a,b] fa(m:Map(a,b), x:a)( (x in? domain(m)) = (ex(z:b)(apply m x = Some z)))

  theorem domain_of_empty is [a, b]
    domain (empty_map :  Map(a,b)) = empty_set

%TODO define using a fold?
  op [a,b] range : Map(a,b) -> Set b
  axiom map_range is
     [a,b] fa(m:Map(a,b), z:b)( z in? range(m) = (ex(x:a)(apply m x = Some z)))

  theorem range_of_empty is [a, b]
    range (empty_map :  Map(a,b)) = empty_set

  %% Special case when key is not already in the map (otherwise, you
  %% may have to delete from the range the value that key previously
  %% mapped to, unless there is another key that also maps to that
  %% value - ugh).
  theorem range_of_update_special_case is [a,b]
    fa(m:Map(a,b), key:a, val:b)
      ~(key in? domain m) => range (update m key val) = set_insert(val, range m)

  theorem update_of_apply_same is [a,b]
    fa(m: Map(a,b), key : a)
      key in? domain m =>
      update m key (case (apply m key) of | Some val -> val) = m

% TODO could use a definedOn? helper predicate.  Or just check whether s is a subset of the domain of the map?
  op [a,b] total? (s:Set a, m:Map(a,b)):Bool =
    fa(x:a) (x in? s => (ex(z:b) apply m x = Some z))

%TODO I guess we don't say how the elements in the list are sorted.
%just call domain and a generic setToList function?
  op [a,b] domainToList: Map(a,b) -> List a
  axiom map_domainToList is
     [a,b] fa(m:Map(a,b)) size(domain m) = length(domainToList m)
                     && (fa(x) (x in? domain(m)) = (x in? domainToList m))

%TODO constrain the length of rangeToList?  otherwise, this allows duplicates
  op [a,b] rangeToList: Map(a,b) -> List b
  axiom map_rangeToList is
     [a,b] fa(m:Map(a,b), z:b) (z in? range(m)) = (z in? rangeToList m)

  theorem rangeToList_of_empty_map is [a,b]
    rangeToList (empty_map:Map(a,b)) = []


 %TODO could also phrase in terms of insert and then prove that insert is either a no-op or insert_new
  theorem domain_update is [a,key]
    fa(m: Map(key,a), x: key, y: a)
      domain(update m x y) 
       = (if x in? domain m 
            then domain m 
          else set_insert_new(x, domain m))

  theorem domain_update2 is [a,key]
    fa(m: Map(key,a), x: key, y: a)
      domain(update m x y) = set_insert(x, domain m)

  theorem remove_does_nothing is [a,b]
    fa(m: Map(a,b), x: a)
      ~(x in? domain m) => (remove m x) = m

  theorem domain_of_remove is [a, b]
    fa(m:Map(a,b), key:a)
      domain (remove m key) = set_delete(key, domain m)


% who added this?
 % This op previously was given meaning by the axiom map_size.  I changed it to just be a definition. -Eric
  op [a,b] size (m:Map(a,b)) : Nat = size(domain m)

%  type TotalMap(a, b) = (Set(a) * Map(a,b) | total?)

  % Strips off the Some constructor.  Only works if the key is known to be in the domain of the map.
  % TODO: Just define using let, as proved equivalent below.
  op [a,b] TMApply(m:Map(a,b), x:a | x in? domain m): b =
    the(z:b)( apply m x = Some z)

  theorem TMApply_becomes_apply is [a,b]
    fa(m: Map(a,b), x:a)
      (x in? domain m) => (TMApply(m,x)) = (let Some y = (apply m x) in y)

  theorem totalmap_equality is [a,b]
    fa(m1: Map(a,b),m2: Map(a,b))
      ((domain m1 = domain m2) &&
       (fa(x) (x in? domain m1) => (TMApply(m1,x) = TMApply(m2,x))))
      => 
      m1 = m2
%% old (didn't seem to type check: what if x is not in the domain of m1 and/or m2?)
%%  axiom totalmap_equality is [a,b]
%%    fa(m1: Map(a,b),m2: Map(a,b)) (fa(x) TMApply(m1,x) = TMApply(m2,x)) => m1 = m2

  theorem TMApply_over_update is [a,b]
    fa(m: Map(a,b), x: a, y: b, z: a)
    z in? domain m => 
    (TMApply(update m x y, z) = (if x = z then y else TMApply(m, z)))

%%This version has a weaker hypothesis than TMApply_over_update.  TODO: Transition to using just this version?
  theorem TMApply_over_update2 is [a,b]
    fa(m: Map(a,b), x: a, y: b, z: a)
    ((z in? domain m) || (z = x)) =>
    (TMApply(update m x y, z) = (if x = z then y else TMApply(m, z)))

  %% Special case of TMApply_over_update for z=x (has no applicability conditions that must be proven).
  theorem TMApply_of_update_same is [a,b]
    fa(m: Map(a,b), x: a, y: b, z: a)
      TMApply(update m x y, x) = y

  %% Curried version of TMApply
  op [a,b] TMApplyC(m:Map(a,b)) (x:a | x in? domain m): b = TMApply(m, x)

  theorem TMApplyC_over_update is [a,b]
    fa(m: Map(a,b), x: a, y: b, z: a)
    z in? domain m => 
    TMApplyC (update m x y) z = (if x = z then y else TMApplyC m z)

% This is useful when refining to the single-threaded MapsAsVectors
% TODO: could this just be the identity function (later, in the refinements, it might have this definition in terms of set_fold)?
  op [a,b] copyMap(m:Map(a,b)):Map(a,b) =
     set_fold (empty_map)
              (fn(newm:Map(a,b),x: {x:a | x in? (domain m)})-> update newm x (TMApply(m,x)))
              (domain m)

%TODO these next theorems don't have much to do with the Map data structure:

 theorem map_map_inv is [a,b]
   fa(f: Bijection(a, b), f': b -> a, l: List b)
   inverse f = f' => map f (map f' l) = l
 
  theorem map_doubleton is [a,b]
    fa(f: a -> b,x:a,y:a) map f [x,y] = [f x,f y]

  theorem map_empty is [a,b]
    fa(f: a -> b) map f [] = []

 %TODO: Pull this into a helper spec, since now we have to repeat it in each implementation of Maps.
 % (Or don't, if eventually this will take the map as an argument and only require foldability over elements in the map.)
  op [a,b,acc] foldable? (f : (a * b * acc -> acc)) : Bool =
    fa(key1:a, val1:b, key2:a, val2:b, accval:acc)
      ~(key1 = key2) =>   %% Excludes the case of the same key twice with different values (can't happen).
      f(key1,val1,f(key2,val2,accval)) = f(key2,val2,f(key1,val1,accval))

 theorem Set_Map_foldable? is [a,b,acc]
  fa (f: acc * a -> acc) 
    Set.foldable? f => Map.foldable?(fn(x, y: b, result) -> f (result, x))

 theorem foldable?_helper is [a,b]
   fa(p : a * b -> Bool)
     foldable? (fn (key:a, val:b, accval:Bool) -> accval && p(key,val))

% TODO: Could allow f to be foldable only on the values in m, rather than in general.
  op [a,b,acc] foldi (f : ((a * b * acc -> acc) | foldable?))
                     (initialacc : acc)  
                     (m: Map (a,b)) : acc       
                     
  axiom map_foldi_empty is [a,b,acc]
    fa(f : ((a * b * acc -> acc) | foldable?), accval : acc)
      foldi f accval empty_map = accval

  %% TODO: Could we drop the remove here if we add an assumption that key is not in the domain of the map?  The remove may get in the way during proofs?
  axiom map_foldi_update is [a,b,acc]
    fa(f : ((a * b * acc -> acc) | foldable?), accval : acc, key : a, val : b, m : Map(a,b))
      foldi f accval (update m key val) = f(key, val, foldi f accval (remove m key))

  op [a,b] forall? (p : a * b -> Bool) (m: Map (a,b)) : Bool =
    foldi (fn (key,val,acc) -> acc && p(key,val))
          true
          m

  theorem forall?_of_update is [a,b]
    fa(p : a * b -> Bool, m : Map(a,b), key:a, val:b)
    forall? p (update m key val) = (forall? p (remove m key) && p(key,val))
    
  theorem forall?_of_remove is [a,b]
    fa(p : a * b -> Bool, m : Map(a,b), key:a)
      (forall? p m) => forall? p (remove m key)

  %% theorem forall?_of_update is [a,b]
  %%   fa(p : a * b -> Bool, m : Map(a,b), key:a, val:b)
  %%   (forall? p m && p(key,val)) => 
  %%   forall? p (update m key val)

  theorem use_forall? is [a,b]
    fa(p : a * b -> Bool, m : Map(a,b), key:a)
      (key in? domain m) && (forall? p m) => p(key,case (apply m key) of | Some val -> val)


  % This is due to the subtype (PosNat) on the values stored in the map.
  % If this is not defined, a declaration is added to the Isabelle translation:
  % Check all pairs in the map to ensure that the preds apply to the keys and values.
  op [a,b] Map_P (preda: a -> Bool, predb: b -> Bool) (m : Map(a,b)) : Bool =
    forall? (fn (key, val) -> preda key && predb val)
            m

  theorem Map_P_of_update is [a,b,acc]
    fa(preda: a -> Bool, predb: b -> Bool, m : Map(a,b), key:a, val:b)
      Map_P(preda, predb) (update m key val) =
      (preda key && predb val && Map_P(preda, predb) (remove m key))

  theorem Map_P_of_remove is [a,b,acc]
    fa(preda: a -> Bool, predb: b -> Bool, m : Map(a,b), key:a)
      Map_P(preda, predb) m =>
      Map_P(preda, predb) (remove m key)

  theorem use_Map_P is [a,b]
    fa(preda: a -> Bool, predb: b -> Bool, m : Map(a,b), key:a)
      (key in? domain m) && (Map_P(preda,predb) m) => preda key && predb (case (apply m key) of | Some val -> val)



  %% TODO: Prove or drop this:
  %% %% This one fits better with reasoning about fold
  %% theorem map_induction2 is [a,b]
  %%       fa (p : Map(a,b) -> Bool)
  %%          p empty_map &&
  %%          (fa(m,x,y) p(remove m x) => p(update m x y)) =>
  %%          (fa(m) p m)

  %% % TODO: using the name pred here caused a name clash?
  %% theorem mypred_of_fold is [a,b,acc]
  %%   fa(m : Map(a,b), acc : acc, f : ((a * b * acc -> acc) | foldable?), mypred : acc -> Bool)
  %%     (mypred(acc) && (fa(key:a,val:b, acc:acc) mypred acc => mypred (f(key,val,acc)))) =>
  %%     mypred (foldi f acc m)


  op [a,b,c,d] isoMap: Bijection(a,c) -> Bijection(b,d) -> Bijection(Map(a, b), Map(c, d)) =
    the (isoMap)
      fa(m: Map(a, b), iso_a: Bijection(a,c), iso_b: Bijection(b,d), x: a, y: Option b)
        (apply m x = y) <=> (apply (isoMap iso_a iso_b m) (iso_a x) = isoOption iso_b y)
    %% fn iso_elem1 -> fn iso_elem2 -> foldi (fn (x, y, new_m) -> update new_m (iso_elem1 x) (iso_elem2 y)) empty_map

  theorem isoMap_over_update is [a,b,c,d]
    fa(m: Map(a,b), x:a, y:b, iso_a: Bijection(a,c), iso_b: Bijection(b,d))
      isoMap iso_a iso_b (update m x y) = update (isoMap iso_a iso_b m) (iso_a x) (iso_b y)

  theorem isoMap_over_empty_map is [a,b,c,d]
    fa(iso_a: Bijection(a, c), iso_b: Bijection(b,d))
      isoMap iso_a iso_b (empty_map: Map(a,b)) = (empty_map: Map(c,d))


(******************************** The Proofs ********************************)

proof Isa Map__use_Map_P
  apply(simp add: Map__Map_P_def)
  apply(cut_tac key=key and m=m and p="\<lambda> (key,val) . preda key \<and> predb val" in Map__use_forall_p)
  apply(auto)
end-proof

proof Isa Map__use_forall_p
  apply(rule_tac P="key in? Map__domain m \<and> Map__forall_p p m" in mp)
  defer
  apply(force)
  apply(cut_tac p="\<lambda> (m:: ('a, 'b)Map__Map) .  key in? Map__domain m \<and> Map__forall_p p m \<longrightarrow> p (key, case Map__apply m key of Some val \<Rightarrow> val)" and m=m in Map__map_induction)
  apply(auto simp add: Map__domain_of_empty Set__empty_set Map__domain_update Set__set_insertion Set__set_insert_new_def Map__update Map__forall_p_of_update)
  apply(case_tac "x in? (Map__domain ma)", auto simp add: Map__remove_does_nothing)
  apply(cut_tac p=p and m="(Map__remove ma x)" and key=key and val=" case Map__apply ma key of Some val \<Rightarrow> val" in Map__forall_p_of_update)
  apply(cut_tac m="(Map__remove ma x)" and key=key in Map__update_of_apply_same)
  apply(auto simp add: Map__domain_of_remove Set__set_deletion)
  apply(metis Map__remove_of_update_both Map__update_of_apply_same) 
end-proof

proof Isa Map__domain_of_remove
  apply(rule Set__membership)
  apply(auto simp add: Map__remove Map__map_domain Set__set_deletion)
end-proof

proof Isa Map__domain_of_empty
  apply(rule Set__membership)
  apply(simp add:  Map__map_domain Set__empty_set Map__empty_map)
end-proof

proof Isa Map__Map_P_of_remove
  apply(simp add: Map__Map_P_def Map__forall_p_of_remove)
end-proof

proof Isa Map__forall_p_of_remove
  apply(case_tac "key in? Map__domain m")
  defer
  apply(force simp add: Map__remove_does_nothing)
  apply(cut_tac m="m" and p=p and key=key and val="(Map__TMApply(m,key))" in Map__forall_p_of_update)
  apply(auto simp add: Map__TMApply_becomes_apply Map__update_of_apply_same)
end-proof

proof Isa Map__update_of_apply_same
  apply(rule Map__map_equality, simp add: Map__update Map__remove)
  apply(auto simp add: Map__map_domain)
end-proof

proof Isa Map__remove_does_nothing
  apply(rule Map__map_equality)
  apply(auto simp add: Map__remove Map__map_domain)
end-proof

proof Isa Map__remove_of_update_both
  apply(rule Map__map_equality, simp add: Map__update Map__remove)
end-proof

proof Isa Map__update_of_update_both
  apply(rule Map__map_equality, simp add: Map__update Map__remove)
end-proof

proof Isa Set_Map_foldable_p
  by (auto simp add: Map__foldable_p_def Set__foldable_p_def)
end-proof

proof Isa Map__foldable_p_helper [simp]
  apply(simp add: Map__foldable_p_def)
  apply(metis)
end-proof

proof Isa Map__remove_of_remove_both
  apply(rule Map__map_equality, simp add: Map__update Map__remove)
end-proof

proof Isa Map__totalmap_equality
  apply(rule Map__map_equality)
  apply(auto simp add: Map__TMApply_becomes_apply)
  by (metis Map__map_domain not_Some_eq option.simps(5))
end-proof

proof isa Map__TMApply_over_update_Obligation_subtype
  apply(simp add: Map__domain_update2 Set__set_insertion)
end-proof

proof isa Map__TMApply_over_update
  apply(auto simp add: Map__TMApply_becomes_apply Map__domain_update2 Set__set_insertion Map__update)
end-proof

proof isa Map__TMApplyC_over_update_Obligation_subtype
  by (rule Map__TMApply_over_update_Obligation_subtype)
end-proof

proof isa Map__TMApplyC_over_update
  by (simp add: Map__TMApplyC_def Map__TMApply_over_update)
end-proof


proof isa Map__map_map_inv
  apply(simp add: map_map)
  by (metis Function__id__def Function__inverse_comp List.map.id)
end-proof

proof isa Map__domain_update
  apply(auto)
  apply(rule Set__membership)
  apply(simp add: Map__map_domain Map__update)
  apply(rule Set__membership)
  apply(simp add: Map__map_domain Map__update Set__set_insert_new_def Set__set_insertion)
end-proof

proof isa Map__domain_update2
  apply(rule Set__membership)
  apply(simp add: Map__map_domain Map__update)
  apply(simp add: Map__map_domain Map__update Set__set_insertion)
end-proof

proof Isa Map__isoMap_Obligation_the
  sorry
end-proof

proof Isa Map__isoMap_over_update
  sorry
end-proof

proof Isa Map__isoMap_over_empty_map
  apply (simp only: Map__isoMap_def)
  apply (rule_tac Q = "\<lambda>f. f iso_a iso_b Map__empty_map = Map__empty_map"
                  in the1I2,
         rule Map__isoMap_Obligation_the)
  apply (auto simp add: Option__isoOption_def)
  apply (drule_tac x=Map__empty_map in spec,
         rotate_tac -1, drule_tac x=iso_a in spec,
         rotate_tac -1, drule_tac x=iso_b in spec)
  apply (rule Map__map_equality, auto simp add: Map__empty_map)
  apply (rotate_tac -1, drule_tac x="(inv iso_a) xa" in spec,
         rotate_tac -1, drule_tac x=None in spec)
  apply (auto simp add: Function__f_inverse_apply)
end-proof

proof Isa TMApply_becomes_apply
  apply(simp add: Map__TMApply_def)
  apply(case_tac  "Map__apply m x")
  apply(simp_all add: Map__map_domain)
end-proof

proof isa TMApply_Obligation_the
  apply(case_tac "Map__apply m x")
  apply(auto)
  by (metis Map__map_domain option.distinct(1))
end-proof

proof isa Map__Map_P_Obligation_subtype
  apply(auto simp add: Map__foldable_p_def)
end-proof

proof Isa Map__map_induction2
  apply(rule Map__map_induction)
  apply(assumption)
  apply(simp add: Map__update_of_remove_same)
end-proof

proof Isa Map__update_of_remove_same
  apply(rule Map__map_equality, simp add: Map__update Map__remove)
end-proof

%% proof Isa Map__mypred_of_fold
%%   sorry
%% end-proof

proof Isa Map__forall_p_Obligation_subtype
  apply(auto simp add: Map__foldable_p_def)
end-proof

proof Isa Map__remove_of_empty
  apply(rule Map__map_equality)
  apply(simp add: Map__remove Map__empty_map)
end-proof


proof Isa Map__forall_p_of_update
  apply(cut_tac p="\<lambda> (m:: ('a, 'b)Map__Map) .  Map__forall_p p (Map__update m key val) = (Map__forall_p p (Map__remove m key) \<and> p (key, val))" and m=m in Map__map_induction)
  defer
  defer
  apply(assumption)
  apply(simp add: Map__forall_p_def Map__map_foldi_update Map__foldable_p_def Map__remove_of_empty Map__map_foldi_empty)
  apply(cut_tac f=" (\<lambda>(key, val, acc__v). acc__v \<and> p (key, val))" and m=" Map__empty_map" and key=key and val=val and accval=True in  Map__map_foldi_update)
  apply(simp add: Map__foldable_p_def)
  apply(metis)
  apply(simp add:  Map__remove_of_empty)
  apply(clarsimp)
  apply(case_tac "x=key")
  apply(simp add: Map__remove_of_update_same Map__forall_p_def)
  apply(auto)[1]
  apply(cut_tac f=" (\<lambda>(key, val, acc__v). acc__v \<and> p (key, val))" and m="(Map__update m key y)" and key=key and val=val and accval=True in  Map__map_foldi_update, force)
  apply(cut_tac f=" (\<lambda>(key, val, acc__v). acc__v \<and> p (key, val))" and m="m" and key=key and val=val and accval=True in  Map__map_foldi_update, force)
apply(auto simp add: Map__remove_of_update_same)[1]
  apply(cut_tac f=" (\<lambda>(key, val, acc__v). acc__v \<and> p (key, val))" and m="(Map__update m key y)" and key=key and val=val and accval=True in  Map__map_foldi_update, force)
  apply(cut_tac f=" (\<lambda>(key, val, acc__v). acc__v \<and> p (key, val))" and m="m" and key=key and val=val and accval=True in  Map__map_foldi_update, force)
apply(auto simp add: Map__remove_of_update_same)[1]
  apply(cut_tac f=" (\<lambda>(key, val, acc__v). acc__v \<and> p (key, val))" and m="(Map__update m key y)" and key=key and val=val and accval=True in  Map__map_foldi_update, force)
  apply(cut_tac f=" (\<lambda>(key, val, acc__v). acc__v \<and> p (key, val))" and m="m" and key=key and val=val and accval=True in  Map__map_foldi_update, force)
apply(auto simp add: Map__remove_of_update_same)[1]
  apply(cut_tac f=" (\<lambda>(key, val, acc__v). acc__v \<and> p (key, val))" and m="(Map__update m key y)" and key=key and val=val and accval=True in  Map__map_foldi_update, force)
  apply(cut_tac f=" (\<lambda>(key, val, acc__v). acc__v \<and> p (key, val))" and m="m" and key=key and val=val and accval=True in  Map__map_foldi_update, force)
apply(auto simp add: Map__remove_of_update_same)[1]
  apply(cut_tac f=" (\<lambda>(key, val, acc__v). acc__v \<and> p (key, val))" and m="(Map__update m key y)" and key=key and val=val and accval=True in  Map__map_foldi_update, force)
  apply(cut_tac f=" (\<lambda>(key, val, acc__v). acc__v \<and> p (key, val))" and m="m" and key=key and val=val and accval=True in  Map__map_foldi_update, force)

apply(auto simp add: Map__remove_of_update_same Map__forall_p_def)
  apply(cut_tac f=" (\<lambda>(key, val, acc__v). acc__v \<and> p (key, val))" and m="m" and key=key and val=val and accval=True in  Map__map_foldi_update, force)
  apply(cut_tac f=" (\<lambda>(key, val, acc__v). acc__v \<and> p (key, val))" and m="(Map__update m x y)" and key=key and val=val and accval=True in  Map__map_foldi_update, force)
apply(auto simp add: Map__remove_of_update_same)
  apply(cut_tac f=" (\<lambda>(key, val, acc__v). acc__v \<and> p (key, val))" and m="m" and key=key and val=val and accval=True in  Map__map_foldi_update, force)
  apply(cut_tac f=" (\<lambda>(key, val, acc__v). acc__v \<and> p (key, val))" and m="(Map__update m x y)" and key=key and val=val and accval=True in  Map__map_foldi_update, force)
apply(auto simp add: Map__remove_of_update_same)
  apply(cut_tac f=" (\<lambda>(key, val, acc__v). acc__v \<and> p (key, val))" and m="m" and key=key and val=val and accval=True in  Map__map_foldi_update, force)
  apply(cut_tac f=" (\<lambda>(key, val, acc__v). acc__v \<and> p (key, val))" and m="(Map__update m x y)" and key=key and val=val and accval=True in  Map__map_foldi_update, force)
apply(auto simp add: Map__remove_of_update_same)
  apply(cut_tac f=" (\<lambda>(key, val, acc__v). acc__v \<and> p (key, val))" and m="m" and key=key and val=val and accval=True in  Map__map_foldi_update, force)
  apply(cut_tac f=" (\<lambda>(key, val, acc__v). acc__v \<and> p (key, val))" and m="(Map__update m x y)" and key=key and val=val and accval=True in  Map__map_foldi_update, force)
apply(auto simp add: Map__remove_of_update_same)
  apply(cut_tac f=" (\<lambda>(key, val, acc__v). acc__v \<and> p (key, val))" and m="m" and key=key and val=val and accval=True in  Map__map_foldi_update, force)
  apply(cut_tac f=" (\<lambda>(key, val, acc__v). acc__v \<and> p (key, val))" and m="(Map__update m x y)" and key=key and val=val and accval=True in  Map__map_foldi_update, force)
apply(auto simp add: Map__remove_of_update_same)
  apply(cut_tac f=" (\<lambda>(key, val, acc__v). acc__v \<and> p (key, val))" and m="m" and key=key and val=val and accval=True in  Map__map_foldi_update, force)
  apply(cut_tac f=" (\<lambda>(key, val, acc__v). acc__v \<and> p (key, val))" and m="(Map__update m x y)" and key=key and val=val and accval=True in  Map__map_foldi_update, force)
apply(auto simp add: Map__remove_of_update_same)
  apply(cut_tac f=" (\<lambda>(key, val, acc__v). acc__v \<and> p (key, val))" and m="m" and key=key and val=val and accval=True in  Map__map_foldi_update, force)
  apply(cut_tac f=" (\<lambda>(key, val, acc__v). acc__v \<and> p (key, val))" and m="(Map__update m x y)" and key=key and val=val and accval=True in  Map__map_foldi_update, force)
apply(auto simp add: Map__remove_of_update_same)
end-proof

proof Isa Map__Map_P_of_update
  apply(auto simp add: Map__Map_P_def Map__forall_p_of_update)
end-proof


proof Isa  Map__remove_of_update_same
  apply(rule Map__map_equality, simp add: Map__update Map__remove)
end-proof

proof Isa Map__range_of_update_special_case
  apply(rule Set__membership)
  apply(auto simp add: Set__set_insertion Map__map_range Map__update)
  apply(metis Map__map_domain)
end-proof

proof Isa Map__range_of_empty
  apply(rule Set__membership)
  apply(simp add:  Map__map_range Set__empty_set Map__empty_map)
end-proof

proof Isa Map__copyMap_Obligation_subtype
  apply(auto simp add: Set__foldable_p__stp_def)
  apply(rule Map__map_equality)
  apply(auto simp add: Map__TMApply_over_update Map__update)
end-proof

proof Isa Map__copyMap_Obligation_subtype0
  apply(auto simp add: Set__Set_P_def Set__forall_p_in_self)
end-proof

proof Isa Map__TMApply_of_update_same_Obligation_subtype
  apply(simp add: Map__domain_update2 Set__set_insertion)
end-proof

proof Isa Map__TMApply_of_update_same
  apply(subst Map__TMApply_becomes_apply)
  apply(simp add: Map__domain_update2 Set__set_insertion)
  apply(simp add: Map__update)
end-proof

proof Isa Map__TMApply_over_update2_Obligation_subtype
  apply(auto simp add: Map__TMApply_becomes_apply Map__domain_update2 Set__set_insertion Map__update)
end-proof

proof Isa Map__TMApply_over_update2_Obligation_subtype0
  apply(auto simp add: Map__TMApply_becomes_apply Map__domain_update2 Set__set_insertion Map__update)
end-proof

proof Isa Map__TMApply_over_update2
  apply(auto simp add: Map__TMApply_becomes_apply Map__domain_update2 Set__set_insertion Map__update)
end-proof

proof Isa Map__rangeToList_of_empty_map
  apply (metis Map__map_rangeToList Map__range_of_empty Set__empty_set all_not_in_conv set_empty)
end-proof


end-spec





% TODO What is the status of this spec?

Maps_extended = Map qualifying spec
  import Maps

 theorem foldable?_of_update is [a,b]
   fa(v:b)
     foldable?(fn (m:Map(a,b), x:a) -> update m x v)

 %% Trying to match the form of something in Isabelle:
 theorem foldable?_of_update_2 is [a,b]
   fa(v:b)
     foldable?(fn (z:(Map(a,b) * a)) -> case z of | (m,x) -> update m x v)

 theorem foldable?_of_update_3 is [a,b]
   fa(v: a -> b)
     foldable?(fn (z:(Map(a,b) * a)) -> case z of | (m,x) -> update m x (v x))

  %% for some reason the version of this in Maps is not seen by Globalize. TODO: Is this still an issue?  If not, delete this:
  theorem TMApply_over_update_2 is [a,b]
    fa(m: Map(a,b), x: a, y: b, z: a)
      z in? domain m =>
    %% theorems with this form induce setf generation in Globalize
      (TMApply(update m x y, z) = (if x = z then y else TMApply(m, z)))

  %% Now only requires f to be defined on elements of S:
  op [a,b] mapFrom(s: Set a) (f: ({x:a | x in? s} -> b)): Map(a,b) =
    set_fold empty_map (fn (m, x) -> update m x (f x)) s

  op [b] mapFromNR_aux(i:Nat, n:Nat, f:Nat->b, m:Map(Nat,b)): Map(Nat,b) =
    if i>n then m
    else mapFromNR_aux(i+1,n,f, (update m i (f i)))

% construct a map over the domain [0,..,n]
  op [b] mapFromNR(n:Nat, f: Nat -> b): Map(Nat,b) =
    mapFromNR_aux(0,n,f,empty_map)

%%  theorem domain_of_mapFromNR

%% This causes a name clash with the Isabelle translation of the definition of mapFrom.
%% %% not quite right
%%   axiom mapFrom_def is [a,b]
%%     fa(x:a, y: b, s: Set a, f: a -> b) 
%%       y = TMApply(mapFrom(s,f), x) <=> x in? s && y = f x

  theorem domain_of_mapFrom is [a,b]
   fa(dom: Set a, g: a -> b) 
     domain(mapFrom dom g) = dom

  proof Isa -hook hook2 end-proof

  theorem mapFrom_TMApply is [a,b]
    fa(x:a, s: Set a, f: a -> b)
      x in? s =>
      TMApply(mapFrom s f, x) = f x

  op [a,b] mapUpdateSet(m: Map(a,b), s: Set a, f: a -> b): Map(a,b) =
     set_fold m (fn (m, x) -> update m x (f x)) s
     
  theorem domain_of_mapUpdateSet is [a,b]
    fa(m: Map(a,b), s: Set a, f: a -> b)
      domain (mapUpdateSet(m,s,f)) = s \/ domain m

  proof Isa -hook hook1 end-proof

  theorem TMApply_of_mapUpdateSet is [a,b]
    fa(m: Map(a,b), s: Set a, f: a -> b, x:a)
      ((x in? s) || x in? domain m) =>
      TMApply(mapUpdateSet(m,s,f),x) = (if (x in? s) then f x else TMApply(m,x))

  theorem mapFrom_if_shadow is [a,b]
    fa(x:a, s: Set a, p: a -> Bool, f: a -> b, g: a -> b)
      mapFrom s (fn x:a -> if p x then f x else g x)
        = mapUpdateSet(mapFrom s g, filter p s, f)

  theorem mapFrom_identity is [a,b]
   fa(m: Map(a,b),dom: Set a) 
     domain(m) = dom => mapFrom dom (fn (x : {x:a | x in? domain m}) -> TMApply(m,x)) = m


(* these should be in a specialized extension
  op [a,b,c] update_map_prepend(m:Map(a*b,c),lst:Set a,bval:b, f:a*b->c):Map(a*b,c) =
     set_fold m (fn (m1, aval) -> update m1 (aval,bval) (f(aval,bval))) lst

  op [a,b,c] map2DFrom(lst1: Set a, lst2: Set b, f: a*b -> c): Map(a*b,c) =
    set_fold empty_map (fn (m, bval) -> update_map_prepend(m,lst1,bval,f)) lst2
*)
  

(*--------  Special ops and axioms for isomorphism between Map(a,b)* Map(a,c) and Map(a,b*c) ---*)

  op [A,B,C] map_compose(m1:Map(A,B), m2:Map(A,C)| domain(m1)=domain(m2)): Map(A,B*C) =
    mapFrom (domain m1) (fn(domelt:A)-> (TMApply(m1,domelt),TMApply(m2,domelt)))
 
  theorem domain_of_map_compose is [A,B,C]
    fa(m1:Map(A,B), m2:Map(A,C)) domain m1 = domain m2 => domain(map_compose(m1,m2)) = domain m1

  theorem TMApply_of_map_compose is [A,B,C]
    fa(m1:Map(A,B), m2:Map(A,C), x:A)
     (domain m1 = domain m2) && (x in? domain m1) => 
     TMApply(map_compose(m1,m2),x) = (TMApply(m1,x),TMApply(m2,x))

  op [A,B,C] map_project1(m:Map(A,B*C)): Map(A,B) =
    mapFrom (domain m) (fn(domelt:A) -> (TMApply(m,domelt)).1)

  theorem domain_of_map_project1 is [A,B,C]
    fa(m:Map(A,B*C)) domain (map_project1 m) = domain m

  theorem TMApply_map_project1 is [A,B,C]
     fa(m:Map(A,B*C),a:A) a in? domain m => (TMApply(map_project1 m,a) = (TMApply(m,a)).1)

  theorem map_project1_of_map_compose is [A,B,C]
    fa(m1:Map(A,B), m2:Map(A,C))
     (domain m1 = domain m2) => 
     map_project1(map_compose(m1,m2)) = m1

  op [A,B,C] map_project2(m:Map(A,B*C)): Map(A,C) =
    mapFrom (domain m) (fn(domelt:A)-> (TMApply(m,domelt)).2)

  theorem domain_of_map_project2 is [A,B,C]
    fa(m:Map(A,B*C)) domain (map_project2 m) = domain m

  theorem TMApply_map_project2 is [A,B,C]
     fa(m:Map(A,B*C),a:A) a in? domain m => (TMApply(map_project2 m,a) = (TMApply(m,a)).2)

  theorem map_project2_of_map_compose is [A,B,C]
    fa(m1:Map(A,B), m2:Map(A,C))
     (domain m1 = domain m2) => 
     map_project2(map_compose(m1,m2)) = m2

  theorem update_map_project1 is [A,B,C]
     fa(m:Map(A,B*C),a:A,b:B)
       a in? domain m =>
       (  map_compose((update (map_project1 m) a b),
                      (map_project2 m))
        = (update m a (b,(TMApply(m,a)).2)) )

  theorem update_map_project2 is [A,B,C]
     fa(m:Map(A,B*C),a:A,c:C)
       a in? domain m =>
       (  map_compose((map_project1 m),
                      (update (map_project2 m) a c))
        = (update m a ((TMApply(m,a)).1,c)) )

  theorem combine_of_map_projections is [A,B,C]
     fa(m:Map(A,B*C)) map_compose((map_project1 m), (map_project2 m)) = m 

  theorem combine_map_project1_map_project2 is [A,B,C]
     fa(m:Map(A,B*C),m1:Map(A,B),m2:Map(A,C))
       domain m1 = domain m2 =>
       ((map_project1 m = m1) && (map_project2 m = m2))
        = (m = map_compose(m1,m2))

  theorem combine_map_project1_map_project2_cond is [A,B,C]
     fa(m:Map(A,B*C),m1:Map(A,B),m2:Map(A,C))
       (map_project1 m = m1) && (domain m1 = domain m2) =>
         ((map_project2 m) = m2) = (m = map_compose(m1,m2))
       
  theorem combine_map_project1_map_project2_simplify is [A,B,C]
     fa(m:Map(A,B*C),m1:Map(A,B),m2:Map(A,C))
       (domain m1 = domain m2) && (m = map_compose(m1,m2)) => 
       (map_project1 m = m1) = true


%----------------- 3-tuple version -----------------------------------------

  op [A,B,C,D] map_compose3(m1:Map(A,B), m2:Map(A,C), m3:Map(A,D)
                             | domain(m1)=domain(m2) && domain(m1)=domain(m3)): Map(A,B*C*D) =
    mapFrom (domain m1) (fn(domelt:A)-> (TMApply(m1,domelt),TMApply(m2,domelt),TMApply(m3,domelt)))

  theorem domain_of_map_compose3 is [A,B,C,D]
   fa (m1:Map(A,B), m2:Map(A,C), m3:Map(A,D))
     (domain m1 = domain m2) && (domain m1 = domain m3) =>
      domain(map_compose3(m1,m2,m3)) = domain m1

  theorem TMApply_of_map_compose3 is [A,B,C,D]
    fa(m1:Map(A,B), m2:Map(A,C), m3:Map(A,D), x:A)
     (domain m1 = domain m2) && (domain m1 = domain m3) && (x in? domain m1) => 
     TMApply(map_compose3(m1,m2,m3),x) = (TMApply(m1,x),TMApply(m2,x),TMApply(m3,x))

  op [A,B,C,D] map_project31(m:Map(A,B*C*D)): Map(A,B) =
    mapFrom (domain m) (fn(domelt:A)-> (TMApply(m,domelt)).1)

  op [A,B,C,D] map_project32(m:Map(A,B*C*D)): Map(A,C) =
    mapFrom (domain m) (fn(domelt:A)-> (TMApply(m,domelt)).2)

  op [A,B,C,D] map_project33(m:Map(A,B*C*D)): Map(A,D) =
    mapFrom (domain m) (fn(domelt:A)-> (TMApply(m,domelt)).3)

  theorem TMApply_map_project31 is [A,B,C,D]
     fa(m:Map(A,B*C*D),a:A) a in? domain m => (TMApply(map_project31(m),a) = (TMApply(m,a)).1)

  theorem TMApply_map_project32 is [A,B,C,D]
     fa(m:Map(A,B*C*D),a:A) a in? domain m => (TMApply(map_project32(m),a) = (TMApply(m,a)).2)

  theorem TMApply_map_project33 is [A,B,C,D]
     fa(m:Map(A,B*C*D),a:A) a in? domain m => (TMApply(map_project33(m),a) = (TMApply(m,a)).3)

  theorem domain_of_map_project31 is [A,B,C,D]
    fa(m:Map(A,B*C*D)) domain (map_project31 m) = domain m

  theorem domain_of_map_project32 is [A,B,C,D]
    fa(m:Map(A,B*C*D)) domain (map_project32 m) = domain m

  theorem domain_of_map_project33 is [A,B,C,D]
    fa(m:Map(A,B*C*D)) domain (map_project33 m) = domain m

  theorem map_project31_of_map_compose3 is [A,B,C,D]
    fa(m1:Map(A,B), m2:Map(A,C), m3:Map(A,D))
     (domain m1 = domain m2) && (domain m1 = domain m3) => 
     map_project31(map_compose3(m1,m2,m3)) = m1

  theorem map_project32_of_map_compose3 is [A,B,C,D]
    fa(m1:Map(A,B), m2:Map(A,C), m3:Map(A,D))
     (domain m1 = domain m2) && (domain m1 = domain m3) => 
     map_project32(map_compose3(m1,m2,m3)) = m2

  theorem map_project33_of_map_compose3 is [A,B,C,D]
    fa(m1:Map(A,B), m2:Map(A,C), m3:Map(A,D))
     (domain m1 = domain m2) && (domain m1 = domain m3) => 
     map_project33(map_compose3(m1,m2,m3)) = m3

  theorem update_map_project31 is [A,B,C,D]
     fa(m:Map(A,B*C*D),a:A,b:B)
       a in? domain m =>
       (  map_compose3((update (map_project31 m) a b),
                      (map_project32 m),(map_project33 m))
        = (update m a (b,(TMApply(m,a)).2,(TMApply(m,a)).3)) )

  theorem update_map_project32 is [A,B,C,D]
     fa(m:Map(A,B*C*D),a:A,c:C)
       a in? domain m =>
       (  map_compose3((map_project31 m),
                       (update (map_project32 m) a c),
                       (map_project33 m))
        = (update m a ((TMApply(m,a)).1,c,(TMApply(m,a)).3)) )

  theorem update_map_project33 is [A,B,C,D]
     fa(m:Map(A,B*C*D),a:A,d:D)
       a in? domain m =>
       (  map_compose3((map_project31 m),
                       (map_project32 m),
                       (update (map_project33 m) a d))
        = (update m a ((TMApply(m,a)).1,(TMApply(m,a)).2,d)) )

  theorem combine_map_project3 is [A,B,C,D]
     fa(m:Map(A,B*C*D),m1:Map(A,B),m2:Map(A,C),m3:Map(A,D))
       map_compose3((map_project31 m),(map_project32 m),(map_project33 m)) = m 

  theorem map_compose3_project31_simplify is [A,B,C,D]
     fa(m:Map(A,B*C*D),m1:Map(A,B),m2:Map(A,C),m3:Map(A,D))
       domain m1 = domain m2 && domain m2 = domain m3 =>
       (m = map_compose3(m1,m2,m3)) => ((map_project31 m) = m1) = true
  theorem map_compose3_project32_simplify is [A,B,C,D]
     fa(m:Map(A,B*C*D),m1:Map(A,B),m2:Map(A,C),m3:Map(A,D))
       domain m1 = domain m2 && domain m2 = domain m3 =>
       (m = map_compose3(m1,m2,m3)) => ((map_project32 m) = m2) = true
  theorem map_compose3_project33_simplify is [A,B,C,D]
     fa(m:Map(A,B*C*D),m1:Map(A,B),m2:Map(A,C),m3:Map(A,D))
       domain m1 = domain m2 && domain m2 = domain m3 =>
       (m = map_compose3(m1,m2,m3)) => ((map_project33 m) = m3) = true
  theorem combine_of_map_projections3 is [A,B,C,D]
     fa(m:Map(A,B*C*D)) map_compose3((map_project31 m), (map_project32 m),(map_project33 m)) = m 

  theorem map_compose3_compose is [a,b,c]
     fa(n:Nat, f1:Nat->a,f2:Nat->b,f3:Nat->c)
        map_compose3(mapFromNR(n,f1),mapFromNR(n,f2),mapFromNR(n,f3))
        = mapFromNR(n, fn(i:Nat)-> (f1 i, f2 i, f3 i))

  % theorem map_compose3_update13 is [B,C,D]
  %    fa(m:Map(Nat,B*C*D),n:Nat,x:B,y:C,z:D)
  %       map_compose3(update (map_project31 m) n x, 
  %                    map_project32 m, 
  %                    update (map_project33 m) n z)
  %       = (update m n (x,(TMApply(m,n)).2,z))

% profligate version:       = (update m n (x,y,z))
  theorem map_compose3_update is [B,C,D]
     fa(m:Map(Nat,B*C*D),n:Nat,x:B,y:C,z:D)
        map_compose3(update (map_project31 m) n x, 
                     update (map_project32 m) n y, 
                     update (map_project33 m) n z)
        = (update m n (x,y,z))
                                         
(******************************** The Proofs ********************************)

proof isa mapFrom_Obligation_subtype
  apply(auto simp add: Set__foldable_p_def)
  apply(simp only: Map__update_of_update_both Set__foldable_p__stp_def)
  apply(simp)
  apply (metis Map__update_of_update_both)
end-proof

proof isa mapFrom_TMApply_Obligation_subtype
 apply(metis Map__domain_of_mapFrom)
end-proof

proof Isa hook1
theorem Map__TMApply_of_mapUpdateSet_helper: 
  "(x in? s \<or> x in? Map__domain m) \<longrightarrow>
   Map__TMApply(Map__mapUpdateSet(m, s, f), x) 
     = (if x in? s then f x else Map__TMApply(m, x))"
  apply(cut_tac p="\<lambda> s . ( x in? s \<or> x in? Map__domain m \<longrightarrow> Map__TMApply (Map__mapUpdateSet (m, s, f), x) = (if x in? s then f x else Map__TMApply (m, x)))" in Set__induction)
  apply(simp add: Set__empty_set Map__mapUpdateSet_def)
  apply(auto simp add: Map__foldable_p_of_update_3 Set__set_fold1)[1]
  apply(cut_tac c=m and f="(\<lambda>(m0,x). Map__update m0 x (f x))" in Set__set_fold1)
  apply (metis Map__foldable_p_of_update_3)
  apply(auto)[1]
  apply(auto simp only:)[1]
  apply(case_tac "xa in? s")
  apply(simp add: Set__set_insert_does_nothing)[1]
  apply(cut_tac c=m and f="(\<lambda>(m0,x). Map__update m0 x (f x))" and x=xa and s=s in Set__set_fold2)
  apply (metis Map__foldable_p_of_update_3)
  apply(simp)
  apply(simp add: Set__set_insertion)
  apply(auto simp add: Map__mapUpdateSet_def)
  apply(cut_tac c=m and f="(\<lambda>(m0,x). Map__update m0 x (f x))" and x=xa and s=s in Set__set_fold2)  
  apply (metis Map__foldable_p_of_update_3)
  apply (metis Map__TMApply_over_update2)
  apply (metis Map__TMApply_over_update2)
  apply(case_tac "xa in? s")
  apply(simp add: Set__set_insert_does_nothing)[1]
  apply(cut_tac c=m and f="(\<lambda>(m0,x). Map__update m0 x (f x))" and x=xa and s=s in Set__set_fold2)  
  apply (metis Map__foldable_p_of_update_3)
  apply(simp)
  apply(auto simp add: Map__TMApply_over_update)
  apply(case_tac "x in? s")
  apply(auto)
  apply(cut_tac m=m and s=s and f=f in Map__domain_of_mapUpdateSet)
  apply(simp add: Map__mapUpdateSet_def)
  apply (metis (lifting, no_types) Map__TMApply_over_update_2 Set__commutativity_of_union Set__distribute_union_over_right_insert Set__set_insert_does_nothing Set__set_insertion)
  apply (metis (lifting, no_types) Map__TMApply_of_update_same Set__set_insertion)
  apply(case_tac "xa in? s")
  apply(simp add: Set__set_insert_does_nothing)[1]
  apply(cut_tac c=m and f="(\<lambda>(m0,x). Map__update m0 x (f x))" and x=xa and s=s in Set__set_fold2)  
  apply (metis Map__foldable_p_of_update_3)
  apply(simp)
  apply(auto simp add: Map__TMApply_over_update)
  apply(case_tac "x in? s")
  apply(auto)
  apply(cut_tac m=m and s=s and f=f in Map__domain_of_mapUpdateSet)
  apply(simp add: Map__mapUpdateSet_def)
  apply (metis (lifting, no_types) Map__TMApply_over_update_2 Set__commutativity_of_union Set__distribute_union_over_right_insert Set__set_insert_does_nothing Set__set_insertion)
  apply (metis (lifting, no_types) Map__TMApply_of_update_same Set__set_insertion)
    apply(case_tac "xa in? s")
  apply(simp add: Set__set_insert_does_nothing)[1]
  apply(cut_tac c=m and f="(\<lambda>(m0,x). Map__update m0 x (f x))" and x=xa and s=s in Set__set_fold2)  
  apply (metis Map__foldable_p_of_update_3)
  apply(simp)
  apply(auto simp add: Map__TMApply_over_update)
  apply(case_tac "x in? s")
  apply (metis Set__set_insertion)
  apply(auto)
  apply(cut_tac m=m and s=s and f=f in Map__domain_of_mapUpdateSet)
  apply(simp add: Map__mapUpdateSet_def)
  apply (metis (lifting, no_types) Map__TMApply_over_update_2 Set__distribute_union_over_right_insert Set__set_insert_does_nothing Set__set_insertion)
done
end-proof

proof isa hook2
theorem Map__mapFrom_TMApply_helper: 
  "x in? s \<longrightarrow> Map__TMApply(Map__mapFrom s f, x) = f x"
  apply(simp add: Map__mapFrom_def)
  apply(rule Set__induction)
  apply(metis Set__empty_set)
  apply(auto)
  apply(metis (mono_tags) Map__TMApply_of_update_same Map__foldable_p_of_update_3 Set__set_fold2 Set__set_insertion split_conv)
  apply(case_tac "xa in? s")
  apply(simp add: Set__set_insert_does_nothing)
  apply(cut_tac c="Map__empty_map" and f="(\<lambda>a. case a of (m, x) \<Rightarrow> Map__update m x (f x))" and x=xa and s=s in Set__set_fold2)
  apply(metis Map__foldable_p_of_update_3)
  apply(simp)
  apply(simp)
  apply(metis Map__TMApply_of_update_same Map__TMApply_over_update_2 Map__domain_of_mapFrom Map__mapFrom_def Set__set_insertion)
done
end-proof

proof isa mapFrom_TMApply
  apply(metis Map__mapFrom_TMApply_helper)
end-proof

proof isa mapUpdateSet_Obligation_subtype
  apply(auto simp add: Set__foldable_p_def)
  apply(rule Map__map_equality, simp add: Map__update)
end-proof

proof isa mapFrom_if_shadow
  apply(rule Map__totalmap_equality)
  apply(auto simp add: Map__domain_of_mapUpdateSet Map__domain_of_mapFrom)
  apply(rule Set__membership)
  apply(auto simp add: Set__filter_def  Set__set_union)
  apply(auto simp add: Map__mapFrom_TMApply Map__TMApply_of_mapUpdateSet Map__domain_of_mapFrom Set__filter_def)
end-proof

proof isa mapFrom_identity
  apply(rule Map__totalmap_equality)
  apply(metis Map__domain_of_mapFrom)
  apply(metis Map__domain_of_mapFrom Map__mapFrom_TMApply)
end-proof

proof isa domain_of_mapFrom
  apply(simp add: Map__mapFrom_def)
  apply(rule Set__induction)
  apply (metis (no_types) Map__domain_of_empty Map__foldable_p_of_update_3 Set__set_fold1)
  apply(auto)
  apply(case_tac "x in? s")
  apply(simp add: Set__set_insert_does_nothing)
  apply(cut_tac c="Map__empty_map" and f="(\<lambda>a. case a of (m, x) \<Rightarrow> Map__update m x (g x))" and x=x and s=s in Set__set_fold2)
  apply (metis (no_types) Map__foldable_p_of_update_3)
  apply(simp)
  apply(simp add: Map__domain_update2)
end-proof

% proof isa map2DFrom_Obligation_subtype
%   sorry
% end-proof

proof isa TMApply_map_project1_Obligation_subtype
  apply (simp add: Map__domain_of_mapFrom Map__map_project1_def)
end-proof

proof isa TMApply_map_project1
  apply(simp add: Map__map_project1_def Map__mapFrom_TMApply)
end-proof

proof isa TMApply_map_project2_Obligation_subtype
  apply (simp add: Map__domain_of_mapFrom Map__map_project2_def)
end-proof

proof isa TMApply_map_project2
  apply(simp add: Map__map_project2_def Map__mapFrom_TMApply)
end-proof

proof isa update_map_project1_Obligation_subtype
  apply(metis Map__domain_of_mapFrom Map__domain_update Map__map_project1_def Map__map_project2_def)
end-proof

proof isa update_map_project1
  apply(rule Map__totalmap_equality)
  apply(simp add: Map__domain_of_map_compose Map__domain_update Map__domain_of_map_project1 Map__domain_of_map_project2)
  apply(auto simp add: Map__TMApply_of_map_compose Map__domain_of_map_compose Map__domain_update Map__domain_of_map_project1 Map__domain_of_map_project2 Map__TMApply_over_update_2 Map__TMApply_map_project2 Map__TMApply_map_project1)
end-proof

proof isa update_map_project2_Obligation_subtype
  apply(metis Map__domain_of_mapFrom Map__domain_update Map__map_project1_def Map__map_project2_def)
end-proof

proof isa update_map_project2
  apply(rule Map__totalmap_equality)
  apply(simp add: Map__domain_of_map_compose Map__domain_update Map__domain_of_map_project1 Map__domain_of_map_project2)
  apply(auto simp add: Map__TMApply_of_map_compose Map__domain_of_map_compose Map__domain_update Map__domain_of_map_project1 Map__domain_of_map_project2 Map__TMApply_over_update_2 Map__TMApply_map_project2 Map__TMApply_map_project1)
end-proof

proof isa combine_map_project1_map_project2
  apply(auto simp add: Map__domain_of_map_project1 Map__domain_of_map_project2 Map__combine_of_map_projections Map__map_project1_of_map_compose Map__map_project2_of_map_compose)
end-proof

proof isa combine_map_project1_map_project2_cond
  apply(auto simp add: Map__domain_of_map_project1 Map__domain_of_map_project2 Map__combine_of_map_projections Map__map_project1_of_map_compose Map__map_project2_of_map_compose)
  apply(metis Map__domain_of_map_project1 Map__map_project2_of_map_compose)
end-proof

proof isa combine_map_project1_map_project2_simplify
  apply(auto simp add: Map__domain_of_map_project1 Map__domain_of_map_project2 Map__combine_of_map_projections Map__map_project1_of_map_compose Map__map_project2_of_map_compose)
end-proof

proof isa combine_of_map_projections_Obligation_subtype
  apply (simp add: Map__domain_of_map_project1 Map__domain_of_map_project2)
end-proof

proof isa combine_of_map_projections
  apply(rule Map__totalmap_equality)
  apply(simp add: Map__domain_of_map_compose Map__domain_update Map__domain_of_map_project1 Map__domain_of_map_project2)
  apply(simp add: Map__domain_of_map_compose Map__domain_update Map__domain_of_map_project1 Map__domain_of_map_project2 Map__TMApply_of_map_compose Map__TMApply_map_project1 Map__TMApply_map_project2)
end-proof

proof isa TMApply_map_project31_Obligation_subtype
   apply (simp add: Map__domain_of_mapFrom Map__map_project31_def)
end-proof

proof isa TMApply_map_project31
  apply(simp add: Map__map_project31_def Map__mapFrom_TMApply)
end-proof

proof isa TMApply_map_project32_Obligation_subtype
  apply (simp add: Map__domain_of_mapFrom Map__map_project32_def)
end-proof

proof isa TMApply_map_project32
  apply(simp add: Map__map_project32_def Map__mapFrom_TMApply)
end-proof

proof isa TMApply_map_project33_Obligation_subtype
   apply (simp add: Map__domain_of_mapFrom Map__map_project33_def)
end-proof

proof isa TMApply_map_project33
  apply(simp add: Map__map_project33_def Map__mapFrom_TMApply)
end-proof

proof isa update_map_project31_Obligation_subtype
  apply(metis Map__domain_of_mapFrom Map__domain_update Map__map_project31_def Map__map_project32_def Map__map_project33_def)
end-proof

proof isa update_map_project31
  apply(rule Map__totalmap_equality)
  apply(simp add: Map__domain_of_map_compose3 Map__domain_update Map__domain_of_map_project31 Map__domain_of_map_project32 Map__domain_of_map_project33)
  apply(simp add: Map__domain_of_map_compose3 Map__domain_update Map__domain_of_map_project31 Map__domain_of_map_project32 Map__domain_of_map_project33 Map__TMApply_map_project31 Map__TMApply_map_project32 Map__TMApply_map_project33 Map__TMApply_of_map_compose3 Map__TMApply_over_update)
end-proof

proof isa update_map_project32_Obligation_subtype
  apply(metis Map__domain_of_mapFrom Map__domain_update Map__map_project31_def Map__map_project32_def Map__map_project33_def)
end-proof

proof isa update_map_project32
  apply(rule Map__totalmap_equality)
  apply(simp add: Map__domain_of_map_compose3 Map__domain_update Map__domain_of_map_project31 Map__domain_of_map_project32 Map__domain_of_map_project33)
  apply(simp add: Map__domain_of_map_compose3 Map__domain_update Map__domain_of_map_project31 Map__domain_of_map_project32 Map__domain_of_map_project33 Map__TMApply_map_project31 Map__TMApply_map_project32 Map__TMApply_map_project33 Map__TMApply_of_map_compose3 Map__TMApply_over_update)
end-proof

proof isa update_map_project33_Obligation_subtype
  apply(metis Map__domain_of_mapFrom Map__domain_update Map__map_project31_def Map__map_project32_def Map__map_project33_def)
end-proof

proof isa update_map_project33
  apply(rule Map__totalmap_equality)
  apply(simp add: Map__domain_of_map_compose3 Map__domain_update Map__domain_of_map_project31 Map__domain_of_map_project32 Map__domain_of_map_project33)
  apply(simp add: Map__domain_of_map_compose3 Map__domain_update Map__domain_of_map_project31 Map__domain_of_map_project32 Map__domain_of_map_project33 Map__TMApply_map_project31 Map__TMApply_map_project32 Map__TMApply_map_project33 Map__TMApply_of_map_compose3 Map__TMApply_over_update)
end-proof

proof isa combine_map_project3_Obligation_subtype
  apply(simp add: Map__domain_of_map_project31 Map__domain_of_map_project32 Map__domain_of_map_project33)
end-proof

proof isa combine_map_project3
  apply(rule Map__totalmap_equality)
  apply(simp add: Map__domain_of_map_compose3 Map__domain_update Map__domain_of_map_project31 Map__domain_of_map_project32 Map__domain_of_map_project33)
  apply(simp add: Map__domain_of_map_compose3 Map__domain_update Map__domain_of_map_project31 Map__domain_of_map_project32 Map__domain_of_map_project33 Map__TMApply_of_map_compose3 Map__TMApply_map_project31 Map__TMApply_map_project32 Map__TMApply_map_project33)
end-proof

proof isa map_compose3_project31_simplify
  apply(auto simp add: Map__domain_of_map_project31 Map__domain_of_map_project32 Map__domain_of_map_project33 Map__combine_map_project3 Map__map_project31_of_map_compose3 Map__map_project32_of_map_compose3 Map__map_project33_of_map_compose3)
end-proof

proof isa map_compose3_project32_simplify
  apply(auto simp add: Map__domain_of_map_project31 Map__domain_of_map_project32 Map__domain_of_map_project33 Map__combine_map_project3 Map__map_project31_of_map_compose3 Map__map_project32_of_map_compose3 Map__map_project33_of_map_compose3)
end-proof

proof isa map_compose3_project33_simplify
  apply(auto simp add: Map__domain_of_map_project31 Map__domain_of_map_project32 Map__domain_of_map_project33 Map__combine_map_project3 Map__map_project31_of_map_compose3 Map__map_project32_of_map_compose3 Map__map_project33_of_map_compose3)
end-proof

proof isa combine_of_map_projections3_Obligation_subtype
  apply(auto simp add: Map__domain_of_map_project31 Map__domain_of_map_project32 Map__domain_of_map_project33)
end-proof

proof isa combine_of_map_projections3
  apply(rule Map__totalmap_equality)
  apply(simp add: Map__domain_of_map_compose3 Map__domain_update Map__domain_of_map_project31 Map__domain_of_map_project32 Map__domain_of_map_project33)
  apply(simp add: Map__domain_of_map_compose3 Map__domain_update Map__domain_of_map_project31 Map__domain_of_map_project32 Map__domain_of_map_project33 Map__TMApply_of_map_compose3 Map__TMApply_map_project31 Map__TMApply_map_project32 Map__TMApply_map_project33)
end-proof

proof isa TMApply_over_update_2_Obligation_subtype
  apply(cut_tac Map__TMApply_over_update_Obligation_subtype)
  apply(auto)
end-proof

proof isa TMApply_over_update_2_Obligation_subtype0
  apply(cut_tac Map__TMApply_over_update_Obligation_subtype0)
  apply(auto)
end-proof

proof isa TMApply_over_update_2
  apply(cut_tac Map__TMApply_over_update)
  apply(auto)
end-proof

proof isa map_compose3_compose
  sorry
end-proof

% Seems true, since the domain of mapFromNR(n,f) is the set containing
% the naturals less than n.  We could express this as a helper lemma
% if we move Pair2S from StructuredTypes into this spec:
proof isa map_compose3_compose_Obligation_subtype
  sorry
end-proof

%% End of proofs for Maps_extended

proof Isa Map__map_compose3_update_Obligation_subtype
  apply(auto simp add: Map__domain_update Map__map_project31_def Map__map_project32_def Map__map_project33_def Map__domain_of_mapFrom)
end-proof

proof Isa Map__map_compose3_update
  apply(auto simp add: Map__domain_update Map__map_project31_def Map__map_project32_def Map__map_project33_def Map__domain_of_mapFrom Map__map_compose3_def Map__TMApply_over_update)
  apply(simp add:  Map__TMApply_over_update_2 Map__domain_of_mapFrom Map__domain_update Map__mapFrom_TMApply Map__totalmap_equality surjective_pairing)
  apply(rule Map__totalmap_equality)
  apply (auto simp add: Map__TMApply_of_update_same Map__TMApply_over_update_2 Map__domain_of_mapFrom Map__domain_update Map__domain_update2 Map__mapFrom_TMApply Map__totalmap_equality Set__set_insertion surjective_pairing)
  apply(simp add: Set__set_insert_new_def)
  apply (auto simp add: Map__TMApply_of_update_same Map__TMApply_over_update_2 Map__domain_of_mapFrom Map__domain_update Map__domain_update2 Map__mapFrom_TMApply Map__totalmap_equality Set__set_insertion surjective_pairing)
end-proof

proof Isa Map__domain_of_map_compose
  apply(simp add: Map__map_compose_def Map__domain_of_mapFrom)
end-proof

proof Isa Map__TMApply_of_map_compose_Obligation_subtype
  apply(simp add: Map__map_compose_def Map__domain_of_mapFrom)
end-proof

proof Isa Map__TMApply_of_map_compose
  apply(simp add: Map__map_compose_def Map__domain_of_mapFrom Map__mapFrom_TMApply)
end-proof

proof Isa Map__domain_of_map_project1
  apply(simp add: Map__map_project1_def Map__domain_of_mapFrom)
end-proof

proof Isa Map__domain_of_map_project2
  apply(simp add: Map__map_project2_def Map__domain_of_mapFrom)
end-proof

proof Isa Map__map_project1_of_map_compose
  apply(rule Map__totalmap_equality)
  apply(simp add: Map__domain_of_map_compose Map__domain_update Map__domain_of_map_project1)
  apply(simp add: Map__domain_of_map_compose Map__domain_update Map__domain_of_map_project1 Map__TMApply_map_project1 Map__TMApply_of_map_compose)
end-proof

proof Isa Map__map_project2_of_map_compose
  apply(rule Map__totalmap_equality)
  apply(simp add: Map__domain_of_map_compose Map__domain_update Map__domain_of_map_project2)
  apply(simp add: Map__domain_of_map_compose Map__domain_update Map__domain_of_map_project2 Map__TMApply_map_project2 Map__TMApply_of_map_compose)
end-proof

proof Isa Map__domain_of_map_compose3
  apply(simp add: Map__map_compose3_def Map__domain_of_mapFrom)
end-proof

proof Isa Map__domain_of_map_project31
  apply(simp add: Map__map_project31_def Map__domain_of_mapFrom)
end-proof

proof Isa Map__domain_of_map_project32
  apply(simp add: Map__map_project32_def Map__domain_of_mapFrom)
end-proof

proof Isa Map__domain_of_map_project33
  apply(simp add: Map__map_project33_def Map__domain_of_mapFrom)
end-proof

proof Isa Map__TMApply_of_map_compose3_Obligation_subtype
  apply(simp add: Map__map_compose3_def Map__domain_of_mapFrom Map__mapFrom_TMApply)
end-proof

proof Isa Map__TMApply_of_map_compose3
  apply(simp add: Map__map_compose3_def Map__domain_of_mapFrom Map__mapFrom_TMApply)
end-proof

proof Isa Map__map_project31_of_map_compose3
  apply(rule Map__totalmap_equality)
  apply(simp add: Map__domain_of_map_compose3 Map__domain_update Map__domain_of_map_project31)
  apply(simp add: Map__domain_of_map_compose3 Map__domain_update Map__domain_of_map_project31 Map__TMApply_map_project31 Map__TMApply_of_map_compose3)
end-proof

proof Isa Map__map_project32_of_map_compose3
  apply(rule Map__totalmap_equality)
  apply(simp add: Map__domain_of_map_compose3 Map__domain_update Map__domain_of_map_project32)
  apply(simp add: Map__domain_of_map_compose3 Map__domain_update Map__domain_of_map_project32 Map__TMApply_map_project32 Map__TMApply_of_map_compose3)
end-proof

proof Isa Map__map_project33_of_map_compose3
  apply(rule Map__totalmap_equality)
  apply(simp add: Map__domain_of_map_compose3 Map__domain_update Map__domain_of_map_project33)
  apply(simp add: Map__domain_of_map_compose3 Map__domain_update Map__domain_of_map_project33 Map__TMApply_map_project33 Map__TMApply_of_map_compose3)
end-proof

proof Isa Map__foldable_p_of_update
  apply(simp add: Set__foldable_p_def)
  apply (metis Map__update_of_update_both)
end-proof

proof Isa Map__foldable_p_of_update_2
  apply(simp add: Set__foldable_p_def)
  apply (metis Map__update_of_update_both)
end-proof

proof Isa Map__foldable_p_of_update_3
  apply(simp add: Set__foldable_p_def)
  apply (metis Map__update_of_update_both)
end-proof

proof Isa Map__domain_of_mapUpdateSet
  apply(simp add: Map__mapUpdateSet_def)
  apply(cut_tac p="\<lambda> s . Map__domain (Set__set_fold m (\<lambda>(m0,x). Map__update m0 x (f x)) s) = s \\/ Map__domain m" in Set__induction)
  apply (metis (lifting, mono_tags) Map__mapUpdateSet_Obligation_subtype Set__set_fold1 Set__union_left_unit)
  apply(auto)
  apply(case_tac "x in? s")
  apply(simp add: Set__set_insert_does_nothing)
  apply(cut_tac c=m and f="(\<lambda>(m0,x). Map__update m0 x (f x))" and x=x and s=s in Set__set_fold2)
  apply (metis Map__foldable_p_of_update_3)
  apply(simp)
  apply(simp)
  apply(metis Map__domain_update2 Set__distribute_union_over_left_insert)
end-proof

proof Isa Map__TMApply_of_mapUpdateSet_Obligation_subtype
  apply(simp add: Map__domain_of_mapUpdateSet Set__set_union)
end-proof

proof Isa Map__TMApply_of_mapUpdateSet_Obligation_subtype0
  apply(simp add: Map__domain_of_mapUpdateSet Set__set_union)
end-proof

proof Isa Map__TMApply_of_mapUpdateSet
  apply(metis Map__TMApply_of_mapUpdateSet_helper)
end-proof

proof isa mapFromNR_aux ()
  apply (metis prod_cases4)
  apply (metis Pair_inject)
end-proof

end-spec
