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

%  who added this?
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

 %TODO delete this comment?
  % we could define several other operations on maps (e.g., "undefinition"
  % of elements (TODO done above as remove), homomorphic application of a function) but the above
  % operations are sufficient for this example

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
      key1 ~= key2 =>   %% Excludes the case of the same key twice with different values (can't happen).
      f(key1,val1,f(key2,val2,accval)) = f(key2,val2,f(key1,val1,accval))

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



  %% FIXME Prove or drop this:
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
  sorry
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


end-spec





% TODO What is the status of this spec?

Maps_extended = spec
  import Maps

  %% for some reason the version of this in Maps is not seen by Globalize. TODO: Is this still an issue?  If not, delete this:
  theorem TMApply_over_update_2 is [a,b]
    fa(m: Map(a,b), x: a, y: b, z: a)
      z in? domain m =>
    %% theorems with this form induce setf generation in Globalize
      (TMApply(update m x y, z) = (if x = z then y else TMApply(m, z)))

  op [a,b] mapFrom(s: Set a, f: a -> b): Map(a,b) =
    set_fold empty_map (fn (m, x) -> update m x (f x)) s

%% This causes a name clash with the Isabelle translation of the definition of mapFrom.
%% %% not quite right
%%   axiom mapFrom_def is [a,b]
%%     fa(x:a, y: b, s: Set a, f: a -> b) 
%%       y = TMApply(mapFrom(s,f), x) <=> x in? s && y = f x

  theorem mapFrom_TMApply is [a,b]
    fa(x:a, s: Set a, f: a -> b)
      x in? s =>
      TMApply(mapFrom(s,f), x) = f x

  theorem mapFrom_if_shadow is [a,b]
    fa(x:a, s: Set a, p: a -> Bool, f: a -> b, g: a -> b)
      mapFrom(s,fn x:a -> if p x then f x else g x)
        = mapUpdateSet(mapFrom(s,g), filter p s, f)

  theorem mapFrom_identity is [a,b]
   fa(m: Map(a,b),dom: Set a) 
     domain(m) = dom => mapFrom(dom, (fn x -> TMApply(m,x))) = m

  theorem domain_of_mapFrom is [a,b]
   fa(dom: Set a, g: a -> b) 
     domain(mapFrom(dom, g)) = dom

  op [a,b,c] update_map_prepend(m:Map(a*b,c),lst:Set a,bval:b, f:a*b->c):Map(a*b,c) =
     set_fold m (fn (m1, aval) -> update m1 (aval,bval) (f(aval,bval))) lst

  op [a,b,c] map2DFrom(lst1: Set a, lst2: Set b, f: a*b -> c): Map(a*b,c) =
    set_fold empty_map (fn (m, bval) -> update_map_prepend(m,lst1,bval,f)) lst2
  
  op [a,b] mapUpdateSet(m: Map(a,b), s: Set a, f: a -> b): Map(a,b) =
     set_fold m (fn (m, x) -> update m x (f x)) s

(*--------  Special ops and axioms for isomorphism between Map(a,b)* Map(a,c) and Map(a,b*c) ---*)

  op [A,B,C] map_compose(m1:Map(A,B), m2:Map(A,C)| domain(m1)=domain(m2)): Map(A,B*C) =
    mapFrom( domain(m1), (fn(domelt:A)-> (TMApply(m1,domelt),TMApply(m2,domelt))))

  op [A,B,C] map_project1(m:Map(A,B*C)): Map(A,B) =
    mapFrom( domain(m), fn(domelt:A)-> (TMApply(m,domelt)).1)

  op [A,B,C] map_project2(m:Map(A,B*C)): Map(A,C) =
    mapFrom( (domain m), fn(domelt:A)-> (TMApply(m,domelt)).2)

  % TODO May not type-check.
  theorem TMApply_map_project1 is [A,B,C]
     fa(m:Map(A,B*C),a:A)( TMApply(map_project1(m),a) = (TMApply(m,a)).1 )

  % TODO May not type-check.
  theorem TMApply_map_project2 is [A,B,C]
     fa(m:Map(A,B*C),a:A)( TMApply(map_project2(m),a) = (TMApply(m,a)).2 )

  theorem update_map_project1 is [A,B,C]
     fa(m:Map(A,B*C),a:A,b:B)
       (  map_compose((update (map_project1 m) a b),
                      (map_project2 m))
        = (update m a (b,(TMApply(m,a)).2)) )

  theorem update_map_project2 is [A,B,C]
     fa(m:Map(A,B*C),a:A,c:C)
       (  map_compose((map_project1 m),
                      (update (map_project2 m) a c))
        = (update m a ((TMApply(m,a)).1,c)) )

  theorem combine_map_project1_map_project2 is [A,B,C]
     fa(m:Map(A,B*C),m1:Map(A,B),m2:Map(A,C))
       (  ((map_project1 m) = m1 && (map_project2 m) = m2)
        = (m = map_compose(m1,m2))
       )

  theorem combine_map_project1_map_project2_cond is [A,B,C]
     fa(m:Map(A,B*C),m1:Map(A,B),m2:Map(A,C))
       (  ((map_project1 m) = m1) =>
          (((map_project2 m) = m2) = (m = map_compose(m1,m2)))
       )

  theorem combine_map_project1_map_project2_simplify is [A,B,C]
     fa(m:Map(A,B*C),m1:Map(A,B),m2:Map(A,C))
       (m = map_compose(m1,m2)) => ((map_project1 m) = m1) = true


  theorem combine_of_map_projections is [A,B,C]
     fa(m:Map(A,B*C)) map_compose((map_project1 m), (map_project2 m)) = m 

%----------------- 3-tuple version -----------------------------------------

  op [A,B,C,D] map_compose3(m1:Map(A,B), m2:Map(A,C), m3:Map(A,D)
                             | domain(m1)=domain(m2) && domain(m1)=domain(m3)): Map(A,B*C*D) =
    mapFrom( domain(m1), (fn(domelt:A)-> (TMApply(m1,domelt),TMApply(m2,domelt),TMApply(m3,domelt))))

  op [A,B,C,D] map_project31(m:Map(A,B*C*D)): Map(A,B) =
    mapFrom( domain(m), fn(domelt:A)-> (TMApply(m,domelt)).1)

  op [A,B,C,D] map_project32(m:Map(A,B*C*D)): Map(A,C) =
    mapFrom( (domain m), fn(domelt:A)-> (TMApply(m,domelt)).2)

  op [A,B,C,D] map_project33(m:Map(A,B*C*D)): Map(A,D) =
    mapFrom( (domain m), fn(domelt:A)-> (TMApply(m,domelt)).3)

  theorem TMApply_map_project31 is [A,B,C,D]
     fa(m:Map(A,B*C*D),a:A)( TMApply(map_project31(m),a) = (TMApply(m,a)).1 )

  theorem TMApply_map_project32 is [A,B,C,D]
     fa(m:Map(A,B*C*D),a:A)( TMApply(map_project32(m),a) = (TMApply(m,a)).2 )

  theorem TMApply_map_project33 is [A,B,C,D]
     fa(m:Map(A,B*C*D),a:A)( TMApply(map_project33(m),a) = (TMApply(m,a)).3 )

% this forms a triple unnecessarily - how to update a triple in the range of a map?
  theorem update_map_project31 is [A,B,C,D]
     fa(m:Map(A,B*C*D),a:A,b:B)
       (  map_compose3((update (map_project31 m) a b),
                      (map_project32 m),(map_project33 m))
        = (update m a (b,(TMApply(m,a)).2,(TMApply(m,a)).3)) )

  theorem update_map_project32 is [A,B,C,D]
     fa(m:Map(A,B*C*D),a:A,c:C)
       (  map_compose3((map_project31 m),
                       (update (map_project32 m) a c),
                       (map_project33 m))
        = (update m a ((TMApply(m,a)).1,c,(TMApply(m,a)).3)) )

  theorem update_map_project33 is [A,B,C,D]
     fa(m:Map(A,B*C*D),a:A,d:D)
       (  map_compose3((map_project31 m),
                       (map_project32 m),
                       (update (map_project33 m) a d))
        = (update m a ((TMApply(m,a)).1,(TMApply(m,a)).2,d)) )

%  theorem combine_map_project3 is [A,B,C,D]
%     fa(m:Map(A,B*C*D),m1:Map(A,B),m2:Map(A,C),m3:Map(A,D))
%       (  ((map_project31 m) = m1 
%             && (map_project32 m) = m2
%             && (map_project33 m) = m3)
%        = (m = map_compose3(m1,m2,m3))
%       )

  theorem combine_map_project3 is [A,B,C,D]
     fa(m:Map(A,B*C*D),m1:Map(A,B),m2:Map(A,C),m3:Map(A,D))
       map_compose3((map_project31 m),(map_project32 m),(map_project33 m)) = m 

%  theorem combine_map_project31_map_project32_cond is [A,B,C,D]
%     fa(m:Map(A,B*C*D),m1:Map(A,B),m2:Map(A,C),m3:Map(A,D))
%       (  ((map_project31 m) = m1) =>
%          (((map_project32 m) = m2) = (m = map_compose(m1,m2)))
%       )

  theorem map_compose3_project31_simplify is [A,B,C,D]
     fa(m:Map(A,B*C*D),m1:Map(A,B),m2:Map(A,C),m3:Map(A,D))
       (m = map_compose3(m1,m2,m3)) => ((map_project31 m) = m1) = true
  theorem map_compose3_project32_simplify is [A,B,C,D]
     fa(m:Map(A,B*C*D),m1:Map(A,B),m2:Map(A,C),m3:Map(A,D))
       (m = map_compose3(m1,m2,m3)) => ((map_project32 m) = m2) = true
  theorem map_compose3_project33_simplify is [A,B,C,D]
     fa(m:Map(A,B*C*D),m1:Map(A,B),m2:Map(A,C),m3:Map(A,D))
       (m = map_compose3(m1,m2,m3)) => ((map_project33 m) = m3) = true

  theorem combine_of_map_projections3 is [A,B,C,D]
     fa(m:Map(A,B*C*D)) map_compose3((map_project31 m), (map_project32 m),(map_project33 m)) = m 


(******************************** The Proofs ********************************)

proof isa mapFrom_Obligation_subtype
  apply(rule Map__map_equality, simp add: Map__update)
end-proof

proof isa mapFrom_TMApply_Obligation_subtype
  sorry
end-proof

proof isa mapFrom_TMApply
  sorry
end-proof

proof isa mapUpdateSet_Obligation_subtype
  apply(rule Map__map_equality, simp add: Map__update)
end-proof

proof isa mapFrom_if_shadow
  sorry
end-proof

proof isa mapFrom_identity_Obligation_subtype
  sorry
end-proof

proof isa mapFrom_identity
  sorry
end-proof

proof isa domain_of_mapFrom
  sorry
end-proof

proof isa update_map_prepend_Obligation_subtype
  sorry
end-proof

proof isa map2DFrom_Obligation_subtype
  sorry
end-proof

proof isa map_compose_Obligation_subtype
  sorry
end-proof

proof isa map_compose_Obligation_subtype0
  sorry
end-proof

proof isa map_project1_Obligation_subtype
  sorry
end-proof

proof isa map_project2_Obligation_subtype
  sorry
end-proof

proof isa TMApply_map_project1_Obligation_subtype
  sorry
end-proof

proof isa TMApply_map_project1_Obligation_subtype0
  sorry
end-proof

proof isa TMApply_map_project1
  sorry
end-proof

proof isa TMApply_map_project2_Obligation_subtype
  sorry
end-proof

proof isa TMApply_map_project2_Obligation_subtype0
  sorry
end-proof

proof isa TMApply_map_project2
  sorry
end-proof

proof isa update_map_project1_Obligation_subtype
  sorry
end-proof

proof isa update_map_project1_Obligation_subtype0
  sorry
end-proof

proof isa update_map_project1
  sorry
end-proof

proof isa update_map_project2_Obligation_subtype
  sorry
end-proof

proof isa update_map_project2_Obligation_subtype0
  sorry
end-proof

proof isa update_map_project2
  sorry
end-proof

proof isa combine_map_project1_map_project2_Obligation_subtype
  sorry
end-proof

proof isa combine_map_project1_map_project2
  sorry
end-proof

proof isa combine_map_project1_map_project2_cond_Obligation_subtype
  sorry
end-proof

proof isa combine_map_project1_map_project2_cond
  sorry
end-proof

proof isa combine_map_project1_map_project2_simplify_Obligation_subtype
  sorry
end-proof

proof isa combine_map_project1_map_project2_simplify
  sorry
end-proof

proof isa combine_of_map_projections_Obligation_subtype
  sorry
end-proof

proof isa combine_of_map_projections
  sorry
end-proof


proof isa map_compose3_Obligation_subtype
  sorry
end-proof

proof isa map_compose3_Obligation_subtype0
  sorry
end-proof

proof isa map_compose3_Obligation_subtype1
  sorry
end-proof

proof isa map_project31_Obligation_subtype
  sorry
end-proof

proof isa map_project32_Obligation_subtype
  sorry
end-proof

proof isa map_project33_Obligation_subtype
  sorry
end-proof

proof isa TMApply_map_project31_Obligation_subtype
  sorry
end-proof

proof isa TMApply_map_project31_Obligation_subtype0
  sorry
end-proof

proof isa TMApply_map_project31
  sorry
end-proof

proof isa TMApply_map_project32_Obligation_subtype
  sorry
end-proof

proof isa TMApply_map_project32_Obligation_subtype0
  sorry
end-proof

proof isa TMApply_map_project32
  sorry
end-proof

proof isa TMApply_map_project33_Obligation_subtype
  sorry
end-proof

proof isa TMApply_map_project33_Obligation_subtype0
  sorry
end-proof

proof isa TMApply_map_project33
  sorry
end-proof

proof isa update_map_project31_Obligation_subtype
  sorry
end-proof

proof isa update_map_project31_Obligation_subtype0
  sorry
end-proof

proof isa update_map_project31_Obligation_subtype1
  sorry
end-proof

proof isa update_map_project31
  sorry
end-proof

proof isa update_map_project32_Obligation_subtype
  sorry
end-proof

proof isa update_map_project32_Obligation_subtype0
  sorry
end-proof

proof isa update_map_project32_Obligation_subtype1
  sorry
end-proof

proof isa update_map_project32
  sorry
end-proof

proof isa update_map_project33_Obligation_subtype
  sorry
end-proof

proof isa update_map_project33_Obligation_subtype0
  sorry
end-proof

proof isa update_map_project33_Obligation_subtype1
  sorry
end-proof

proof isa update_map_project33
  sorry
end-proof

proof isa combine_map_project3_Obligation_subtype
  sorry
end-proof

proof isa combine_map_project3
  sorry
end-proof

proof isa map_compose3_project31_simplify_Obligation_subtype
  sorry
end-proof

proof isa map_compose3_project31_simplify
  sorry
end-proof

proof isa map_compose3_project32_simplify_Obligation_subtype
  sorry
end-proof

proof isa map_compose3_project32_simplify
  sorry
end-proof

proof isa map_compose3_project33_simplify_Obligation_subtype
  sorry
end-proof

proof isa map_compose3_project33_simplify
  sorry
end-proof

proof isa combine_of_map_projections3_Obligation_subtype
  sorry
end-proof

proof isa combine_of_map_projections3
  sorry
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

%% End of proofs for Maps_extended

end-spec
