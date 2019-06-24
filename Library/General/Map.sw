(* Copyright 2015 Kestrel Institute. See file LICENSE for license details *)

Map qualifying spec

import Set

% ------------------------------------------------------------------------------
% ---------- Part 1: Specifications --------------------------------------------
% ------------------------------------------------------------------------------


(* We model a map from A to B as a "partial" function from A to B, where
"partiality" is realized via Option. (Recall that in Metaslang all functions are
total.) *)

type Map(a,b) = a -> Option b

% -------------------------------------------------------------
% domain and range:

op [a,b] domain (m:Map(a,b)) : Set a = fn x:a -> m x ~= None

op [a,b] range (m:Map(a,b))  : Set b = fn y:b -> (ex(x:a) m x = Some y)

op [a,b] definedAt (m: Map(a,b), x:a) infixl 20 : Bool =
  x in? domain m
proof Isa -> definedAt_m end-proof

op [a,b] undefinedAt (m: Map(a,b), x:a) infixl 20 : Bool =
  x nin? domain m
proof Isa -> undefinedAt_m end-proof

% -------------------------------------------------------------
% forward and backward composition:

op [a,b,c] :> (m1:Map(a,b), m2:Map(b,c)) infixl 24 : Map(a,c) =
  fn x:a -> case m1 x of Some y -> m2 y | None -> None

op [a,b,c] o (m1:Map(b,c), m2:Map(a,b)) infixl 24 : Map(a,c) = m2 :> m1

op [a,b,c] map (f: b -> c) (m: Map(a,b)) : Map(a,c) =
  fn x:a -> case m x of Some y -> Some (f y) | None -> None

% -------------------------------------------------------------
% application of map to element/set in domain:

op [a,b] @ (m:Map(a,b), x:a | x in? domain m) infixl 30 : b =
  let Some y = m x in y
proof Isa -> @_m end-proof              % Avoid overloading

op [a,b] maps? (m: Map(a,b)) (x:a) (y:b) : Bool =
  m definedAt x && m @ x = y

op [a,b] applys (m: Map(a,b)) (xS: Set a) : Set b =
  fn y:b -> (ex (x:a) x in? xS && maps? m x y)

% -------------------------------------------------------------
% application of inverse map to element/set in range:

op [a,b] applyi (m: Map(a,b)) (y:b) : Set a =
  fn x:a -> maps? m x y

op [a,b] applyis (m: Map(a,b)) (yS: Set b) : Set a =
  fn x:a -> (ex (y:b) y in? yS && maps? m x y)

% -------------------------------------------------------------
% (strict) sub/supermap:

op [a,b] <= (m1:Map(a,b), m2:Map(a,b)) infixl 20 : Bool =
  fa(x:a) x in? domain m1 => m1 x = m2 x

op [a,b] < (m1:Map(a,b), m2:Map(a,b)) infixl 20 : Bool =
  m1 <= m2 && m1 ~= m2
proof Isa -> <_m end-proof              % Avoid overloading

op [a,b] >= (m1:Map(a,b), m2:Map(a,b)) infixl 20 : Bool =
  m2 <= m1

op [a,b] > (m1:Map(a,b), m2:Map(a,b)) infixl 20 : Bool =
  m2 < m1
proof Isa -> >_m end-proof              % Avoid overloading

% -------------------------------------------------------------
% empty map:

op [a,b] empty : Map(a,b) = fn x:a -> None

op [a,b] empty? (m:Map(a,b)) : Bool = (m = empty)

op [a,b] nonEmpty? (m:Map(a,b)) : Bool = (m ~= empty)

% -------------------------------------------------------------
% singleton map:

op [a,b] single (x:a) (y:b) : Map(a,b) = fn z:a -> if z = x then Some y else None

op [a,b] single? (m: Map(a,b)) : Bool = single? (domain m)

% -------------------------------------------------------------
% identity map:

% op [a] id (dom: Set a) : Map(a,a) = fn x:a -> Some x

op [a] id (dom: Set a) : Map(a,a) =
  fn x:a -> if x in? dom then Some x else None

% -------------------------------------------------------------
% update map at point(s) (analogous to record update):

op [a,b] <<< (m1:Map(a,b), m2:Map(a,b)) infixl 25 : Map(a,b) =
  fn x:a -> case m2 x of Some y -> Some y | None -> m1 x

op [a,b] update (m: Map(a,b)) (x:a) (y:b) : Map(a,b) =
  fn z:a -> if z = x then Some y else m z

% -------------------------------------------------------------
% restrict domain/range to set:

op [a,b] restrictDomain (m:Map(a,b), xS:Set a) infixl 25 : Map(a,b) =
  fn x:a -> if x in? xS then m x else None

op [a,b] restrictRange (m:Map(a,b), yS:Set b) infixl 25 : Map(a,b) =
  fn x:a -> if x in? domain m && (m @ x) in? yS then m x else None

% -------------------------------------------------------------
% remove domain value(s) from map:

op [a,b] -- (m:Map(a,b), xS:Set a) infixl 25 : Map(a,b) =
  fn x:a -> if x in? xS then None else m x
proof Isa -> --_m end-proof

op [a,b] - (m: Map(a,b), x:a) infixl 25 : Map(a,b) = m -- single x
proof Isa -> mless [simp] end-proof

% -------------------------------------------------------------
% injectivity/surjectivity/bijectivity:

op [a,b] injective? (m:Map(a,b)) : Bool =
  fa (x1:a, x2:a) x1 in? domain m && x2 in? domain m && m x1 = m x2 => x1 = x2

type InjectiveMap(a,b) = (Map(a,b) | injective?)
proof Isa -typedef
 by (rule_tac x="Map__update Map.empty x y" in exI,
     simp add:  Map__injective_p_def Map__update_def dom_if )
end-proof

theorem InjectiveMap_injective is  [a,b] fa (m:InjectiveMap(a,b)) injective? m

op [a,b] inverse (m: InjectiveMap(a,b)) : InjectiveMap(b,a) =
  fn y:b -> (let yS = applyi m y in
             if yS = empty then None else Some (theMember yS))

op [a,b] totalOn? (s:Set a) (r:Map(a,b)) : Bool =
  domain r = s

op [a,b] surjectiveOn? (s:Set b) (r:Map(a,b)) : Bool =
  range r = s

op [a,b] bijectiveOn? (s:Set a) (s':Set b) : Map(a,b) -> Bool =
  totalOn? s /\ surjectiveOn? s' /\ injective?

% -------------------------------------------------------------
% cardinalities:

op [a,b] finite?      (m:Map(a,b)) : Bool = finite?      (domain m)
op [a,b] infinite?    (m:Map(a,b)) : Bool = infinite?    (domain m)
op [a,b] countable?   (m:Map(a,b)) : Bool = countable?   (domain m)
op [a,b] uncountable? (m:Map(a,b)) : Bool = uncountable? (domain m)

type      FiniteMap(a,b) = (Map(a,b) | finite?)
proof Isa -typedef
 by (rule_tac x="Map.empty" in exI, simp)
end-proof


theorem FiniteMap_finite is  [a,b] fa (m:FiniteMap(a,b)) finite? m


theorem update_preserves_finite1 is [a,b]
  fa (m:Map(a,b), x:a, y:b) finite? (domain (update m x y)) = finite? (domain m)

theorem update_preserves_finite is [a,b]
  fa (m:Map(a,b), x:a, y:b) finite? (update m x y) = finite? m

type    InfiniteMap(a,b) = (Map(a,b) | infinite?)
type   CountableMap(a,b) = (Map(a,b) | countable?)
type UncountableMap(a,b) = (Map(a,b) | uncountable?)

% -------------------------------------------------------------
% convert association list to map:

op [a,b] fromAssocList
   (alist: List (a * b) | let (xs,_) = unzip alist in noRepetitions? xs)
   : FiniteMap (a, b) =
  let (xs,ys) = unzip alist in
  fn x:a -> if x in? xs then Some (ys @ (positionOf(xs,x))) else None

% -------------------------------------------------------------
% map intersection/union

op [a,b] agree? (m1: Map(a,b), m2: Map(a,b)) : Bool =
  fa(x:a) x in? domain m1 && x in? domain m2 => m1 x = m2 x

op [a,b] /\ (m1: Map(a,b), m2: Map(a,b) | agree?(m1,m2)) infixr 25 : Map(a,b) =
  fn x:a -> if x in? domain m1 && x in? domain m2 then m1 x else None
proof Isa -> /\_m end-proof

op [a,b] \/ (m1: Map(a,b), m2: Map(a,b) | agree?(m1,m2)) infixr 24 : Map(a,b) =
  fn x:a -> if x in? domain m1 then m1 x
            else if x in? domain m2 then m2 x else None
proof Isa -> \/_m end-proof

% ------------------------------------------------------------------------------
% ---------- Part 2: Theorems about properties of operations -------------------
% ------------------------------------------------------------------------------

theorem dom_update is [a,b]
  fa(m:Map(a,b),x:a,y:b) domain (update m x y) = domain m <| x

theorem at_update_same is [a,b]
  fa(m:Map(a,b),x:a,y:b) (update m x y) @ x = y

theorem at_update_diff is [a,b]
  fa(m:Map(a,b), x1:a, x2:a, y:b) (x1 ~= x2) && x2 in? domain m => ((update m x1 y) @ x2 = (m @ x2))

theorem double_update is [a,b]
  fa(m:Map(a,b), x:a, y:b, z:b) update (update m x y) x z  = update m x z

%%TODO add a theorem about reordering the updates if the keys are different

% ------------------------------------------------------------------------------
% ---------- Part 3: Main theorems ---------------------------------------------
% ------------------------------------------------------------------------------

% ------------------------------------------------------------------------------
% ---------- Part 4: Theory Morphisms ------------------------------------------
% ------------------------------------------------------------------------------


% ------------------------------------------------------------------------------
% ---------- Mapping to Isabelle -----------------------------------------------
% ------------------------------------------------------------------------------


proof Isa Thy_Morphism
  type Map.Map       -> map
  Map.domain         -> dom
  Map.range          -> ran
  Map.:>             -> \<circ>\<^sub>m   Left  55 reversed
  Map.o              -> \<circ>\<^sub>m   Left  55
  Map.<=             -> \<subseteq>\<^sub>m Left  50
  Map.empty          -> Map.empty
  Map.<<<            -> ++                  Left 100
  Map.restrictDomain -> |`                  Left 110
end-proof



% ------------------------------------------------------------------------------
% ---------- Part 5: The proofs ------------------------------------------------
% ------------------------------------------------------------------------------
% Note: for the time being we place Isabelle lemmas that are needed for a proof
%       and cannot be expressed in SpecWare as "verbatim" lemmas into the
%       preceeding proofs
% ------------------------------------------------------------------------------

% Some proofs can be removed, as the obligation isn't generated anymore

proof Isa range__def
 by (auto simp: ran_def)
end-proof

proof Isa maps_p_Obligation_subtype
 by (auto simp: definedAt_m_def)
end-proof

proof Isa e_lt_eq__def
  by (auto simp: map_le_def)
end-proof

proof Isa empty_p [simp] end-proof

proof Isa e_lt_lt_lt__def
  by (auto simp: map_add_def split: option.split)
end-proof

proof Isa e_lt_lt_lt__def1
  by (auto simp: map_add_def)
end-proof

proof Isa InjectiveMap_injective [simp]
  by (case_tac "m", simp add: Abs_Map__InjectiveMap_inverse)

(******************************************************************************)
declare Rep_Map__InjectiveMap_inverse [simp add]
declare Abs_Map__InjectiveMap_inverse [simp add]
(******************************************************************************)

(* Here is a very specific form that I need *)

lemma Rep_Map__InjectiveMap_simp [simp]:
  "\<lbrakk>Map__injective_p y\<rbrakk>
   \<Longrightarrow>  (Rep_Map__InjectiveMap x = y) = (x = Abs_Map__InjectiveMap y)"
by auto
(******************************************************************************)

lemma Map__Map__applyi_simp:
  "Map__applyi m y  = {x. x \<in> dom m \<and> m x = Some y}"
  by (simp add: Map__applyi_def Map__maps_p_def definedAt_m_def
                Map__domain__def e_at_m_def,
      auto simp add:  split: option.split)

lemma Map__Map__applys_simp:
  "Map__applys m S  = {y. \<exists>x. x \<in> S \<and> m x = Some y}"
  apply (simp add: Map__applys_def Map__maps_p_def definedAt_m_def
                Map__domain__def e_at_m_def,
      auto simp add:  split: option.split)
(******************************************************************************)


end-proof

proof Isa inverse_Obligation_subtype
  apply (case_tac "m",
         auto simp add: Map__injective_p_def Let_def split: if_splits)
  apply (simp add: Map__Map__applyi_simp)
  apply (rotate_tac -2, thin_tac _, thin_tac _, erule notE)
  apply (subgoal_tac "the_elem {x \<in> dom y. y x = Some x1} = x
                    \<and> the_elem {x \<in> dom y. y x = Some x2} = xa",
         clarsimp,  thin_tac "m = _", thin_tac "_ = _", auto)
  apply (simp add: the_elem_def set_eq_iff, rule the_equality, auto)
  apply (drule spec, drule spec, erule mp, simp add: Map__domain__def)
  apply (rotate_tac -1, drule_tac x=x in spec, auto)
  apply (simp add: the_elem_def set_eq_iff, rule the_equality, auto)
  apply (drule spec, drule spec, erule mp, simp add: Map__domain__def)
  apply (rotate_tac -1, drule_tac x=xa in spec, auto)
end-proof

proof Isa inverse_Obligation_subtype0
  apply (case_tac "m",
         auto simp add: Map__injective_p_def Let_def split: if_splits)
  apply (rotate_tac -2, drule_tac x=x in spec, simp add: Map__Map__applyi_simp)
  apply (erule notE, auto simp add: set_eq_iff)
  apply (drule spec, drule spec, erule mp, simp add: Map__domain__def)
end-proof

proof Isa finite_p [simp] end-proof

proof Isa FiniteMap_finite [simp]
  apply (case_tac "m", simp)
  using Rep_Map__FiniteMap by auto

(******************************************************************************)
declare Rep_Map__FiniteMap_inverse [simp add]
declare Abs_Map__FiniteMap_inverse [simp add]
(******************************************************************************)

(* Here is a very specific form that I need *)

lemma Map__FiniteMap_has_finite_domain [simp]:
  "finite (dom (Rep_Map__FiniteMap m))"
  by (case_tac "m", simp)

lemma Rep_Map__FiniteMap_simp [simp]:
  "\<lbrakk>Map__finite_p y\<rbrakk> \<Longrightarrow>  (Rep_Map__FiniteMap x = y) = (x = Abs_Map__FiniteMap y)"
  by (subst Abs_Map__FiniteMap_inject [symmetric], auto)

end-proof


proof Isa update_preserves_finite1 [simp]
  apply (auto simp add: Map__update_def dom_if)
  apply (erule rev_mp,
         rule_tac t="{z. z \<noteq> x}" and s="UNIV - {x}" in subst,
         auto simp add: Diff_Int_distrib)
end-proof

proof Isa fromAssocList_Obligation_subtype
  by (simp add: member_def dom_if)
end-proof

proof Isa fromAssocList_Obligation_subtype1
  apply (cut_tac d__x=alist in List__unzip_subtype_constr)
  apply (auto simp add:  dom_if member_def
         List__positionOf_def List__theElement_def)

(******************************************************************************
*** Note the correct type of Map__fromAssocList__stp is
consts Map__fromAssocList__stp :: "('a \<Rightarrow> bool) \<Rightarrow>
                                   ('a \<times> 'b) list \<Rightarrow>  ('a, 'b)Map__FiniteMap"
******************************************************************************)

end-proof

proof Isa fromAssocList_Obligation_subtype2
  by (metis List__equiLong_def List__positionOf_length2 List__unzip_subtype_constr prod.case prod.inject)
end-proof

% ------------------------------------------------------------------------------
% ---------- Part 6: verbatim Isabelle lemmas             ----------------------
% ----------         that cannot be expressed in SpecWare ----------------------
% ------------------------------------------------------------------------------


%  ---------- most of the following can be converted into SpecWare Theorems
% ----------- need to do this later

proof Isa -verbatim

lemma Map__fromAssocList_empty [simp]:
  "Rep_Map__FiniteMap (Map__fromAssocList [])  = Map.empty"
  by (simp add: Map__fromAssocList_def dom_if)

lemma Map__fromAssocList_singleton [simp]:
  "Rep_Map__FiniteMap (Map__fromAssocList [(x,y)]) = Map__update Map.empty x y "
  by (simp add: Map__fromAssocList_def dom_if Map__update_def ext)

lemma Map__singleton_element [simp]:
  "Map__update Map.empty x y x = Some y"
  by (simp add: Map__update_def)

end-proof
% ------------------------------------------------------------------------------

%% TODO This should be in [simp], but I am afraid of breaking things before we have the regression tests running. -EWS
proof isa Map__dom_update
  by(auto simp: Map__update_def)
end-proof

proof isa Map__at_update_same_Obligation_subtype
  by (simp add: Map__dom_update)
end-proof

%% TODO This should be in [simp], but I am afraid of breaking things before we have the regression tests running. -EWS
proof isa Map__at_update_same
  by(simp add:Map__update_def e_at_m_def)
end-proof

proof isa Map__at_update_diff_Obligation_subtype
  by (simp add: Map__dom_update)
end-proof

proof isa Map__at_update_diff
  by(simp add:Map__update_def e_at_m_def)
end-proof

proof isa Map__double_update [simp]
  by (rule ext, simp add: Map__update_def)
end-proof

endspec
