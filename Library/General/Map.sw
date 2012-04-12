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
 by (rule_tac x="Map__update empty x y" in exI,
     simp add: mem_def Map__injective_p_def Map__update_def dom_if Collect_def)
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
 by (rule_tac x="empty" in exI, simp add: mem_def Map__finite_p_def Collect_def)
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
  fa(m:Map(a,b), x1:a, x2:{x2:a | x2 in? domain m}, y:b) (x1 ~= x2) => ((update m x1 y) @ x2 = (m @ x2))

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


proof Isa Thy_Morphism Map
  type Map.Map       -> map
  Map.domain         -> dom
  Map.range          -> ran
  Map.:>             -> o_m                 Left  55 reversed
  Map.o              -> o_m                 Left  55
  Map.<=             -> \<subseteq>\<^sub>m Left  50
  Map.empty          -> empty
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
  by (case_tac "m",
      simp add: Abs_Map__InjectiveMap_inverse Map__InjectiveMap_def 
                Collect_def mem_def)

(******************************************************************************)
declare Rep_Map__InjectiveMap_inverse [simp add]
declare Abs_Map__InjectiveMap_inverse [simp add]
(******************************************************************************)

(* Here is a very specific form that I need *)

lemma Rep_Map__InjectiveMap_simp [simp]:
  "\<lbrakk>Map__injective_p y\<rbrakk>
   \<Longrightarrow>  (Rep_Map__InjectiveMap x = y) = (x = Abs_Map__InjectiveMap y)"
apply (subst Abs_Map__InjectiveMap_inject [symmetric],
       simp add: Rep_Map__InjectiveMap,
       simp add: Map__InjectiveMap_def Collect_def mem_def,
       simp add: Rep_Map__InjectiveMap_inverse)
done
(******************************************************************************)

lemma Map__Map__applyi_simp:
  "Map__applyi m y  = {x. x \<in> dom m \<and> m x = Some y}"
  by (simp add: Map__applyi_def Map__maps_p_def definedAt_m_def 
                Map__domain__def e_at_m_def,
      auto simp add: mem_def split: option.split)

lemma Map__Map__applys_simp:
  "Map__applys m S  = {y. \<exists>x. x \<in> S \<and> m x = Some y}"
  apply (simp add: Map__applys_def Map__maps_p_def definedAt_m_def 
                Map__domain__def e_at_m_def,
      auto simp add: mem_def split: option.split, 
      rule exI, auto)
(******************************************************************************)


end-proof

proof Isa inverse_Obligation_subtype
  apply (case_tac "m", 
         simp add: Map__InjectiveMap_def Collect_def mem_def,
         auto simp add: Map__injective_p_def Let_def split: split_if_asm)
  apply (simp add: Map__Map__applyi_simp)
  apply (rotate_tac -2, thin_tac ?P, thin_tac ?P, erule notE)
  apply (subgoal_tac "the_elem {x \<in> dom y. y x = Some x1} = x
                    \<and> the_elem {x \<in> dom y. y x = Some x2} = xa",
         clarsimp, thin_tac "?a = ?b", auto)
  apply (simp add: the_elem_def set_eq_iff, rule the_equality, auto)
  apply (drule spec, drule spec, erule mp, simp add: Map__domain__def)
  apply (rotate_tac -1, drule_tac x=x in spec, auto)
  apply (simp add: the_elem_def set_eq_iff, rule the_equality, auto)
  apply (drule spec, drule spec, erule mp, simp add: Map__domain__def)
  apply (rotate_tac -1, drule_tac x=xa in spec, auto)
end-proof

proof Isa inverse_Obligation_subtype0
  apply (case_tac "m", 
         simp add: Map__InjectiveMap_def Collect_def mem_def,
         auto simp add: Map__injective_p_def Let_def split: split_if_asm)
  apply (rotate_tac -2, drule_tac x=x in spec, simp add: Map__Map__applyi_simp)
  apply (erule notE, auto simp add: set_eq_iff)
  apply (drule spec, drule spec, erule mp, simp add: Map__domain__def)
end-proof

proof Isa finite_p [simp] end-proof

proof Isa FiniteMap_finite [simp]
  by (case_tac "m",
      simp add: Abs_Map__FiniteMap_inverse Map__FiniteMap_def 
                Collect_def mem_def)

(******************************************************************************)
declare Rep_Map__FiniteMap_inverse [simp add]
declare Abs_Map__FiniteMap_inverse [simp add]
(******************************************************************************)

(* Here is a very specific form that I need *)

lemma Map__FiniteMap_has_finite_domain [simp]:
  "finite (dom (Rep_Map__FiniteMap m))"
  by (case_tac "m",
      simp add: Abs_Map__FiniteMap_inverse Map__FiniteMap_def 
                Collect_def mem_def)

lemma Rep_Map__FiniteMap_simp [simp]:
  "\<lbrakk>Map__finite_p y\<rbrakk> \<Longrightarrow>  (Rep_Map__FiniteMap x = y) = (x = Abs_Map__FiniteMap y)"
apply (subst Abs_Map__FiniteMap_inject [symmetric],
       simp add: Rep_Map__FiniteMap,
       simp add: Map__FiniteMap_def Collect_def mem_def,
       simp add: Rep_Map__FiniteMap_inverse)
(******************************************************************************)

end-proof


proof Isa update_preserves_finite1 [simp]
  apply (auto simp add: Map__update_def mem_def dom_if)
  apply (erule rev_mp,
         rule_tac t="{z. z \<noteq> x}" and s="UNIV - {x}" in subst, 
         auto simp add: Diff_Int_distrib)
end-proof

proof Isa update_preserves_finite1 [simp] end-proof

proof Isa fromAssocList_Obligation_subtype 
  by (simp add: member_def dom_if)
end-proof

proof Isa fromAssocList_Obligation_subtype1
  apply (cut_tac d__x=alist in List__unzip_subtype_constr)  
  apply (auto simp add: Collect_def dom_if member_def 
         List__positionOf_def List__theElement_def)
  apply (rule the1I2,
         rule List__theElement_Obligation_the, 
         rule List__positionOf_Obligation_subtype,
         simp_all add: member_def List__positionsOf_subtype_constr)
  apply (simp add: List__positionsOf_def List__positionsSuchThat_def)
  apply (rotate_tac -1, erule rev_mp)
  apply (rule the1I2,
         cut_tac l=xs_1 and p="\<lambda>z. z=x" 
            in List__positionsSuchThat_Obligation_the, 
         simp, clarify)
  apply (drule spec, auto)

(******************************************************************************
*** Note the correct type of Map__fromAssocList__stp is
consts Map__fromAssocList__stp :: "('a \<Rightarrow> bool) \<Rightarrow> 
                                   ('a \<times> 'b) list \<Rightarrow>  ('a, 'b)Map__FiniteMap"
******************************************************************************)

end-proof
  

% ------------------------------------------------------------------------------
% ---------- Part 6: verbatim Isabelle lemmas             ----------------------
% ----------         that cannot be expressed in SpecWare ----------------------
% ------------------------------------------------------------------------------


%  ---------- most of the following can be converted into SpecWare Theorems 
% ----------- need to do this later

proof Isa -verbatim

(******************************************************************************)
lemma finiteRange [simp]: 
  "finite  (\<lambda> (x::int). l \<le> x \<and> x \<le> u)"
  by (rule_tac t="\<lambda>x. l \<le> x \<and> x \<le> u" and  s="{l..u}" 
      in subst, simp_all,
      auto simp add: atLeastAtMost_def atLeast_def atMost_def mem_def)

lemma finiteRange2 [simp]: 
  "finite  (\<lambda>(x::int). l \<le>  x \<and>  x < u)"
  by (rule_tac t="\<lambda>(x::int). l \<le>  x \<and>  x < u" and  s="{l..u - 1}" 
      in subst, simp_all,
      auto simp add: atLeastAtMost_def atLeast_def atMost_def mem_def)

(******************************************************************************)

(******* ZIP ... move into the base libraries ********)

lemma List__unzip_zip_inv [simp]:
  "\<lbrakk>l1 equiLong l2\<rbrakk> \<Longrightarrow> List__unzip (zip l1 l2) = (l1,l2)"
  apply (simp add: List__unzip_def del: List__equiLong_def)
  apply (rule_tac t="zip l1 l2"
              and s="(\<lambda>(x_1, x_2). zip x_1 x_2)(l1,l2)" in subst, simp)
  apply (cut_tac List__unzip_Obligation_subtype,
         simp only: TRUE_def Function__bijective_p__stp_univ)
  apply (subst Function__inverse__stp_simp, simp)
  apply (subst inv_on_f_f, simp_all add: bij_on_def mem_def)
done

lemma List__unzip_as_zip [simp]:
  "\<lbrakk>List__unzip l = (l1,l2)\<rbrakk> \<Longrightarrow>  l = (zip l1 l2)"
  apply (simp add: List__unzip_def del: List__equiLong_def)
  apply (rule_tac t="zip l1 l2" and s="split zip (l1,l2)" in subst, simp)
  apply (drule sym, erule ssubst)
  apply (cut_tac List__unzip_Obligation_subtype,
         simp only: TRUE_def Function__bijective_p__stp_univ)
  apply (subst Function__inverse__stp_simp, auto)
  apply (cut_tac y=l and f="split zip" and A="\<lambda>(x, y). x equiLong y" 
             and B=UNIV in surj_on_f_inv_on_f)
  apply (simp_all add: bij_on_def del: List__equiLong_def)
done

lemma List__unzip_zip_conv:
  "\<lbrakk>l1 equiLong l2\<rbrakk> \<Longrightarrow> (List__unzip l = (l1,l2)) = (l = (zip l1 l2))"
  by auto

lemma List__unzip_empty [simp]:
  "List__unzip [] = ([],[])"
  by (simp add:  List__unzip_zip_conv)

lemma List__unzip_singleton [simp]:
  "List__unzip [(x,y)] = ([x],[y])"
  by (simp add:  List__unzip_zip_conv)

lemma List__unzip_cons [simp]:
  "\<lbrakk>List__unzip l = (l1,l2)\<rbrakk> \<Longrightarrow> List__unzip ((x,y) # l) = (x#l1,y#l2)"
  by (cut_tac d__x=l in List__unzip_subtype_constr,
      simp add: List__unzip_zip_conv)

lemma List__unzip_append [simp]:
  "\<lbrakk>List__unzip l = (l1,l2); List__unzip l' = (l1',l2')\<rbrakk>
   \<Longrightarrow> List__unzip (l @ l') = (l1@l1', l2@l2')"
  by (cut_tac d__x=l in List__unzip_subtype_constr,
      cut_tac d__x="l'" in List__unzip_subtype_constr,
      simp add: List__unzip_zip_conv)

lemma List__unzip_snoc [simp]:
  "\<lbrakk>List__unzip l = (l1,l2)\<rbrakk>
   \<Longrightarrow> List__unzip (l @ [(x,y)]) = (l1@[x], l2@[y])"
  by simp

lemma List__unzip_double [simp]:
  "List__unzip [(x,y),(u,v)] = ([x,u],[y,v])"
  by simp

(******* Increasing ********)


lemma List__increasingNats_p_nil [simp]:
   "List__increasingNats_p []"
  by (simp add: List__increasingNats_p_def)

lemma List__increasingNats_p_snoc [simp]:
   "List__increasingNats_p (l @ [i]) = 
        (List__increasingNats_p l \<and> (\<forall>j \<in> set l. j < i))"
  by (auto simp add: List__increasingNats_p_def 
                     nth_append not_less set_conv_nth,
      induct_tac ia rule: strict_inc_induct, auto)

lemma List__increasingNats_p_singleton [simp]:
   "List__increasingNats_p [i]" 
  by (simp add: List__increasingNats_p_def)

lemma sorted_equals_nth_mono2:
  "sorted xs = (\<forall>j < length xs. \<forall>i < length xs - j. xs ! j \<le> xs ! (j+i))"
  apply (auto simp add: sorted_equals_nth_mono)
  apply (drule_tac x=i in spec, simp,
         drule_tac x="j-i" in spec, auto)
done

lemma  List__increasingNats_p_is_sorted [simp]:
  "\<lbrakk>List__increasingNats_p l\<rbrakk> \<Longrightarrow> sorted l"
  apply (auto simp add: List__increasingNats_p_def sorted_equals_nth_mono2)
  apply (rotate_tac -1, erule rev_mp, rule_tac n="i" in nat_induct, auto)
  apply (drule_tac x="j+n" in spec, auto simp only: int_1 [symmetric] zdiff_int)
done

(****** Positions *********)

lemma List__positionsSuchThat_distinct [simp]: 
  "distinct (List__positionsSuchThat(l, p))"
  by (simp add: List__positionsSuchThat_subtype_constr)

lemma List__positionsSuchThat_increasing [simp]: 
  "List__increasingNats_p (List__positionsSuchThat(l, p))"
  by (simp add: List__positionsSuchThat_def,
      rule the1I2, 
      simp_all add: List__positionsSuchThat_Obligation_the)

lemma List__positionsSuchThat_membership [simp]: 
  "i mem  List__positionsSuchThat(l, p) = (i < length l \<and> p (l ! i))"
  by (simp add: List__positionsSuchThat_def,
      rule the1I2, 
      simp_all add: List__positionsSuchThat_Obligation_the)

lemma List__positionsSuchThat_membership2 [simp]: 
  "i \<in> set (List__positionsSuchThat(l, p)) = (i < length l \<and> p (l ! i))"
  by simp

lemma List__positionsSuchThat_nil [simp]:
  "List__positionsSuchThat ([], p) = []"
  by (simp add: List__positionsSuchThat_def member_def,
      rule the_equality, auto)

lemma List__positionsSuchThat_snoc1 [simp]:
  "\<lbrakk>p x\<rbrakk> \<Longrightarrow> 
   List__positionsSuchThat (l@[x], p) = List__positionsSuchThat (l, p) @ [length l]"
  apply (subst List__positionsSuchThat_def, simp)
  apply (rule the_equality, simp add: member_def nth_append, safe, simp_all)
  apply (simp add: List__positionsSuchThat_def)
  apply (rule the1I2, simp add: List__positionsSuchThat_Obligation_the)
  apply (rule sorted_distinct_set_unique, 
         auto simp add: set_eq_iff less_Suc_eq nth_append)
done

lemma List__positionsSuchThat_snoc2 [simp]:
  "\<lbrakk>\<not> (p x)\<rbrakk> \<Longrightarrow> 
   List__positionsSuchThat (l@[x], p) = List__positionsSuchThat (l, p)"
  apply (subst List__positionsSuchThat_def, simp)
  apply (rule the_equality, simp add: member_def nth_append, safe)
  apply (simp add: List__positionsSuchThat_def)
  apply (rule the1I2, simp add: List__positionsSuchThat_Obligation_the)
  apply (rule sorted_distinct_set_unique, 
         auto simp add: set_eq_iff less_Suc_eq nth_append)
done

lemma List__positionsOf_nil [simp]:
  "List__positionsOf ([], x) = []"
  by (simp add: List__positionsOf_def)

lemma List__positionsOf_snoc1 [simp]:
  "List__positionsOf (l@[x], x) = List__positionsOf (l, x) @ [length l]"
  by (simp add: List__positionsOf_def)

lemma List__positionsOf_snoc2 [simp]:
  "\<lbrakk>a \<noteq> x\<rbrakk> \<Longrightarrow> List__positionsOf (l @ [a], x) = List__positionsOf (l, x)"
  by (simp add: List__positionsOf_def)

lemma List__positionsOf_singleton [simp]:
  "List__positionsOf ([x], x) = [0]"
  by (rule_tac t="[x]" and s="[]@[x]" in subst, simp,
      simp only: List__positionsOf_snoc1, simp)

lemma List__positionsOf_not_found [simp]:
  "\<lbrakk>\<forall>a\<in>set l. a \<noteq> x\<rbrakk> \<Longrightarrow> List__positionsOf (l, x) = []"
  by (induct l rule: rev_induct, simp_all)

lemma List__positionsOf_not_found_later [simp]:
  "\<lbrakk>\<forall>a\<in>set l'. a \<noteq> x\<rbrakk> \<Longrightarrow> List__positionsOf (l@l', x) =  List__positionsOf (l, x)"
  by (induct l' rule: rev_induct, 
      simp_all add: append_assoc [symmetric] del: append_assoc)

lemma List__positionsOf_last [simp]:
  "\<lbrakk>\<forall>a\<in>set l. a \<noteq> x\<rbrakk>
   \<Longrightarrow> List__positionsOf (l@[x], x) = [length l]"
  by simp

lemma List__positionsOf_only_one [simp]:
  "\<lbrakk>\<forall>a\<in>set l. a \<noteq> x; \<forall>a\<in>set l'. a \<noteq> x\<rbrakk>
   \<Longrightarrow> List__positionsOf (l@[x]@l', x) = [length l]"
  by (simp only: append_assoc [symmetric], simp del: append_assoc)

lemma List__positionsOf_2 [simp]:
  "\<lbrakk>a \<noteq> x\<rbrakk> \<Longrightarrow> List__positionsOf ([a,x], x) = [1]"
 by (rule_tac t="[a,x]" and s="[a]@[x]" in subst, simp,
     subst List__positionsOf_last, auto)

lemma List__theElement_singleton [simp]:
  "List__theElement [x] = x"
  by (simp add: List__theElement_def)

lemma List__positionOf_singleton [simp]:
  "List__positionOf ([x], x) = 0"
  by (simp add:  List__positionOf_def)

lemma List__positionOf_2 [simp]:
  "\<lbrakk>a \<noteq> x\<rbrakk> \<Longrightarrow> List__positionOf ([a,x], x) = 1"
  by (simp add:  List__positionOf_def)

(*********************************)

lemma Map__fromAssocList_empty [simp]:
  "Rep_Map__FiniteMap (Map__fromAssocList [])  = Map.empty"
  by (simp add: Map__fromAssocList_def Map__FiniteMap_def dom_if)


lemma Map__fromAssocList_singleton [simp]:
  "Rep_Map__FiniteMap (Map__fromAssocList [(x,y)]) = Map__update empty x y "
  by (simp add: Map__fromAssocList_def Map__FiniteMap_def dom_if 
                Map__update_def ext)


lemma Map__singleton_element [simp]: 
  "Map__update Map.empty x y x = Some y"
  by (simp add: Map__update_def)



end-proof
% ------------------------------------------------------------------------------

%% TODO This should be in [simp], but I am afraid of breaking things before we have the regression tests running. -EWS
proof isa Map__dom_update
  apply(auto simp: add Map__update_def)
end-proof

proof isa Map__at_update_same_Obligation_subtype
  apply (simp add: Map__dom_update)
end-proof

%% TODO This should be in [simp], but I am afraid of breaking things before we have the regression tests running. -EWS
proof isa Map__at_update_same
  apply(simp add:Map__update_def e_at_m_def)
end-proof

proof isa Map__at_update_diff_Obligation_subtype
  apply (simp add: Map__dom_update)
end-proof

proof isa Map__at_update_diff
  apply(simp add:Map__update_def e_at_m_def)
end-proof

proof isa Map__double_update [simp]
  by (rule ext, simp add: Map__update_def)
end-proof

endspec
