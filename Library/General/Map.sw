(* change this qualifier to "Map" -> *) MapAC qualifying spec

import Relation

%%% Generate stp version of map_result_in_range in case it is useful later
proof Isa -stp-theorems end-proof

% recall that spec `Relations' defines type `Map(a,b)'

% ------------------------------------------------------------------------------
proof Isa -verbatim
(****************************************************************************
* Isabelle defines the type of maps as functions from 'a to 'b Option
* The following theorem establishes the conversion between specware maps
* and Isabelle maps
****************************************************************************)

consts MapAC__toIsaMap :: "('a, 'b)Relation__Map \<Rightarrow> ('a \<rightharpoonup> 'b)"
       MapAC__fromIsaMap :: "('a \<rightharpoonup> 'b) \<Rightarrow> ('a, 'b)Relation__Map "
defs
   MapAC__toIsaMap_def:
   "MapAC__toIsaMap m
    \<equiv> (\<lambda>(a::'a). if a \<in> Domain m 
                                   then Some (contents (Relation__apply m a)) 
                                   else None)"
   MapAC__fromIsaMap_def:
   "MapAC__fromIsaMap m
    \<equiv> {(a,b). m a = Some b}"

lemma Relation__functional_p_alt_def:
    "Relation__functional_p m = (\<forall>x \<in> Domain m. \<exists>!y. (x, y) \<in> m)" 
 apply (simp add: Relation__functional_p_def Relation__apply_def,
        auto simp add: mem_def)
 apply(drule_tac x=x in spec, safe)
 apply (simp add: expand_set_eq, 
        frule_tac x=ya in spec,drule_tac x=yb in spec,simp add: mem_def)
 apply (thin_tac "?P", simp only: expand_set_eq mem_def, simp)
 apply (drule_tac x=x in bspec)
 apply (simp add: Domain_def, auto simp add: mem_def)
 apply (drule_tac x=xa in spec, auto simp add: mem_def)
done

lemma Relation__functional_p_unfold:
    "Relation__functional_p m = (\<forall>x. (\<exists>y. {z. (x,z)\<in>m} = {y}) \<or>  {z. (x,z)\<in>m} ={})"
 apply (auto simp add: Relation__functional_p_alt_def)
 apply (drule_tac x=x in bspec, simp add: Domain_def, auto simp add: mem_def)
 apply (drule_tac x=x in spec, safe)
 apply (simp add: expand_set_eq, drule_tac x=ya in spec, simp add: mem_def)
done

lemma Relation__finite_if_finite_domain: 
  "\<lbrakk>Relation__functional_p m; finite (Domain m)\<rbrakk>  \<Longrightarrow> finite m"
  apply (rule_tac B="(\<lambda>x. (x, THE y. (x,y)\<in>m)) ` (Domain m)" in finite_subset)
  apply (thin_tac "finite ?m", auto simp add: image_def Bex_def Domain_def)
  apply (rule exI, auto)
  apply (rule the1I2, auto simp add: Relation__functional_p_alt_def)
done

lemma MapAC_unique:
  "\<lbrakk>Relation__functional_p m; a \<in> Domain m\<rbrakk>  
   \<Longrightarrow> Set__single_p (Relation__apply m a)"
 apply (simp add: Relation__functional_p_def)
 apply (drule_tac x=a in spec, simp add: Domain_def, clarify)
 apply (auto simp add: mem_def Relation__apply_def)
done


lemma MapAC__toIsaMap_bij:
  "bij_on MapAC__toIsaMap Relation__functional_p UNIV"
  apply (simp add: bij_on_def inj_on_def surj_on_def Ball_def Bex_def mem_def)
  apply (auto simp add:  MapAC__toIsaMap_def)
  apply (auto simp add: expand_fun_eq)
  apply (drule_tac x=a in spec, simp add: Relation__apply_def split: split_if_asm)
  apply (drule_tac a=a and m=x in MapAC_unique, simp,
         drule_tac a=a and m=xa in MapAC_unique, simp, 
         simp add: Relation__apply_def, auto)
  apply (drule sym, simp add: expand_set_eq,
         drule_tac x=b in spec, simp add: mem_def)
  apply (drule_tac x=a in spec, simp add: Relation__apply_def split: split_if_asm)
  apply (drule_tac a=a and m=x in MapAC_unique, simp,
         drule_tac a=a and m=xa in MapAC_unique, simp, 
         simp add: Relation__apply_def, auto)
  apply (drule sym, simp add: expand_set_eq,
         drule_tac x=b in spec, simp add: mem_def)
  apply (rule_tac x="MapAC__fromIsaMap x" in exI, 
         auto simp add: MapAC__fromIsaMap_def)
  apply (auto simp add: Relation__functional_p_def Relation__apply_def)
  apply (auto simp add: mem_def ex_in_conv [symmetric])
  apply (rule_tac t="contents (op = b)" and s="contents {x. x=b}" in subst)
  apply (rule_tac f="contents" in arg_cong)
  apply (simp only: expand_set_eq mem_def, auto)
done


lemma MapAC__fromIsa_inv_toIsa:
  "MapAC__fromIsaMap = inv_on Relation__functional_p MapAC__toIsaMap"
  apply (rule ext, rule sym,  simp add: inv_on_def inv_into_def mem_def)
  apply (rule some1_equality, simp add: inv_on_unique  MapAC__toIsaMap_bij)
  apply (auto simp add: MapAC__fromIsaMap_def MapAC__toIsaMap_def
                        Relation__functional_p_alt_def)
  apply (auto simp add: expand_fun_eq Relation__apply_def)
  apply (rule_tac t="contents (op = b)" and s="contents {x. x=b}" in subst)
  apply (rule_tac f="contents" in arg_cong)
  apply (simp only: expand_set_eq mem_def, auto)
done
  

notation
   MapAC__toIsaMap ("_\<triangleright>" [1000] 999) 

notation
   MapAC__fromIsaMap ("\<triangleleft>_" [1000] 999) 

(******************************************************************************)
end-proof
% ------------------------------------------------------------------------------


% map (not) defined at element:

op [a,b] definedAt (m: Map(a,b), x:a) infixl 20 : Bool = x in? domain m
proof Isa [simp] end-proof        % we don't need that distinction in Isabelle

op [a,b] undefinedAt (m: Map(a,b), x:a) infixl 20 : Bool = x nin? domain m
proof Isa [simp] end-proof        % we don't need that distinction in Isabelle


% map application (op @@ is a totalization of @):

op [a,b] @ (m: Map(a,b), x:a | m definedAt x) infixl 30 : b = the(y:b) m(x,y)
proof Isa -> @_m end-proof              % Avoid overloading

op [a,b] @@ (m: Map(a,b), x:a) infixl 30 : Option b =
  if m definedAt x then Some (m @ x) else None
proof Isa -> @@_m end-proof


proof Isa e_at_Obligation_the
 apply (drule MapAC_unique, simp, simp)
 apply (simp add: unique_singleton Relation__apply_def)
end-proof

proof Isa -verbatim

lemma MapAC__e_at__stp_Obligation_the: 
  "\<lbrakk>Relation__functional_p__stp(P__a, P__b) m; P__a (x::'a); 
    MapAC__definedAt__stp P__b(m, x)\<rbrakk> \<Longrightarrow> 
   \<exists>!(y::'b). (x, y) \<in> m"
 apply (simp add: Relation__functional_p__stp_def MapAC__definedAt__stp_def)
 apply (drule_tac x=x in spec, simp add: Relation__domain__stp_def)
 apply (auto simp add: mem_def Relation__apply_def Set__single_p__stp_def)
 apply (simp add: expand_set_eq)
 apply (frule_tac x=yb in spec, drule_tac x=ya in spec, simp add: mem_def)
done

lemma MapAC__e_at_m_eq:
 "\<lbrakk>Relation__functional_p m; (a,b) \<in> m\<rbrakk> 
   \<Longrightarrow> m @_m a = b"
 apply (simp add: e_at_m_def Relation__functional_p_alt_def)
 apply (drule_tac x=a in bspec, auto simp add: Domain_def)
done


lemma MapAC__e_at_m_element:
  "\<lbrakk>Relation__functional_p m; a \<in> Domain m\<rbrakk> \<Longrightarrow> (a, m @_m a) \<in> m"
 apply (simp add: e_at_m_def Relation__functional_p_alt_def)
 apply (rule the1I2, drule_tac x=a in bspec, simp_all)
done

lemma MapAC__e_at_m_eq2:
  "\<lbrakk>P a\<rbrakk> \<Longrightarrow> {(a, b). P a \<and> b = f a } @_m a = f a"
 by (simp add: e_at_m_def)

end-proof

theorem map_result_in_range is [a,b]
  fa (m:Map(a,b), x:a) m definedAt x => (m @ x) in? range m

proof Isa map_result_in_range__stp
 apply (simp add: e_at_m_def)
 apply (rule the1I2, rule_tac P__a=P__a in MapAC__e_at__stp_Obligation_the)
 apply (auto simp add:mem_def  Relation__range__stp_def) 
end-proof

proof Isa map_result_in_range
 apply (simp add: e_at_m_def)
 apply (rule the1I2, rule MapAC__e_at_Obligation_the, auto)
end-proof

% update map at point(s) (analogous to record update):

op [a,b] <<< (m1: Map(a,b), m2: Map(a,b)) infixl 25 : Map(a,b) = the(m)
  domain m = domain m1 \/ domain m2 &&
  (fa(x) x in? domain m =>
         m @ x = (if m2 definedAt x then m2 @ x else m1 @ x))

op [a,b] update (m: Map(a,b)) (x:a) (y:b) : Map(a,b) = m <<< single (x, y)

proof Isa e_lt_lt_lt_Obligation_the
  apply (simp add: Relation__functional_p_alt_def)
  apply (rule_tac 
         a="{(a,b).  a \<in> Domain m1 \<union> Domain m2 
                  \<and> b = (if a \<in> Domain m2 then m2 @_m a else m1 @_m a)}"
         in ex1I, simp_all)
  apply (simp_all add:  Relation__functional_p_alt_def [symmetric])
  apply (auto simp add: MapAC__e_at_m_eq, auto)
  apply (subgoal_tac "x \<in> Domain m2 \<and> (x \<in> Domain m1 \<or> x \<in> Domain m2)",
         simp add: MapAC__e_at_m_eq2 MapAC__e_at_m_eq, simp add: DomainI)
  apply (subgoal_tac "x \<in> Domain m1 \<and> (x \<in> Domain m1 \<or> x \<in> Domain m2)",
         simp add: MapAC__e_at_m_eq2 MapAC__e_at_m_eq, simp add: DomainI)
  apply (drule_tac x=a in spec, clarify, drule mp, simp add: DomainI,
         simp add: MapAC__e_at_m_eq)
  apply (drule_tac x=a in spec, clarify, rotate_tac -1, drule mp,
         subgoal_tac "a \<in> Domain x", simp, erule DomainI,
         simp add: MapAC__e_at_m_eq)
  apply (drule_tac x=a in spec, clarify, drule mp, simp add: DomainI,
         simp add: MapAC__e_at_m_eq,
         rotate_tac -1, drule sym, simp, erule MapAC__e_at_m_element,
         simp add: DomainI)
  apply (drule_tac x=a in spec, clarify, rotate_tac -1, drule mp, simp add: DomainI,
         simp add: MapAC__e_at_m_eq,
         rotate_tac -1, drule sym, simp, erule MapAC__e_at_m_element,
         simp add: DomainI)
  apply (drule_tac x=a in spec, clarify, drule mp, simp add: DomainI,
         simp add: MapAC__e_at_m_eq,
         rotate_tac -1, drule sym, simp, erule MapAC__e_at_m_element,
         simp add: DomainI)
end-proof

proof Isa update_Obligation_subtype
  by (auto simp add: Relation__functional_p_unfold)
end-proof

% remove domain value(s) from map:

op [a,b] -- (m: Map(a,b), xS: Set a) infixl 25 : Map(a,b) =
  m restrictDomain (~~ xS)
proof Isa -> --_m end-proof

op [a,b] - (m: Map(a,b), x:a) infixl 25 : Map(a,b) = m -- single x
proof Isa -> mless [simp] end-proof

proof Isa e_dsh_dsh_Obligation_subtype
 apply (simp add: Relation__functional_p_unfold Relation__restrictDomain_def,
        simp add: mem_def, auto)
 apply (drule_tac x=x in spec, auto)
end-proof

% maps agree on intersection of domains:

op [a,b] agree? (m1: Map(a,b), m2: Map(a,b)) : Bool =
  functional? (m1 \/ m2)

type TotalMap(a,b) = (Map(a,b) | total?)

% convert between (total) maps and functions:

op [a,b] fromFunction (f: a -> b) : TotalMap(a,b) = fn (x,y) -> y = f x

op toFunction : [a,b] TotalMap(a,b) -> (a -> b) = inverse fromFunction

proof Isa fromFunction_Obligation_subtype
  by (auto simp add: Relation__total_p_def mem_def)
end-proof

proof Isa fromFunction_Obligation_subtype0
  by (auto simp add: Relation__functional_p_alt_def mem_def)
end-proof

proof Isa toFunction_Obligation_subtype
  apply (simp add: bij_ON_def inj_on_def surj_on_def Ball_def Bex_def mem_def)
  apply (auto simp add: MapAC__fromFunction_def)
  apply (auto simp add: expand_fun_eq)
  apply (rule_tac x="\<lambda>a. x @_m a" in exI, auto)
  apply (rule sym, erule MapAC__e_at_m_eq, simp add: mem_def)
  apply (drule_tac a=a in MapAC__e_at_m_element,
         simp_all add: Relation__total_p_def mem_def)
end-proof

% convert between maps and (partial) functions (modeled via Option):

op [a,b] fromPartialFun (f: a -> Option b) : Map(a,b) =
  fn (x,y) -> f x = Some y

op toPartialFun : [a,b] Map(a,b) -> (a -> Option b) = inverse fromPartialFun

proof Isa fromPartialFun_Obligation_subtype
  by (auto simp add: Relation__functional_p_alt_def mem_def)
end-proof

proof Isa toPartialFun_Obligation_subtype
  apply (auto simp add: bij_ON_def inj_on_def surj_on_def Ball_def Bex_def mem_def
                        MapAC__fromPartialFun_def,
         simp add: expand_fun_eq, auto)
  apply (drule_tac x=xb in spec, case_tac "x xb = None \<and> xa xb = None", auto)
  apply (rule_tac x="MapAC__toIsaMap x" in exI, simp add: MapAC__toIsaMap_def)
  apply (simp add: expand_fun_eq Relation__apply_def, clarify, rule conjI, clarify)
  apply (rule_tac t="(\<lambda>y. (a, y) \<in> x)" and s="{y}" in subst,
         simp_all only: contents_eq)
  apply (simp add: Relation__functional_p_alt_def expand_set_eq mem_def Domain_def, auto)
  apply (simp add: Relation__functional_p_alt_def mem_def Domain_def, auto)
  apply (simp add: mem_def)
  apply (simp add: Domain_def, simp add: mem_def)
end-proof

% surjective, injective, and bijective:

type SurjectiveMap(a,b) = (Map(a,b) | Relation.surjective?)

type InjectiveMap(a,b) = (Map(a,b) | Relation.injective?)

type BijectiveMap(a,b) = (Map(a,b) | Relation.bijective?)

% cardinalities:

type      FiniteMap(a,b) = (Map(a,b) | finite?)
type    InfiniteMap(a,b) = (Map(a,b) | infinite?)
type   CountableMap(a,b) = (Map(a,b) | countable?)
type UncountableMap(a,b) = (Map(a,b) | uncountable?)

(**************
proof Isa Thy_Morphism 
%%  type Relation.Map      ->  "~=>" (id,id)
  Map.?? -> 
  Map.?? -> 
end-proof
*****************)

endspec
