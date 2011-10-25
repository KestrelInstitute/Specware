FMap qualifying spec

(* The motivation for this spec is analogous to the one for spec `FiniteSet';
see comments in that spec.

Some of the operations on maps in spec `Map' involve sets. In this spec, we use
the (refinable) finite sets specified in spec `FiniteSet', otherwise we would be
unable to refine this spec for finite maps. *)

import Map, EndoRelation, FiniteSet

type FMap(a,b)

% isomorphisms:

op toFMap : [a,b] Bijection (FiniteMap(a,b), FMap(a,b))

op fromFMap : [a,b] FMap(a,b) -> FiniteMap(a,b) = inverse toFMap

% ------------------------------------------------------------------------------
proof Isa -verbatim

lemma FMap__fromFMap_alt_def:
  "FMap__fromFMap = inv_on (finite &&& Relation__functional_p) FMap__toFMap"
 apply (cut_tac FMap__toFMap_subtype_constr)
 apply (simp add: FMap__fromFMap_def univ_true bij_ON_UNIV_bij_on)
 apply (erule   Function__inverse__stp_simp)
done
lemma FMap__fromFMap_alt_bij: 
  "bij_on  FMap__fromFMap UNIV (finite &&& Relation__functional_p)"
 apply (cut_tac FMap__toFMap_subtype_constr)
 apply (simp add: FMap__fromFMap_alt_def univ_true bij_ON_UNIV_bij_on)
 apply (erule bij_on_imp_bij_on_inv)
done
lemma FMap__fromFMap_finite:
  "finite (FMap__fromFMap m)"
  apply (cut_tac FMap__fromFMap_alt_bij)
  apply (auto simp add: bij_on_def defined_on_simp_set mem_def)
done 
lemma FMap__fromFMap_functional:
  "Relation__functional_p (FMap__fromFMap m)"
  apply (cut_tac FMap__fromFMap_alt_bij)
  apply (auto simp add: bij_on_def defined_on_simp_set mem_def)
done 

lemma FMap__fromFMap_f_f:
   "\<lbrakk>finite m; Relation__functional_p m\<rbrakk>
   \<Longrightarrow> FMap__fromFMap (FMap__toFMap m) = m"
   apply (simp add: FMap__fromFMap_alt_def)
   apply (rule inv_on_f_f)
   apply (cut_tac FMap__toFMap_subtype_constr, 
          auto simp add: bij_ON_def mem_def)
done

end-proof
% ------------------------------------------------------------------------------

(* Since `FiniteMap' is a subtype of `Map' which is a subtype of `Relation'
which is a subtype of `Set', it "inherits" ops for maps, (endo)relations, and
sets. Since `FMap(a,b)' is only isomorphic to `FiniteSet(a*b)' (as opposed to
being a subtype), the relevant inherited ops (those that make sense for finite
maps and that can be refined to actual implementations) are introduced here for
type `FMap', and defined using the isomorphism. Some of the inherited ops for
`Relation' and `Set' are renamed here to use names that are more appropriate to
maps vs. relations and sets. *)

% operations and subtypes:

op [a,b] maps? (m: FMap(a,b)) (x:a) (y:b) : Bool = (x,y) in? fromFMap m

op [a,b] domain (m: FMap(a,b)) : FSet a = toFSet (domain (fromFMap m))

proof Isa domain_Obligation_subtype
  by (simp add: FMap__fromFMap_finite finite_Domain)
end-proof

op [a,b] range (m: FMap(a,b)) : FSet b = toFSet (range (fromFMap m))

proof Isa range_Obligation_subtype
  by (simp add: FMap__fromFMap_finite finite_Range)
end-proof

op [a,b] definedAt (m: FMap(a,b), x:a) infixl 20 : Bool =
  (fromFMap m) definedAt x
proof Isa -> definedAt_fm end-proof

op [a,b] undefinedAt (m: FMap(a,b), x:a) infixl 20 : Bool =
  (fromFMap m) undefinedAt x
proof Isa -> undefinedAt_fm end-proof

op [a,b] @ (m: FMap(a,b), x:a | m definedAt x) infixl 30 : b =
  (fromFMap m) @ x
proof Isa -> @_fm end-proof

proof Isa e_at_Obligation_subtype
 by (simp add: definedAt_fm_def)
end-proof

op [a,b] @@ (m: FMap(a,b), x:a) infixl 30 : Option b = (fromFMap m) @@ x
proof Isa -> @@_fm end-proof

op [a,b] applyi (m: FMap(a,b)) (y:b) : FSet a =
  toFSet (applyi (fromFMap m) y)

proof Isa applyi_Obligation_subtype
  apply (simp add: Relation__applyi_def)
  apply (rule_tac B="Domain (FMap__fromFMap m)" in finite_subset)
  apply (simp_all add: FMap__domain_Obligation_subtype)
  apply (auto simp add: Domain_def mem_def)
end-proof

op [a,b] applys (m: FMap(a,b)) (xS: FSet a) : FSet b =
  toFSet (applys (fromFMap m) (fromFSet xS))

proof Isa applys_Obligation_subtype
  apply (cut_tac F="{(x,y). x \<in> FSet__fromFSet xS}" 
             and G="FMap__fromFMap m" in finite_Int)
  apply (cut_tac m=m in FMap__fromFMap_finite, simp)
  apply (drule_tac h="\<lambda>(x,y). y" in finite_imageI)
  apply (simp add: Image_def image_def Bex_def)
end-proof

op [a,b] applyis (m: FMap(a,b)) (yS: FSet b) : FSet a =
  toFSet (applyis (fromFMap m) (fromFSet yS))

proof Isa applyis_Obligation_subtype
  apply (simp add: Relation__applyis_def)
  apply (cut_tac F="{(x,y). y \<in> FSet__fromFSet yS}" 
             and G="FMap__fromFMap m" in finite_Int)
  apply (cut_tac m=m in FMap__fromFMap_finite, simp)
  apply (drule_tac h="\<lambda>(x,y). x" in finite_imageI)
  apply (simp add: Image_def image_def Bex_def, simp add: Collect_def)
end-proof

op [a] id (dom: FSet a) : FMap(a,a) = toFMap (idOver (fromFSet dom))

proof Isa id_Obligation_subtype
  apply (simp add: Id_on_def )
  apply (cut_tac A="{S. \<exists>x\<in>FSet__fromFSet dom__v. S={(x,x)}}"  in finite_Union)
  apply (auto simp add: Bex_def)
  apply (cut_tac s=dom__v in FSet__fromFSet_finite,
         drule_tac h="\<lambda>x. {(x,x)}" in finite_imageI,
         simp add: image_def Bex_def)
  apply (rule finite_subset, auto)
end-proof

proof Isa id_Obligation_subtype0
 by (simp add: Id_on_def Relation__functional_p_alt_def Domain_def)
end-proof

op [a,b,c] :> (m1: FMap(a,b), m2: FMap(b,c)) infixl 24 : FMap(a,c) =
  toFMap (fromFMap m1 :> fromFMap m2)
proof Isa -> :>_fm end-proof

proof Isa e_cl_gt_Obligation_subtype
  apply (cut_tac m=m1 in FMap__fromFMap_finite,
         cut_tac m=m2 in FMap__fromFMap_finite)
  apply (simp add: rel_comp_def)
  apply (drule_tac h="\<lambda>(x,y). x" in finite_imageI)
  apply (drule_tac h="\<lambda>(x,y). y" in finite_imageI)
  apply (drule finite_cartesian_product, auto)
  apply (rule finite_subset, auto)
end-proof

proof Isa e_cl_gt_Obligation_subtype0
  apply (cut_tac m=m1 in FMap__fromFMap_functional,
         cut_tac m=m2 in FMap__fromFMap_functional)
  apply (simp add: rel_comp_def Relation__functional_p_alt_def Domain_def, 
         clarify)
  apply (drule_tac x=x in spec, drule mp, rule exI, simp, erule ex1E)
  apply (drule_tac x=ya in spec, drule mp, rule exI, simp, erule ex1E)
  apply (rule_tac a=y in ex1I, auto)
end-proof

op [a,b,c] o (m1: FMap(b,c), m2: FMap(a,b)) infixl 24 : FMap(a,c) =
  toFMap (fromFMap m1 o fromFMap m2)
proof Isa -> o_fm end-proof

proof Isa o_Obligation_subtype
 by (simp add: o_R_def FMap__e_cl_gt_Obligation_subtype)
end-proof

proof Isa o_Obligation_subtype0
 by (simp add: o_R_def FMap__e_cl_gt_Obligation_subtype0)
end-proof

op [a,b] <= (m1: FMap(a,b), m2: FMap(a,b)) infixl 20 : Bool =
  fromFMap m1 <= fromFMap m2
proof Isa -> <=_fm end-proof

op [a,b] < (m1: FMap(a,b), m2: FMap(a,b)) infixl 20 : Bool =
  fromFMap m1 < fromFMap m2
proof Isa -> <_fm end-proof

op [a,b] >= (m1: FMap(a,b), m2: FMap(a,b)) infixl 20 : Bool =
  fromFMap m1 >= fromFMap m2
proof Isa -> >=_fm end-proof

op [a,b] > (m1: FMap(a,b), m2: FMap(a,b)) infixl 20 : Bool =
  fromFMap m1 > fromFMap m2
proof Isa -> >_fm end-proof

op empty : [a,b] FMap(a,b) = toFMap empty
proof Isa -> empty_fm end-proof

proof Isa empty_Obligation_subtype0
 by  (simp add: Relation__functional_p_alt_def)
end-proof

op [a,b] empty? (m: FMap(a,b)) : Bool = empty? (fromFMap m)

op [a,b] nonEmpty? (m: FMap(a,b)) : Bool = nonEmpty? (fromFMap m)

type NonEmptyFMap(a,b) = (FMap(a,b) | nonEmpty?)

op [a,b] <<< (m1: FMap(a,b), m2: FMap(a,b)) infixl 25 : FMap(a,b) =
  toFMap (fromFMap m1 <<< fromFMap m2)
proof Isa -> <<<_fm end-proof

proof Isa e_lt_lt_lt_Obligation_subtype
   apply (simp (no_asm_simp) only: MapAC__e_lt_lt_lt_def)
   apply (rule_tac P="\<lambda>m. Relation__functional_p m \<and>
             Domain m = Domain (FMap__fromFMap m1) \<union> Domain (FMap__fromFMap m2) \<and>
             (\<forall>x. x \<in> Domain m \<longrightarrow>
                  m @_m x =
                  (if FMap__fromFMap m2 definedAt x then FMap__fromFMap m2 @_m x
                   else FMap__fromFMap m1 @_m x))" in the1I2)
   apply (rule MapAC__e_lt_lt_lt_Obligation_the,
          auto simp add: FMap__fromFMap_functional)
   apply (simp add: Relation__finite_if_finite_domain FMap__domain_Obligation_subtype)
end-proof

op [a,b] update (m: FMap(a,b)) (x:a) (y:b) : FMap(a,b) =
  toFMap (update (fromFMap m) x y)

proof Isa update_Obligation_subtype
   apply (subgoal_tac "MapAC__update (FMap__fromFMap m) x y
                       = FMap__fromFMap m <<< FMap__fromFMap (FMap__toFMap {(x,y)})")
   apply (simp add: MapAC__update_def  FMap__e_lt_lt_lt_Obligation_subtype)
   apply (thin_tac "?P", simp add: MapAC__update_def,
          rule_tac f="MapAC__e_lt_lt_lt" in arg_cong2, simp)
   apply (rule FMap__fromFMap_f_f [symmetric])
   apply (simp_all add: mem_def Relation__functional_p_alt_def Domain_def)
end-proof

op [a,b] -- (m: FMap(a,b), xS: FSet a) infixl 25 : FMap(a,b) =
  toFMap (fromFMap m -- fromFSet xS)
proof Isa -> --_fm end-proof

proof Isa e_dsh_dsh_Obligation_subtype
   apply (rule_tac B="FMap__fromFMap m" in finite_subset,
          auto simp add: FMap__fromFMap_finite)
   apply (simp add: e_dsh_dsh_m_def  Relation__restrictDomain_def mem_def)
end-proof

op [a,b] - (m: FMap(a,b), x:a) infixl 25 : FMap(a,b) =
  toFMap (fromFMap m - x)
proof Isa -> less_fm end-proof

proof Isa e_dsh_Obligation_subtype
   apply (subgoal_tac "FMap__fromFMap m mless x
                    =  FMap__fromFMap m --_m FSet__fromFSet (FSet__toFSet {x})")
   apply (simp add: FMap__e_dsh_dsh_Obligation_subtype)
   apply (simp, rule_tac f="e_dsh_dsh_m" in arg_cong2,
          simp_all add: FSet__fromFSet_f_f)
end-proof

op [a,b] agree? (m1: FMap(a,b), m2: FMap(a,b)) : Bool =
  agree? (fromFMap m1, fromFMap m2)

op [a,b] /\ (m1: FMap(a,b), m2: FMap(a,b) | agree?(m1,m2)) infixr 25
            : FMap(a,b) = toFMap (fromFMap m1 /\ fromFMap m2)
proof Isa -> /\_fm end-proof

proof Isa e_fsl_bsl_Obligation_subtype
 by (simp add: FMap__fromFMap_finite)
end-proof

proof Isa e_fsl_bsl_Obligation_subtype0
  apply (cut_tac m=m1 in FMap__fromFMap_functional,
         cut_tac m=m2 in FMap__fromFMap_functional)
  apply (auto simp add: Relation__functional_p_alt_def Domain_def)
end-proof

op [a,b] \/ (m1: FMap(a,b), m2: FMap(a,b) | agree?(m1,m2)) infixr 24
            : FMap(a,b) = toFMap (fromFMap m1 \/ fromFMap m2)
proof Isa -> \/_fm end-proof

proof Isa e_bsl_fsl_Obligation_subtype
 by (simp add: FMap__fromFMap_finite)
end-proof

proof Isa e_bsl_fsl_Obligation_subtype0
 by (simp add: FMap__agree_p_def MapAC__agree_p_def)
end-proof

op [a,b] forall? (p: a * b -> Bool) (m: FMap(a,b)) : Bool =
  fromFMap m <= p

op [a,b] exists? (p: a * b -> Bool) (m: FMap(a,b)) : Bool =
  nonEmpty? (fromFMap m /\ p)

op [a,b] exists1? (p: a * b -> Bool) (m: FMap(a,b)) : Bool =
  single? (fromFMap m /\ p)

op [a,b] filter (p: a * b -> Bool) (m: FMap(a,b)) : FMap(a,b) =
  toFMap (fromFMap m /\ p)

proof Isa filter_Obligation_subtype
 by (simp add: FMap__fromFMap_finite)
end-proof

proof Isa filter_Obligation_subtype0
 by (cut_tac m=m in FMap__fromFMap_functional,
     auto simp add: Relation__functional_p_alt_def Domain_def)
end-proof

op [a,b] restrictDomain (m: FMap(a,b), p: a -> Bool) infixl 25
                        : FMap(a,b) = toFMap (fromFMap m restrictDomain p)
proof Isa -> restrictDomain_fm end-proof

proof Isa restrictDomain_Obligation_subtype
  apply (rule_tac B="FMap__fromFMap m" in finite_subset)
  apply (auto simp add: Relation__restrictDomain_def mem_def 
                        FMap__fromFMap_finite)
end-proof

proof Isa restrictDomain_Obligation_subtype0
 by (cut_tac m=m in FMap__fromFMap_functional,
     auto simp add: Relation__functional_p_alt_def Domain_def
                    Relation__restrictDomain_def mem_def)

end-proof

op [a,b] restrictRange (m: FMap(a,b), p: b -> Bool) infixl 25
                       : FMap(a,b) = toFMap (fromFMap m restrictRange p)
proof Isa -> restrictRange_fm end-proof

proof Isa restrictRange_Obligation_subtype
  apply (rule_tac B="FMap__fromFMap m" in finite_subset)
  apply (auto simp add: Relation__restrictRange_def mem_def 
                        FMap__fromFMap_finite)
end-proof

proof Isa restrictRange_Obligation_subtype0
 by (cut_tac m=m in FMap__fromFMap_functional,
     auto simp add: Relation__functional_p_alt_def Domain_def
                    Relation__restrictRange_def mem_def)
end-proof

op [a,b] single (x:a) (y:b) : FMap(a,b) = toFMap (single (x,y))

proof Isa single_Obligation_subtype0
  by (auto simp add: Relation__functional_p_unfold)
end-proof

op [a,b] single? (m: FMap(a,b)) : Bool = single? (fromFMap m)

type SingletonFMap(a,b) = (FMap(a,b) | single?)

op [a,b] thePair (m: SingletonFMap(a,b)) : a * b = theMember (fromFMap m)

op [a,b] size (m: FMap(a,b)) : Nat = size (fromFMap m)

op [a,b,c] foldable? (c:c, f: c * (a*b) -> c, m: FMap(a,b)) : Bool =
  foldable? (c, f, fromFMap m)

op [a,b,c] fold(c: c, f: c * (a*b) -> c, m: FMap(a,b) | foldable?(c,f,m)): c =
  fold (c, f, fromFMap m)

proof Isa fold_Obligation_subtype
 by (simp add: FMap__foldable_p_def)
end-proof

op [a,b] injective? (m: FMap(a,b)) : Bool =
  Relation.injective? (fromFMap m)

type InjectiveFMap(a,b) = (FMap(a,b) | injective?)

op [a,b] inverse (m: InjectiveFMap(a,b)) : InjectiveFMap(b,a) =
  toFMap (inverse (fromFMap m))


proof Isa inverse_Obligation_subtype
 by (simp add: finite_converse FMap__fromFMap_finite)
end-proof

proof Isa inverse_Obligation_subtype0
 by (simp add: Relation__injective_p_def Relation__applyi_def
               Relation__functional_p_def Relation__apply_def)
end-proof

proof Isa inverse_Obligation_subtype1
 apply (frule FMap__inverse_Obligation_subtype,
        frule FMap__inverse_Obligation_subtype0)
 apply (simp add: FMap__injective_p_def FMap__fromFMap_f_f)
 apply (thin_tac "?P", thin_tac "?P", thin_tac "?P", 
        cut_tac m=m in FMap__fromFMap_functional)
 apply (simp add: Relation__functional_p_def Relation__apply_def
                  Relation__injective_p_def Relation__applyi_def)
end-proof


% apply function to all range values:
op [a,b,c] map (f: b -> c) (m: FMap(a,b)) : FMap(a,c) =
  let fLiftedToPairs: a * b -> a * c = (fn (x,y) -> (x, f y)) in
  toFMap (map fLiftedToPairs (fromFMap m))

proof Isa map_Obligation_subtype
  by (simp add: FMap__fromFMap_finite)
end-proof

proof Isa map_Obligation_subtype0
   apply (cut_tac m=m in FMap__fromFMap_functional)
   apply (auto simp add: FMap__map__fLiftedToPairs_def image_def Bex_def
                         Relation__functional_p_alt_def Domain_def)
end-proof

% like previous op but also include domain value:
op [a,b,c] mapWithDomain (f: a * b -> c) (m: FMap(a,b)) : FMap(a,c) =
  let fLiftedToPairs: a * b -> a * c = (fn (x,y) -> (x, f(x,y))) in
  toFMap (map fLiftedToPairs (fromFMap m))

proof Isa mapWithDomain_Obligation_subtype
  by (simp add: FMap__fromFMap_finite)
end-proof

proof Isa mapWithDomain_Obligation_subtype0
   apply (cut_tac m=m in FMap__fromFMap_functional)
   apply (auto simp add: FMap__mapWithDomain__fLiftedToPairs_def 
                         image_def Bex_def
                         Relation__functional_p_alt_def Domain_def)
end-proof

(* While `FiniteMap(a,b)' is a subtype of `FiniteSet(a*b)', the types
`FMap(a,b)' and `FSet(a*b)' are just isomorphic. So, we provide explicit
conversions here. *)

op [a,b] toFSet (m: FMap(a,b)) : FSet(a*b) = toFSet (fromFMap m)

op [a,b] fromFSet (s : FSet(a*b) | functional? (fromFSet s)) : FMap(a,b) =
  toFMap (fromFSet s)

% intersection of all sets in a map's range:

op [a,b] //\\ (setValuedMap: NonEmptyFMap (a, FSet b)) : FSet b =
  FSet.//\\ (range setValuedMap)

proof Isa e_fsl_fsl_bsl_bsl_Obligation_subtype
  by (simp add: FSet__nonEmpty_p_def FMap__range_def
                FSet__fromFSet_f_f FMap__range_Obligation_subtype
                Set__nonEmpty_p_def,
      auto)
end-proof

% union of all sets in a map's range:

op [a,b] \\// (setValuedMap: FMap (a, FSet b)) : FSet b =
  FSet.\\// (range setValuedMap)

% construct map x1->y1,...,xn->yn from lists x1,...,xn and y1,...,yn:

op [a,b] fromLists
         (domList: InjList a, rngList: List b | domList equiLong rngList)
         : FMap(a,b) =
  toFMap (fn (x,y) ->
    (ex(i:Nat) i < length domList && domList @ i = x && y = rngList @ i))

proof Isa fromLists_Obligation_subtype
  apply (cut_tac k="length domList" in finite_Collect_less_nat,
         cut_tac k="length rngList" in finite_Collect_less_nat)
  apply (drule_tac h="\<lambda>i. domList ! i" in finite_imageI,
         drule_tac h="\<lambda>i. rngList ! i" in finite_imageI,
         simp only: image_def Bex_def mem_Collect_eq)
  apply (drule_tac B="{y. \<exists>x<length rngList. y = rngList ! x}" 
         in finite_cartesian_product, simp, thin_tac "?P")
  apply (rule finite_subset, simp_all (no_asm_simp))
  apply (auto simp add: mem_def)
end-proof

proof Isa fromLists_Obligation_subtype0
  apply (auto simp add: Relation__functional_p_alt_def Domain_def mem_def)
  apply (frule_tac xs=domList and i=ia and j=i in nth_eq_iff_index_eq, simp_all)
  apply (frule_tac xs=domList and i=ib and j=i in nth_eq_iff_index_eq, simp_all)
end-proof

endspec
