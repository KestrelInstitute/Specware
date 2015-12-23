(* Copyright 2015 Kestrel Institute. See file LICENSE for license details *)

FMap qualifying spec

(* The motivation for this spec is analogous to the one for spec `FiniteSet';
see comments in that spec.

Some of the operations on maps in spec `Map' involve sets. In this spec, we use
the (refinable) finite sets specified in spec `FiniteSet', otherwise we would be
unable to refine this spec for finite maps. *)

import Map, Relation, FiniteSet

type FMap(a,b)

% isomorphisms:

op toFMap : [a,b] Bijection (FiniteMap(a,b), FMap(a,b))

op fromFMap : [a,b] FMap(a,b) -> FiniteMap(a,b) = inverse toFMap



% ------------------------------------------------------------------------------
% ------------------------------------------------------------------------------
proof Isa -verbatim
(******************************************************************************)

lemma FMap__fromFMap_f_f:  "FMap__fromFMap (FMap__toFMap m) = m"
   by (simp add: FMap__fromFMap_def  inv_f_f 
                 FMap__toFMap_subtype_constr bij_is_inj)

lemma FMap__toFMap_f_f:    "FMap__toFMap (FMap__fromFMap m) = m"
   by (simp add: FMap__fromFMap_def FMap__toFMap_subtype_constr
                 Function__f_inverse_apply)

(******************************************************************************)

end-proof
% ------------------------------------------------------------------------------
% ------------------------------------------------------------------------------






% operations and subtypes:

op [a,b] maps? (m: FMap(a,b)) (x:a) (y:b) : Bool = maps? (fromFMap m) x y

op [a,b] domain (m: FMap(a,b)) : FSet a = toFSet (domain (fromFMap m))

op [a,b] range (m: FMap(a,b)) : FSet b = toFSet (range (fromFMap m))

op [a,b] definedAt (m: FMap(a,b), x:a) infixl 20 : Bool =
  (fromFMap m) definedAt x
proof Isa -> definedAt_fm end-proof

op [a,b] undefinedAt (m: FMap(a,b), x:a) infixl 20 : Bool =
  (fromFMap m) undefinedAt x
proof Isa -> undefinedAt_fm end-proof

op [a,b] @ (m: FMap(a,b), x:a | m definedAt x) infixl 30 : b =
  (fromFMap m) @ x
proof Isa -> @_fm end-proof


op [a,b] @@ (m: FMap(a,b), x:a) infixl 30 : Option b = (fromFMap m) x
proof Isa -> @@_fm end-proof

op [a,b] applyi (m: FMap(a,b)) (y:b) : FSet a =
  toFSet (applyi (fromFMap m) y)


op [a,b] applys (m: FMap(a,b)) (xS: FSet a) : FSet b =
  toFSet (applys (fromFMap m) (fromFSet xS))

op [a,b] applyis (m: FMap(a,b)) (yS: FSet b) : FSet a =
  toFSet (applyis (fromFMap m) (fromFSet yS))

op [a] id (dom: FSet a) : FMap(a,a) = toFMap (id (fromFSet dom))

op [a,b,c] :> (m1: FMap(a,b), m2: FMap(b,c)) infixl 24 : FMap(a,c) =
  toFMap (fromFMap m1 :> fromFMap m2)
proof Isa -> :>_fm end-proof

op [a,b,c] o (m1: FMap(b,c), m2: FMap(a,b)) infixl 24 : FMap(a,c) =
  toFMap (fromFMap m1 o fromFMap m2)
proof Isa -> o_fm end-proof

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

op [a,b] empty? (m: FMap(a,b)) : Bool = empty? (fromFMap m)

op [a,b] nonEmpty? (m: FMap(a,b)) : Bool = nonEmpty? (fromFMap m)

type NonEmptyFMap(a,b) = (FMap(a,b) | nonEmpty?)

op [a,b] <<< (m1: FMap(a,b), m2: FMap(a,b)) infixl 25 : FMap(a,b) =
  toFMap (fromFMap m1 <<< fromFMap m2)
proof Isa -> <<<_fm end-proof

op [a,b] update (m: FMap(a,b)) (x:a) (y:b) : FMap(a,b) =
  toFMap (update (fromFMap m) x y)

% remove domain value(s) from map:
op [a,b] -- (m: FMap(a,b), xS: FSet a) infixl 25 : FMap(a,b) =
  toFMap (fromFMap m -- fromFSet xS)
proof Isa -> --_fm end-proof

op [a,b] - (m: FMap(a,b), x:a) infixl 25 : FMap(a,b) =
  toFMap (fromFMap m - x)
proof Isa -> less_fm end-proof

op [a,b] agree? (m1: FMap(a,b), m2: FMap(a,b)) : Bool =
  agree? (fromFMap m1, fromFMap m2)

op [a,b] /\ (m1: FMap(a,b), m2: FMap(a,b) | agree?(m1,m2)) infixr 25
            : FMap(a,b) = toFMap (fromFMap m1 /\ fromFMap m2)
proof Isa -> /\_fm end-proof

op [a,b] \/ (m1: FMap(a,b), m2: FMap(a,b) | agree?(m1,m2)) infixr 24
            : FMap(a,b) = toFMap (fromFMap m1 \/ fromFMap m2)
proof Isa -> \/_fm end-proof

op [a,b] forall? (p: a * b -> Bool) (m: FMap(a,b)) : Bool =
  fa (x:a, y:b) maps? (fromFMap m) x y => p(x,y)

op [a,b] exists? (p: a * b -> Bool) (m: FMap(a,b)) : Bool =
  ex (x:a, y:b) maps? (fromFMap m) x y && p(x,y)

op [a,b] exists1? (p: a * b -> Bool) (m: FMap(a,b)) : Bool =
  single? (fn (x:a, y:b) -> maps? (fromFMap m) x y && p(x,y))

op [a,b] filter (p: a * b -> Bool) (m: FMap(a,b)) : FMap(a,b) =
  let m' = fromFMap m in
  toFMap(fn (x:a) -> if x in? domain m' && p(x, m' @ x) then m' x else None)

op [a,b] restrictDomain (m: FMap(a,b), p: a -> Bool) infixl 25
                        : FMap(a,b) = toFMap (fromFMap m restrictDomain p)
proof Isa -> restrictDomain_fm end-proof

op [a,b] restrictRange (m: FMap(a,b), p: b -> Bool) infixl 25
                       : FMap(a,b) = toFMap (fromFMap m restrictRange p)
proof Isa -> restrictRange_fm end-proof

op [a,b] single (x:a) (y:b) : FMap(a,b) = toFMap (single x y)

op [a,b] single? (m: FMap(a,b)) : Bool = single? (fromFMap m)

type SingletonFMap(a,b) = (FMap(a,b) | single?)

op [a,b] thePair (m: SingletonFMap(a,b)) : a * b = 
  let x = theMember (domain (fromFMap m)) in
  (x, m @ x)


op [a,b] size (m: FMap(a,b)) : Nat = size (domain (fromFMap m))

op [a,b,c] foldable? (c:c, f: c * (a*b) -> c, m: FMap(a,b)) : Bool =
  fa (x1:a, x2:a, z:c) x1 in? domain m && x2 in? domain m
  => f(f(z,(x1,m@x1)),(x2,m@x2)) = f(f(z,(x2,m@x2)),(x1,m@x1))


proof Isa -verbatim
(******************************************************************************)

lemma FMap__foldable_p_is_aux [simp]: "FMap__foldable_p = FMap__foldable_aux"
  by (simp add: FMap__foldable_p_def FMap__foldable_aux_def)

(******************************************************************************)
end-proof
  

op fold: [a,b,c] (c * (c * (a*b) -> c) * FMap(a,b) | foldable?) -> c =
  the(fold)
    (fa (c: c, f: c * (a*b) -> c) fold (c, f, empty) = c) &&
    (fa (c: c, f: c * (a*b) -> c, m: FMap(a,b), x: a, y: b)
       foldable? (c, f, update m x y) =>
         fold (c, f, update m x y) = f (fold (c, f, m - x), (x, y)))

op [a,b] injective? (m: FMap(a,b)) : Bool =
  Map.injective? (fromFMap m)

type InjectiveFMap(a,b) = (FMap(a,b) | injective?)

op [a,b] inverse (m: InjectiveFMap(a,b)) : InjectiveFMap(b,a) =
  toFMap (inverse (fromFMap m))


% apply function to all range values:
op [a,b,c] map (f: b -> c) (m: FMap(a,b)) : FMap(a,c) =
  toFMap (map f (fromFMap m))

% like previous op but also include domain value:
op [a,b,c] mapWithDomain (f: a * b -> c) (m: FMap(a,b)) : FMap(a,c) =
  toFMap (fn x:a -> case (fromFMap m) x of Some y -> Some(f(x,y)) | None -> None)

op [a,b] toFSet (m: FMap(a,b)) : FSet(a*b) =
  toFSet(fn (x:a, y:b) -> maps? (fromFMap m) x y)

op [a,b] fromFSet (s : FSet(a*b) | functional? (fromFSet s)) : FMap(a,b) =
  toFMap (fn (x:a) ->
            let yS = apply (fromFSet s) x in
            if empty? yS then None else Some(theMember yS))

% intersection of all sets in a map's range:

op [a,b] //\\ (setValuedMap: NonEmptyFMap (a, FSet b)) : FSet b =
  FSet.//\\ (range setValuedMap)

% union of all sets in a map's range:

op [a,b] \\// (setValuedMap: FMap (a, FSet b)) : FSet b =
  FSet.\\// (range setValuedMap)

% construct map x1->y1,...,xn->yn from lists x1,...,xn and y1,...,yn:

op [a,b] fromLists
         (domList: InjList a, rngList: List b | domList equiLong rngList)
         : FMap(a,b) =
  toFMap (fn (x:a) ->
            if x in? domList
              then Some (rngList @ (positionOf(domList,x))) else None)


% ------------------------------------------------------------------------------
% ------------------ The proofs ------------------------------------------------
% ------------------------------------------------------------------------------

proof Isa range_Obligation_subtype
  by (simp add: finite_dom_ran)
end-proof

proof Isa e_at_Obligation_subtype
   by (simp add: definedAt_fm_def definedAt_m_def)
end-proof

proof Isa applyi_Obligation_subtype
  by (simp add: Map__Map__applyi_simp)
end-proof

proof Isa applys_Obligation_subtype
  apply (auto simp add: Map__Map__applys_simp FSet__fromFSet_finite 
                        finite_Collect_bounded_ex)
  apply (cut_tac m=m in FMap__range_Obligation_subtype, simp add: ran_def)
  apply (rule finite_subset, auto)
end-proof

proof Isa applyis_Obligation_subtype
  apply (simp add: Map__applyis_def Map__maps_p_def definedAt_m_def 
                   Map__domain__def e_at_m_def,
         auto simp add:  split: option.split)
  apply (cut_tac m=m in FMap__domain_Obligation_subtype, simp add: dom_def)
end-proof

proof Isa id_Obligation_subtype
  by (simp add: Map__id_def dom_def FSet__fromFSet_finite)
end-proof

proof Isa e_cl_gt_Obligation_subtype
  apply (cut_tac m=m1 in FMap__domain_Obligation_subtype,          
         simp add: map_comp_def dom_def)
  apply (rule finite_subset, auto simp add:  split: option.split)
end-proof

proof Isa o_Obligation_subtype
   by (rule FMap__e_cl_gt_Obligation_subtype)
end-proof

proof Isa e_dsh_dsh_Obligation_subtype
  apply (cut_tac m=m in FMap__domain_Obligation_subtype,          
         simp add: e_dsh_dsh_m_def dom_def)
  apply (rule finite_subset, auto simp add:  split: option.split)
end-proof

proof Isa e_dsh_Obligation_subtype
  apply (cut_tac m=m in FMap__domain_Obligation_subtype,          
         simp add: e_dsh_dsh_m_def dom_def)
  apply (rule finite_subset, auto simp add:  split: option.split)
end-proof

proof Isa e_fsl_bsl_Obligation_subtype
  by (simp add: FMap__agree_p_def FMap__domain_Obligation_subtype)
end-proof

proof Isa e_fsl_bsl_Obligation_subtype0
  (* Must change syntax from /\_m to /\\_m *)
  by (cut_tac m=m1 in FMap__domain_Obligation_subtype,          
      simp add: e_fsl_bsl_m_def dom_def)
end-proof

proof Isa e_bsl_fsl_Obligation_subtype
  by (simp add: FMap__agree_p_def FMap__domain_Obligation_subtype)
end-proof

proof Isa e_bsl_fsl_Obligation_subtype0
  (* Must change syntax from \/_m to \\/_m *)
  by (cut_tac m=m1 in FMap__domain_Obligation_subtype,          
      cut_tac m=m2 in FMap__domain_Obligation_subtype,          
      simp add: e_bsl_fsl_m_def dom_def disj_not1 [symmetric])
end-proof

proof Isa filter_Obligation_subtype
  apply (auto, rule_tac B="dom (Rep_Map__FiniteMap (FMap__fromFMap m))" 
                  in finite_subset, simp_all)
  apply (cut_tac m=m in FMap__domain_Obligation_subtype, 
         auto simp add: dom_def )
end-proof

proof Isa restrictDomain_Obligation_subtype
  by (simp add: Map__restrictDomain__def)
end-proof

proof Isa restrictRange_Obligation_subtype
  by (simp, rule_tac B="dom (Rep_Map__FiniteMap (FMap__fromFMap m))" 
                in finite_subset, simp_all,
      auto simp add: Map__restrictRange_def dom_def )
end-proof

proof Isa single_Obligation_subtype
  by (simp add: Map__single_def dom_def)
end-proof

proof Isa thePair_Obligation_subtype
  by (simp add: Map__single_p_def )
end-proof

proof Isa thePair_Obligation_subtype0
  apply (simp add: Map__single_p_def unique_singleton 
                   definedAt_fm_def definedAt_m_def the_elem_def )
  apply (rule the1I2, auto simp add: unique_singleton1 set_eq_iff )  
end-proof

proof Isa foldable_p_Obligation_subtype
  by (simp add: in_fset_p_def FMap__domain_def 
                FSet__fromFSet_f_f FMap__domain_Obligation_subtype
                definedAt_fm_def definedAt_m_def)
end-proof

proof Isa foldable_p_Obligation_subtype0
  by (simp add: FMap__foldable_p_Obligation_subtype)
end-proof

proof Isa foldable_p_Obligation_subtype1
  by (simp add: FMap__foldable_p_Obligation_subtype)
end-proof

proof Isa foldable_p_Obligation_subtype2
  by (simp add: FMap__foldable_p_Obligation_subtype)

(******************************************************************************
 ** To prove the theorem "fold_Obligation_the" I have to link to Set__fold
 ** This requires a conversion between (finite and relation functional) sets
 ** and FMaps, which is almost identical to the one between FSets and FMaps
 ** that will be defined later.
 ******************************************************************************)

consts FMap__fromSet :: "('a \<times> 'b) Set__FiniteSet \<Rightarrow>  ('a, 'b)FMap__FMap"
defs FMap__fromSet_def: 
  "FMap__fromSet s
     \<equiv> FMap__toFMap
          (Abs_Map__FiniteMap
              (\<lambda> (x::'a). 
                 let yS = Relation__apply s x 
                 in 
                 if Set__empty_p yS then 
                   None
                 else 
                   Some (the_elem yS)))"

consts FMap__toSet :: " ('a, 'b)FMap__FMap \<Rightarrow> ('a \<times> 'b) Set__FiniteSet"
defs FMap__toSet_def: 
  "FMap__toSet m
     \<equiv> Collect (\<lambda> ((x::'a), (y::'b)). 
             Map__maps_p (Rep_Map__FiniteMap (FMap__fromFMap m)) x y)"

(****** now link various concepts on FMaps to those on sets *****************)

lemma FMap__toSet_inv_aux:
  "\<lbrakk>finite s\<rbrakk> \<Longrightarrow>  
    (\<lambda>x. if \<forall>xa. (x, xa) \<notin> s then None else Some (the_elem {y. (x, y) \<in> s}))
    \<in>  {x. Map__finite_p x}"
  apply (simp add: dom_if)
  apply (rule_tac B="{fst x |x.  x \<in> s}" in finite_subset)
  defer
  apply (rule finite_image_set, auto)
done

lemma  FMap__toSet_inv : 
  "\<lbrakk>finite s; Relation__functional_p s\<rbrakk> \<Longrightarrow> FMap__toSet (FMap__fromSet s) = s"
  apply (frule_tac FMap__toSet_inv_aux) 
  apply (simp add: FMap__toSet_def Map__maps_p_def definedAt_m_def e_at_m_def
                   FMap__fromSet_def
                   Relation__functional_p_def Relation__apply_def dom_def
                   FMap__fromFMap_def Function__inverse_f_apply                  
                   FMap__update_Obligation_subtype
                   FMap__toFMap_subtype_constr)
  apply (rule set_eqI, case_tac x, simp)
  apply (drule_tac x=a in spec, erule disjE, simp_all)
  apply (clarsimp, auto simp add: set_eq_iff)
done


lemma  FMap__fromSet_inv :  "FMap__fromSet (FMap__toSet m) = m"
  apply (simp add: FMap__toSet_def Map__maps_p_def definedAt_m_def e_at_m_def
                   FMap__fromSet_def Relation__apply_def)
  apply (rule_tac t="_ = m" and s="_ = FMap__toFMap (FMap__fromFMap m)"
         in subst, simp add: FMap__toFMap_f_f)
  apply (rule_tac f=FMap__toFMap in arg_cong, rule sym)
  apply (subst Rep_Map__FiniteMap_simp [symmetric],
         simp add: Let_def dom_if  set_eq_iff)
  apply (rule sym, rule ext, 
         auto simp add: Let_def set_eq_iff dom_def the_elem_def)
  apply (rule the1_equality, auto)
done

lemma  FMap__Set_inv: 
  "\<lbrakk>finite s; Relation__functional_p s\<rbrakk>
    \<Longrightarrow> (FMap__fromSet s = m) = (FMap__toSet m = s)"
  by (auto simp add: FMap__fromSet_inv FMap__toSet_inv)

(****************)

lemma FMap__Set_finite [simp]:
  "finite (FMap__toSet m)"
  apply (simp add: FMap__toSet_def Map__maps_p_def definedAt_m_def  e_at_m_def)
  apply (cut_tac m=m in FMap__domain_Obligation_subtype, simp add: dom_def,
         cut_tac m=m in FMap__range_Obligation_subtype, simp add: ran_def,
         drule_tac  finite_cartesian_product, simp, thin_tac _)
  apply (rule finite_subset, auto)
done

lemma FMap__Set_Relation__functional_p [simp]:
  "Relation__functional_p (FMap__toSet m)"
  by (simp add: FMap__toSet_def Map__maps_p_def definedAt_m_def e_at_m_def
                Relation__functional_p_def Relation__apply_def,
      auto)

lemma FMap__Set_empty [simp]:
  "FMap__toSet empty_fm = {}"
  by (simp add: empty_fm_def
                FMap__fromFMap_def Function__inverse_f_apply  
                FMap__toFMap_subtype_constr 
                FMap__toSet_def Map__maps_p_def definedAt_m_def)

lemma FMap__fromSet_empty [simp]:  "FMap__fromSet {} = empty_fm"
  by (simp add: FMap__Set_inv)
  
lemma  FMap__toSet_less_less [simp]:
  "FMap__toSet m less (x, m @_fm x) less (x, y)
   = FMap__toSet m less (x, m @_fm x)"
  by (simp add: FMap__toSet_def Map__maps_p_def definedAt_m_def
                Relation__functional_p_def Relation__apply_def
                e_at_fm_def e_at_m_def)

lemma FMap__Set_less [simp]:
  "FMap__toSet (m less_fm x) = (FMap__toSet m) less (x, m @_fm x)"
   apply (simp add: FMap__update_def e_at_fm_def
                 less_fm_def  
                 in_fset_p_def FMap__domain_def FSet__fromFSet_f_f
                 FMap__fromFMap_def Function__inverse_f_apply                  
                 FMap__update_Obligation_subtype
                 FMap__toFMap_subtype_constr
                 FMap__toSet_def Map__maps_p_def definedAt_m_def,
          simp only: FMap__fromFMap_def [symmetric],
          cut_tac m=m and x=x in FMap__e_dsh_Obligation_subtype, 
          simp, thin_tac "finite _")
   apply (auto simp add: e_dsh_dsh_m_def e_at_m_def split: split_if_asm)
done

lemma FMap__fromSet_less [simp]:
  "\<lbrakk>finite s; Relation__functional_p s\<rbrakk>
    \<Longrightarrow> FMap__fromSet s less_fm a
      = FMap__fromSet (s less (a, FMap__fromSet s @_fm a))"
  apply (rule sym, subst FMap__Set_inv)
  apply (simp, drule Relation__functional_p_less, simp)
  apply (simp add: FMap__toSet_inv)
done

lemma FMap__Set_update [simp]:
  "FMap__toSet (FMap__update m x y) = insert (x,y) (FMap__toSet (m less_fm x))"
   apply (simp,
          simp add: FMap__update_def e_at_fm_def
                 in_fset_p_def FMap__domain_def FSet__fromFSet_f_f
                 FMap__fromFMap_def Function__inverse_f_apply                  
                 FMap__update_Obligation_subtype
                 FMap__toFMap_subtype_constr 
                 FMap__toSet_def Map__maps_p_def definedAt_m_def,
          simp only: FMap__fromFMap_def [symmetric])
   apply (auto simp add: Map__update_def e_at_m_def split: split_if_asm)
done

lemma FMap__fromSet_insert [simp]:
  "\<lbrakk>finite s; Relation__functional_p (insert (a, b) s)\<rbrakk>
    \<Longrightarrow> FMap__update (FMap__fromSet s) a b = FMap__fromSet (insert (a, b) s)"
  apply (rule sym, subst FMap__Set_inv, simp_all)
  apply (frule Relation__functional_p_insert)
  apply (simp add: FMap__toSet_inv)
  apply (case_tac "FMap__fromSet s @_fm a = b", simp)
  apply (frule Relation__functional_p_insert_new, auto)
done


lemma FMap__update_at:
   "\<lbrakk>FMap__toSet m = insert (a, b) s\<rbrakk> \<Longrightarrow>  m @_fm a = b"
  apply (simp add: e_at_fm_def e_at_m_def)
  apply (cut_tac m=m in FMap__Set_Relation__functional_p, simp)
  apply (cut_tac m=m in FMap__Set_finite, simp)
  apply (erule rev_mp, subst FMap__Set_inv [symmetric], auto)
  apply (simp add: FMap__fromSet_def FMap__fromFMap_f_f Relation__apply_def)
  apply (subst Abs_Map__FiniteMap_inverse)
  apply (simp add:   dom_if non_empty_simp          )
  apply (auto simp add: non_empty_simp  )
  apply (rule_tac B="{fst x |x. x \<in> insert (a, b) s}" in finite_subset)
  defer apply (rule finite_image_set, simp) prefer 3
  apply (auto  )
  apply (simp add: the_elem_def, rule the1_equality,
         simp add: unique_singleton1 Relation__functional_p_alt_def, 
         rule_tac a=b in ex1I, auto simp add: ,
         simp add: Relation__functional_p_alt_def, auto simp add: )+
done

lemma FMap__update_simp:
   "\<lbrakk>FMap__toSet m = insert (a, b) s; (a, b) \<notin> s\<rbrakk>
     \<Longrightarrow>  FMap__toSet (m less_fm a) = s"
  apply (cut_tac m=m in FMap__Set_Relation__functional_p, simp,
         simp add: Relation__functional_p_alt_def)
  apply (drule_tac x=a in spec, drule_tac x=b in spec, 
         drule_tac x="m @_fm a" in spec, auto)
  apply (simp add: FMap__update_at)
done

lemma FMap__update_twice:
   "\<lbrakk>FMap__toSet m = insert (a, b) s\<rbrakk> \<Longrightarrow>  FMap__update m a b = m"
  apply (subgoal_tac "FMap__toSet (FMap__update m a b) = FMap__toSet m")
  apply (thin_tac _, drule_tac f=FMap__fromSet in arg_cong,
         simp only: FMap__fromSet_inv)
  apply (simp add: FMap__update_at)
done

(******************************************************************************)

(*** This is a temporary trick:
     The translator places all these defs and lemmas BEFORE the definition
     of  FMap__foldable_p.
     I don't want to insert them verbatim into the Specware text, so I create 
     a definition here that is identical to FMap__foldable_p and link it to
     the real def via a small verbatim lemma
******************************************************************************)

consts FMap__foldable_aux :: "'c \<times> ('c \<times> ('a \<times> 'b) \<Rightarrow> 'c) \<times>  ('a, 'b)FMap__FMap
                             \<Rightarrow> bool"
defs FMap__foldable_aux_def: 
  "FMap__foldable_aux
     \<equiv> (\<lambda> ((c::'c), (f::'c \<times> ('a \<times> 'b) \<Rightarrow> 'c), (m:: ('a, 'b)FMap__FMap)). 
          \<forall>(x1::'a) (x2::'a) (z::'c). 
            x1 in_fset? FMap__domain m 
              \<and> x2 in_fset? FMap__domain m 
              \<longrightarrow> f(f(z, (x1, m @_fm x1)), (x2, m @_fm x2)) 
                    = f(f(z, (x2, m @_fm x2)), (x1, m @_fm x1)))"

lemma FMap__Set_foldable_p [simp]:
 "FMap__foldable_aux (c,f,m) = Set__foldable_p (c, f, FMap__toSet m)"
  by (simp add: FMap__foldable_aux_def e_at_fm_def
                in_fset_p_def FMap__domain_def FSet__fromFSet_f_f
                FMap__fromFMap_def Function__inverse_f_apply  
                FMap__toFMap_subtype_constr 
                FMap__toSet_def Map__maps_p_def definedAt_m_def )




(******************************************************************************)

lemma Set__fold_if_unfoldable:
   "\<not> Set__foldable_p (c,f,s) \<Longrightarrow>  Set__fold (c,f,s) = regular_val"
   apply (simp only: Set__fold_def)
   (* for some reason Isabelle cannot figure out the P inside THE *)
   apply (rule_tac P="\<lambda>fold__v. Fun_PD
             (Set__foldable_p &&& (\<lambda>(ignore1, ignore2, x_3). finite x_3))
              fold__v \<and>
             (\<forall>c f. fold__v (c, f, {}) = c) \<and>
             (\<forall>c f s x.
                finite s \<and> Set__foldable_p (c, f, insert x s) \<longrightarrow>
                  fold__v (c, f, insert x s) =
               f (fold__v (c, f, s less x), x))" in the1I2,
          rule Set__fold_Obligation_the)
   apply (simp del: Set__foldable_p_def)
done

lemma Set__fold_empty:
  "Set__fold (c, f, {}) = c"
   apply (simp only: Set__fold_def)
   (* for some reason Isabelle cannot figure out the P inside THE *)
   apply (rule_tac P="\<lambda>fold__v. Fun_PD
             (Set__foldable_p &&& (\<lambda>(ignore1, ignore2, x_3). finite x_3))
              fold__v \<and>
             (\<forall>c f. fold__v (c, f, {}) = c) \<and>
             (\<forall>c f s x.
                finite s \<and> Set__foldable_p (c, f, insert x s) \<longrightarrow>
                  fold__v (c, f, insert x s) =
               f (fold__v (c, f, s less x), x))" in the1I2,
          rule Set__fold_Obligation_the)
   apply (clarify, drule spec,  erule spec)
done

lemma Set__fold_insert:
  "\<lbrakk>finite s; Set__foldable_p (c, f, insert x s)\<rbrakk> \<Longrightarrow>
    Set__fold (c, f, insert x s) = f (Set__fold (c, f, s less x), x)"
   apply (simp only: Set__fold_def)
   (* for some reason Isabelle cannot figure out the P inside THE *)
   apply (rule_tac P="\<lambda>fold__v. Fun_PD
             (Set__foldable_p &&& (\<lambda>(ignore1, ignore2, x_3). finite x_3))
              fold__v \<and>
             (\<forall>c f. fold__v (c, f, {}) = c) \<and>
             (\<forall>c f s x.
                finite s \<and> Set__foldable_p (c, f, insert x s) \<longrightarrow>
                  fold__v (c, f, insert x s) =
               f (fold__v (c, f, s less x), x))" in the1I2,
          rule Set__fold_Obligation_the)
   apply (simp)
done

lemma Set__fold_unique:
  "\<lbrakk>\<forall>c f s.    \<not> Set__foldable_p (c,f,s) \<or> \<not> finite s \<longrightarrow>
                 fld (c,f,s) = regular_val;
    \<forall>c f.      fld (c, f, {}) = c;
    \<forall>c f s x.  finite s \<and> Set__foldable_p (c, f, insert x s) \<longrightarrow>
                 fld (c, f, insert x s) =  f (fld (c, f, s less x), x)\<rbrakk>
   \<Longrightarrow> fld = Set__fold"
   apply (simp only: Set__fold_def)
   apply (rule sym, rule the1_equality, rule Set__fold_Obligation_the)
   apply (auto simp del: Set__foldable_p_def)
(** done **)



(******************************************************************************
 ** End of preparation lemmas 
 ******************************************************************************)


end-proof


proof Isa fold_Obligation_the
  apply (rule_tac a="\<lambda>(c, f, m). Set__fold (c, f, FMap__toSet m)" in ex1I,
         auto simp del: Set__foldable_p_def less_def)
  apply (simp add: Set__fold_if_unfoldable)
  apply (simp add: Set__fold_empty)
  apply (cut_tac s="FMap__toSet m less (x, m @_fm x)" 
             and c=c_1 and f=f_1 and x="(x,y)" in Set__fold_insert,
         simp, simp,  erule ssubst, simp only: FMap__toSet_less_less )
  (* Uniqueness ***)
  apply (rule ext, simp add: split_paired_all del: Set__foldable_p_def)
  apply (subgoal_tac
          "\<forall>s. finite s \<longrightarrow> (\<forall>b. FMap__toSet b =s
           \<longrightarrow> x (a, aa, b) = Set__fold (a, aa, s))",  simp)
  apply (rule allI, rule impI, induct_tac s rule: finite_induct, simp)
  apply (rule allI, subst FMap__Set_inv [symmetric], 
         simp, simp, simp add: Set__fold_empty)
  apply (auto simp del: Set__foldable_p_def)
  apply (case_tac "Set__foldable_p (a, aa, FMap__toSet ba)",
         simp_all add: Set__fold_if_unfoldable del: Set__foldable_p_def,
         thin_tac _, thin_tac _)   
  apply (frule_tac s=F and c=a and f=aa and x="(ab,b)" in Set__fold_insert, 
         auto simp del: Set__foldable_p_def, rotate_tac -1, thin_tac _)
  apply (cut_tac m=ba in FMap__Set_Relation__functional_p, 
         simp del: Set__foldable_p_def)
  apply (cut_tac m=ba and s = "insert (ab, b) F" in FMap__Set_inv [symmetric], 
         simp, simp, simp del: Set__foldable_p_def)
  apply (rotate_tac -3, drule_tac x="ba less_fm ab" in spec,
         frule FMap__update_simp, simp, simp del: Set__foldable_p_def)
  apply (drule_tac x=a in spec, drule_tac x=aa in spec, 
         drule_tac x=ba in spec, 
         drule_tac x=ab in spec, drule_tac x=b in spec)
  apply (simp add: FMap__update_twice)
end-proof

proof Isa fold_Obligation_subtype
   (*** change aux back to "p" if the translator provides new capabilities *)
   by (simp add: FMap__foldable_aux_def empty_fm_def e_at_fm_def 
                 FMap__fromFMap_def Function__inverse_f_apply 
                 in_fset_p_def FMap__domain_def FSet__fromFSet_f_f 
                 FMap__toFMap_subtype_constr )
end-proof

proof Isa fold_Obligation_subtype0
   (*** change aux back to "p" if the translator provides new capabilities *)
   apply (simp add: FMap__foldable_aux_def FMap__update_def e_at_fm_def
                 less_fm_def  
                 in_fset_p_def FMap__domain_def FSet__fromFSet_f_f
                 FMap__fromFMap_def Function__inverse_f_apply                  
                 FMap__update_Obligation_subtype
                 FMap__toFMap_subtype_constr ,
          simp only: FMap__fromFMap_def [symmetric],
          cut_tac m=m and x=x in FMap__e_dsh_Obligation_subtype, 
          simp add: ,
          thin_tac "finite _")
   apply (auto simp add: e_dsh_dsh_m_def Map__update_def dom_def e_at_m_def)
   apply (drule_tac x=x1 in spec, drule_tac x=x2 in spec, simp)  
end-proof


proof Isa inverse_Obligation_subtype
  apply (cut_tac 
           m="Abs_Map__InjectiveMap (Rep_Map__FiniteMap (FMap__fromFMap m))" 
         in Map__inverse_Obligation_subtype)
  apply (simp add: FMap__injective_p_def Map__inverse_def 
                 FMap__fromFMap_def Function__inverse_f_apply  
                 FMap__toFMap_subtype_constr ,
         simp only: FMap__fromFMap_def [symmetric]
        )
  apply (subst Abs_Map__FiniteMap_inverse, simp_all,
         simp (no_asm_simp) add: dom_def Let_def Map__Map__applyi_simp
                 FMap__toFMap_subtype_constr  ,
         cut_tac m=m in FMap__domain_Obligation_subtype, auto simp add: dom_def)
end-proof

proof Isa map_Obligation_subtype
  by (cut_tac m=m in FMap__domain_Obligation_subtype,
      auto simp add: Map__map_def dom_def split: option.split)
end-proof

proof Isa mapWithDomain_Obligation_subtype
  by (cut_tac m=m in FMap__domain_Obligation_subtype,
      auto simp add: dom_def split: option.split)
end-proof

proof Isa toFSet_Obligation_subtype
  apply (simp add: Map__maps_p_def definedAt_m_def e_at_m_def)
  apply (cut_tac m=m in FMap__domain_Obligation_subtype, simp add: dom_def,
         cut_tac m=m in FMap__range_Obligation_subtype, simp add: ran_def,
         drule_tac  finite_cartesian_product, simp, thin_tac _)
  apply (rule finite_subset, auto)
end-proof


proof Isa fromFSet_Obligation_subtype
  apply (simp add: dom_def Relation__apply_def Let_def 
                   Relation__functional_p_def unique_singleton)
  apply (rule_tac B="{fst x |x. x \<in> FSet__fromFSet s}" in finite_subset)
  defer
  apply (rule finite_image_set, auto simp add: FSet__fromFSet_finite)
end-proof

proof Isa fromFSet_Obligation_subtype0
  by (simp add: Relation__apply_def Relation__functional_p_def,
      drule_tac x=x in spec, erule disjE, auto)
end-proof

proof Isa e_fsl_fsl_bsl_bsl_Obligation_subtype
  apply (auto simp add: FSet__nonEmpty_p_def FMap__range_def Map__nonEmpty_p_def
                FSet__fromFSet_f_f FMap__range_Obligation_subtype
                Set__nonEmpty_p_def )
  apply (erule notE, simp add: Rep_Map__FiniteMap_simp [symmetric] ran_empty1)
end-proof

proof Isa fromLists_Obligation_subtype
  by (simp add: dom_def)
end-proof

proof Isa fromLists_Obligation_subtype0
  apply (simp, drule sym, erule ssubst, 
         auto simp add: in_set_conv_nth List__positionOf_def 
                        List__theElement_def List__positionsOf_def
                        singleton_list_to_set)
  apply (rule the1I2, auto simp add: unique_singleton2 nth_eq_iff_index_eq)
end-proof

endspec
