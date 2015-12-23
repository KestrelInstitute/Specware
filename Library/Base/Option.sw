(* Copyright 2015 Kestrel Institute. See file LICENSE.text for license details *)

Option qualifying spec

% (Note that the generated proofs for this spec go into SW_Option.thy
% rather than Option.thy, because Option is already a theory in the
% Isabelle libary.)

import Compare, Function

proof Isa -subtype_constrs -free-theorems -stp-theorems end-proof

% add an extra element to a type:

type Option a = | None | Some a

% synonyms of embedding tests ("embed? Some" and "embed? None"):

op [a] some? (x: Option a) : Bool = embed? Some x

%% quick and dirty fix for failing proofs:
proof Isa -verbatim
theorem some_old_def [simp]:
  "Option__some_p x = (x \<noteq> None)"
  apply(case_tac "x", auto)
done
declare Option__some_p_def [simp del]
end-proof

op [a] none? (x: Option a) : Bool = (x = None)

op [a] extractOption(n:a)(o:Option a):a =
   case o of
     | None -> n
     | Some x -> x
       

(* Given a comparison function over type a, type Option a can be linearly
ordered and compared by considering the extra element None to be smaller than
any element of a. *)

op [a] compare (comp: a * a -> Comparison) (o1: Option a, o2: Option a): Comparison =
  case (o1,o2) of
    | (Some x,Some y) -> comp (x,y)
    | (None,  Some _) -> Less
    | (Some _,None)   -> Greater
    | (None,  None)   -> Equal

% lift function to also map extra element:
%% This map function is given special treatment in
%% Languages/MetaSlang/Transformations/Coercions.sw (see op
%% lifterFuns).

op [a,b] mapOption (f: a -> b) : Option a -> Option b = fn
  | None   -> None
  | Some x -> Some (f x)

% lift isomorphism (i.e. bijection) to also map extra element:

op [a,b] isoOption : Bijection(a,b) -> Bijection(Option a, Option b) =
  fn iso_elem -> mapOption iso_elem

% Apply a map to another type, with a default element
op [a,b] mapOptionDefault (f : a -> b) (df : b) (o : Option a) : b =
  case o of
    | None -> df
    | Some a -> f a

(* Isabelle pragmas *)
proof Isa some? [simp] end-proof  % always expand definition in Isabelle proof
proof Isa none? [simp] end-proof  % always expand definition in Isabelle proof

proof Isa mapOption_subtype_constr
  by (cases xx, auto)
end-proof

proof Isa isoOption_subtype_constr
   apply(auto simp add: Option__isoOption_def bij_def
                   inj_on_def surj_def map_option_case 
              split: option.split_asm option.split)
   apply (induct_tac y, 
          simp,
          drule_tac x = "a" in spec, auto) 
   by (metis option.sel)
end-proof

proof Isa isoOption_subtype_constr1
 apply(simp add: bij_ON_def Option__isoOption_def, auto)
 (** first subgoal **)
 apply(simp add: inj_on_def map_option_case, auto)
 apply (simp split: option.split_asm)
 (** second subgoal **)
 apply(simp add:surj_on_def map_option_case, auto)
 by (metis Option__Option_P.simps(1) Option__Option_P.simps(2) not_Some_eq option.simps(4) option.simps(5))
end-proof

proof Isa Option__isoOption_subtype_constr2
  apply(simp add: Option__isoOption_def, auto)
  apply (rule_tac P="x = None" in case_split, auto)
end-proof

proof Isa Option__mapOptionDefault_subtype_constr
  apply (induct o__v)
  by auto
end-proof

proof Isa Option__extractOption_subtype_constr
  apply (case_tac o__v)
  apply auto
end-proof


(*** Some helpful lemmas for proving things about options ***)

proof Isa -verbatim
lemma mapOption_preserves_P: "[| (\<forall> x. P x --> P (f x)); Option__Option_P P opt |] ==> Option__Option_P P (map_option f opt)"
  apply (induct opt)
  by auto

lemma mapOptionDefault_Pin_Pout:
  "[| Pout dflt; (\<forall> x . Pin x --> Pout (f x)); Option__Option_P Pin opt |] ==>
   Pout (Option__mapOptionDefault f dflt opt)"
  apply (induct opt)
  by auto

(* Congruence rule, for function definitions using Option_P *)
lemma Option_P_cong[fundef_cong]:
  "[| opt1 = opt2 ; (\<And> x . opt2 = Some x ==> P1 x = P2 x)|] ==>
    Option__Option_P P1 opt1 = Option__Option_P P2 opt2"
  by (case_tac opt1, auto)
end-proof


% mapping to Isabelle:

proof Isa Thy_Morphism
 type Option.Option -> option
 Option.mapOption -> map_option
end-proof

(* Haskell Pragmas *)
#translate Haskell -header
{-# OPTIONS -fno-warn-duplicate-exports #-}
#end

#translate Haskell mapOption -> mapOption #end

#translate Haskell -morphism Maybe
 type Option.Option \_rightarrow Maybe
 None \_rightarrow Nothing
 Some \_rightarrow Just
 Option.some? \_rightarrow isJust
 Option.none? \_rightarrow isNothing 
#end



endspec
