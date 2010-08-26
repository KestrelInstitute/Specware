Option qualifying spec

import Compare, Function

proof Isa -subtype_constrs -free-theorems -stp-theorems end-proof

% add an extra element to a type:

type Option a = | None | Some a

% synonyms of embedding tests ("embed? Some" and "embed? None"):

op [a] some? (x: Option a) : Bool = (x ~= None)
proof Isa [simp] end-proof  % always expand definition in Isabelle proof

op [a] none? (x: Option a) : Bool = (x = None)
proof Isa [simp] end-proof  % always expand definition in Isabelle proof

(* Given a comparison function over type a, type Option a can be linearly
ordered and compared by considering the extra element None to be smaller than
any element of a. *)

op [a] compare (comp: a * a -> Comparison) (o1: Option a, o2: Option a): Comparison =
  case (o1,o2) of
    | (Some x,Some y) -> comp (x,y)
    | (None,  Some _) -> Less
    | (Some _,None)   -> Greater
    | (None,  None)   -> Equal

proof Isa compare_Obligation_exhaustive
  by (cases D, cases pV1, cases pV2, auto, cases pV2, auto)
end-proof

% lift function to also map extra element:

op [a,b] mapOption (f: a -> b) : Option a -> Option b = fn
  | None   -> None
  | Some x -> Some (f x)

proof Isa mapOption_subtype_constr
  by (cases xx, auto)
end-proof

% lift isomorphism (i.e. bijection) to also map extra element:

op [a,b] isoOption : Bijection(a,b) -> Bijection(Option a, Option b) =
  fn iso_elem -> mapOption iso_elem

proof Isa isoOption_subtype_constr
 apply(simp add: Option__isoOption_def bij_def, auto)
 (** first subgoal **)
 apply(simp add: inj_on_def Option.map_def, auto)
 apply (simp split: option.split_asm)
 (** second subgoal **)
 apply(simp add:surj_def Option.map_def, auto)
 apply (induct_tac y)
 (** subgoal 2.1    **)
 apply (simp split: option.split)
 (** subgoal 2.2 needs some guidance   **)
 apply (drule_tac x = "a" in  spec, auto)
 apply (rule_tac x="Some x" in exI, auto)  
end-proof

proof Isa isoOption_subtype_constr2
 apply(simp add: bij_ON_def Option__isoOption_def, auto) 
 (** first subgoal **)
 apply(simp add: inj_on_def Option.map_def, auto)
 apply (simp split: option.split_asm add: Option__Option_P.simps mem_def)
 (** second subgoal **)
 apply(simp add:surj_on_def Option.map_def, auto)
 apply (simp add: Option__Option_P.simps mem_def)
 apply (rule_tac P="y = None" in case_split, auto)
 (** subgoal 2.1    **)
 apply (rule_tac x="None" in bexI, simp, simp add: mem_def)
 (** subgoal 2.2 needs some guidance   **)
 apply (drule_tac x = "ya" in  bspec, auto simp add: mem_def)
 apply (rule_tac x="Some x" in bexI, auto  simp add: mem_def)
end-proof

proof Isa Option__isoOption_subtype_constr1
  apply(simp add: Option__isoOption_def, auto)
  apply (rule_tac P="x = None" in case_split, auto)
end-proof

% mapping to Isabelle:

proof Isa Thy_Morphism
 type Option.Option \_rightarrow option
 Option.mapOption \_rightarrow Option.map
end-proof

#translate Haskell -header
{-# OPTIONS -fno-warn-duplicate-exports #-}
#end

proof Haskell Thy_Morphism Maybe
 type Option.Option \_rightarrow Maybe
 None \_rightarrow Nothing
 Some \_rightarrow Just
 Option.some? \_rightarrow isJust
 Option.none? \_rightarrow isNothing 
end-proof

endspec
