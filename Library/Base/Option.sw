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
  apply(case_tac "x", auto simp add: Option__some_p_def)
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


(* Isabelle pragmas *)
proof Isa some? [simp] end-proof  % always expand definition in Isabelle proof
proof Isa none? [simp] end-proof  % always expand definition in Isabelle proof

proof Isa mapOption_subtype_constr
  by (cases xx, auto)
end-proof

proof Isa isoOption_subtype_constr
   apply(auto simp add: Option__isoOption_def bij_def
                   inj_on_def surj_def Option.map_def 
              split: option.split_asm  option.split)
   apply (induct_tac y, 
          simp,
          drule_tac x = "a" in spec, auto) 
end-proof

proof Isa Option__isoOption_subtype_constr2
  apply(simp add: Option__isoOption_def, auto)
  apply (rule_tac P="x = None" in case_split, auto)
end-proof

proof Isa isoOption_subtype_constr1
 apply(simp add: bij_ON_def Option__isoOption_def, auto)
 (** first subgoal **)
 apply(simp add: inj_on_def Option.map_def, auto)
 apply (simp split: option.split_asm add: Option__Option_P.simps)
 (** second subgoal **)
 apply(simp add:surj_on_def Option.map_def, auto)
 apply(metis (full_types) Option.map_def Option__Option_P.simps(1) 
       Option__Option_P.simps(2) not_Some_eq option_map_None option_map_Some)
end-proof

proof Isa Option__extractOption_subtype_constr
  apply (case_tac o__v)
  apply auto
end-proof


% mapping to Isabelle:

proof Isa Thy_Morphism
 type Option.Option \_rightarrow option
 Option.mapOption \_rightarrow Option.map
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
