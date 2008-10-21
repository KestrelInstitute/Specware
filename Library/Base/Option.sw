Option qualifying spec

  import Compare, Function

  % add an extra element to a type:

  type Option a = | None | Some a

  % ops synonym of embedders and embedding tests:

  op some : [a] a -> Option a = embed Some
  op none : [a]      Option a = embed None

  op [a] some? (x: Option a) : Bool = (x ~= None)
  op [a] none? (x: Option a) : Bool = (x  = None)

  (* Given a comparison function over type a, type Option a can be linearly
  ordered and compared by considering the extra element None to be smaller than
  any element of a. *)

  op [a] compare
     (comp: a * a -> Comparison) (o1: Option a, o2: Option a) : Comparison =
    case (o1,o2) of
       | (Some x,Some y) -> comp (x,y)
       | (None,  Some _) -> Less
       | (Some _,None)   -> Greater
       | (None,  None)   -> Equal

  % lift function to also map extra element:

  op [a,b] mapOption (f: a -> b) : Option a -> Option b = fn
    | None   -> None
    | Some x -> Some (f x)

  % lift isomorphism (i.e. bijection) to also map extra element:

  op [a,b] isoOption : Bijection(a,b) -> Bijection(Option a, Option b) =
    fn iso_elem -> mapOption iso_elem

  proof Isa isoOption_Obligation_subsort
   apply(simp add: bij_def, auto) 
   (** first subgoal **)
   apply(simp add: inj_on_def option_map_def, auto)
   apply (simp split: option.split_asm)
   (** second subgoal **)
   apply(simp add:surj_def option_map_def, auto)
   apply (induct_tac y)
   (** subgoal 2.1    **)
   apply (simp split: option.split)
   (** subgoal 2.2 needs some guidance   **)
   apply (drule_tac x = "a" in  spec, auto)
   apply (rule_tac x="Some x" in exI, auto)
  end-proof

  proof Isa isoOption_subtype_constr
   apply(simp add: Option__isoOption_def  Option__isoOption_Obligation_subsort)
  end-proof

  % mapping to Isabelle:

  proof Isa Thy_Morphism
   type Option.Option \_rightarrow option
   Option.mapOption \_rightarrow option_map
  end-proof

endspec
