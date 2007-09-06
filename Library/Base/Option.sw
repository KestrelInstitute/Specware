Option qualifying spec

  import Compare

  % add an extra element to a type:

  type Option a = | None | Some a

  % ops synonym of embedders and embedding tests:

  op some : [a] a -> Option a = embed Some

  op none : [a] Option a = embed None

  op [a] some? (x: Option a) : Boolean = (x ~= none)

  op [a] none? (x: Option a) : Boolean = (x = none)

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

  % mapping to Isabelle:

  proof Isa Thy_Morphism
   type Option.Option \_rightarrow option
   Option.mapOption \_rightarrow option_map
  end-proof

endspec
