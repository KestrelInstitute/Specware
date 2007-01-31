Option qualifying spec

  import Compare

  type Option a = | None | Some a

  op some : [a] a -> Option a = embed Some

  op none : [a] Option a = embed None

  op [a] some? (x: Option a) : Boolean = (x ~= none)

  op [a] none? (x: Option a) : Boolean = (x = none)

  op [a] compare
     (comp: a * a -> Comparison) (o1: Option a, o2: Option a) : Comparison =
    case (o1,o2) of
       | (Some x,Some y) -> comp (x,y)
       | (None,  Some _) -> Less
       | (Some _,None)   -> Greater
       | (None,  None)   -> Equal

  op [a,b] mapOption (f: a -> b) (opt: Option a) : Option b =
    case opt of
    | None   -> None
    | Some x -> Some (f x)

  proof Isa Thy_Morphism
   type Option.Option \_rightarrow option
   Option.mapOption \_rightarrow option_map
  end-proof

endspec
