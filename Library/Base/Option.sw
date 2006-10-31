Option qualifying spec

  import Compare

  type Option a = | None | Some a

  op some : [a] a -> Option a
  def some x = Some x

  op none : [a] Option a
  def none = None

  op some? : [a] Option a -> Boolean
  def some? x = (x ~= none)

  op none? : [a] Option a -> Boolean
  def none? x = (x = none)

  op compare : [a] (a * a -> Comparison) -> Option a * Option a -> Comparison
  def compare comp (o1,o2) =
    case (o1,o2) of
       | (Some x,Some y) -> comp (x,y)
       | (None,  Some _) -> Less
       | (Some _,None)   -> Greater
       | _               -> Equal

  op mapOption : [a,b] (a -> b) -> Option a -> Option b
  def mapOption f opt =
    case opt of
      | None   -> None
      | Some x -> Some(f x)

  proof Isa Thy_Morphism
   type Option.Option \_rightarrow option
   Option.mapOption \_rightarrow option_map
  end-proof

endspec
