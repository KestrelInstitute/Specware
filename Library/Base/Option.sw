Option qualifying spec

  import Compare

  type Option a = | None | Some a

  op some      : [a] a -> Option a
  op none      : [a] Option a
  op some?     : [a] Option a -> Boolean
  op none?     : [a] Option a -> Boolean
  op compare   : [a] (a * a -> Comparison) ->
                       Option a * Option a -> Comparison
  op mapOption : [a,b] (a -> b) -> Option a -> Option b

  def some x = Some x

  def none = None

  def some? x = (x ~= none)

  def none? x = (x = none)

  def compare comp (o1,o2) =
    case (o1,o2) of
       | (Some x,Some y) -> comp (x,y)
       | (None,  Some _) -> Less
       | (Some _,None)   -> Greater
       | _               -> Equal

  def mapOption f opt =
    case opt of
      | None   -> None
      | Some x -> Some(f x)

endspec
