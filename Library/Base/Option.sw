Option qualifying spec

  import Compare

  sort Option a = | None | Some a

  op some      : fa(a) a -> Option a
  op none      : fa(a) Option a
  op some?     : fa(a) Option a -> Boolean
  op none?     : fa(a) Option a -> Boolean
  op compare   : fa(a) (a * a -> Comparison) ->
                       Option a * Option a -> Comparison
  op mapOption : fa(a,b) (a -> b) -> Option a -> Option b

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
