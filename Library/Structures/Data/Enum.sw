Enum qualifying spec
  import Elem

  sort Collection

  sort TakeResult = | None | One (Elem * Collection)

  op takeOne : Collection -> TakeResult
endspec
