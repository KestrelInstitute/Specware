(* Copyright 2015 Kestrel Institute. See file LICENSE.text for license details *)

spec
  import /Library/Structures/Data/Monad

  type MapRef (a,b)

  op new : fa (a,b) Monad (MapRef (a,b))
  op copy : fa (a,b) MapRef (a,b) -> Monad (MapRef (a,b))
  op eval : fa (a,b) MapRef (a,b) * a -> Monad b
  op update : fa (a,b) MapRef (a,b) * a * b -> Monad ()
  op fold : fa (a,b,c) (c * (a * b) -> Monad c) * c * MapRef (a,b) -> Monad b
endspec
