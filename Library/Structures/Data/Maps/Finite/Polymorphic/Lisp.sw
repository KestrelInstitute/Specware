(* Copyright 2015 Kestrel Institute. See file LICENSE.text for license details *)

MonadicMapsInternal qualifying spec
  type Lisp.HashTable (a,b)
  op makeHashEqual : fa (a,b) (Nat * Nat) -> Lisp.HashTable (a,b)
  op makeHashEq    : fa (a,b) (Nat * Nat) -> Lisp.HashTable (a,b)
  op getHash       : fa (a,b) Lisp.HashTable (a,b) * a * b -> b
  op remHash       : fa (a,b) Lisp.HashTable (a,b) * a -> Bool
  op setHash       : fa (a,b) Lisp.HashTable (a,b) * a * b -> b
  op mapHash       : fa (a,b) Lisp.HashTable (a,b) * (a * b -> ()) -> ()
endspec
