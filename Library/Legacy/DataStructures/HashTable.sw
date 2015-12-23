(* Copyright 2015 Kestrel Institute. See file LICENSE.text for license details *)

HashTable qualifying spec

  type HashTable(A,B)

  % In Common Lisp, these are the only hash table tests allowed.
  type Test = | EQ | EQL | EQUAL | EQUALP

  op initialize : [A,B] Test * Nat -> HashTable (A,B)
  op insert     : [A,B] A * B * HashTable (A,B) -> ()
  op lookup     : [A,B] A * HashTable (A,B) -> Option B
endspec

