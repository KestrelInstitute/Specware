HashTable qualifying spec {
  sort HashTable(A,B)

  % In Common Lisp, these are the only hash table tests allowed.
  sort Test = | EQ | EQL | EQUAL | EQUALP

  op initialize : fa(A,B) Test * Nat -> HashTable (A,B)
  op insert     : fa(A,B) A * B * HashTable (A,B) -> ()
  op lookup     : fa(A,B) A * HashTable (A,B) -> Option B
}
