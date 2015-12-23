(* Copyright 2015 Kestrel Institute. See file LICENSE for license details *)

%% toplogical type

TopSort qualifying spec
  import HashTable
  % import List       % DataStructures/List.sl

  type Graph a = a -> List a

  type Tree a =
    | Leaf
    | Node a * Tree a * Tree a

  op mkLeaf   : [a] Tree a
  op topSort  : [a] HashTable.Test * Graph a * List a -> List a
  op dfs      : [a] HashTable.Test * Graph a * List a -> Tree a
  op inorder  : [a] Tree a -> List a
  op inorderL : [a] Tree a * List a -> List a

  def topSort (test, g, vs) =
    inorder (dfs (test, g, vs))

  def dfs (test, g, vs) =
    let t = HashTable.initialize (test, List.length vs) in

    let def mark v =
      HashTable.insert (v, (), t)

    def marked v =
      case HashTable.lookup (v, t)
        of Some _ -> true
         | None   -> false

    def dfsLoop vs =
      case vs
        of []      -> Leaf
         | v :: vs ->
           if marked v
             then dfsLoop vs
           else
           let _ = mark v in
           let ps = dfsLoop (g v) in
           let qs = dfsLoop vs in
           Node (v, ps, qs)

    in dfsLoop vs

  def inorder t = inorderL(t,[])

  def inorderL(t,ls) = 
      case t
        of Leaf -> ls
         | Node(a,l,r) -> inorderL(l,Cons(a,inorderL(r,ls)))
endspec
