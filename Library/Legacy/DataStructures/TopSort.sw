%% toplogical sort

TopSort qualifying spec {
  import HashTable
  % import List       % DataStructures/List.sl

  sort Graph a = a -> List a

  sort Tree a =
    | Leaf
    | Node a * Tree a * Tree a

  op mkLeaf   : fa (a) Tree a
  op topSort  : fa (a) HashTable.Test * Graph a * List a -> List a
  op dfs      : fa (a) HashTable.Test * Graph a * List a -> Tree a
  op inorder  : fa (a) Tree a -> List a
  op inorderL : fa (a) Tree a * List a -> List a

  def mkLeaf = Leaf

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
        of []      -> mkLeaf
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
         | Node(a,l,r) -> inorderL(l,List.cons(a,inorderL(r,ls)))
}
