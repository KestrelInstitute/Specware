SplaySet qualifying spec {  
  import /Library/Legacy/State
  import SplayTree

  sort Set key =
    | EMPTY (key * key -> Comparison)
    | SET {
          comp : (key * key -> Comparison),
          root : Ref (Splay key),
          nobj : Nat
        }

  op empty        : fa(key) (key * key -> Comparison) -> Set key
  op singleton    : fa(key) (key * key -> Comparison) * key -> Set key
  op add          : fa(key) Set key * key -> Set key 
  op add_         : fa(key) key * Set key -> Set key
  op addList      : fa(key) Set key * List key -> Set key
  op delete       : fa(key) Set key * key -> Set key
  op member       : fa(key) Set key * key -> Boolean
  op numItems     : fa(key) Set key -> Nat
  op listItems    : fa(key) Set key -> List key
  op isEmpty      : fa(key) Set key -> Boolean
 
  op equal        : fa(key) Set key * Set key -> Boolean
  op isSubset     : fa(key) Set key * Set key -> Boolean
 
  op compare      : fa(key) Set key * Set key -> Comparison
 
  op intersection : fa(key) Set key * Set key -> Set key
  op difference   : fa(key) Set key * Set key -> Set key
  op union        : fa(key) Set key * Set key -> Set key
  op map          : fa(key) (key -> key) -> Set key -> Set key
  op app          : fa(key) (key -> ()) -> Set key -> ()
  op foldr        : fa(key,a) (key * a -> a) -> a -> Set key -> a
  op foldl        : fa(key,a) (key * a -> a) -> a -> Set key -> a
  op filter       : fa(key) (key -> Boolean) -> Set key -> Set key
  op exists       : fa(key) (key -> Boolean) -> Set key -> Boolean
  op find         : fa(key) (key -> Boolean) -> Set key -> Option key
 
  op compf        : fa(a) (a * a -> Comparison) * a -> a -> Comparison
  op insert       : fa(a) (a * a -> Comparison) -> a * (Nat * Splay a) -> Nat * Splay a
  op listItemsApp : fa(key) Splay key * List key -> List key
  op memberT      : fa(key) (key * key -> Comparison) * key * Splay key -> Boolean
  op treeIn       : fa(key) ((key * key -> Comparison) * Splay key * Splay key) -> Boolean
  op next         : fa(key) List (Splay key) -> Splay key * List (Splay key)
  op left         : fa(key) Splay key * List (Splay key) -> List (Splay key)
  op cmp :
    fa(key)
       (key * key -> Comparison)
     * List (Splay key)
     * List (Splay key)
     -> Comparison

  op compOf       : fa(a) Set a -> (a * a -> Comparison)
  op split        : fa(a) (a * a -> Comparison) * a * Splay a -> Option a * Splay a * Splay a
  op intersectionSplay : fa(a) (a * a -> Comparison) * Splay a * Splay a -> Splay a * Nat
  op count        : fa(a) Splay a * Nat -> Nat
  op diffSplay    : fa(a) (a * a -> Comparison) * Splay a * Splay a -> Splay a * Nat
  op unionSplay   : fa(a) (a * a -> Comparison) * Splay a * Splay a -> Splay a * Nat
  op mapf         : fa(a) (a -> a) * Set a * Splay a -> Set a
  op appSplay     : fa(a) (a -> ()) -> Splay a -> ()
  op foldrSplay   : fa(a,b) (a * b -> b) -> b -> Splay a -> b
  op foldlSplay   : fa(a,b) (a * b -> b) -> b -> Splay a -> b
  % op mkSplayNil   : fa(a) Splay a
  op filterSplay  : fa(a) (a * a -> Comparison) -> (a -> Boolean) * Splay a * (Nat * Splay a) -> Nat * Splay a
  op existsSplay  : fa(a) (a -> Boolean) -> Splay a -> Boolean
  op findSplay    : fa(a) (a -> Boolean) -> Splay a -> Option a

  %% ========================================================================

  def empty comp = EMPTY comp 

  def compf (comp, k) k_ =
    comp (k_, k)

  def singleton(comp,v) = 
    SET {root = Ref(SplayObj{value = v,left = SplayNil,right = SplayNil}),
         comp = comp,
         nobj = 1}
    
  (* Primitive insertion. *)
  def insert comp (v,(nobj,root)) =
    case splay (compf (comp, v), root) of
      | (Equal,SplayObj{value,left,right}) -> 
           (nobj,SplayObj{value = v,left = left,right = right})
      | (Less,SplayObj{value,left,right}) -> 
              (nobj + 1,
               SplayObj {
                 value = v,
                 left = SplayObj {value = value,left = left,right = SplayNil},
                 right = right})
      | (Greater,SplayObj{value,left,right}) -> 
              (nobj + 1,
               SplayObj{
                  value = v,
                  left = left,
                  right = SplayObj{value = value,left = SplayNil,right = right}})
      | (_,SplayNil) -> (1,SplayObj{value = v,left = SplayNil,right = SplayNil})

  def add (set,v) = 
    case set of
      | EMPTY comp -> singleton(comp,v)
      | SET {root,nobj,comp} -> 
          let (cnt,t) = insert comp (v,(nobj,State.! root)) in
          SET {comp = comp,nobj = cnt,root = Ref t}

  def add_ (s, x) = add(x, s)

  (* Insert a list of items. *)

  def addList (set,l) = 
    case l of
      | [] -> set 
      | _ -> 
          let (n,r,c) = 
            case set of
               | SET{root,nobj,comp} -> (nobj,State.! root,comp)
               | EMPTY comp -> (0,SplayNil,comp) 
          in
          let (cnt,t) = List.foldr (insert c) (n,r) l in
          SET{nobj = cnt,root = Ref t,comp = c}

  (* Remove an item. *)
  def delete (set,key) = 
    case set of
      | EMPTY _ -> set
      | SET {root,nobj,comp} -> 
          (case splay(compf (comp, key), State.! root) of
            | (Equal,SplayObj{value,left,right}) -> 
                if nobj = 1 then
                  empty comp
                else
                  SET {
                      root = Ref (join(left,right)),
                      nobj = toNat ((Nat.fromNat nobj) - (Nat.fromNat 1)),
                      comp = comp
                    }
            | (_,r) -> (root := r; set))

  (* return true if the item is in the set *)
  def member (set,key) = 
    case set of
      | EMPTY _ -> false
      | SET {root,nobj,comp} -> 
          (case splay (compf (comp, key), State.! root) of
            | (Equal, r) -> (root := r; true)
            | (_, r) -> (root := r; false))

  def isEmpty set =
    case set of
      | EMPTY _ -> true
      | _ -> false

  (* Return the number of items in the table *)
  def numItems set = 
    case set of
      | EMPTY _ -> 0
      | SET {nobj,comp,root} -> nobj

  def listItemsApp (sp,l) =
    case sp of
      | SplayNil -> l
      | SplayObj{value,left,right} -> 
            listItemsApp (left, cons(value,listItemsApp (right,l)))

  def listItems set =
    case set of
      | EMPTY _ -> []
      | SET{nobj,comp,root} -> listItemsApp(State.! root,[])

  def memberT(comp,x,tree) = 
    case tree of
      | SplayNil -> false
      | SplayObj {value,left,right} -> 
           (case comp(x,value) of
             | Less -> memberT(comp,x,left)
             | Greater -> memberT(comp,x,right)
             | _ -> true)

  (* true if every item in t is in t_ *)
  def treeIn (comp,t,t_) = 
    case t of
      | SplayNil -> true
      | SplayObj{value,left = SplayNil,right = SplayNil} -> 
           memberT(comp,value,t_)
      | SplayObj{value,left,right = SplayNil} -> 
           memberT(comp,value, t_) & treeIn(comp,left,t_)
      | SplayObj{value,left = SplayNil,right} -> 
           memberT(comp,value, t_) & treeIn(comp,right,t_)
      | SplayObj{value,left,right} -> 
             memberT(comp,value, t_)
           & treeIn(comp,left,t_) 
           & treeIn(comp,right,t_)


  %
  % Assume that the same comparison function is used.
  %
  def equal(set1,set2) = 
    case (set1,set2) of
      | (SET{root,nobj,comp},SET{root = r2,nobj = n2,comp = c2}) -> 
                 nobj = n2 & treeIn(comp,State.! root,State.! r2)
      | (EMPTY _,EMPTY _) -> true
      | _ -> false

  def isSubset(set1,set2) = 
    case (set1,set2) of
      | (SET {root,nobj,comp},SET{root = r2,nobj = n2,comp = c2}) -> 
                 nobj <= n2 & treeIn(comp,State.! root,State.! r2)
      | (EMPTY _,_) -> true
      | _ -> false

  def next splays =
    case splays of
      | ((t as SplayObj vl)::rest) -> (t, left(vl.right, rest))
      | _ -> (SplayNil,[])

  def left (sp,rest) =
    case sp of
      | SplayNil -> rest
      | (t as SplayObj vl) -> left(vl.left, cons(t,rest))

  def cmp(comp,t1,t2) = 
    case (next t1,next t2) of
      | ((SplayNil, _), (SplayNil, _)) -> Equal
      | ((SplayNil, _), _) -> Less
      | (_, (SplayNil, _)) -> Greater
      | ((SplayObj s1, r1), (SplayObj s2, r2)) -> 
          (case comp(s1.value, s2.value) of
            | Equal -> cmp (comp,r1, r2)
            | order -> order)

  def compare(set1,set2) = 
    case (set1,set2) of
      | (EMPTY _,EMPTY _) -> Equal
      | (EMPTY _,_) -> Less
      | (_,EMPTY _) -> Greater
      | (SET {root = s1,comp,nobj},SET{root = s2,comp = c2,nobj = n2}) -> 
             cmp(comp,left(State.! s1,[]),left(State.! s2,[]))

  def compOf(set) = 
    case set of
      | EMPTY comp -> comp
      | SET {comp,root,nobj} -> comp

  def split (comp,value,s) =
    case splay (compf (comp, value), s) of
      | (Equal,SplayObj{value,left,right}) -> (Some value, left, right)
      | (Less,SplayObj{value,left,right}) -> 
             (None, SplayObj{value = value,left = left,right = SplayNil},right)
      | (Greater,SplayObj{value,left,right}) -> 
             (None, left, SplayObj{value = value,right = right,left = SplayNil})
      | (_,SplayNil) -> (None, SplayNil, SplayNil)

  def intersection (set1,set2) = 
    case (set1,set2) of
      | (EMPTY _,_) -> set1
      | (_,EMPTY _) -> set2
      | (SET{root = r1,nobj = n1,comp = c1}, SET{root = r2,nobj = n2,comp = c2}) -> 
          (case intersectionSplay(c1,State.! r1,State.! r2) of
            | (_,0) -> EMPTY c1
            | (sp,nobj) -> SET{root =  Ref sp,nobj = nobj,comp = c1})

  def intersectionSplay(comp,s1,s2) = 
    case (s1,s2) of
      | (SplayNil,_) -> (SplayNil,0)
      | (_,SplayNil) -> (SplayNil,0)
      | (s, SplayObj{value,left,right}) ->
          (case split(comp,value,s) of
             | (Some v, l, r) ->
                 let (l_,lcnt) = intersectionSplay(comp,l,left) in
                 let (r_,rcnt) = intersectionSplay(comp,r,right) in
                 (SplayObj{value = v,left = l_,right = r_},lcnt + rcnt + 1)
             | (_,l,r) ->
                 let (l_,lcnt) = intersectionSplay(comp,l,left) in
                 let (r_,rcnt) = intersectionSplay(comp,r,right) in
                 (join(l_,r_),lcnt + rcnt))
               
  def count(sp,n) = 
    case sp of
      | SplayNil -> n
      | SplayObj {left,right,value} -> count(left,count(right,n + 1))

  def difference (set1,set2) = 
    case (set1,set2) of
      | (EMPTY _,_) -> set1
      | (_,EMPTY _) -> set1
      | (SET{root = r1,nobj = n1,comp = c1}, SET{root = r2,nobj = n2,comp = c2}) ->
          (case diffSplay (c1,State.! r1,State.! r2) of
            | (_,0) -> EMPTY c1
            | (root,cnt) -> SET{root = Ref root,nobj = cnt,comp = c1})

  def diffSplay(comp,sp1,sp2) = 
    case (sp1,sp2) of
      | (SplayNil,_) -> (SplayNil,0)
      | (s,SplayNil) -> (s,count(s,0))
      | (s,SplayObj{value,right,left}) ->
          let (_,l,r) = split(comp,value,s) in
          let (l_,lcnt) = diffSplay(comp,l,left) in
          let (r_,rcnt) = diffSplay(comp,r,right) in
          (join(l_,r_),lcnt + rcnt)

  def union (set1,set2) = 
    case (set1,set2) of
      | (EMPTY _,_) -> set2
      | (_,EMPTY _) -> set1
      | (SET {root = r1,nobj = n1,comp = c1}, SET {root = r2,nobj = n2,comp = c2}) -> 
          let (root,cnt) = unionSplay (c1,State.! r1,State.! r2) in
          SET {root = Ref root,nobj = cnt,comp = c1}


  def unionSplay (comp,sp1,sp2) = 
    case (sp1,sp2) of
      | (SplayNil,_) -> (sp2,count(sp2,0))
      | (_,SplayNil) -> (sp1,count(sp1,0))
      | (_,SplayObj {value,right,left}) -> 
          let (_,l,r) = split (comp,value,sp1) in
          let (l_,lcnt) = unionSplay (comp,l,left) in
          let (r_,rcnt) = unionSplay (comp,r,right) in
            (SplayObj {value = value,right = r_,left = l_},lcnt + rcnt + 1)

  def map f set = 
    case set of
      | EMPTY _ -> set
      | SET {root,nobj,comp} -> mapf (f,EMPTY comp,State.! root)

  def mapf (f,acc, sp) = 
    case sp of
      | SplayNil -> acc
      | SplayObj{value,left,right} -> 
            mapf (f,add (mapf (f,acc, left), f value), right)

  def app f set = 
    case set of
      | EMPTY _ -> ()
      | SET {root,nobj,comp} -> appSplay f (State.! root)

  def appSplay f sp = 
    case sp of
      | SplayNil -> ()
      | SplayObj {value,left,right} ->
            (appSplay f left; f value; appSplay f right)

  (* fold function *)
  def foldr abf b set = 
    case set of
      | EMPTY _ -> b
      | SET {root,nobj,comp} -> foldrSplay abf b (State.! root)

  def foldrSplay f b sp = 
    case sp of
      | SplayNil -> b
      | SplayObj {value,left,right} -> 
            foldrSplay f (f (value, foldrSplay f b right)) left

  def foldl abf b set = 
    case set of
      | EMPTY _ -> b
      | SET {root,nobj,comp} -> foldlSplay abf b (State.! root)

  def foldlSplay f b sp = 
    case sp of
      | SplayNil -> b
      | SplayObj {value,left,right} -> 
           foldlSplay f (f (value, foldlSplay f b left)) right

  def filter p set = 
    case set of
      | EMPTY _ -> set
      | SET {root,nobj,comp} -> 
           (case filterSplay comp (p,State.! root,(0,mkSplayNil)) of
             | (0,_) -> EMPTY comp
             | (count,sp) -> SET {root = Ref sp,nobj = count,comp = comp})

  % def mkSplayNil = SplayNil

  def filterSplay comp (p,sp,tree) = 
    case sp of
      | SplayNil -> tree
      | SplayObj{value,left,right} -> 
          let t_ = filterSplay comp (p,right,filterSplay comp (p,left,tree)) in
          if p value then
            insert comp (value,t_)
          else
            t_

  def exists p set = 
    case set of
      | EMPTY _ -> false
      | SET {root,nobj,comp} -> existsSplay p (State.! root)
    
  def existsSplay p sp = 
    case sp of
      | SplayNil -> false
      | SplayObj {value,left,right} ->
          if p value then
            true 
          else 
            if existsSplay p left then
              true
            else
              existsSplay p right 

  def find p set = 
    case set of
      | EMPTY _ -> None
      | SET {root,nobj,comp} -> findSplay p (State.! root)

  def findSplay p sp = 
    case sp of
      | SplayNil -> None
      | SplayObj {value,left,right} ->
          if p value then
            Some value
          else 
            (case findSplay p left of
               | (r as Some _) -> r
               | _ -> findSplay p right)
}
