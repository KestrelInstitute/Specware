\section{Splay Map}

Aadapted from SML/NJ 

\begin{spec}
SplayMap qualifying spec {
  import /Library/Base
  import /Library/Legacy/State
  import SplayTree

  sort Map (key, a) =
    | EMPTY (key * key -> Comparison)
    | MAP  {
          comp : (key * key -> Comparison),
          root : Ref (Splay (key * a)),
          nobj : Nat
        }

  %% Create an empty Map, given an order function

  op  empty : fa(key,a) (key * key -> Comparison) -> Map(key,a)

  %% insert (map, key, rangeElement)
  %%    returns a map' which behaves as map on all elements but, "key", where
  %%    "key" is now mapped to "rangeElement"

  op  insert : fa(key,a) Map(key,a) * key * a -> Map(key,a)

  %% find (map, key)
  %%     returns the range element that "key" maps to if there is any

  op find : fa(key,a) Map(key,a) * key -> Option a

  %% Remove an item. 

  op remove : fa(a,key) Map(key,a) * key -> Map(key,a)

  %% Return the number of items in the table 

  op numItems       : fa(a,key) Map(key,a) -> Nat

  %% List elements in the range in order of appearance (with duplications)

  op listItems      : fa(key,a) Map(key,a) -> List a


  %% List key/range pairs in order of appearance.

  op listItemsi     : fa(key,a) Map(key,a) -> List(key*a)
  op listDomain     : fa(key,a) Map(key,a) -> List(key)
  op inDomain       : fa(key,a) Map(key,a) * key -> Boolean

  %% Apply a function to the entries of the map

  op appi           : fa(key,a)   (key * a -> ()) -> Map(key,a) -> ()
  op app            : fa(key,a)   (a -> ()) -> Map(key,a) -> ()
  op mapi           : fa(key,a,b) (key*a -> b) -> Map(key,a) -> Map(key,b)
  op map            : fa(key,a,b) (a -> b) -> Map(key,a) -> Map(key,b)
  op foldri         : fa(key,a,b)  (key * a * b -> b) -> b -> Map(key,a) -> b
  op foldriDouble   : fa(key1,key2,a,b) (key1 * key2 * a * b -> b) -> b -> Map (key1, Map (key2, a)) -> b
  op foldr          : fa(key,a,b) (a * b -> b) -> b -> Map(key,a) -> b
  op foldli         : fa(key,a,b) (key * a * b -> b) -> b -> Map(key,a) -> b
  op foldl          : fa(key,a,b) (a * b -> b) -> b -> Map(key,a) -> b
  op compose        : fa(dom,med,rng) Map(dom,med) * Map(med,rng) -> Map(dom,rng)
  op unionWith      : fa(key,a)   (a * a -> a) -> Map(key,a) * Map(key,a) -> Map(key,a)
  op unionWithi     : fa(key,a)   (key * a * a -> a) -> Map(key,a) * Map(key,a) -> Map(key,a)
  op intersectWith  : fa(key,a)   (a * a -> a) -> Map(key,a) * Map(key,a) -> Map(key,a)
  op intersectWithi : fa(key,a)   (key * a * a -> a) -> Map(key,a) * Map(key,a) -> Map(key,a)
  op filter         : fa(key,a)   (a -> Boolean) -> Map(key,a) -> Map(key,a)          
  op filteri        : fa(key,a)   (key * a -> Boolean) -> Map(key,a) -> Map(key,a)          
  op mapPartial     : fa(key,a,b) (a -> Option(b)) -> Map(key,a) -> Map(key,b)
  op compare        : fa(a,key)   (a * a -> Comparison) -> (Map(key,a) * Map(key,a)) -> Comparison
  op toList         : fa (a,b)    Map (a, b) -> List (a * b)
  op fromList       : fa (a,b)    (a * a -> Comparison) -> List (a * b) -> Map (a, b)

  op applyi         : fa(a) (a -> ()) -> Splay(a) -> ()
    
  op subset?        : fa (a,b) Map (a,b) * Map (a,b) -> Boolean

  op all            : fa (a,b) (a * b -> Boolean) -> Map (a,b) -> Boolean
  op exists         : fa (a,b) (a * b -> Boolean) -> Map (a,b) -> Boolean

  op listItemsf     : fa(a,b) (a -> b) * Splay(a) * List(b) -> List b
  op api            : fa(key,a,b) (key*a -> b) -> Splay(key*a) -> Splay(key*b)
  op ap             : fa(key,a,b) (a -> b) -> Splay(key*a) -> Splay(key*b)
  op foldriAp       : fa(key,a,b)  (key * a * b -> b) -> Splay(key * a) * b -> b 
  op foldrAp        : fa(key,a,b)  (a * b -> b) -> Splay(key * a) * b -> b 
  op foldliAp       : fa(key,a,b)  (key * a * b -> b) -> Splay(key * a) * b -> b 
  op foldlAp        : fa(key,a,b)  (a * b -> b) -> Splay(key * a) * b -> b 

  op apply          : fa(key,a) (a -> ()) -> Splay(key*a) -> ()
  op mapPartiali    : fa(key,a,b) (key * a -> Option(b)) -> Map(key,a) -> Map(key,b)
  op next           : fa(a) List(Splay(a)) -> Splay(a) * List(Splay(a))
  op left           : fa(a) Splay(a) * List(Splay(a)) -> List(Splay(a))  
  op compOf         : fa(key,a) Map(key,a) -> (key * key -> Comparison)

  %% ========================================================================

  % def fa(a) f(x:a)  = x : a(b)

  def empty = EMPTY

  def insert (map,key,v) = 
    case map of
      | EMPTY comp -> 
          MAP {
              comp = comp,
              nobj = 1,
              root = Ref (SplayObj {
                 value = (key,v),
                 left = SplayNil,
                 right = SplayNil
              })
           }
      | MAP {comp,root,nobj} ->
         (case splay (fn (k,_) -> comp(k,key), State.! root) of
           | (Equal,SplayObj {value,left,right}) -> 
              MAP {comp = comp,
                  nobj = nobj,
                 root = Ref(SplayObj{value = (key,v),left = left,right = right})}
          | (Less,SplayObj {value,left,right}) -> 
              MAP {
                comp = comp,
                nobj = nobj + 1,
                root = Ref(SplayObj{value = (key,v),left = SplayObj{value = value,left = left,right = SplayNil},right = right})
              } 
          | (Greater,SplayObj{value,left,right}) -> 
              MAP {
                comp = comp,
                nobj = nobj + 1,
                root = Ref(SplayObj {
                              value = (key,v),
                              left = left,
                              right = SplayObj{value = value,left = SplayNil,right = right}
                           })
                 }
          | (_,SplayNil) -> System.fail "SplayMap.insert SplayNil")


  def findR(sTree,key,comp) =
    case sTree of
      | SplayNil -> None
      | SplayObj{value = (k,val),left,right} ->
          (case comp(key,k) of
            | Equal -> Some val
            | Less -> findR(left,key,comp)
            | _ -> findR(right,key,comp))

  %% Look for an item, return None if the item doesn't exist

  def find (map,key) = 
    case map of
      | (EMPTY _) -> None
      | MAP{comp,root,nobj} ->
         %let 
         findR(State.! root,key,comp)

  %% The following is the standard code for find to make sure things are balanced, but it does a lot of
  %% consing and is slower in most cases
  %        case splay (fn (k,_) -> comp(k,key), State.! root)
  %          of (Equal, r as SplayObj{value = value as (_,e),left,right}) -> 
  %             (root State.:= r; Some(e))
  %           | (_, r) -> (root State.:= r; None)

  def remove (map,key) = 
    case map of
      | EMPTY _ -> map
      | MAP {comp,root,nobj} -> 
          (case splay (fn (k,_) -> comp(k,key), State.! root) of
            | (Equal, SplayObj{value = value as (_,e), left, right}) -> 
              if nobj = 1 then
                  EMPTY comp
                else
                  MAP {
                     comp = comp,
                     root = Ref(join(left,right)),
                     nobj = toNat ((Integer.fromNat nobj) - (Integer.fromNat 1))
                   }
            | (_,r) -> (root State.:= r; map))
          
  def numItems map = 
    case map of
      | EMPTY _ -> 0
      | MAP{nobj,comp,root} -> nobj

 (* Return a list of the items (and their keys) in the dictionary *)

  def listItemsf(f,sp,l) = 
    case sp of
      | SplayNil -> l
      | SplayObj{value,left,right} -> 
          listItemsf(f,left,cons(f value,listItemsf(f,right,l)))


  def listItems map = 
    case map of
      | EMPTY _ -> []
      | MAP {root,nobj,comp} -> listItemsf(fn(_,v) -> v,State.! root,[])


  def listItemsi map =
    case map of
      | EMPTY _ -> []
      | MAP {root,nobj,comp} -> listItemsf(fn v -> v,State.! root,[])

  def listDomain map = 
    case map of
      | EMPTY _ -> []
      | MAP {root,nobj,comp} -> listItemsf(fn(k,_) -> k,State.! root,[])


  def inDomain(map,key) = 
    case find(map,key) of
      | Some _ -> true
      | None -> false

  def applyi af sp =
    case sp of
      | SplayNil -> ()
      | SplayObj {value,left,right} ->
          (applyi af left; af value; applyi af right)

  def appi af map = 
    case map of
      | EMPTY _ -> ()
      | MAP {root,nobj,comp} -> applyi af (State.! root)

  def apply af sp =
    case sp of
      | SplayNil -> ()
      | SplayObj {value = (_,v),left,right} -> 
             (apply af left; af v; apply af right)

  def app af map = 
    case map of
      | EMPTY _ -> ()
      | MAP {root,nobj,comp} -> apply af (State.! root)

  def api af sp = 
    case sp of
      | SplayNil -> SplayNil
      | SplayObj {value = value as (key,_),left,right} ->
          let left = api af left in
          let value = (key, af value) in
          SplayObj{value = value, left = left, right = api af right}

  def mapi af map = 
    case map of
      | EMPTY comp -> EMPTY comp
      | MAP {nobj,root,comp} -> 
             MAP{root = Ref(api af (State.! root)),nobj = nobj,comp = comp}

  def ap af sp = 
    case sp of
      | SplayNil -> SplayNil
      | SplayObj {value = value as (key,v),left,right} ->
          let left = ap af left in
          let value = (key, af v) in
          SplayObj{value = value, left = left, right = ap af right}

  def map af map = 
    case map of
      | EMPTY comp -> EMPTY comp
      | MAP {nobj,root,comp} -> 
          MAP {root = Ref(ap af (State.! root)),nobj = nobj,comp = comp}

  def foldriAp abf (sp,b) = 
    case sp of
      | SplayNil -> b
      | SplayObj {value = (k,a),left,right} -> 
          foldriAp abf (left,abf(k,a,foldriAp abf (right,b)))

  def foldri abf b map = 
    case map of
      | EMPTY _ -> b
      | MAP {root,comp,nobj} -> foldriAp abf (State.! root,b)

  def foldriDouble f ob omap = 
      foldri
        (fn (key1,map,b)->
           foldri
             (fn(key2,a,b) -> f(key1,key2,a,b))
             b map) ob omap

  def foldrAp abf (sp,b) = 
    case sp of
      | SplayNil -> b
      | SplayObj{value = (k,a),left,right} -> 
          foldrAp abf (left,abf(a,foldrAp abf (right,b)))

  def foldr abf b map = 
    case map of
      | EMPTY _ -> b
      | MAP {root,comp,nobj} -> foldrAp abf (State.! root,b)

  def foldliAp abf (sp,b) = 
    case sp of
      | SplayNil -> b
      | SplayObj {value = (k,a),left,right} -> 
            foldliAp abf (right,abf(k,a,foldliAp abf (left,b)))

  def foldli abf b map = 
    case map of
      | EMPTY _ -> b
      | MAP {root,comp,nobj} -> foldliAp abf (State.! root,b)

  def foldlAp abf (sp,b) = 
    case sp of
      | SplayNil -> b
      | SplayObj {value = (k,a),left,right} -> 
          foldlAp abf (right,abf(a,foldlAp abf (left,b)))

  def foldl abf b map = 
    case map of
      | EMPTY _ -> b
      | MAP {root,comp,nobj} -> foldlAp abf (State.! root,b)

  def compose(map1,map2) = 
    foldri (fn (d,m,map3) ->
             (case find (map2,m) of
               | Some r -> insert(map3,d,r)
               | None -> map3))
        (empty (case map1 of
                  | EMPTY comp -> comp
                  | MAP m -> m.comp)) map1 
  (*  
   The following are generic implementations of the unionWith and intersectWith
   operations.  These should be specialized for the internal representations
   at some point.
   *)

  def compOf(map) = 
        case map
          of EMPTY comp -> comp
           | MAP{comp,root,nobj} -> comp

  def unionWith f (m1, m2) = 
        let
          def ins f (key, x, m) = 
              case find(m, key)
                of None -> insert(m, key, x)
                 | Some x_ -> insert(m, key, f(x, x_))
        in
            if (numItems m1 > numItems m2)
                then foldli (ins (fn (a, b) -> f(b, a))) m1 m2
            else foldli (ins f) m2 m1

  def unionWithi f (m1, m2) = 
        let
           def ins f (key, x, m) = 
               case find(m, key)
                 of None -> insert(m, key, x)
                  | Some x_ -> insert(m, key, f(key, x, x_))
        in
            if (numItems m1 > numItems m2)
              then foldli (ins (fn (k, a, b) -> f(k, b, a))) m1 m2
              else foldli (ins f) m2 m1

  def intersectWith f (m1, m2) = 
        let
        (* iterate over the elements of m1, checking for membership in m2 *)
           def intersect f (m1, m2) = 
               let
                  def ins (key, x, m) = 
                      case find(m2, key)
                        of None -> m
                         | Some x_ -> insert(m, key, f(x, x_))
                in
                  foldli ins (empty(compOf m1)) m1
                
         in
            if (numItems m1 > numItems m2)
              then intersect f (m1, m2)
            else intersect (fn (a, b) -> f(b, a)) (m2, m1)

  def intersectWithi f (m1, m2) = 
        let
        (* iterate over the elements of m1, checking for membership in m2 *)
           def intersect f (m1, m2) = 
               let
                  def ins (key, x, m) = 
                      case find(m2, key)
                        of None -> m
                         | Some x_ -> insert(m, key, f(key, x, x_))
               in
                    foldli ins (empty(compOf m1)) m1
          in
            if (numItems m1 > numItems m2)
              then intersect f (m1, m2)
              else intersect (fn (k, a, b) -> f(k, b, a)) (m2, m1)


  (* 
   this is a generic implementation of filter.  It should
   be specialized to the data-structure at some point.
   *)

  def filter predFn m = 
        let
          def f (key, item, m) = 
              if predFn item
                then insert(m, key, item)
              else m
        in
            foldli f (empty(compOf m)) m

    def filteri predFn m = 
        let
           def f (key, item, m) = 
              if predFn(key, item)
                  then insert(m, key, item)
              else m
         in
            foldli f (empty(compOf m)) m

  (* 
   This is a generic implementation of mapPartial.  It should
   be specialized to the data-structure at some point.
   *)


  def mapPartial f m = 
        let
          def g (key, item, m) = 
              case f item
                of None -> m
                 | (Some item_) -> insert(m, key, item_)
        in
            foldli g (empty (compOf m)) m

  def mapPartiali f m = 
        let
           def g (key, item, m) = 
               case f(key, item)
                 of None -> m
                  | (Some item_) -> insert(m, key, item_)
        in
            foldli g (empty (compOf m)) m

  def next splays = 
        case splays
          of (t as SplayObj s)::rest -> 
                (t,left(s.right, rest))
           | _ -> (SplayNil, [])

  def left (sp,rest) = 
        case sp
          of SplayNil -> rest
           | SplayObj{left = l,right,value} -> left(l, cons(sp,rest))

  def compare cmpRng (map1,map2) = 
        case (map1,map2)
          of (EMPTY _,EMPTY _) -> Equal
           | (EMPTY _,_) -> Less
           | (_,EMPTY _) -> Greater
           | (MAP{root = s1,comp = c1,nobj = n1},
              MAP{root = s2,comp = c2,nobj = n2}) -> 
        let 
            def cmp(t1,t2) : Comparison = 
                case (next t1, next t2)
                  of ((SplayNil, _), (SplayNil, _)) -> Equal
                   | ((SplayNil, _), _) -> Less
                   | (_, (SplayNil, _)) -> Greater
                   | ((SplayObj{value = (x1, y1),left = _,right = _}, r1),
                      (SplayObj{value = (x2, y2),left = _,right = _}, r2)) -> 
                (case c1(x1, x2)
                   of Equal -> 
                      (case cmpRng (y1, y2)
                         of Equal -> cmp (r1, r2)
                          | order -> order)
                    | order -> order)
          in
             cmp (left(State.! s1, []), left(State.! s2, []))

  %% Conversion to and from lists

  def toList = listItemsi

  def fromList comp l =
    List.foldr
      (fn ((a,b), m) -> insert (m, a, b))
      (empty comp) l

  def all p? m =
    foldri
      (fn (a, b, r) -> r & p? (a, b))
      true m

  def exists p? m =
    foldri
      (fn (a, b, r) -> r or p? (a, b))
      false m

  def subset? (m1, m2) =
    all (fn (a1, b1) ->
           (case find (m2, a1) of
             | None -> false
             | Some b2 -> b1 = b2))
        m1
}      
\end{spec}

