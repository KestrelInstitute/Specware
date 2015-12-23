(* Copyright 2015 Kestrel Institute. See file LICENSE for license details *)

StringMap qualifying spec
  import SplayMap   

  type Map a = SplayMap.Map (String,a)

  %% Alias so importers can avoid qualification

  type StringMap a = SplayMap.Map (String, a)

  op empty : [a] Map a

  op insert : [a] Map a * String * a -> Map a
  op insert2 :
    [a] Map(Map a)
        * String
        * String
        * a -> Map(Map a)

  op remove : [a] Map a * String  -> Map a
  op find : [a] Map a * String -> Option a 
  op find2 : [a] Map(Map a) * String * String -> Option a 

  op map : [a,b] (a -> b) -> Map a -> Map b
  op mapDouble :
    [a,b] (a -> b)
         -> Map(Map a)
         -> Map(Map b)
  op mapi : [a,b] (String * a -> b) -> Map a -> Map b
  op mapiDouble :
    [a,b] (String * String * a -> b)
          -> Map(Map a)
          -> Map(Map b)
  op mapiPartialDouble :
    [a,b] (String * String * a -> Option b)
          -> Map(Map a)
          -> Map(Map b)

  op app : [a] (a -> ()) -> Map a -> ()
  op appDouble : [a] (a -> ()) -> Map (Map a) -> ()
  op appi : [a] (String * a -> ()) -> Map a -> ()
  op appiDouble :
    [a] (String * String * a -> ())
        -> Map (Map a)
        -> ()

  op foldri : [a,b] (String * a * b -> b) -> b ->  Map a -> b
  op foldli : [a,b] (String * a * b -> b) -> b ->  Map a -> b
  op foldriDouble :
    [a,b] (String * String * a * b -> b)
          -> b
          -> Map (Map a) -> b

  op compose : [a] Map String * Map a -> Map a

  op unionWith :
    [a] (a * a -> a)
        -> Map a
         * Map a
        -> Map a  
  op union2With :
     [a] (a * a -> a)
         -> Map (Map a) 
          * Map (Map a)
         -> Map(Map a)  

  op intersectWith :
    [a] (a * a -> a)
        -> Map a
         * Map a
        -> Map a  

  op listDomain : [a] Map a -> List String
  op filter : [a] (a -> Bool) -> Map a -> Map a
  op listItems : [a] Map a -> List a
  op listItemsi : [a] Map a -> List (String * a)
  op inDomain : [a] Map a * String -> Bool
 
  op toList : [a] Map a -> List (String * a)
  op fromList : [a] List (String * a) -> Map a
  op numItems : [a] Map a -> Nat
 
  op mapPartial : [a,b] (a -> Option b) -> Map a -> Map b
  op mapPartiali :
    [a,b] (String * a -> Option b)
          -> Map a
          -> Map b
 
  op subset? : [a] Map a * Map a -> Bool

  def empty  = SplayMap.empty String.compare
  def insert = SplayMap.insert
 
  def insert2 (m, x, y, v) =
   insert (m, x, insert(case find (m, x) of
                         | Some sm -> sm
                         | _ -> empty,
                        y, v))

  def remove = SplayMap.remove
  def find = SplayMap.find
 
  def find2 (m, x, y) =
    case find (m, x) of
      | None -> None
      | Some m2 -> find (m2, y)
     
  def map = SplayMap.map
  def mapDouble f m = map (fn sm -> map f sm) m
  def mapi  = SplayMap.mapi
  def mapiDouble f m =
    mapi (fn (x,sm) -> mapi (fn(y,z) -> f(x,y,z)) sm) m
  def mapiPartialDouble f m =
    mapi (fn (x,sm) -> mapPartiali (fn(y,z) -> f(x,y,z)) sm) m
  def mapPartial = SplayMap.mapPartial
  def mapPartiali = SplayMap.mapPartiali
  def app = SplayMap.app
  def appDouble f m = app (fn sm -> app f sm) m
  def appi = SplayMap.appi
  def appiDouble f m =
    appi (fn (x,sm) -> appi (fn(y,z) -> f(x,y,z)) sm) m
 
  def foldri = SplayMap.foldri
  def foldli = SplayMap.foldli
  def foldriDouble = SplayMap.foldriDouble
  def compose = SplayMap.compose
     
  def unionWith = SplayMap.unionWith
  %% Unions two-level maps wih preference function f
  def union2With f (m1, m2)  =
    foldri (
      fn (x, sm2, resm) ->
        (case find (resm, x) of
          | None -> insert (resm, x, sm2)
          | Some sm1 -> insert (resm, x, unionWith f (sm1, sm2))))
       m1 m2
   
  def intersectWith = SplayMap.intersectWith
  def listDomain    = SplayMap.listDomain
  def filter        = SplayMap.filter
  def listItems     = SplayMap.listItems
  def listItemsi    = SplayMap.listItemsi
  def inDomain      = SplayMap.inDomain
 
  def toList        = SplayMap.toList
  def fromList      = SplayMap.fromList String.compare
  def numItems      = SplayMap.numItems
 
  def subset?       = SplayMap.subset?
end-spec
