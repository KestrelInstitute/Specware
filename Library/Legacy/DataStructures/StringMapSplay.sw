StringMap qualifying spec {
  import SplayMap   

  sort StringMap.Map a = SplayMap.Map (String,a)

  %% Alias so importers can avoid qualification

  sort StringMap a = SplayMap.Map (String, a)

  op empty : fa(a) StringMap.Map a

  op StringMap.insert : fa(a) StringMap.Map a * String * a -> StringMap.Map a
  op insert2 :
    fa(a) StringMap.Map(StringMap.Map a)
        * String
        * String
        * a -> StringMap.Map(StringMap.Map a)

  op remove : fa(a) StringMap.Map a * String  -> StringMap.Map a
  op StringMap.find : fa(a) StringMap.Map a * String -> Option a 
  op find2 : fa(a) StringMap.Map(StringMap.Map a) * String * String -> Option a 

  op StringMap.map : fa(a,b) (a -> b) -> StringMap.Map a -> StringMap.Map b
  op mapDouble :
    fa(a,b) (a -> b)
         -> StringMap.Map(StringMap.Map a)
         -> StringMap.Map(StringMap.Map b)
  op StringMap.mapi : fa(a,b) (String * a -> b) -> StringMap.Map a -> StringMap.Map b
  op mapiDouble :
    fa(a,b) (String * String * a -> b)
          -> StringMap.Map(StringMap.Map a)
          -> StringMap.Map(StringMap.Map b)

  op StringMap.app : fa(a) (a -> ()) -> StringMap.Map a -> ()
  op appDouble : fa(a) (a -> ()) -> StringMap.Map (StringMap.Map a) -> ()
  op StringMap.appi : fa(a) (String * a -> ()) -> StringMap.Map a -> ()
  op appiDouble :
    fa(a) (String * String * a -> ())
        -> StringMap.Map (StringMap.Map a)
        -> ()

  op StringMap.foldri : fa(a,b) (String * a * b -> b) -> b ->  StringMap.Map a -> b
  op foldli : fa(a,b) (String * a * b -> b) -> b ->  StringMap.Map a -> b
  op foldriDouble :
    fa(a,b) (String * String * a * b -> b)
          -> b
          -> StringMap.Map (StringMap.Map a) -> b

  op compose : fa(a) StringMap.Map String * StringMap.Map a -> StringMap.Map a

  op StringMap.unionWith :
    fa(a) (a * a -> a)
        -> StringMap.Map a
         * StringMap.Map a
        -> StringMap.Map a  
  op union2With :
     fa(a) (a * a -> a)
         -> StringMap.Map (StringMap.Map a) 
          * StringMap.Map (StringMap.Map a)
         -> StringMap.Map(StringMap.Map a)  

  op intersectWith :
    fa(a) (a * a -> a)
        -> StringMap.Map a
         * StringMap.Map a
        -> StringMap.Map a  

  op listDomain : fa(a) StringMap.Map a -> List String
  op filter : fa(a) (a -> Boolean) -> StringMap.Map a -> StringMap.Map a
  op listItems : fa(a) StringMap.Map a -> List a
  op listItemsi : fa(a) StringMap.Map a -> List (String * a)
  op inDomain : fa(a) StringMap.Map a * String -> Boolean
 
  op toList : fa(a) StringMap.Map a -> List (String * a)
  op fromList : fa(a) List (String * a) -> StringMap.Map a
  op numItems : fa(a) StringMap.Map a -> Nat
 
  op mapPartial : fa(a,b) (a -> Option b) -> StringMap.Map a -> StringMap.Map b
  op mapPartiali :
    fa(a,b) (String * a -> Option b)
          -> StringMap.Map a
          -> StringMap.Map b
 
  op subset? : fa(a) StringMap.Map a * StringMap.Map a -> Boolean

  def empty  = SplayMap.empty String.compare
  def StringMap.insert = SplayMap.insert
 
  def insert2 (m, x, y, v) =
   StringMap.insert (m, x, StringMap.insert(case StringMap.find (m, x) of
                         | Some sm -> sm
                         | _ -> empty,
                        y, v))

  def remove = SplayMap.remove
  def StringMap.find = SplayMap.find
 
  def find2 (m, x, y) =
    case StringMap.find (m, x) of
      | None -> None
      | Some m2 -> StringMap.find (m2, y)
     
  def StringMap.map = SplayMap.map
  def mapDouble f m = StringMap.map (fn sm -> StringMap.map f sm) m
  def StringMap.mapi  = SplayMap.mapi
  def mapiDouble f m =
    StringMap.mapi (fn (x,sm) -> StringMap.mapi (fn(y,z) -> f(x,y,z)) sm) m
  def mapPartial = SplayMap.mapPartial
  def mapPartiali = SplayMap.mapPartiali
  def StringMap.app = SplayMap.app
  def appDouble f m = StringMap.app (fn sm -> StringMap.app f sm) m
  def StringMap.appi = SplayMap.appi
  def appiDouble f m =
    StringMap.appi (fn (x,sm) -> StringMap.appi (fn(y,z) -> f(x,y,z)) sm) m
 
  def StringMap.foldri = SplayMap.foldri
  def foldli = SplayMap.foldli
  def foldriDouble = SplayMap.foldriDouble
  def compose = SplayMap.compose
     
  def StringMap.unionWith = SplayMap.unionWith
  %% Unions two-level maps wih preference function f
  def union2With f (m1, m2)  =
    StringMap.foldri (
      fn (x, sm2, resm) ->
        (case StringMap.find (resm, x) of
          | None -> StringMap.insert (resm, x, sm2)
          | Some sm1 -> StringMap.insert (resm, x, StringMap.unionWith f (sm1, sm2))))
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
}
