StringMap qualifying spec {
  import SplayMap   
  sort Map a = SplayMap.Map (String,a)

  %% Alias so importers can avoid qualification

  sort StringMap a = SplayMap.Map (String, a)

  op empty          : fa(a)   Map a
  op insert         : fa(a)   Map a * String * a -> Map a
  op insert2        : fa(a)   Map(Map a) * String * String * a -> Map(Map a)
  op remove         : fa(a)   Map a * String  -> Map a
  op find           : fa(a)   Map a * String -> Option a 
  op find2          : fa(a)   Map(Map a) * String * String -> Option a 
  op map            : fa(a,b) (a -> b) -> Map a -> Map b
  op mapDouble      : fa(a,b) (a -> b) -> Map(Map a) -> Map(Map b)
  op mapi           : fa(a,b) (String * a -> b) -> Map a -> Map b
  op mapiDouble     : fa(a,b) (String * String * a -> b) -> Map(Map a) -> Map(Map b)
  op app            : fa(a)   (a -> ()) -> Map a -> ()
  op appDouble      : fa(a)   (a -> ()) -> Map (Map a) -> ()
  op appi           : fa(a)   (String * a -> ()) -> Map a -> ()
  op appiDouble     : fa(a)   (String * String * a -> ()) -> Map (Map a) -> ()
  op foldri         : fa(a,b) (String * a * b -> b) -> b ->  Map a -> b
  op foldli         : fa(a,b) (String * a * b -> b) -> b ->  Map a -> b
  op foldriDouble   : fa(a,b) (String * String * a * b -> b) -> b -> Map (Map a) -> b
  op compose        : fa(a)   Map(String) * Map a -> Map a

  op unionWith      : fa(a)   (a * a -> a) -> Map a * Map a -> Map a  
  op union2With     : fa(a)   (a * a -> a) -> Map(Map a) * Map(Map a) -> Map(Map a)  
  op intersectWith  : fa(a)   (a * a -> a) -> Map a * Map a -> Map a  
  op listDomain     : fa(a)   Map a -> List String
  op filter         : fa(a)   (a -> Boolean) -> Map a -> Map a
  op listItems      : fa(a)   Map a -> List (a)
  op listItemsi     : fa(a)   Map a -> List (String * a)
  op inDomain       : fa(a)   Map a * String -> Boolean
 
  op toList         : fa(a)   Map a -> List (String * a)
  op fromList       : fa(a)   List (String * a) -> Map a
  op numItems       : fa(a)   Map a -> Nat
 
  op mapPartial     : fa(a,b) (a          -> Option b) -> Map a -> Map b
  op mapPartiali    : fa(a,b) (String * a -> Option b) -> Map a -> Map b
 
  op subset?        : fa(a)   Map a * Map a -> Boolean

  %% ========================================================================

  def empty  = SplayMap.empty String.compare
  def insert = SplayMap.insert
 
  def insert2 (m, x, y, v) =
   insert (m, x, insert(case find (m, x) of
                         | Some sm -> sm
                         | _ -> empty,
                        y, v))

  def remove = SplayMap.remove
  def find   = SplayMap.find
 
  def find2 (m, x, y) =
   case find (m, x) of
    | None   -> None
    | Some m2 -> find (m2, y)
     
  def map             = SplayMap.map
  def mapDouble f m   = map(fn sm -> map f sm) m
  def mapi            = SplayMap.mapi
  def mapiDouble f m  = mapi(fn (x,sm) -> mapi (fn(y,z) -> f(x,y,z)) sm) m
  def mapPartial      = SplayMap.mapPartial
  def mapPartiali     = SplayMap.mapPartiali
  def app             = SplayMap.app
  def appDouble f m   = app(fn sm -> app f sm) m
  def appi            = SplayMap.appi
  def appiDouble f m  = appi(fn (x,sm) -> appi (fn(y,z) -> f(x,y,z)) sm) m
 
  def foldri          = SplayMap.foldri
  def foldli          = SplayMap.foldli
  def foldriDouble    = SplayMap.foldriDouble
  def compose         = SplayMap.compose
     
  def unionWith   = SplayMap.unionWith
  %% Unions two-level maps wih preference function f
  def union2With f (m1, m2)  =
   foldri (fn (x, sm2, resm) ->
            case find (resm, x) of
             | None     -> insert (resm, x, sm2)
             | Some sm1 -> insert (resm, x, unionWith f (sm1, sm2)))
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
