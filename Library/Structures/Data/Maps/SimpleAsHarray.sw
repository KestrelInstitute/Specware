Map qualifying
spec
  import Simple

  op MapHashtable.emptyMap : fa(key,a) Map (key,a)
  op MapHashtable.numItems : fa(a,key) Map (key,a) -> Nat

  op MapHashtable.apply : fa(key,a) Map(key,a) * key -> Option a
  op MapHashtable.eval  : fa(key,a) Map(key,a) * key -> a

  op MapHashtable.update : fa (key,a) Map (key,a) * key * a -> Map (key,a)
  op MapHashtable.remove : fa (a,key) Map (key,a) * key -> Map (key,a)
  op MapHashtable.inDomain? : fa(key,a) Map (key,a) * key -> Boolean
  op MapHashtable.mapi : fa(key,a,b) (key * a -> b) * Map (key,a) -> Map (key,b)
  op MapHashtable.map  : fa(key,a,b) (a -> b) * Map (key,a) -> Map (key,b)

  op MapHashtable.app   : fa(key,a) (a -> ()) * Map (key,a) -> ()
  op MapHashtable.appi  : fa(key,a) (key * a -> ()) * Map (key,a) -> ()

  op MapHashtable.foldi : fa(Dom,Cod,a) (Dom * Cod * a -> a) * a * Map (Dom,Cod) -> a

  op MapHashtable.imageToList : fa(key,a) Map (key,a) -> List a
  op MapHashtable.mapToList : fa(key,a) Map (key,a) -> List (key * a)
  op MapHashtable.domainToList : fa(key,a) Map (key,a) -> List key

  def emptyMap = MapHashtable.emptyMap
  def numItems = MapHashtable.numItems

  def apply = MapHashtable.apply
  def eval (m, x) =
    case MapHashtable.apply(m,x) of
      | Some v -> v
      | None -> fail "inside eval"   % shame shame
  def update = MapHashtable.update
  def remove = MapHashtable.remove
  def inDomain? (m, x) =
    case apply (m, x) of
      | None -> false
      | Some _ -> true

  def mapi f m = MapHashtable.mapi(f,m)
  def map  f m = MapHashtable.map (f,m)

  def app  f m = MapHashtable.app (f,m)
  def appi f m = MapHashtable.appi(f,m)

  def foldi f e m = MapHashtable.foldi(f,e,m)

  def imageToList = MapHashtable.imageToList
  def mapToList   = MapHashtable.mapToList
  def domainToList = MapHashtable.domainToList

endspec