Map qualifying
spec
  import Simple

  op MapSTHashtable.emptyMap : fa(key,a) Map (key,a)
  op MapSTHashtable.numItems : fa(a,key) Map (key,a) -> Nat

  op MapSTHashtable.apply : fa(key,a) Map(key,a) * key -> Option a
  op MapSTHashtable.eval  : fa(key,a) Map(key,a) * key -> a

  op MapSTHashtable.update : fa (key,a) Map (key,a) * key * a -> Map (key,a)
  op MapSTHashtable.remove : fa (a,key) Map (key,a) * key -> Map (key,a)
  op MapSTHashtable.inDomain? : fa(key,a) Map (key,a) * key -> Boolean
  op MapSTHashtable.mapi : fa(key,a,b) (key * a -> b) * Map (key,a) -> Map (key,b)
  op MapSTHashtable.map  : fa(key,a,b) (a -> b) * Map (key,a) -> Map (key,b)

  op MapSTHashtable.mapPartial  : fa(key,a,b) (a -> Option b) * Map (key,a)
                                             -> Map (key,b)
  op MapSTHashtable.mapiPartial : fa(key,a,b) (key * a -> Option b) * Map (key,a)
                                             -> Map (key,b)


  op MapSTHashtable.app   : fa(key,a) (a -> ()) * Map (key,a) -> ()
  op MapSTHashtable.appi  : fa(key,a) (key * a -> ()) * Map (key,a) -> ()

  op MapSTHashtable.foldi : fa(Dom,Cod,a) (Dom * Cod * a -> a) * a * Map (Dom,Cod) -> a

  op MapSTHashtable.imageToList : fa(key,a) Map (key,a) -> List a
  op MapSTHashtable.mapToList : fa(key,a) Map (key,a) -> List (key * a)
  op MapSTHashtable.domainToList : fa(key,a) Map (key,a) -> List key

  def emptyMap = MapSTHashtable.emptyMap
  def numItems = MapSTHashtable.numItems

  def apply = MapSTHashtable.apply
  def eval (m, x) =
    case MapSTHashtable.apply(m,x) of
      | Some v -> v
      | None -> fail "inside eval"   % shame shame
  def update = MapSTHashtable.update
  def remove = MapSTHashtable.remove
  def inDomain? (m, x) =
    case apply (m, x) of
      | None -> false
      | Some _ -> true

  def mapi f m = MapSTHashtable.mapi(f,m)
  def map  f m = MapSTHashtable.map (f,m)
  def mapiPartial f m = MapSTHashtable.mapiPartial(f,m)
  def mapPartial  f m = MapSTHashtable.mapPartial (f,m)

  def app  f m = MapSTHashtable.app (f,m)
  def appi f m = MapSTHashtable.appi(f,m)

  def foldi f e m = MapSTHashtable.foldi(f,e,m)

  def imageToList = MapSTHashtable.imageToList
  def mapToList   = MapSTHashtable.mapToList
  def domainToList = MapSTHashtable.domainToList

endspec
