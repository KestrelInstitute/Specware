BTHMap qualifying
spec
  import Simple

  op MapBTHashtable.BTH_empty_map : fa(key,a) Map (key,a)
  op MapBTHashtable.BTH_numItems : fa(a,key) Map (key,a) -> Nat

  op MapBTHashtable.BTH_apply : fa(key,a) Map(key,a) * key -> Option a
  op MapBTHashtable.BTH_eval  : fa(key,a) Map(key,a) * key -> a

  op MapBTHashtable.BTH_update : fa (key,a) Map (key,a) * key * a -> Map (key,a)
  op MapBTHashtable.BTH_remove : fa (a,key) Map (key,a) * key -> Map (key,a)
  op MapBTHashtable.BTH_inDomain? : fa(key,a) Map (key,a) * key -> Boolean
  op MapBTHashtable.BTH_mapi : fa(key,a,b) (key * a -> b) * Map (key,a) -> Map (key,b)
  op MapBTHashtable.BTH_map  : fa(key,a,b) (a -> b) * Map (key,a) -> Map (key,b)

  op MapBTHashtable.BTH_mapPartial  : fa(key,a,b) (a -> Option b) * Map (key,a)
                                             -> Map (key,b)
  op MapBTHashtable.BTH_mapiPartial : fa(key,a,b) (key * a -> Option b) * Map (key,a)
                                             -> Map (key,b)


  op MapBTHashtable.BTH_app   : fa(key,a) (a -> ()) * Map (key,a) -> ()
  op MapBTHashtable.BTH_appi  : fa(key,a) (key * a -> ()) * Map (key,a) -> ()

  op MapBTHashtable.BTH_foldi : fa(Dom,Cod,a) (Dom * Cod * a -> a) * a * Map (Dom,Cod) -> a

  op MapBTHashtable.BTH_imageToList : fa(key,a) Map (key,a) -> List a
  op MapBTHashtable.BTH_mapToList : fa(key,a) Map (key,a) -> List (key * a)
  op MapBTHashtable.BTH_domainToList : fa(key,a) Map (key,a) -> List key

  def emptyMap = MapBTHashtable.BTH_empty_map
  def numItems = MapBTHashtable.BTH_numItems

  def apply = MapBTHashtable.BTH_apply
  def eval  = MapBTHashtable.BTH_eval
  def update(x,y,z) = MapBTHashtable.BTH_update(x,y,z)
  def remove = MapBTHashtable.BTH_remove
  def inDomain? (m, x) =
    case apply (m, x) of
      | None -> false
      | Some _ -> true

  def mapi f m = MapBTHashtable.BTH_mapi(f,m)
  def map  f m = MapBTHashtable.BTH_map (f,m)
  def mapiPartial f m = MapBTHashtable.BTH_mapiPartial(f,m)
  def mapPartial  f m = MapBTHashtable.BTH_mapPartial (f,m)

  def app  f m = MapBTHashtable.BTH_app (f,m)
  def appi f m = MapBTHashtable.BTH_appi(f,m)

  def foldi f e m = MapBTHashtable.BTH_foldi(f,e,m)

  def imageToList = MapBTHashtable.BTH_imageToList
  def mapToList   = MapBTHashtable.BTH_mapToList
  def domainToList = MapBTHashtable.BTH_domainToList

endspec
