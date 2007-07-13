STHMap qualifying
spec
  import Simple

  op MapSTHashtable.STH_empty_map : fa(key,a) Map (key,a)
  op MapSTHashtable.STH_numItems : fa(a,key) Map (key,a) -> Nat

  op MapSTHashtable.STH_apply : fa(key,a) Map(key,a) * key -> Option a
  op MapSTHashtable.STH_eval  : fa(key,a) Map(key,a) * key -> a

  op MapSTHashtable.STH_update : fa (key,a) Map (key,a) * key * a -> Map (key,a)
  op MapSTHashtable.STH_remove : fa (a,key) Map (key,a) * key -> Map (key,a)
  op MapSTHashtable.STH_inDomain? : fa(key,a) Map (key,a) * key -> Boolean
  op MapSTHashtable.STH_mapi : fa(key,a,b) (key * a -> b) * Map (key,a) -> Map (key,b)
  op MapSTHashtable.STH_map  : fa(key,a,b) (a -> b) * Map (key,a) -> Map (key,b)

  op MapSTHashtable.STH_mapPartial  : fa(key,a,b) (a -> Option b) * Map (key,a)
                                             -> Map (key,b)
  op MapSTHashtable.STH_mapiPartial : fa(key,a,b) (key * a -> Option b) * Map (key,a)
                                             -> Map (key,b)


  op MapSTHashtable.STH_app   : fa(key,a) (a -> ()) * Map (key,a) -> ()
  op MapSTHashtable.STH_appi  : fa(key,a) (key * a -> ()) * Map (key,a) -> ()

  op MapSTHashtable.STH_foldi : fa(Dom,Cod,a) (Dom * Cod * a -> a) * a * Map (Dom,Cod) -> a

  op MapSTHashtable.STH_imageToList : fa(key,a) Map (key,a) -> List a
  op MapSTHashtable.STH_mapToList : fa(key,a) Map (key,a) -> List (key * a)
  op MapSTHashtable.STH_domainToList : fa(key,a) Map (key,a) -> List key

  def emptyMap = MapSTHashtable.STH_empty_map
  def numItems = MapSTHashtable.STH_numItems

  def apply = MapSTHashtable.STH_apply
  def eval  = MapSTHashtable.STH_eval
  def update(x,y,z) = MapSTHashtable.STH_update(x,y,z)
  def remove = MapSTHashtable.STH_remove
  def inDomain? (m, x) =
    case apply (m, x) of
      | None -> false
      | Some _ -> true

  def mapi f m = MapSTHashtable.STH_mapi(f,m)
  def map  f m = MapSTHashtable.STH_map (f,m)
  def mapiPartial f m = MapSTHashtable.STH_mapiPartial(f,m)
  def mapPartial  f m = MapSTHashtable.STH_mapPartial (f,m)

  def app  f m = MapSTHashtable.STH_app (f,m)
  def appi f m = MapSTHashtable.STH_appi(f,m)

  def foldi f e m = MapSTHashtable.STH_foldi(f,e,m)

  def imageToList = MapSTHashtable.STH_imageToList
  def mapToList   = MapSTHashtable.STH_mapToList
  def domainToList = MapSTHashtable.STH_domainToList

endspec
