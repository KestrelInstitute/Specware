(* Map with Nat domain implemented as vector
   Note that it assumes the usage is single-threaded! *)

SimpleAsVector = VMap qualifying
spec
  import Simple

  op MapVec.V_empty_map : fa(key,a) Map (key,a)
  op MapVec.V_numItems  : fa(a,key) Map (key,a) -> Nat

  op MapVec.V_apply : fa(key,a) Map(key,a) * key -> Option a
  op MapVec.V_eval  : fa(key,a) Map(key,a) * key -> a

  op MapVec.V_update      : fa (key,a) Map (key,a) * key * a -> Map (key,a)
  op MapVec.V_remove      : fa (a,key) Map (key,a) * key -> Map (key,a)
  op MapVec.V_inDomain?   : fa (key,a) Map (key,a) * key -> Bool
  op MapVec.V_mapi        : fa (key,a,b) (key * a -> b)        * Map (key,a) -> Map (key,b)
  op MapVec.V_map         : fa (key,a,b) (a       -> b)        * Map (key,a) -> Map (key,b)
  op MapVec.V_mapPartial  : fa (key,a,b) (a       -> Option b) * Map (key,a) -> Map (key,b)
  op MapVec.V_mapiPartial : fa (key,a,b) (key * a -> Option b) * Map (key,a)  -> Map (key,b)


  op MapVec.V_app   : fa (key,a) (a -> ()) * Map (key,a) -> ()
  op MapVec.V_appi  : fa (key,a) (key * a -> ()) * Map (key,a) -> ()

  op MapVec.V_foldi : fa (Dom,Cod,a) (Dom * Cod * a -> a) * a * Map (Dom,Cod) -> a

  op MapVec.V_imageToList  : fa (key,a) Map (key,a) -> List a
  op MapVec.V_mapToList    : fa (key,a) Map (key,a) -> List (key * a)
  op MapVec.V_domainToList : fa (key,a) Map (key,a) -> List key

  def emptyMap = MapVec.V_empty_map
  def numItems = MapVec.V_numItems

  def apply = MapVec.V_apply
  def eval  = MapVec.V_eval

  def update(x,y,z) = MapVec.V_update(x,y,z)
  def remove = MapVec.V_remove
  def inDomain? (m, x) =
    case apply (m, x) of
      | None -> false
      | Some _ -> true

  def mapi        f m = MapVec.V_mapi        (f,m)
  def map         f m = MapVec.V_map         (f,m)
  def mapiPartial f m = MapVec.V_mapiPartial (f,m)
  def mapPartial  f m = MapVec.V_mapPartial  (f,m)

  def app  f m = MapVec.V_app  (f,m)
  def appi f m = MapVec.V_appi (f,m)

  def foldi f e m = MapVec.V_foldi(f,e,m)

  def imageToList  = MapVec.V_imageToList
  def mapToList    = MapVec.V_mapToList
  def domainToList = MapVec.V_domainToList

end-spec

M = morphism Simple -> SimpleAsVector {}
