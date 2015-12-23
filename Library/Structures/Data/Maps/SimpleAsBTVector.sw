(* Copyright 2015 Kestrel Institute. See file LICENSE for license details *)

%%TODO Does this only work for maps whose domain is Nat?

SimpleAsBTVector = BTVMap qualifying
spec
  import Simple

  op MapBTV.BTV_empty_map : fa(key,a) Map (key,a)
  op MapBTV.BTV_numItems  : fa(a,key) Map (key,a) -> Nat

  op MapBTV.BTV_apply : fa(key,a) Map(key,a) * key -> Option a
  op MapBTV.BTV_eval  : fa(key,a) Map(key,a) * key -> a

  op MapBTV.BTV_update      : fa (key,a) Map (key,a) * key * a -> Map (key,a)
  op MapBTV.BTV_remove      : fa (a,key) Map (key,a) * key -> Map (key,a)
  op MapBTV.BTV_inDomain?   : fa (key,a) Map (key,a) * key -> Bool
  op MapBTV.BTV_mapi        : fa (key,a,b) (key * a -> b)        * Map (key,a) -> Map (key,b)
  op MapBTV.BTV_map         : fa (key,a,b) (a       -> b)        * Map (key,a) -> Map (key,b)
  op MapBTV.BTV_mapPartial  : fa (key,a,b) (a       -> Option b) * Map (key,a) -> Map (key,b)
  op MapBTV.BTV_mapiPartial : fa (key,a,b) (key * a -> Option b) * Map (key,a)  -> Map (key,b)


  op MapBTV.BTV_app   : fa (key,a) (a -> ()) * Map (key,a) -> ()
  op MapBTV.BTV_appi  : fa (key,a) (key * a -> ()) * Map (key,a) -> ()

  op MapBTV.BTV_foldi : fa (Dom,Cod,a) (Dom * Cod * a -> a) * a * Map (Dom,Cod) -> a

  op MapBTV.BTV_imageToList  : fa (key,a) Map (key,a) -> List a
  op MapBTV.BTV_mapToList    : fa (key,a) Map (key,a) -> List (key * a)
  op MapBTV.BTV_domainToList : fa (key,a) Map (key,a) -> List key

  def emptyMap = MapBTV.BTV_empty_map
  def numItems = MapBTV.BTV_numItems

  def apply = MapBTV.BTV_apply
  def eval  = MapBTV.BTV_eval

  def update(x,y,z) = MapBTV.BTV_update(x,y,z)
  def remove = MapBTV.BTV_remove
  def inDomain? (m, x) =
    case apply (m, x) of
      | None -> false
      | Some _ -> true

  def mapi        f m = MapBTV.BTV_mapi        (f,m)
  def map         f m = MapBTV.BTV_map         (f,m)
  def mapiPartial f m = MapBTV.BTV_mapiPartial (f,m)
  def mapPartial  f m = MapBTV.BTV_mapPartial  (f,m)

  def app  f m = MapBTV.BTV_app  (f,m)
  def appi f m = MapBTV.BTV_appi (f,m)

  def foldi f e m = MapBTV.BTV_foldi(f,e,m)

  def imageToList  = MapBTV.BTV_imageToList
  def mapToList    = MapBTV.BTV_mapToList
  def domainToList = MapBTV.BTV_domainToList

endspec

M = morphism Simple -> SimpleAsBTVector {}
