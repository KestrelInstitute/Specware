(* Copyright 2015 Kestrel Institute. See file LICENSE.text for license details *)

SimpleAsSTHarray = STHMap qualifying
spec
  import Simple

%% TODO Where does the semantics of these functions come from?  Just
%% the handwritten Lisp code (which seems to be in
%% /Library/Structures/Data/Maps/Handwritten/Lisp/MapAsSTHarray.lisp)?

%% TODO: Pull these MapSTHashtable functions out into a separate spec?
  op MapSTHashtable.STH_empty_map    : [key,a] Map (key,a)
  op MapSTHashtable.STH_numItems     : [a,key] Map (key,a) -> Nat
  op MapSTHashtable.STH_apply        : [key,a] Map (key,a) * key     -> Option a
  op MapSTHashtable.STH_eval         : [key,a] Map (key,a) * key     -> a
  op MapSTHashtable.STH_update       : [key,a] Map (key,a) * key * a -> Map (key,a)
  op MapSTHashtable.STH_remove       : [a,key] Map (key,a) * key     -> Map (key,a)
  op MapSTHashtable.STH_inDomain?    : [key,a] Map (key,a) * key     -> Bool

  op MapSTHashtable.STH_mapi         : [key,a,b]   (key * a -> b)           * Map (key,a) -> Map (key,b)
  op MapSTHashtable.STH_map          : [key,a,b]   (a       -> b)           * Map (key,a) -> Map (key,b)
  op MapSTHashtable.STH_mapPartial   : [key,a,b]   (a -> Option b)          * Map (key,a) -> Map (key,b)
  op MapSTHashtable.STH_mapiPartial  : [key,a,b]   (key * a -> Option b)    * Map (key,a) -> Map (key,b)
  op MapSTHashtable.STH_app          : [key,a]     (a       -> ())          * Map (key,a) -> ()
  op MapSTHashtable.STH_appi         : [key,a]     (key * a -> ())          * Map (key,a) -> ()
  op MapSTHashtable.STH_foldi        : [Dom,Cod,a] (Dom * Cod * a -> a) * a * Map (Dom,Cod) -> a
  op MapSTHashtable.STH_imageToList  : [key,a]     Map (key,a) -> List a
  op MapSTHashtable.STH_mapToList    : [key,a]     Map (key,a) -> List (key * a)
  op MapSTHashtable.STH_domainToList : [key,a]     Map (key,a) -> List key

  def emptyMap     = MapSTHashtable.STH_empty_map
  def numItems     = MapSTHashtable.STH_numItems
  def apply        = MapSTHashtable.STH_apply
  def eval         = MapSTHashtable.STH_eval
  def remove       = MapSTHashtable.STH_remove
  def imageToList  = MapSTHashtable.STH_imageToList
  def mapToList    = MapSTHashtable.STH_mapToList
  def domainToList = MapSTHashtable.STH_domainToList

  def update (x, y, z) = MapSTHashtable.STH_update (x, y, z)

  def inDomain? (m, x) =
    case apply (m, x) of
      | None -> false
      | Some _ -> true

  def mapi        f m = MapSTHashtable.STH_mapi        (f,m)
  def map         f m = MapSTHashtable.STH_map         (f,m)
  def mapiPartial f m = MapSTHashtable.STH_mapiPartial (f,m)
  def mapPartial  f m = MapSTHashtable.STH_mapPartial  (f,m)
  def app         f m = MapSTHashtable.STH_app         (f,m)
  def appi        f m = MapSTHashtable.STH_appi        (f,m)

  def foldi f e m = MapSTHashtable.STH_foldi(f,e,m)

  op [Dom,Cod,a] foldMap (f: a -> Dom -> Cod -> a) (e: a) (m: Map(Dom,Cod)): a =
    MapSTHashtable.STH_foldi(fn(key, val, e) -> f e key val, e, m)
endspec

M = morphism Simple -> SimpleAsSTHarray {}
