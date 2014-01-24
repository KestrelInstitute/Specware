(* Map with Nat domain implemented as vector
   Note that it assumes the usage is single-threaded! *)

%% TODO Where is the expression of the requirement that the domain of the map is Nat (is an initial segment of Nat allowed)?
%% TODO Where is the semantics given on the MapVec operations?  Just in the hand-written Lisp code?

%% Note: The lisp code for these functions is in Handwritten/Lisp/MapAsVector.lisp.

MapVec qualifying spec

  import Simple#Map  %% TODO This brings in Map as an unqualified type name.

  op MapVec.V_empty_map : [key,a] Map (key,a)
  op MapVec.V_numItems  : [a,key] Map (key,a) -> Nat

  op MapVec.V_apply : [key,a] Map(key,a) * key -> Option a
 %TODO require that the key is present in the map?
  op MapVec.V_eval  : [key,a] Map(key,a) * key -> a

  op MapVec.V_update      : [key,a] Map (key,a) * key * a -> Map (key,a)
  op MapVec.V_remove      : [a,key] Map (key,a) * key -> Map (key,a)
  %% TODO delete this?  There seems to be no code for it.
  %% op MapVec.V_inDomain?   : [key,a] Map (key,a) * key -> Bool
  op MapVec.V_mapi        : [key,a,b] (key * a -> b)        * Map (key,a) -> Map (key,b)
  op MapVec.V_map         : [key,a,b] (a       -> b)        * Map (key,a) -> Map (key,b)
  op MapVec.V_mapPartial  : [key,a,b] (a       -> Option b) * Map (key,a) -> Map (key,b)
  op MapVec.V_mapiPartial : [key,a,b] (key * a -> Option b) * Map (key,a)  -> Map (key,b)

  op MapVec.V_app   : [key,a] (a -> ()) * Map (key,a) -> ()
  op MapVec.V_appi  : [key,a] (key * a -> ()) * Map (key,a) -> ()

  %TODO change the type vars of this for consistency?
  op MapVec.V_foldi : [Dom,Cod,a] (Dom * Cod * a -> a) * a * Map (Dom,Cod) -> a

  op MapVec.V_imageToList  : [key,a] Map (key,a) -> List a
  op MapVec.V_mapToList    : [key,a] Map (key,a) -> List (key * a)
  op MapVec.V_domainToList : [key,a] Map (key,a) -> List key

end-spec
