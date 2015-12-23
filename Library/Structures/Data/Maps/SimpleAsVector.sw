(* Copyright 2015 Kestrel Institute. See file LICENSE for license details *)

(* Map with Nat domain implemented as vector
   Note that it assumes the usage is single-threaded! *)

%% TODO Where is the expression of the requirement that the domain of the map is Nat?
%% TODO Where is the semantics given on the Simple map operations?
%% TODO This leaves the type Map undefined, unlike SimpleAsAlist.

SimpleAsVector = VMap qualifying
spec
  import Simple
  import translate MapVec by {MapVec.Map +-> VMap.Map}

  def emptyMap      = V_empty_map
  def numItems      = V_numItems
  def apply         = V_apply
  def eval          = V_eval
  def update(x,y,z) = V_update(x,y,z)
  def remove        = V_remove
  % TODO why not call V_inDomain? ?  Maybe because there is no code for it?
  def inDomain? (m, x) =
    case apply (m, x) of
      | None -> false
      | Some _ -> true

  def mapi        f m = V_mapi        (f,m)
  def map         f m = V_map         (f,m)
  def mapiPartial f m = V_mapiPartial (f,m)
  def mapPartial  f m = V_mapPartial  (f,m)

  def app  f m = V_app  (f,m)
  def appi f m = V_appi (f,m)

  def foldi f e m = V_foldi(f,e,m)

  def imageToList  = V_imageToList  def mapToList    = V_mapToList
  def domainToList = V_domainToList

end-spec


% TODO Do we need this morphism?  Why not just import SimpleAsVector
% (which imports Simple and gives definitions to some of its ops)?
M = morphism Simple -> SimpleAsVector {}
