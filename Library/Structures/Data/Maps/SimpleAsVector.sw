(* Map with Nat domain implemented as vector
   Note that it assumes the usage is single-threaded! *)

%% TODO Where is the expression of the requirement that the domain of the map is Nat?
%% TODO Where is the semantics given on the Simple map operations?
%% TODO This leaves the type Map undefined, unlike SimpleAsAlist.

SimpleAsVector = VMap qualifying
spec
  import Simple
  import MapVec  %% This adds the VMap qualifier to the Map type.

  def emptyMap      = MapVec.V_empty_map
  def numItems      = MapVec.V_numItems
  def apply         = MapVec.V_apply
  def eval          = MapVec.V_eval
  def update(x,y,z) = MapVec.V_update(x,y,z)
  def remove        = MapVec.V_remove
  % TODO why not call MapVec.V_inDomain? ?  Maybe because there is no code for it?
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


% TODO Do we need this morphism?  Why not just import SimpleAsVector
% (which imports Simple and gives definitions to some of its ops)?
M = morphism Simple -> SimpleAsVector {}
