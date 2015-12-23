(* Copyright 2015 Kestrel Institute. See file LICENSE for license details *)

%% Codomain Type of a Monomorphic Map

%% This spec is the ``parameter'' to monomorphic maps defining the
%% type of the codomain of the maps.

spec
  import /Library/PrettyPrinter/WadlerLindig

  type Cod
  op ppCod : Cod -> WLPretty
end-spec
