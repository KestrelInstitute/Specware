(* Copyright 2015 Kestrel Institute. See file LICENSE for license details *)

%% Domain of a Monomorphic Map

%% This spec is the ``parameter'' to monomorphic maps defining the
%% type of the domain of the maps.

spec
  import /Library/PrettyPrinter/WadlerLindig

  type Dom
  op ppDom : Dom -> WLPretty
end-spec
