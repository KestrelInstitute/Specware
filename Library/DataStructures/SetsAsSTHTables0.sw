(* Copyright 2015 Kestrel Institute. See file LICENSE.text for license details *)

%% Why the "0" in this name?
SetsAsSTHTables0 = SetsAsBagMaps[MapsAsSTHTables#M]

M = morphism Sets -> SetsAsSTHTables0 {Set._ +-> SetsAsBags._}