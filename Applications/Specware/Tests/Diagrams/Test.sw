(* Copyright 2015 Kestrel Institute. See file LICENSE for license details *)


  a = spec 
     type X
     op x : X
    end-spec
  b = spec 
     type Y
     op y : Y
    end-spec
  c = spec 
     type Z
     op z : Z
    end-spec
  m = morphism a -> b {X +-> Y, x +-> y}
  n = morphism a -> c {X +-> Z, x +-> z}
  p = morphism b -> c {Y +-> Z, y +-> z}
  d = diagram {
      u : v -> w +-> m,
      x : v -> z +-> n
    }

Test = colimit d
