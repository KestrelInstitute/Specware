
R = spec

 type X

endspec

S = spec

 type Y

endspec

T = spec

 type Z

endspec

D = diagram
  {
   a : r -> s +-> morphism R -> S {X +-> Y},
   b : r -> t +-> morphism R -> T {X +-> Z}
  }

C = colimit D

T_XX_YY_ZZ = translate C by {X +-> X, Y +-> Y, Z +-> Z}

T_XY    = translate C by {X +-> Y}
T_XZ    = translate C by {X +-> Z}
T_YX    = translate C by {Y +-> X}
T_YZ    = translate C by {Y +-> Z}
T_ZX    = translate C by {Z +-> X}
T_ZY    = translate C by {Z +-> Y}

T_XY_YX = translate C by {X +-> Y, Y +-> X}
T_XY_YZ = translate C by {X +-> Y, Y +-> Z}
T_XY_YP = translate C by {X +-> Y, Y +-> P}
T_XY_ZX = translate C by {X +-> Y, Z +-> X}
T_XY_ZY = translate C by {X +-> Y, Z +-> Y}
T_XY_ZP = translate C by {X +-> Y, Z +-> P}

T_XZ_YX = translate C by {X +-> Z, Y +-> X}
T_XZ_YZ = translate C by {X +-> Z, Y +-> Z}
T_XZ_YP = translate C by {X +-> Z, Y +-> P}
T_XZ_ZX = translate C by {X +-> Z, Z +-> X}
T_XZ_ZY = translate C by {X +-> Z, Z +-> Y}
T_XZ_ZP = translate C by {X +-> Z, Z +-> P}

T_XP_YX = translate C by {X +-> P, Y +-> X}
T_XP_YZ = translate C by {X +-> P, Y +-> Z}
T_XP_YP = translate C by {X +-> P, Y +-> P}
T_XP_YQ = translate C by {X +-> P, Y +-> Q}
T_XP_ZX = translate C by {X +-> P, Z +-> X}
T_XP_ZY = translate C by {X +-> P, Z +-> Y}
T_XP_ZP = translate C by {X +-> P, Z +-> P}
T_XP_ZR = translate C by {X +-> P, Z +-> R}

T_YX_ZX = translate C by {Y +-> X, Z +-> X}
T_YX_ZY = translate C by {Y +-> X, Z +-> Y}
T_YX_ZP = translate C by {Y +-> X, Z +-> P}

T_YZ_ZX = translate C by {Y +-> Z, Z +-> X}
T_YZ_ZY = translate C by {Y +-> Z, Z +-> Y}
T_YZ_ZP = translate C by {Y +-> Z, Z +-> P}

T_YP_ZX = translate C by {Y +-> P, Z +-> X}
T_YP_ZY = translate C by {Y +-> P, Z +-> Y}
T_YP_ZP = translate C by {Y +-> P, Z +-> P}
T_YP_ZR = translate C by {Y +-> P, Z +-> R}

T_XY_YX_ZX = translate C by {X +-> Y, Y +-> X, Z +-> X}
T_XY_YX_ZY = translate C by {X +-> Y, Y +-> X, Z +-> Y}
T_XY_YX_ZR = translate C by {X +-> Y, Y +-> X, Z +-> R}

T_XY_YZ_ZX = translate C by {X +-> Y, Y +-> Z, Z +-> X}
T_XY_YZ_ZY = translate C by {X +-> Y, Y +-> Z, Z +-> Y}
T_XY_YZ_ZR = translate C by {X +-> Y, Y +-> Z, Z +-> R}

T_XY_YP_ZX = translate C by {X +-> Y, Y +-> P, Z +-> X}
T_XY_YP_ZY = translate C by {X +-> Y, Y +-> P, Z +-> Y}
T_XY_YP_ZP = translate C by {X +-> Y, Y +-> P, Z +-> P}
T_XY_YP_ZR = translate C by {X +-> Y, Y +-> P, Z +-> R}

T_XZ_YX_ZX = translate C by {X +-> Z, Y +-> X, Z +-> X}
T_XZ_YX_ZY = translate C by {X +-> Z, Y +-> X, Z +-> Y}
T_XZ_YX_ZR = translate C by {X +-> Z, Y +-> X, Z +-> R}

T_XZ_YZ_ZX = translate C by {X +-> Z, Y +-> Z, Z +-> X}
T_XZ_YZ_ZY = translate C by {X +-> Z, Y +-> Z, Z +-> Y}
T_XZ_YZ_ZR = translate C by {X +-> Z, Y +-> Z, Z +-> R}

T_XZ_YP_ZX = translate C by {X +-> Z, Y +-> P, Z +-> X}
T_XZ_YP_ZY = translate C by {X +-> Z, Y +-> P, Z +-> Y}
T_XZ_YP_ZP = translate C by {X +-> Z, Y +-> P, Z +-> P}
T_XZ_YP_ZR = translate C by {X +-> Z, Y +-> P, Z +-> R}


T_XP_YX_ZX = translate C by {X +-> P, Y +-> X, Z +-> X}
T_XP_YX_ZY = translate C by {X +-> P, Y +-> X, Z +-> Y}
T_XP_YX_ZP = translate C by {X +-> P, Y +-> X, Z +-> P}
T_XP_YX_ZR = translate C by {X +-> P, Y +-> X, Z +-> R}

T_XP_YZ_ZX = translate C by {X +-> P, Y +-> Z, Z +-> X}
T_XP_YZ_ZY = translate C by {X +-> P, Y +-> Z, Z +-> Y}
T_XP_YZ_ZP = translate C by {X +-> P, Y +-> Z, Z +-> P}
T_XP_YZ_ZR = translate C by {X +-> P, Y +-> Z, Z +-> R}

T_XP_YP_ZX = translate C by {X +-> P, Y +-> P, Z +-> X}
T_XP_YP_ZY = translate C by {X +-> P, Y +-> P, Z +-> Y}
T_XP_YP_ZP = translate C by {X +-> P, Y +-> P, Z +-> P}
T_XP_YP_ZR = translate C by {X +-> P, Y +-> P, Z +-> R}

T_XP_YQ_ZX = translate C by {X +-> P, Y +-> Q, Z +-> X}
T_XP_YQ_ZY = translate C by {X +-> P, Y +-> Q, Z +-> Y}
T_XP_YQ_ZP = translate C by {X +-> P, Y +-> Q, Z +-> P}
T_XP_YQ_ZQ = translate C by {X +-> P, Y +-> Q, Z +-> Q}
T_XP_YQ_ZR = translate C by {X +-> P, Y +-> Q, Z +-> R}


