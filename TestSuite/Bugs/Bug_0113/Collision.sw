
S = spec

 type X
 type Y

 op f : Nat
 op g : Nat

 type A.T
 type B.T

 op D.m : Nat
 op E.m : Nat

endspec


%% types direct 
T1 = translate S by {type X +-> Y} 
T2 = translate S by {X +-> Y}

%% types collision
T3 = translate S by {type X +-> Z, type Y +-> Z}
T4 = translate S by {X +-> Z, Y +-> Z}


%% ops direct
T5 = translate S by {op f +-> g}
T6 = translate S by {f +-> g}

%% ops collision
T7 = translate S by {op f +-> h, op g +-> h}
T8 = translate S by {f +-> h, g +-> h}

%% types direct via wildcards

T9 = translate S by {A._ +-> B._}

%% types collision via wildcards

T10 = translate S by {A._ +-> C._, B._ +-> C._}

%% ops direct via wildcards

T11 = translate S by {D._ +-> E._}

%% ops collision via wildcards

T12 = translate S by {D._ +-> F._, E._ +-> F._}
