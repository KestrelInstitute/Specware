
S = spec

 type X
 type Y

 op f : X
 op g : X

 op p : X
 op q : Y

 type A.T
 type B.T

 op D.m : Y
 op E.m : Y

endspec


%% types direct 
Bad1 = translate S by {type X +-> Y} 
Bad2 = translate S by {X +-> Y}

%% types collision
Bad3 = translate S by {type X +-> Z, type Y +-> Z}
Bad4 = translate S by {X +-> Z, Y +-> Z}


%% ops direct
Bad5 = translate S by {op f +-> g}
Bad6 = translate S by {f +-> g}

%% ops collision
Bad7 = translate S by {op f +-> h, op g +-> h}
Bad8 = translate S by {f +-> h, g +-> h}

%% types direct via wildcards

Bad9 = translate S by {A._ +-> B._}

%% types collision via wildcards

Bad10 = translate S by {A._ +-> C._, B._ +-> C._}

%% ops direct via wildcards

Bad11 = translate S by {D._ +-> E._}

%% ops collision via wildcards

Bad12 = translate S by {D._ +-> F._, E._ +-> F._}


%% ok ---

Ok1 = translate S by {X +-> Y, Y +-> Z}

Ok2 = translate S by {Y +-> Z, X +-> Y}

Ok3 = translate S by {X +-> Y, Y +-> X}

Ok4 = translate S by {Y +-> X, X +-> Y}


Ok5 = translate S by {p +-> q, q +-> r}

Ok6 = translate S by {q +-> r, p +-> q}

Ok7 = translate S by {p +-> q, q +-> p}

Ok8 = translate S by {q +-> p, p +-> q}

