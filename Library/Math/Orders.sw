(* Copyright 2015 Kestrel Institute. See file LICENSE.text for license details *)

spec

 op [a] reflexive?(binop: a*a->Bool):Bool = 
    fa(x:a) binop(x,x)

end-spec
