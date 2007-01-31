Compare qualifying spec

  type Comparison =
    | Less
    | Equal
    | Greater

  op compare (cmp1:Comparison, cmp2:Comparison) : Comparison =
         if  cmp1 = cmp2     then Equal
    else if (cmp1 = Less ||
             cmp2 = Greater) then Less
    else (*  cmp1 = Greater ||
             cmp2 = Less *)       Greater

  op Boolean.compare (x:Boolean, y:Boolean) : Comparison =
         if (x = y)    then Equal
    else if (x = true) then Greater
    else  (* x = false *)   Less

endspec
