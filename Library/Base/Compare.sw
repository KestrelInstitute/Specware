Compare qualifying spec

  % possible results of a comparison (w.r.t. a linear order):

  type Comparison =
    | Less
    | Equal
    | Greater

  % comparison results themselves can be linearly ordered and compared
  % (Less < Equal < Greater):

  op compare (cmp1:Comparison, cmp2:Comparison) : Comparison =
         if  cmp1 = cmp2     then Equal
    else if (cmp1 = Less ||
             cmp2 = Greater) then Less
    else (*  cmp1 = Greater ||
             cmp2 = Less *)       Greater

  (* We can linearly order and compare booleans (false < true). We use the
  Boolean qualifier to distinguish this op from the previous one and from
  similar ops in other specs (e.g. String.compare). *)

  op Boolean.compare (x:Boolean, y:Boolean) : Comparison =
         if (x = y)    then Equal
    else if (x = true) then Greater
    else  (* x = false *)   Less

endspec
