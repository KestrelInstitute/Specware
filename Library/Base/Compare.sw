(* Copyright 2015 Kestrel Institute. See file LICENSE.text for license details *)

Compare qualifying spec

import Boolean

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

(* We can linearly order and compare booleans (false < true). We use the Bool
qualifier to distinguish this op from the previous one and from similar ops in
other specs (e.g. String.compare). *)

op Bool.compare (x:Bool, y:Bool) : Comparison =
       if (x = y)    then Equal
  else if (x = true) then Greater
  else  (* x = false *)   Less

#translate Haskell -morphism
 type Compare.Comparison \_rightarrow Ordering
 Less \_rightarrow LT
 Equal \_rightarrow EQ
 Greater \_rightarrow GT
 Compare.compare \_rightarrow compare curried
 Bool.compare    \_rightarrow compare curried
#end

endspec
