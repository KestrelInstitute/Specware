Compare qualifying spec

  % refinement of base spec Compare

  import Boolean

  % sorts:

  sort Comparison =
    | Greater
    | Equal
    | Less

  % ops whose Lisp code is generated:

  op compare : Comparison * Comparison -> Comparison

  def compare(cmp1,cmp2) = if cmp1 = cmp2 then Equal
                           else if (cmp1 = Greater or
                                    cmp1 = Equal & cmp2 = Less) then Greater
                           else (*  cmp1 = Less or
                                    cmp1 = Equal & cmp2 = Greater *) Less

  % ops conceptually belonging to this spec but introduced elsewhere:

  % op show : Comparison -> String

  % ops conceptually belonging to other specs but introduced here,
  % whose Lisp code is generated:

  op Boolean.compare : Boolean * Boolean -> Comparison

  def Boolean.compare(x,y) = if (x = y)    then Equal
                        else if (x = true) then Greater
                        else  (* x = false *)   Less

endspec
