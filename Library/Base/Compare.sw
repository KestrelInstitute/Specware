Compare qualifying spec

  import Boolean

  % sorts:

  sort Comparison =
    | Less
    | Equal
    | Greater

  % ops whose Lisp code is generated:

  op compare : Comparison * Comparison -> Comparison

  def compare(cmp1,cmp2) = if  cmp1 = cmp2     then Equal
                      else if (cmp1 = Less or
                               cmp2 = Greater) then Less
                      else (*  cmp1 = Greater or
                               cmp2 = Less *)       Greater

  % ops conceptually belonging to this spec but introduced elsewhere:

  % op show : Comparison -> String

  % ops conceptually belonging to other specs but introduced here,
  % whose Lisp code is generated:
(*
  op Boolean.compare : Boolean * Boolean -> Comparison

  def Boolean.compare(x,y) = if (x = y)    then Equal
                        else if (x = true) then Greater
                        else  (* x = false *)   Less
*)
endspec
