Compare qualifying spec

  sort Comparison =
    | Less
    | Equal
    | Greater

  op compare : Comparison * Comparison -> Comparison

  def compare(cmp1,cmp2) = if  cmp1 = cmp2     then Equal
                      else if (cmp1 = Less or
                               cmp2 = Greater) then Less
                      else (*  cmp1 = Greater or
                               cmp2 = Less *)       Greater

  op Boolean.compare : Boolean * Boolean -> Comparison

  def Boolean.compare(x,y) = if (x = y)    then Equal
                        else if (x = true) then Greater
                        else  (* x = false *)   Less
endspec
