spec 
  import PrimitiveSorts
  import List
  import String

  op List.show : String -> List String -> String
  def List.show sep l =
    case l of
      | [] -> ""
      | x::[] -> x 
      | x::rest ->
           x
         ^ sep
         ^ (List.show sep rest)

  op Option.show : fa (a) (a -> String) -> Option a -> String
  def Option.show showX opt =
    case opt of
      | None -> "None"
      | Some x ->
          "(Some "
          ^ (showX x)
          ^ ")"
endspec
