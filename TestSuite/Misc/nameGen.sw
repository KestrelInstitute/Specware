spec
  %import /Library/Base/Boolean
  %type Option a = | None | Some a
  def f x = case x of
              | Some (Some y) -> y
	      | _ -> true
  def g x = case x of
              | Some (Some y) -> y
	      | _ -> false
endspec
