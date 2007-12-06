spec
  import Structs

  type Text = Seq String

  op  glue : Seq Text -> Text
  def glue = tl o flatten o map (fn t -> Cons("", t))

  op  writeText : Text -> ()
  def writeText = foldl (fn(line, _) -> writeLine line) ()

endspec
