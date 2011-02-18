spec
  import /Library/PrettyPrinter/WadlerLindig
  op String.pp : String -> Doc
  def String.pp = ppString  % legacy

  op Nat.pp : Nat -> Doc
  def Nat.pp n = pp (Nat.toString n)

  op Integer.pp : Int -> Doc
  def Integer.pp n = pp (Integer.toString n)

  op Boolean.pp : Bool -> Doc
  def Boolean.pp b = pp (Boolean.toString b)

  op Char.pp : Char -> Doc
  def Char.pp c = pp (Char.toString c)
endspec

