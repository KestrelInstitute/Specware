Compare qualifying spec {
  import PrimitiveSorts

  sort Comparison =
    | Greater
    | Equal
    | Less

  op show : Comparison -> String
  def show cmp =
    case cmp of
      | Greater -> "Greater"
      | Equal -> "Equal"
      | Less -> "Less"
}
