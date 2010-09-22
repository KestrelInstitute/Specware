Pragma qualifying spec
import /Languages/MetaSlang/Specs/Position
import /Library/Unvetted/StringUtilities
type Pragma = String * String * String * Position

op getFirstLine(s: String): String =
  case search("\n", s) of
    | None -> s
    | Some n -> subFromTo(s, 0, n)


op controlPragmaString(s: String): Option(List String) =
   let line1 = case search("\n", s) of
                 | None -> s
                 | Some n -> subFromTo(s, 0, n)
   in
   case removeEmpty(splitStringAt(line1, " ")) of
    | _::str::rst | length str > 1 && str@0 = #- && str@1 ~= #> ->
      Some(str::rst)
    | _ -> None

op controlPragma?(s: String): Boolean =
  embed? Some (controlPragmaString s)

op validName?(s: String): Bool =
  s ~= "" &&
  ~(s = "fa" || s@0 in? [#(,#[,#\\,#",#-])

op namedPragma?(p: Pragma): Boolean =
   let (_,s,_,_) = p in
   let line1 = getFirstLine s in
   case removeEmpty(splitStringAt(line1, " ")) of
    | pragma_kind::name?::r -> validName? name?
    | _ -> false

 op unnamedPragma?(p: Pragma): Boolean =
   let control? = controlPragmaString p.2 in
   ~(namedPragma? p || some? control?) || control? = Some ["-typedef"]

 op verbatimIdString: String = "-verbatim"

 op verbatimPragma?(s: String): Boolean =
   case controlPragmaString s of
     | Some(str::_) -> str = verbatimIdString
     | _ -> false

 op splitNameFromPragmaStr(prag_str: String): Option(String * String) =
   let line1 = stripOuterSpaces(getFirstLine prag_str) in
   case splitAtStr(line1, " ") of
     | None -> None
     | Some(_, rl1) ->
   case splitAtStr(rl1, " ") of
     | Some(name?, rl2) | validName? name? -> Some(name?, rl2)
     | _ -> None

endspec
