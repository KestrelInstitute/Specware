(* Copyright 2015 Kestrel Institute. See file LICENSE for license details *)

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

op controlPragma?(s: String): Bool =
  embed? Some (controlPragmaString s)

op validName?(s: String): Bool =
  s ~= "" &&
  ~(s = "fa" || s@0 in? [#(,#[,#\\,#",#-])

op namedPragma?(p: Pragma): Bool =
   let (_,s,_,_) = p in
   let line1 = getFirstLine s in
   case removeEmpty(splitStringAt(line1, " ")) of
    | pragma_kind::name?::r -> validName? name?
    | _ -> false

 op unnamedPragma?(p: Pragma): Bool =
   let control? = controlPragmaString p.2 in
   ~(namedPragma? p || some? control?) || control? = Some ["-typedef"]

 op verbatimIdString: String = "-verbatim"

 op verbatimPragma?(s: String): Bool =
   case controlPragmaString s of
     | Some(str::_) -> str = verbatimIdString
     | _ -> false

 op defaultProofStrings: List String = ["-default-proof", "-Default-Proof", "-defaultProof", "-DefaultProof"]

 op defaultProofPragma?(p: Pragma): Bool =
   let (_,s,_,_) = p in
   let line1 = getFirstLine s in
   case removeEmpty(splitStringAt(line1, " ")) of
     | _::str::_ -> str in? defaultProofStrings
     | _ -> false

 op hookIdString: String = "-hook"

 op hookPragma?(s: String): Bool =
   case controlPragmaString s of
     | Some(str::_) -> str = hookIdString
     | _ -> false

 op splitNameFromPragmaStr(prag_str: String): Option(String * String) =
   let line1 = stripOuterSpaces(getFirstLine prag_str) in
   case splitAtStr(line1, " ") of
     | None -> None
     | Some(_, rl1) ->
   case splitAtStr(rl1, " ") of
     | Some(name?, rl2) | validName? name? -> Some(name?, rl2)
     | _ -> None

op isPragmaKind(s: String, kind: String): Bool =
  case searchPredFirstAfter(s, fn c -> ~(whiteSpaceChar? c), 0) of
    | Some firstNonSpace ->
       (if isUpperCase(kind@0) && isLowerCase(s@firstNonSpace)
          then case searchPredFirstAfter(s, whiteSpaceChar?, firstNonSpace + 1) of
                 | Some end_kind ->
                   kind = capitalize(subFromTo(s, firstNonSpace, end_kind))
                 | None -> false
          else testSubseqEqual?(kind, s, 0, firstNonSpace))
    | None -> false

op isOneOfPragmaKinds(s: String, kinds: List String): Bool =
  exists? (fn kind -> isPragmaKind(s, kind)) kinds

end-spec
