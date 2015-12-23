(* Copyright 2015 Kestrel Institute. See file LICENSE.text for license details *)

spec
  import Typedef
  import Text

  op  typedefToText : Typedef -> Text
  def typedefToText{typename, rhs} =
    case rhs of
       | Sum ss -> ["type " ++ typename ++ " ="] ++ map sumToString ss
       | _      -> ["type " ++ typename ++ " = " ++ typeToString rhs]

  op  sumToString : Summand -> String
  def sumToString{cname, tipo?} =
    "   | " ++ cname ++
    (case tipo? of
        | None   -> ""
        | Some t -> " " ++ typeToString t)

  op  typeToString : (Type | (~) o embed? Sum) -> String
  def typeToString tipo =
    case tipo of
       | Typename  n -> n
       | Option    t -> "Option "    ++ typeToString t
       | Seq       t -> "Seq "       ++ typeToString t
       | ProperSeq t -> "ProperSeq " ++ typeToString t
       | Record   fs -> fieldsToString fs

  op  fieldsToString : Seq Field -> String
  def fieldsToString fs =
    let def fieldToString{fname, tipo} =
      fname ++ " : " ++ typeToString tipo
    in
    let body =
      if fs = []
      then ""
      else 
        let bb = concatList (map ((fn s -> ", " ++ s) o fieldToString) fs)
	in substring(bb, 2, length bb)
    in "{" ++ body ++ "}"

  op typedefsToText : Seq Typedef -> Text
  def typedefsToText = glue o map typedefToText


endspec
