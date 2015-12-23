(* Copyright 2015 Kestrel Institute. See file LICENSE for license details *)

(* The Wadler / Lindig pretty printer combinators

sjw 4/15/11: Written to match Lindig's algorithm (with a few extensions)

ppBreak() -- an optional line break
ppGroup d -- If d doesn't fit in line then enable all ppBreaks 
ppNest i d -- Set indentation of following breaks to be current column +i
ppNestG i d --> ppGroup (ppNest i d)  common pattern
ppString s -- print string s
d1 ^ d2   -- command d1 followed by d2
ppConcat dl -- sequence of commands dl
ppConcatGN i dl -- ppGroup (ppNest i (ppConcat dl))


*)

WadlerLindig qualifying spec
  import /Library/Legacy/Utilities/IO
  import /Library/Legacy/Utilities/System

  type Doc =
    | DocNil
    | DocCons (Doc * Doc)
    | DocText String
    | DocNest   (Int * Doc)   % Offset relative to current column
    | DocIndent (Int * Doc) % Offset absolute (from left)
    | DocNewline
    | DocBreak String
    | DocGroup Doc
    | DocBreaking? Bool * Doc    % For internal use to limit scope of breaking? parameter in layout

  type WLPretty = Doc

  op PrettyPrint.blanks : Nat -> String
  op spaces : Nat -> String
  def spaces n = 
    if n > 0 then
      blanks n
    else
      ""

  op fits(doc: Doc, rest: Doc, len: Nat, breaking?: Bool): Bool =
    if len < 0 then false
    else
    case doc of
      | DocGroup d -> fits(d, rest, len, breaking?)
      | DocText s -> fits(rest, DocNil, len - length s, breaking?)
      | DocNewline -> true
      | DocBreak s -> breaking? || fits(rest, DocNil, len - length s, breaking?)
      | DocIndent (newIndent,doc) -> fits(doc, rest, len, breaking?)
      | DocNest (n,innerDoc) -> fits(innerDoc, rest, len, breaking?)
      | DocCons (l,r) -> fits(l, DocCons (r, rest), len, breaking?)
      | DocBreaking?(prev_breaking?, d) -> fits(d, rest, len, prev_breaking?)
      | DocNil ->
    case rest of
      | DocCons (l, r) -> fits(l, r, len, breaking?)
      | DocNil -> true
      | DocIndent(_, d) -> fits(d, rest, len, breaking?)
      | DocBreaking?(prev_breaking?, d) -> fits(d, rest, len, prev_breaking?)
      | _ -> fits(rest, DocNil, len, breaking?)

  op lineLength: Nat = 90

  % The following is a tail recursive version of the function "layout" defined above.
  % The functions spaces and aux would normally be defined within the scope of the "layout"
  % function, but doing so generates Lisp code that the ACL compiler fails to detect as
  % tail recursive.

  op layout : Doc -> Doc -> Nat -> Nat -> Nat -> Bool -> List String -> List String
  def layout doc rest line_length column indent breaking? stream =
    case doc of
      | DocGroup d -> let prev_break_rest = DocBreaking?(breaking?, rest) in
                      let break_group? = ~(fits(d, prev_break_rest, line_length - column, false)) in
                      layout d prev_break_rest line_length column indent break_group? stream
      | DocText s  -> layout rest DocNil line_length (column + (length s)) indent breaking? (s :: stream)
      | DocNewline -> layout rest DocNil line_length indent indent breaking?
                        (spaces indent :: "\n" :: stream)
      | DocBreak s ->
        if indent < column - 1    % Only break if you save at least 2 spaces
            && (breaking? || ~(fits(rest, DocNil, line_length - column, true)))
          then layout rest DocNil line_length indent indent breaking? (spaces indent :: "\n" :: stream)
          else layout rest DocNil line_length column indent breaking? (s :: stream)
      | DocIndent (newIndent,doc) -> layout doc rest line_length column newIndent breaking? stream
      | DocNest (n,innerDoc) -> layout innerDoc (DocIndent (indent, rest)) line_length column (column + n) breaking? stream
      | DocCons (l,r) -> layout l (ppCons r rest) line_length column indent breaking? stream
      | DocBreaking?(prev_breaking?, d) -> layout d rest line_length column indent prev_breaking? stream
      | DocNil ->
         if rest = DocNil then
           stream
         else
           layout rest DocNil line_length column indent breaking? stream
 
  op WadlerLindig.^  infixl 25  : Doc * Doc -> Doc
  def WadlerLindig.^ (x,y) = ppCons x y

  op ppCons : Doc -> Doc -> Doc
  def ppCons x y = 
    case (x,y) of
      | (DocNil,DocNil) -> DocNil
      | (DocNil,x) -> x
      | (x,DocNil) -> x
      | _ -> DocCons (x,y)
  
  op ppNil : Doc
  def ppNil = DocNil
  
  op ppString : String -> Doc
  def ppString s = DocText s
  
  op ppNest : Int -> Doc -> Doc
  def ppNest i x = DocNest (i,x)

  op ppBreak : Doc
  def ppBreak = DocBreak ""
  
  op ppBreakWith : String -> Doc
  def ppBreakWith s = DocBreak s
  
  op ppGroup : Doc -> Doc
  def ppGroup d = DocGroup d
  
  op ppNestG (i: Int) (x: Doc): Doc = DocGroup(DocNest (i,x))
  
  type SDoc =
    | SNil
    | SText (String * SDoc)
    | SLine (Int    * SDoc)   (* newline + spaces *)
  
  % def ppFormat doc = ppFormatWidth 80 doc
  def ppFormat doc = ppFormatWidth lineLength doc

  op ppFormatWidth : Int -> Doc -> String

  def ppFormatWidth line_length doc =
    let strings = layout doc DocNil line_length 0 0 false [] in
    % concatList (rev strings)
    IO.withOutputToString
       (fn stream ->
	app (fn s -> IO.format1 (stream, "~A", s))
	  (reverse strings))

  op ppAppend : Doc -> Doc -> Doc
  def ppAppend p1 p2 = ppCons p1 p2

  op ppIndent : Doc -> Doc
  def ppIndent p = ppNest 2 p

  op ppConcat : List Doc -> Doc
  def ppConcat l =
    case l of
      | Nil ->  ppNil
      | (s::ss) -> ppCons s (ppConcat ss)

  op ppConcatGN (i: Int) (dl: List Doc): Doc = ppGroup (ppNest i (ppConcat dl))

  op ppNewline : Doc
  def ppNewline = DocNewline

  op commaBreak: WLPretty = ppConcat [ppString ", ", ppBreak]

  op ppSep : Doc -> List Doc -> Doc
  def ppSep sep l = 
    case l of
      | [] -> ppNil
      | s::ss -> 
         let rest = ppSep sep ss in
         if rest = DocNil then
           s
         else
           ppCons s (ppCons sep rest)

op example: Doc =
  ppConcatGN 0
   [ppNest 3 (ppConcat [ppString "begin ",
                        ppBreak,
                        ppGroup (ppConcat [ppString "stat; ", ppBreak, ppString "stat; ", ppBreak, ppString "stat; "])]),
    ppBreak, ppString "end"]

op prEx(i: Nat): String =
  ppFormatWidth i example

%  let pretty w doc =
%    let sdoc = ppBest w 0 [0,Flat,DocGroup doc] in
%    let str = ppLayout sdoc in print_endline str
end-spec
