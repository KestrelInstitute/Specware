(* Copyright 2015 Kestrel Institute. See file LICENSE for license details *)

(* The Wadler / Lindig pretty printer combinators}

This one just does indentation with not attempt to fit to some width. Most
of the code here is not used but we want it to be a substitute
for the usual Wadler Lindig version.

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
   type WLPretty = Doc

%   op layout : Doc -> Doc -> Nat -> Nat -> List String
%   def layout doc rest column indent =
%     let def replicate (cnt:Int) str suffix =
%       if cnt <= 0 then
%         suffix
%       else
%         Cons (str, replicate (cnt - 1) str suffix) in
%     case doc of
%       | DocGroup d -> layout d rest column indent
%       | DocText s -> Cons (s, layout rest DocNil (column + (length s)) indent)
%       | DocBreak s -> Cons ("\n", replicate indent " " (layout rest DocNil indent indent))
%       | DocIndent (newIndent,doc) -> layout doc rest column newIndent
%       | DocNest (n,innerDoc) ->
%           replicate (indent + n - column) " " (layout innerDoc (DocIndent (indent, rest)) column (indent + n))
%       | DocCons (l,r) -> layout l (ppCons r rest) column indent
%       | DocNil ->
%          if rest = DocNil then
%            []
%          else
%            layout rest DocNil column indent

  op PrettyPrint.blanks : Nat -> String
  op spaces : Nat -> String
  def spaces n = 
    if n > 0 then
      blanks n
    else
      ""

  op fits(doc: Doc, rest: Doc, len: Nat): Bool =
    if len < 0 then false
    else
    case doc of
      | DocGroup d -> false
      | DocText s -> fits(rest, DocNil, len - length s)
      | DocNewline -> true
      | DocBreak s -> true
      | DocIndent (newIndent,doc) -> false
      | DocNest (n,innerDoc) -> false
      | DocCons (l,r) -> fits(l, DocCons (r, rest), len)
      | DocNil ->
    case rest of
      | DocCons (l, r) -> fits(l, r, len)
      | DocNil -> true
      | _ -> fits(rest, DocNil, len)

  op lineLength: Nat = 90

  % The following is a tail recursive version of the function "layout" defined above.
  % The functions spaces and aux would normally be defined within the scope of the "layout"
  % function, but doing so generates Lisp code that the ACL compiler fails to detect as
  % tail recursive.

  op layout : Doc -> Doc -> Nat -> Nat -> List String -> List String
  def layout doc rest column indent stream =
    case doc of
      | DocGroup d -> layout d rest column indent stream
      | DocText s  -> layout rest DocNil (column + (length s)) indent (s :: stream)
      | DocNewline -> layout rest DocNil indent indent
                        (spaces indent :: "\n" :: stream)
      | DocBreak s ->
        if fits(DocText s, rest, lineLength - column)
          then layout rest DocNil column indent (s :: stream)
        else layout rest DocNil indent indent (spaces indent :: "\n" :: stream)
      | DocIndent (newIndent,doc) -> layout doc rest column newIndent stream
      | DocNest (n,innerDoc) ->
          layout innerDoc (DocIndent (indent, rest)) column (column + n) stream
      | DocCons (l,r) -> layout l (ppCons r rest) column indent stream
      | DocNil ->
         if rest = DocNil then
           stream
         else
           layout rest DocNil column indent stream
 
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
  
  type SDoc =
    | SNil
    | SText (String * SDoc)
    | SLine (Int    * SDoc)   (* newline + spaces *)
  
  % def ppFormat doc = ppFormatWidth 80 doc
  def ppFormat doc = ppFormatWidth doc

  % op ppFormatWidth : Int -> Doc -> String
  op ppFormatWidth : Doc -> String

  def ppFormatWidth doc =
    let strings = layout doc DocNil 0 0 [] in
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

  op ppNewline : Doc
  def ppNewline = DocNewline

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

%  let pretty w doc =
%    let sdoc = ppBest w 0 [0,Flat,DocGroup doc] in
%    let str = ppLayout sdoc in print_endline str
end
