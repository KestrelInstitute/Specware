(* The Wadler / Lindig pretty printer combinators}

This one just does indentation with not attempt to fit to some width. Most
of the code here is not used but we want it to be a substitute
for the usual Wadler Lindig version.

*)

WadlerLindig qualifying spec
  import /Library/Legacy/Utilities/IO

  type Doc =
    | DocNil
    | DocCons (Doc * Doc)
    | DocText String
    | DocNest (Integer * Doc)   % Offset relative to current column
    | DocIndent (Integer * Doc) % Offset absolute (from left)
    | DocNewline
    | DocBreak String
    | DocGroup Doc
   type Pretty = Doc

%   op layout : Doc -> Doc -> Nat -> Nat -> List String
%   def layout doc rest column indent =
%     let def replicate (cnt:Integer) str suffix =
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

  % The following is a tail recursive version of the function "layout" defined above.
  % The functions spaces and aux would normally be defined within the scope of the "layout"
  % function, but doing so generates Lisp code that the ACL compiler fails to detect as
  % tail recursive.

  op layout : Doc -> Doc -> Nat -> Nat -> List String -> List String
  def layout doc rest column indent stream =
    case doc of
      | DocGroup d -> layout d rest column indent stream
      | DocText s -> layout rest DocNil (column + (length s)) indent (Cons (s, stream))
      | DocNewline -> layout rest DocNil indent indent (Cons (spaces indent, Cons ("\n", stream)))
      | DocBreak s -> layout rest DocNil indent indent (Cons (spaces indent, Cons ("\n", stream)))
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
  
  op ppNest : Integer -> Doc -> Doc
  def ppNest i x = DocNest (i,x)
  
  op ppBreak : Doc
  def ppBreak = DocBreak " "
  
  op ppBreakWith : String -> Doc
  def breakWith s = DocBreak s
  
  op ppGroup : Doc -> Doc
  def ppGroup d = DocGroup d
  
  sort SDoc =
    | SNil
    | SText (String * SDoc)
    | SLine (Integer * SDoc)   (* newline + spaces *)
  
  % def ppFormat doc = ppFormatWidth 80 doc
  def ppFormat doc = ppFormatWidth doc

  % op ppFormatWidth : Integer -> Doc -> String
  op ppFormatWidth : Doc -> String

  def ppFormatWidth doc =
    let strings = layout doc DocNil 0 0 [] in
    % concatList (rev strings)
    IO.withOutputToString
       (fn stream ->
	app (fn s -> IO.format1 (stream, "~A", s))
	  (rev strings))

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
