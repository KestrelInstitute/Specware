\section{The Wadler / Lindig pretty printer combinators}

This one just does no indentation with not attempt to fit to some width. Most
of the code here is not used but we want it to be a substitute
for the usual Wadler Lindig version.

\begin{spec}
WadlerLindig qualifying spec
  import /Library/Base

  sort Pretty = Doc

  op simpleLayout : Doc -> List String -> Nat -> Nat -> Nat * List String
  def simpleLayout doc rest column indent =
    let def replicate (cnt:Integer) str suffix =
      if cnt = 0 then
        suffix
      else
        Cons (str, replicate (cnt - 1) str suffix) in
    case doc of
      | DocNil -> (column,rest)
      | DocCons (l,r) ->
          let (newColumn,right) = simpleLayout r rest column indent
          in simpleLayout l right newColumn indent
      | DocText s -> (column + (length s), cons (s, rest))
      | DocNest (n,otherDoc) ->
          let (newColumn,x) = simpleLayout otherDoc rest column (column + n) in
            (newColumn, x)
      | DocBreak s -> (indent, Cons ("\n", replicate indent " " rest))
      | DocGroup d -> simpleLayout d rest column indent

  sort Doc =
    | DocNil
    | DocCons (Doc * Doc)
    | DocText String
    | DocNest (Integer * Doc)
    | DocBreak String
    | DocGroup Doc
  
  op ppCons : Doc -> Doc -> Doc
  % def ppCons x y = DocCons (x,y)  % original
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
  
  op ppLayout : SDoc -> String
  def ppLayout doc =
    let def replicate (cnt:Integer) str =
      if cnt = 0 then
        [""]
      else
        Cons (str, replicate (cnt - 1) str) in
    let def makeStringList doc =
      case doc of
        | SNil -> [""]
        | SText (s,d) -> Cons (s,makeStringList d)
        | SLine (indent,d) ->
               Cons (concatList (Cons ("\n", replicate indent " ")), makeStringList d) in
    concatList (makeStringList doc)
  
%     case doc of
%         SNil -> ""
%       | SText (s,d) -> s ^ (ppLayout d)
%       | SLine (indent,d) ->
%          let def replicate cnt str =
%            if cnt = 0 then
%              ""
%            else
%              str ++ (replicate (cnt - 1) str)
%            in
%              "\n" ++ (replicate indent " ") ++ (ppLayout d)
  
  op ppFits : Integer -> List (Integer * BreakMode * Doc) -> Boolean
  def ppFits w x =
    (w >= 0) &
    (case x of
       | [] -> true
       | (i,m,DocNil) :: z -> ppFits w z
       | (i,m,DocCons(x,y)) :: z -> ppFits w (Cons((i,m,x),Cons((i,m,y),z)))
       | (i,m,DocNest(j,x)) :: z -> ppFits w (Cons ((i+j,m,x),z))
       | (i,m,DocText(s)) :: z -> ppFits (w - (length s)) z
       | (i,Flat,DocBreak s) :: z -> ppFits (w - (length s)) z
       % | (i,Flat,DocBreak s) :: z -> false % ppFits (w - (length s)) z
       | (i,Break,DocBreak _) :: z -> true % impossible 
       | (i,m,DocGroup(x)) :: z -> ppFits w (Cons((i,Flat,x),z)))
  
  sort BreakMode =
    | Flat
    | Break
  
  op ppBest : Integer -> Integer -> List (Integer * BreakMode * Doc) -> SDoc
  def ppBest w k x = 
    case x of
      | [] -> SNil
      | (i,m,DocNil) :: z -> ppBest w k z
      | (i,m,DocCons(x,y)) :: z -> ppBest w k (Cons((i,m,x),Cons((i,m,y),z)))
      | (i,m,DocNest(j,x)) :: z -> ppBest w k (Cons((i+j,m,x),z))
      | (i,m,DocText s) :: z -> SText(s,ppBest w (k + (length s)) z)
      | (i,Flat,DocBreak s) :: z ->
          SText(s,ppBest w (k + (length s)) z)
      | (i,Break,DocBreak s) :: z -> SLine(i,ppBest w i z)
      | (i,m,DocGroup(x)) :: z ->
          if ppFits (w-k) (Cons((i,Flat,x),z)) then
            (ppBest w k (Cons((i,Flat,x),z)))
          else
            (ppBest w k (Cons((i,Break,x),z)))
  
  % let (^|) x y = match x,y with
  %   | DocNil, _ -> y
  %   | _, DocNil -> x
  %   | _, _ -> x ^^ break ^^ y
  % 
  % let binop left op right =
  %    group (nest 2 ( group (text left ^| text op) ^| text right ) )
  % 
  % let cond = binop "a" "==" "b"
  % let expr1 = binop "a" "<<" "2"
  % let expr2 = binop "a" "+" "b"
  % let ifthen c e1 e2 =
  %   group ( group (nest 2 (text "if" ^| c ))
  %   ^| group (nest 2 (text "then" ^| e1))
  %   ^| group (nest 2 (text "else" ^| e2)) )
  % 
  % let doc = ifthen cond expr1 expr2
  

  % def ppFormat doc = ppFormatWidth 80 doc
  def ppFormat doc = ppFormatWidth doc

  % op ppFormatWidth : Integer -> Doc -> String
  op ppFormatWidth : Doc -> String

  % def ppFormatWidth w  doc =
  %  ppLayout (ppBest w 0 [(0,Flat,DocGroup doc)])

  def ppFormatWidth doc =
    let (indent, strings) = simpleLayout doc [] 0 0 in
    concatList strings

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
  def ppNewline = ppBreak

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
\end{spec}
