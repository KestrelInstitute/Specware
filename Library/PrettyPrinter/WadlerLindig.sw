\section{The Wadler / Lindig pretty printer combinators}

\begin{spec}
WadlerLindig qualifying spec
  import /Library/Base

  sort Pretty = Doc

  sort Doc =
    | DocNil
    | DocCons (Doc * Doc)
    | DocText String
    | DocNest (Integer * Doc)
    | DocBreak String
    | DocGroup Doc
  
  op ppCons : Doc -> Doc -> Doc
  def ppCons x y = DocCons (x,y)
  
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
  
  op concatList : List String -> String

  op ppLayout : SDoc -> String
  def ppLayout doc =
    let def replicate cnt str =
      if cnt = 0 then
        [""]
      else
        Cons(str, replicate (cnt - 1) str) in
    let def makeStringList doc =
      case doc of
          SNil -> [""]
        | SText (s,d) -> Cons(s,(makeStringList d))
        | SLine (indent,d) ->
               Cons (concatList(Cons("\n", replicate indent " ")),
                    (makeStringList d)) in
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
  
  op ppFits : Integer -> List (Integer * Mode * Doc) -> Boolean
  def ppFits w x =
    (w >= 0) &
    (case x of
       | [] -> true
       | (i,m,DocNil) :: z -> ppFits w z
       | (i,m,DocCons(x,y)) :: z -> ppFits w (Cons((i,m,x),Cons((i,m,y),z)))
       | (i,m,DocNest(j,x)) :: z -> ppFits w (Cons ((i+j,m,x),z))
       | (i,m,DocText(s)) :: z -> ppFits (w - (length s)) z
       | (i,Flat,DocBreak s) :: z -> false % ppFits (w - (length s)) z
       | (i,Break,DocBreak _) :: z -> true % impossible 
       | (i,m,DocGroup(x)) :: z -> ppFits w (Cons((i,Flat,x),z)))
  
  sort Mode =
    | Flat
    | Break
  
  op ppBest : Integer -> Integer -> List (Integer * Mode * Doc) -> SDoc
  def ppBest w k x = 
    case x of
      | [] -> SNil
      | (i,m,DocNil) :: z -> ppBest w k z
      | (i,m,DocCons(x,y)) :: z -> ppBest w k (Cons((i,m,x),Cons((i,m,y),z)))
      | (i,m,DocNest(j,x)) :: z -> ppBest w k (Cons((i+j,m,x),z))
      | (i,m,DocText s) :: z -> SText(s,ppBest w (k + (length s)) z)
      | (i,Flat,DocBreak s) :: z -> SText(s,ppBest w (k + (length s)) z)
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
  
  op ppFormatWidth : Integer -> Doc -> String

  def ppFormatWidth w doc = ppLayout (ppBest w 0 [(0,Flat,DocGroup doc)])
  def ppFormat doc = ppFormatWidth 80 doc

  op ppAppend : Doc -> Doc -> Doc
  def ppAppend p1 p2 = ppCons p1 p2

  op ppIndent : Doc -> Doc
  def ppIndent p = ppNest 2 p

  op ppConcat : List Doc -> Doc
  def ppConcat l =
    case l of
        Nil ->  ppNil
      | (s::ss) -> ppCons s (ppConcat ss)

  op ppNewline : Doc
  def ppNewline = ppBreak

  op ppSep : Doc ->  List Doc -> Doc
  def ppSep sep l = 
    case l of
        Nil -> ppNil
      | s::Nil -> s
      | s::ss -> ppCons s (ppCons sep (ppSep sep ss))

%  let pretty w doc =
%    let sdoc = ppBest w 0 [0,Flat,DocGroup doc] in
%    let str = ppLayout sdoc in print_endline str
end
\end{spec}
