(* Copyright 2015 Kestrel Institute. See file LICENSE for license details *)


(**

Pretty Printer
Nikolaj Bjorner
David Espinosa
April 14, 1999

This is a standard combinator-style pretty printer.  There is a single
type Pretty of pretty-printed strings, and several constructors:

   op string      : String -> Pretty
   op blockNone   : Nat * List [Nat * Pretty] -> Pretty
   op blockAll    : Nat * List [Nat * Pretty] -> Pretty
   op blockFill   : Nat * List [Nat * Pretty] -> Pretty
   op blockLinear : Nat * List [Nat * Pretty] -> Pretty

Blocks take a number of extra newlines to insert at each break
(usually 0), and list of pairs of indentations and subprettys.

The type of block controls when breaks are inserted *between*
subprettys.

None means never  insert breaks.
All  means always insert breaks.

Fill means possibly insert breaks.  Each subpretty may or may not
have a break.

Linear means either All or None.  That is, either all breaks are
inserted or none are inserted.

The indentations are offsets from the starting column of the block.
The indentation of the first subpretty is always ignored.

Format maps a Pretty to a Text that fits within the specified width,
if at all possible.  A text can be rendered to a string, the terminal,
or a file.

**)
   
PrettyPrint qualifying spec

  import /Library/Legacy/Utilities/IO
  import /Library/Legacy/Utilities/System
  import /Library/Legacy/DataStructures/StringUtilities

  %% ========================================================================
  %%%% Interface

  type NatStrings = List (Nat * String)
  type Text  = List (Nat * NatStrings)
  type Pretty = Nat * (Nat * Text -> Text)
  type Line  = Nat * Pretty
  type Lines = List (Line)
  type Prettys = List (Pretty)

  %% ========================================================================

  op string : String -> Pretty
  op lengthString : Nat * String -> Pretty

  op blockNone   : Nat * Lines -> Pretty
  op blockAll    : Nat * Lines -> Pretty
  op blockFill   : Nat * Lines -> Pretty
  op blockLinear : Nat * Lines -> Pretty

  op format : Nat * Pretty -> Text

  op toString   : Text -> String
  op toTerminal : Text -> ()
  op toFile     : String * Text -> ()
  op appendFile : String * Text -> ()

  %% More convenient API funs

  op  prNum: Int -> Pretty
  def prNum n = prString(show n)

  def prString s = string s

  op  prConcat: List Pretty -> Pretty
  def prConcat l = prettysNone l

  op  prEmpty: Pretty
  def prEmpty = prConcat []

  op  prBreak: Nat -> List Pretty -> Pretty
  def prBreak n l = blockFill(0, (map (fn x -> (n, x)) l))

  op  prLinear: Nat -> List Pretty -> Pretty
  def prLinear n l = blockLinear(0, (map (fn x -> (n, x)) l))

  op  prLines: Nat -> List Pretty -> Pretty
  def prLines n l = blockAll(0, (map (fn x -> (n, x)) l))

  op  prBreakCat: Nat -> List (List Pretty) -> Pretty
  def prBreakCat n l = blockFill(0, (map (fn x -> (n, prConcat x)) l))

  op  prLinearCat: Nat -> List (List Pretty) -> Pretty
  def prLinearCat n l = blockLinear(0, (map (fn x -> (n, prConcat x)) l))

  op  prLinesCat: Nat -> List (List Pretty) -> Pretty
  def prLinesCat n l = blockAll(0, (map (fn x -> (n, prConcat x)) l))

  op  prSep: Nat -> (Nat * Lines -> Pretty) -> Pretty -> List Pretty -> Pretty
  def prSep n blockFn sep l =
    case l of
      | [] -> prEmpty
      | [p] -> p
      | p::r ->
        blockFn(0, Cons((0, p), map (fn x -> (n, prConcat [sep, x])) r))

  op  prPostSep: Nat -> (Nat * Lines -> Pretty) -> Pretty -> List Pretty -> Pretty
  def prPostSep n blockFn sep l =
    case l of
      | [] -> prEmpty
      | [p] -> p
      | _ ->
        blockFn(0, (map (fn x -> (n, prConcat [x, sep])) (butLast l)) ++ [(0, last l)])


  %% ========================================================================
  %%%% Implementation

  %%% Text

  %% Text is stored backwards: right to left, bottom to top.

  op emptyText () : Text = []

  op extend (length : Nat, string : String, text : Text) : Text = 
      case text
        of [] -> [(0, [(length,string)])]
         | Cons ((indent, strings), text) ->
           Cons ((indent, Cons ((length,string), strings)), text)
      

  %% Length of last line in text.

  op lengthStrings (strings : NatStrings) : Nat =
    foldl (fn (n, (l,s)) -> n + l) 0 strings

  op lengthLast (t : Text) : Nat =
    case t
      of [] -> 0 
       | (indent, strings):: _ -> indent + lengthStrings strings
    

  op blankLines (n : Nat, text : Text) : Text =
    if n <= 0 then
      text
    else
      Cons ((0, []), blankLines (n - 1, text))

  op addBreak (indent : Nat, newlines : Nat, text : Text) : Text =
      Cons ((indent, []), blankLines (newlines, text))

 
  %%% Pretty

  %% Width is the width of the pretty when placed entirely on a single
  %% line.

  op pretty (width : Nat, format : (Nat * Text -> Text)) : Pretty =
    (width, format)

  op widthPretty (p : Pretty) : Nat =
    case p of (width, _) -> width 

  op formatPretty (columns : Nat, p : Pretty, text : Text) : Text =
    case p of (_, format) -> format (columns, text) 

  op format (columns : Nat, p : Pretty) : Text =
    formatPretty (columns, p, emptyText ())

  op widthLine : Line -> Nat
  def widthLine (indent, pretty) = indent + widthPretty (pretty)

  op widthLines (lines : Lines) : Nat = 
      foldr (fn (line, num) -> widthLine line + num) 0 lines

  op formatLines
      (columns : Nat,
       lines : Lines,
       text  : Text,
       break : Nat * Pretty * Text -> Text) : Text = 
  let def formatRestLines (lines : Lines, text : Text) =
    case lines
      of [] -> text
       | Cons ((indent, pretty), lines) -> 
         formatRestLines (lines, break (indent, pretty, text))
    
%  measure length lines
  in
  case lines        % First line has no break.
   of [] -> text
    | Cons ((_, pretty), lines) -> 
      formatRestLines (lines, formatPretty (columns, pretty, text))
  

  op fits? (columns : Nat, width : Nat, text : Text) : Bool =
     lengthLast text + width <= columns

  def lengthString(l,s) = 
    pretty
     (l, fn (_,text) -> extend(l,s,text))

  def string s = lengthString(String.length s,s)

  op blockAll (newlines : Nat, lines : Lines) : Pretty =
    pretty
    (widthLines lines,
     fn (columns : Nat, text : Text) ->
       let start = lengthLast text in
       formatLines
       (columns, lines, text,
        fn (indent : Nat, pretty : Pretty, text : Text) ->
          formatPretty
            (columns, pretty,
             if lengthLast text - start - indent  < 1     % Don't break unless it gains more than 1 character
               then text
             else addBreak (start + indent, newlines, text))))

  op blockNone (_ (* newlines *) : Nat, lines : Lines) : Pretty =
    pretty
    (widthLines lines,
     fn (columns : Nat, text : Text) ->
       formatLines
       (columns, lines, text,
        fn (indent : Nat, pretty : Pretty, text : Text) ->
          formatPretty (columns, pretty, text)))

  op blockFill (newlines : Nat, lines : Lines) : Pretty =
    pretty
    (widthLines lines,
     fn (columns : Nat, text : Text) ->
       let start = lengthLast text in
       formatLines
       (columns, lines, text,
        fn (indent : Nat, pretty : Pretty, text : Text) ->
          formatPretty
          (columns, pretty,
           if fits? (columns, widthPretty pretty, text)
                || lengthLast text - start - indent  < 2     % Don't break unless it gains more than 1 character
           then text
           else addBreak (start + indent, newlines, text))))

  op blockLinear (newlines : Nat, lines : Lines) : Pretty =
    let width = widthLines lines in
    pretty (width,
            fn (columns : Nat, text : Text) ->
              if fits? (columns, width, text)
                then formatPretty (columns, blockNone (newlines, lines), text)
              else formatPretty (columns, blockAll  (newlines, lines), text))


  %%% Text output
  op blanks: Nat -> String
%% Defined in /Library/Legacy/Utilities/Handwritten/Lisp/IO.lisp  to avoid n-squared behavior
%  def blanks (n : Nat) : String = 
%    case n of
%      | 0 -> ""
%      | _ -> String.concat (" ", blanks (n - 1))
    

  op newlineString () : String = Char.show (Char.chr 10)

  op newlineAndBlanks (n : Nat) : String = 
     (newlineString () ^ blanks (n))

  op latexBlanks(n : Nat) : String = 
      if n = 0 then "" else
      "\\SWspace{" ^ Nat.show (6 * n) ^ "}"

  op latexNewlineAndBlanks(n : Nat) : String = 
      "\\\\[0.3em]" ^ newlineString() ^ latexBlanks(n)

  op  toStream : [a] Text * 
                     ((Nat * String) * a  -> a) * a * 
                     (Nat * a -> a) -> a

  def toStream (text, cont, base, newlineIndent) = 
      let def loop (text : Text, indent) = 
        case text
          of [] -> cont ((indent,blanks indent), base)
	   | (_, [(0,_)]) :: rest -> 
	     %% Empty line so ignore indent
             let head = loop (rest, 0) in
             let head = newlineIndent(indent,head) in
             head
           | (indent2, strings) :: rest -> 
             let head = loop (rest, indent2) in
             let head = foldr cont head strings in
             let head = newlineIndent(indent,head) in
             head
        
      in
        case text
          of [] -> base
           | (indent, strings) :: rest -> 
             let head = loop (rest, indent) in
             let head = foldr cont head strings in
             head
        
  %% A tail recursive version of toStream that processes text in the reverse order
  %% Shouldn't need two versions, but some calls would need to be rewritten to
  %% to handle the order reversal
  op toStreamT (text: Text, cont: Nat * String -> (), newlineIndent: Nat -> ()): () = 
      case reverse text
	of [] -> ()
	 | (_, strings) :: rest ->	% Indentation of first line ignored!
	   let _ = foldr (fn (x,_) -> cont x) () strings in
	   let _ = app (fn textel ->
			case textel of 
			  | (_, [(0,_)]) -> 
			    %% Empty line so ignore indent
			    newlineIndent(0)
			  | (indent2, strings) -> 
			  let _ = newlineIndent(indent2) in
			  foldr (fn (x,_) -> cont x) () strings)
		      rest
	   in cont (0,blanks 0)

   op toString (text : Text) : String =
       IO.withOutputToString
         (fn stream ->
            toStreamT (text,
		       fn (_,string) -> streamWriter(stream,string),
		       fn (n) -> (streamWriter(stream,newlineString());
                                  streamWriter(stream,blanks n))))
%% This is much less efficient (n**2 instead of n) 
%       toStream (text, 
%                 fn ((_,s1),s2) -> s2 ^ s1, 
%                 "",
%                 fn (n,s) -> s ^ newlineAndBlanks n)

   op toLatexString (text : Text) : String = 
       IO.withOutputToString
         (fn stream ->
            toStreamT (text,
		       fn (_,string) -> streamWriter(stream,string),
		       fn (n) -> streamWriter(stream,latexNewlineAndBlanks n)))
%% This is much less efficient (n**2 instead of n)
%       toStream (text, 
%                 fn ((_,s1),s2) -> s2 ^ s1,
%                 "",
%                 fn (n,s) -> s ^ latexNewlineAndBlanks n)

   op toTerminal (text : Text) : () = 
       toStreamT (text, 
		  fn (_,s) -> toScreen s, 
		  fn (n) -> (toScreen (newlineString());
                             toScreen (blanks n)))

   def streamWriter (stream, string) =
     IO.format1 (stream, "~A", string)

   op  toFileWithNewline : String * Text * (Nat -> String) -> ()

   def toFileWithNewline (fileName, text, newlineIndent) =
     IO.withOpenFileForWrite
       (fileName,
        fn stream ->
            toStreamT (text,
		       fn (_,string) -> streamWriter(stream,string),
		       fn (n) -> streamWriter(stream,newlineIndent n)))

%
% Pretty printer for accumulating path indexing.
% Each %( )% pair corresponds to a highlight point.
% The structure of these are recorded in a PathStack
% that is returned by the function call.
%
   type PathTree = String * Nat * Nat * Bool * List PathTree
   type PathStack = List PathTree

   op markPretty : Nat * Pretty -> Pretty
   def markPretty(uniqueId,p) = 
       prettysNone ([lengthString(0,"%("),
                     lengthString(0,Nat.show uniqueId),
                     p,
                     lengthString(0,"%)")])

   op markLines : Nat * Lines -> Lines
   def markLines(uniqueId,p) = 
       [(0,lengthString(0,"%(")),
        (0,lengthString(0,Nat.show uniqueId))] ++
        p
        ++
        [(0,lengthString(0,"%)"))]

    op printInt(i:Int): String = show i

   op buttonPretty : Bool * Int * Pretty * Bool -> Pretty
   def buttonPretty(enabled,number,p,sos?) = 
       let string = show enabled^":"^printInt number^":"^show sos? in
       prettysNone ([lengthString(0,"%["),lengthString(0,string),p])


   op shift : String * Nat * PathStack -> PathStack
   def shift (id,pos1,stack) = Cons((id,pos1,0,false,[]),stack)

   op insertElem (elem: PathTree, (id,pos1,pos2,closed,elems): PathTree): PathTree = 
       (id,pos1,pos2,closed,Cons(elem,elems))

   % Make the top-most element of the stack a child of the 
   % second to top-most element, unless the second to top-most
   % element has already been "closed". In this case the top-most
   % is also closed.
   def reduce(pos2,stack:PathStack) = 
       case stack
         of (id1,pos1,_,_,elems1)::elem2::stack -> 
            let elem = (id1,pos1,pos2,true,elems1) in
            let (_,_,_,closed,_) = elem2 in
            if ~closed
                then Cons(insertElem(elem,elem2),stack)
            else Cons(elem,Cons(elem2,stack))
          | [(id,pos1,_,_,elems)] -> [(id,pos1,pos2,true,elems)]
          | _ -> stack


   op toStringWithPathIndexing (text : Text) : String = 
       let
           def appendString(length,s,{charPos,stack,readId?,axiom?,string}) = 
               if readId?
                  then 
                  if axiom?
                     then
                     let [enabled,value,sos?] = 
                         StringUtilities.tokens
                           (fn | #: -> true | _ -> false) s
                     in
                     let enabled = 
                         case enabled of "true" -> "t" | _ -> "nil"
                     in
                     let sos? = 
                         case sos? of "true" -> "t" | _ -> "nil"
                     in
                     {charPos = charPos,
                      stack = stack,
                      readId? = false,
                      axiom? = false,
                      string = string^
        "\\\") (theorem-widget "^value^" "^enabled^" "^sos?^")"^
        "(widget-insert \\\""
                }
                  else
                  {charPos = 0,
                   stack   = shift(s,charPos,stack),
                   readId? = false,
                   axiom? = false,
                   string = string}
               else
               case s
                 of "%(" -> 
                    {charPos = charPos,
                     stack   = stack,
                     readId? = true,
                     axiom? = false,
                     string = string}
                  | "%)" -> 
                    {charPos = 0,
                     stack   = reduce(charPos,stack),
                     readId? = false,
                     axiom? = false,
                     string = string}
                  | "%[" -> 
                    {charPos = charPos  + 1 ,
                     stack = stack,
                     readId? = true,
                     axiom? = true,
                     string = string}
                  | _ -> 
                    ({charPos = charPos + length,
                      stack = stack,
                      axiom? = false,
                      readId? = false,
                      string = string^
                               (String.translate (fn | #" -> "\\\\\\\"" | ch -> Char.show ch) s)})
       in
       let {charPos,stack,readId?,axiom?,string} =
                  toStream (text,
                      fn ((length,string),context) ->
                        appendString(length,string,context),
                      {charPos = 0,stack = [],readId? = false,
                       axiom? = false,string = ""},
                      fn (n,{charPos,stack,axiom?,readId?,string}) -> 
                        ({charPos = charPos + n + 1,
                          stack = stack,
                          readId? = readId?,
                          axiom? = axiom?,
                          string = string ^newlineAndBlanks n}))
       in
       let tree = "(mspe-add-extents '(" ^ treesToString stack ^ "))" in
       "(insert-mouse-sensitive-spec \"(progn (let ((pt (point))) (widget-insert \\\""^string^" \\\") (goto-char pt)) "^ tree^ ")\")"


   op toFileWithPathIndexing (fileName : String, text : Text) : PathStack = 
       let
           def appendString(stream,length,s,{charPos,stack,axiom?,readId?}) = 
               if readId?
                  then 
                 if axiom?
                    then
                    {charPos = charPos,
                     stack = stack,
                     readId? = false,
                     axiom? = false}
                 else
                  {charPos = 0,
                   stack   = shift(s,charPos,stack),
                   axiom? = false,
                   readId? = false}
               else
               case s
                 of "%(" -> 
                    {charPos = charPos,
                     stack   = stack,
                     axiom? = false,
                     readId? = true}
                  | "%)" -> 
                    {charPos = 0,
                     stack   = reduce(charPos,stack),
                     axiom? = false,
                     readId? = false}
                  | "%[" -> 
                    {charPos = charPos,
                     stack = stack,
                     axiom? = true,
                     readId? = true}
                  | _ -> 
                    (streamWriter(stream,s);
                     {charPos = charPos + length,
                      stack = stack,
                      axiom? = false,
                      readId? = false})
       in
       let
          def writeFun stream =
                  toStream (text,
                      fn ((length,string),context) ->
                        appendString(stream,length,string,context),
                      {charPos = 0,stack = [],axiom? = false,readId? = false},
                      fn (n,{charPos,stack,axiom?,readId?}) -> 
                        (streamWriter(stream,newlineAndBlanks n);
                         {charPos = charPos + n + 1,
                          stack = stack,
                          axiom? = axiom?,
                          readId? = readId?}))
       in
       let {charPos,stack,readId?,axiom?} =
           IO.withOpenFileForWrite (fileName, writeFun) in
       stack

   def treeToString((id,startPos,endPos,_(* closed *),subtrees):PathTree) = 
       "(" ^ id ^
       " " ^ Nat.show startPos ^
       treesToString(subtrees) ^
       " " ^ id ^
       " " ^ Nat.show endPos ^ ")"
   def treesToString(trees) = 
       case trees 
         of [] -> ""
          | tree::trees -> treesToString(trees) ^ " " ^ treeToString(tree)

          

   op toPathFiles(fileName : String,pathFileName: String, text : Text) : () = 
       let trees = toFileWithPathIndexing(fileName,text) in
       let 
           def writeFun stream = 
           streamWriter(stream,"(mspe-add-extents '(" ^ treesToString trees ^ "))")
       in
       let _ = IO.withOpenFileForWrite (pathFileName, writeFun) in
       ()      

   op appendFileWithNewline (fileName : String, text : Text, newlineIndent : Nat -> String) : () =
       let def writeFun stream =
            toStreamT (text,
		       fn (_,string) -> streamWriter(stream,string),
		       fn (n) -> streamWriter(stream,newlineIndent n)) in
       let _ = IO.withOpenFileForAppend (fileName, writeFun) in
       ()

  op toFile (fileName : String, text : Text) : () =
      toFileWithNewline(fileName,text,newlineAndBlanks)

  op toLatexFile(fileName : String, text : Text) : () =
      toFileWithNewline(fileName,text,latexNewlineAndBlanks)

  op appendFile (fileName : String, text : Text) : () =
      appendFileWithNewline(fileName,text,newlineAndBlanks)

  op appendLatexFile(fileName : String, text : Text) : () =
      appendFileWithNewline(fileName,text,latexNewlineAndBlanks)
 
      

  %%% For compatibility:

  type Style = | None | All | Linear | Fill 

  op block (style : Style, newlines : Nat, lines : Lines) : Pretty =
    case style
      of None   -> blockNone   (newlines, lines)
       | All    -> blockAll    (newlines, lines)
       | Fill   -> blockFill   (newlines, lines)
       | Linear -> blockLinear (newlines, lines)
    


  %%%% Utility functions

  def prettysBlock block ps =
      block (0, map (fn p -> (0, p)) ps)

  def prettysNone ps = 
      prettysBlock blockNone ps

  def prettysAll ps =
      prettysBlock blockAll ps

  def prettysLinear ps =
      prettysBlock blockLinear ps

  def prettysFill ps =
      prettysBlock blockFill ps

  def prettys ps = prettysNone ps

  def lines   ps = prettysAll  ps

  def emptyPretty () : Pretty = string ""

  op newline: () -> Pretty
  def newline () : Pretty = 
      prettysAll [emptyPretty (), emptyPretty ()]

  op  strings : List(String) -> Pretty

  def strings ss =
      prettysNone (map string ss)

  op addSeparator (sep : Pretty) (ps : Prettys) : Prettys =
    case ps
      of []  -> []
       | [p] -> [p]
       | p :: ps -> 
         Cons(prettysNone [p, sep], addSeparator sep ps)
    

  op prettysBlockDelim
     : (Prettys -> Pretty) -> String * String * String ->
       Prettys -> Pretty

  def prettysBlockDelim prettysBlock (left, sep, right) ps =
    prettysNone
      [string left,
       prettysBlock (addSeparator (string sep) ps),
       string right]

  def prettysNoneDelim delims ps =
    prettysBlockDelim prettysNone delims ps

  def prettysAllDelim delims ps =
    prettysBlockDelim prettysAll delims ps

  def prettysLinearDelim delims ps =
    prettysBlockDelim prettysLinear delims ps

  def prettysFillDelim delims ps =
    prettysBlockDelim prettysFill delims ps

  op ppList : [T] (T -> Pretty) -> 
                 (String * String * String) -> 
                 List T -> Pretty

  def ppList f (left, sep, right) ts =
    prettysLinearDelim (left, sep, right) (map f ts)

  (*

  % ppList ppFun (leftDelimitor,separator,rightDelimitor) stream list
  % pretty prints elements from list using ppFun, enclosing the list using the 
  % delimitors, and separating the elements using the separator.

  def ppList ppfun (left,sep,right) list = 
      case list
        of [] -> strings [left,right]

         | Cons(e,es) -> 
           blockLinear(0,
           [(0,string left),
            (0,ppfun e)] ++
           (foldr (fn (e,l) ->
                 Cons((0,string sep),
                 Cons((1,ppfun e),l)))
                 [(0,string right)]
                 es))         
               
  *)
endspec

(*
spec TestPrettyPrint =

 import PrettyPrint

 def test () = 
     let pretty = 
         blockLinear
         (0,
          [(99, string "hello"),
           (6, blockAll
               (1,
                [(99, string "David "),
                 (2,  string "Doug "),
                 (4,  string "Dusko ")])),
           (2, string "world")])
     in
     let text = format (25, pretty) in (
       toTerminal text;
       toFile ("test.txt", text)
       (* toString text *)
     )

end-spec
*)

(**

Miscellaneous comments
----------------------

To format a block, we decide whether to insert breaks in the current
block or to format the subprettys in smaller widths.

The "outer" strategy inserts breaks at the outside first, giving inner
blocks maximal space.

The "inner" strategy inserts breaks at the inside first, giving outer
blocks maximal space.

Ideally, we would maximize a "prettiness" metric, but this is a poor
man's pretty printer, so we follow the outer strategy.

Note that pretty-printing isn't symmetric horizontally and verically.
For example, we can't transpose this layout

  AAAA
  BBB

to get this one:

  AB
  AB
  AB
  A

because the first "linearizes" to AAAABBB while the second linearizes
to ABABABA since we read left-to-right, top-to-bottom.

Therefore the inner strategy doesn't really make sense, since if we
format AAA AAA AAA BBB BBB BBB CCC CCC CCC, we necessarily obtain
layouts like

  AAA
  AAA
  AAA BBB
      BBB
      BBB CCC
          CCC
          CCC

instead of

  AAA BBB CCC
  AAA BBB CCC
  AAA BBB CCC

because the latter linearizes incorrectly.  But the former isn't very
pretty, while the outer strategy yields

  AAA AAA AAA
  BBB BBB BBB
  CCC CCC CCC

which is fine.

**)
