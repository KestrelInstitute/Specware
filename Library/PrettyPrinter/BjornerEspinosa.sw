
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
   
PrettyPrint qualifying spec {

  import /Library/Legacy/Utilities/IO
  import /Library/Legacy/DataStructures/StringUtilities
  % import List

  %% ========================================================================
  %%%% Interface

  sort NatStrings = List (Nat * String)
  sort Text  = List (Nat * NatStrings)
  sort Pretty = Nat * (Nat * Text -> Text)
  sort Line  = Nat * Pretty
  sort Lines = List (Line)
  sort Prettys = List (Pretty)

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


  %% ========================================================================
  %%%% Implementation

  %%% Text

  %% Text is stored backwards: right to left, bottom to top.

  def emptyText () : Text = []

  def extend (length : Nat, string : String, text : Text) : Text = 
      case text
        of [] -> [(0, [(length,string)])]
         | Cons ((indent, strings), text) ->
           Cons ((indent, Cons ((length,string), strings)), text)
      

  %% Length of last line in text.

  def lengthStrings (strings : NatStrings) : Nat =
    foldr (fn ((l,s), n) -> n + l) 0 strings

  def lengthLast (t : Text) : Nat =
    case t
      of [] -> 0 
       | (indent, strings):: _ -> indent + lengthStrings strings
    

  def blankLines (n : Nat, text : Text) : Text =
    if n <= 0 then
      text
    else
      Cons ((0, []), blankLines (n - 1, text))

  def addBreak (indent : Nat, newlines : Nat, text : Text) : Text =
      Cons ((indent, []), blankLines (newlines, text))

 
  %%% Pretty

  %% Width is the width of the pretty when placed entirely on a single
  %% line.

  def pretty (width : Nat, format : (Nat * Text -> Text)) : Pretty =
    (width, format)

  def widthPretty (p : Pretty) : Nat =
    case p of (width, _) -> width 

  def formatPretty (columns : Nat, p : Pretty, text : Text) : Text =
    case p of (_, format) -> format (columns, text) 

  def format (columns : Nat, p : Pretty) : Text =
    formatPretty (columns, p, emptyText ())

  op widthLine : Line -> Nat
  def widthLine (indent, pretty) = indent + widthPretty (pretty)

  def widthLines (lines : Lines) : Nat = 
      foldr (fn (line, num) -> widthLine line + num) 0 lines

  def formatLines
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
  

  def fits? (columns : Nat, width : Nat, text : Text) : Boolean =
     lengthLast text + width <= columns

  def lengthString(l,s) = 
    pretty
     (l, fn (_,text) -> extend(l,s,text))

  def string s = lengthString(String.length s,s)

  def blockAll (newlines : Nat, lines : Lines) : Pretty =
    pretty
    (widthLines lines,
     fn (columns : Nat, text : Text) ->
       let start = lengthLast text in
       formatLines
       (columns, lines, text,
        fn (indent : Nat, pretty : Pretty, text : Text) ->
          formatPretty
          (columns, pretty,
           addBreak (start + indent, newlines, text))))

  def blockNone (_ (* newlines *) : Nat, lines : Lines) : Pretty =
    pretty
    (widthLines lines,
     fn (columns : Nat, text : Text) ->
       formatLines
       (columns, lines, text,
        fn (indent : Nat, pretty : Pretty, text : Text) ->
          formatPretty (columns, pretty, text)))

  def blockFill (newlines : Nat, lines : Lines) : Pretty =
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
           then text
           else addBreak (start + indent, newlines, text))))

  def blockLinear (newlines : Nat, lines : Lines) : Pretty =
    let width = widthLines lines in
    pretty
    (width,
     fn (columns : Nat, text : Text) ->
       if fits? (columns, width, text)
       then formatPretty (columns, blockNone (newlines, lines), text)
       else formatPretty (columns, blockAll  (newlines, lines), text))


  %%% Text output

  def blanks (n : Nat) : String = 
    case n of
      | 0 -> ""
      | _ -> String.concat (" ", blanks (n - 1))
    

  def newlineString () : String = Char.toString (Char.chr 10)

  def newlineAndBlanks (n : Nat) : String = 
     (newlineString () ^ blanks (n))

  def latexBlanks(n : Nat) : String = 
      if n = 0 then "" else
      "\\SWspace{" ^ Nat.toString (6 * n) ^ "}"

  def latexNewlineAndBlanks(n : Nat) : String = 
      "\\\\[0.3em]" ^ newlineString() ^ latexBlanks(n)

  op  toStream : fa(a) Text * 
                     ((Nat * String) * a  -> a) * a * 
                     (Nat * a -> a) -> a

  def toStream (text, cont, base, newlineAndBlanks) = 
      let def loop (text : Text, indent) = 
        case text
          of [] -> cont ((indent,blanks indent), base)
           | (indent2, strings) :: rest -> 
             let head = loop (rest, indent2) in
             let head = foldr cont head strings in
             let head = newlineAndBlanks(indent,head) in
             head
        
      in
        case text
          of [] -> base
           | (indent, strings) :: rest -> 
             let head = loop (rest, indent) in
             let head = foldr cont head strings in
             head
        

   def toString (text : Text) : String = 
       toStream (text, 
                 fn ((_,s1),s2) -> s2 ^ s1, 
                 "",
                 fn (n,s) -> s ^ newlineAndBlanks n)

   def toLatexString (text : Text) : String = 
       toStream (text, 
                 fn ((_,s1),s2) -> s2 ^ s1,
                 "",
                 fn (n,s) -> s ^ latexNewlineAndBlanks n)

   def toTerminal (text : Text) : () = 
       toStream (text, 
                 fn ((_,s), ()) -> toScreen s, 
                 (),
                 fn (n,()) -> toScreen (newlineAndBlanks n))

   def streamWriter (stream, string) =
     IO.format1 (stream, "~A", string)

   op  toFileWithNewline : String * Text * (Nat -> String) -> ()

   def toFileWithNewline (fileName, text, newlineAndBlanks) =
     IO.withOpenFileForWrite
       (fileName,
        fn stream ->
            toStream (text,
                      fn ((_,string), ()) -> streamWriter(stream,string),
                      (),
                      fn (n,()) -> streamWriter(stream,newlineAndBlanks n)))

%
% Pretty printer for accumulating path indexing.
% Each %( )% pair corresponds to a highlight point.
% The structure of these are recorded in a PathStack
% that is returned by the function call.
%
   sort PathTree = String * Nat * Nat * Boolean * List PathTree
   sort PathStack = List PathTree

   op markPretty : Nat * Pretty -> Pretty
   def markPretty(uniqueId,p) = 
       prettysNone ([lengthString(0,"%("),
                     lengthString(0,Nat.toString uniqueId),
                     p,
                     lengthString(0,"%)")])

   op markLines : Nat * Lines -> Lines
   def markLines(uniqueId,p) = 
       [(0,lengthString(0,"%(")),
        (0,lengthString(0,Nat.toString uniqueId))] List.@
        p
        List.@
        [(0,lengthString(0,"%)"))]

    def printInt(i:Integer) = Integer.toString i

   op buttonPretty : Boolean * Integer * Pretty * Boolean -> Pretty
   def buttonPretty(enabled,number,p,sos?) = 
       let string = Boolean.toString enabled^":"^printInt number^":"^Boolean.toString sos? in
       prettysNone ([lengthString(0,"%["),lengthString(0,string),p])


   op shift : String * Nat * PathStack -> PathStack
   def shift (id,pos1,stack) = List.cons((id,pos1,0,false,[]),stack)

   def insertElem (elem,(id,pos1,pos2,closed,elems)) = 
       (id,pos1,pos2,closed,List.cons(elem,elems))

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
                then List.cons(insertElem(elem,elem2),stack)
            else List.cons(elem,List.cons(elem2,stack))
          | [(id,pos1,_,_,elems)] -> [(id,pos1,pos2,true,elems)]
          | _ -> stack


   def toStringWithPathIndexing (text : Text) : String = 
       let
           def appendString(length,s,{charPos,stack,readId?,axiom?,string}) = 
               if readId?
                  then 
                  if axiom?
                     then
                     let [enabled,value,sos?] = 
                         StringUtilities.tokens
                           (fn #: -> true | _ -> false) s
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
                               (String.translate (fn #" -> "\\\\\\\"" | ch -> Char.toString ch) s)})
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


   def toFileWithPathIndexing (fileName : String, text : Text) : PathStack = 
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
       " " ^ Nat.toString startPos ^
       treesToString(subtrees) ^
       " " ^ id ^
       " " ^ Nat.toString endPos ^ ")"
   def treesToString(trees) = 
       case trees 
         of [] -> ""
          | tree::trees -> treesToString(trees) ^ " " ^ treeToString(tree)

          

   def toPathFiles(fileName : String,pathFileName: String, text : Text) : () = 
       let trees = toFileWithPathIndexing(fileName,text) in
       let 
           def writeFun stream = 
           streamWriter(stream,"(mspe-add-extents '(" ^ treesToString trees ^ "))")
       in
       let _ = IO.withOpenFileForWrite (pathFileName, writeFun) in
       ()      

   def appendFileWithNewline (fileName : String, text : Text, newlineAndBlanks : Nat -> String) : () =
       let def writeFun stream =
            toStream (text,
                      fn ((_,string), ()) -> streamWriter(stream,string),
                      (),
                      fn (n,()) -> streamWriter(stream,newlineAndBlanks n)) in
       let _ = IO.withOpenFileForAppend (fileName, writeFun) in
       ()

  def toFile (fileName : String, text : Text) : () =
      toFileWithNewline(fileName,text,newlineAndBlanks)

  def toLatexFile(fileName : String, text : Text) : () =
      toFileWithNewline(fileName,text,latexNewlineAndBlanks)

  def appendFile (fileName : String, text : Text) : () =
      appendFileWithNewline(fileName,text,newlineAndBlanks)

  def appendLatexFile(fileName : String, text : Text) : () =
      appendFileWithNewline(fileName,text,latexNewlineAndBlanks)
 
      

  %%% For compatibility:

  sort Style = | None | All | Linear | Fill 

  def block (style : Style, newlines : Nat, lines : Lines) : Pretty =
    case style
      of None   -> blockNone   (newlines, lines)
       | All    -> blockAll    (newlines, lines)
       | Fill   -> blockFill   (newlines, lines)
       | Linear -> blockLinear (newlines, lines)
    


  %%%% Utility functions

  def prettysBlock block ps =
      block (0, List.map (fn p -> (0, p)) ps)

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
      prettysNone (List.map string ss)

  def addSeparator (sep : Pretty) (ps : Prettys) : Prettys =
    case ps
      of []  -> []
       | [p] -> [p]
       | p :: ps -> 
         List.cons(prettysNone [p, sep], addSeparator sep ps)
    

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

  op ppList : fa(T) (T -> Pretty) -> 
                 (String * String * String) -> 
                 List T -> Pretty

  def ppList f (left, sep, right) ts =
    prettysLinearDelim (left, sep, right) (List.map f ts)

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
            (0,ppfun e)] List.++
           (List.foldr (fn (e,l) ->
                 Cons((0,string sep),
                 Cons((1,ppfun e),l)))
                 [(0,string right)]
                 es))         
               
  *)
}

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
