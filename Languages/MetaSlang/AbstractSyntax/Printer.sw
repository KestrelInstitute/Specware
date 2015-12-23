(* Copyright 2015 Kestrel Institute. See file LICENSE for license details *)

% Synchronized with version 1.1.1.1 of SW4/Languages/MetaSlang/Printer/ATermPrinter.sl

(*
 * MetaSlang pretty printer.
 * This module contains utilities for printing terms, types, and patterns to 
 * strings, files, or standard out.
 *
 * Formats supported are:
 *
 *  - Ascii
 *  - HTML
 *  - LaTeX
 *  - pdfLaTeX

 *  - highligthable Ascii
 *)

AnnTermPrinter qualifying spec
  import AnnTerm
  import /Library/PrettyPrinter/BjornerEspinosa
  import /Library/Legacy/DataStructures/ListUtilities
  import /Library/Legacy/DataStructures/StringMapSplay
  import /Library/Legacy/Utilities/State

  %% ========================================================================

  %% Dispatchable pretty printers.
  type ATermPrinter = 
   {
    ppOpId             : QualifiedId -> Pretty,
    ppPOpId            : QualifiedId -> Pretty,
    ppTypeId           : QualifiedId -> Pretty,
    ppPTypeId          : QualifiedId -> Pretty,
    ppDefaultQualifier : String -> Pretty,
    fromString         : String -> Pretty,
    ppOp               : String -> Pretty,
    ppType             : String -> Pretty,
    ppFormulaDesc      : String -> Pretty,
    Spec               : Pretty,
    EndSpec            : Pretty,
    Module             : Pretty,
    EndModule          : Pretty,
    Type               : Pretty,
    Axiom              : Pretty,
    Theorem            : Pretty,
    Conjecture         : Pretty,
    Is                 : Pretty,
    Import             : Pretty,
    Op                 : Pretty,
    Of                 : Pretty,
    Def                : Pretty,
    Refine             : Pretty,
    Arrow              : Pretty,
    LetDeclsAnd        : Pretty,    % ?? see Specware4/Languages/MetaSlang/Specs/Printer.sw
    Fa                 : Pretty,
    Ex                 : Pretty,
    Ex1                : Pretty,
    Where              : Pretty,
    Let                : Pretty,
    In                 : Pretty,
    Not                : Pretty,
    And                : Pretty,
    Or                 : Pretty,
    Implies            : Pretty,
    Iff                : Pretty,
    Equals             : Pretty,
    NotEquals          : Pretty,
    DefEquals          : Pretty,
    Product            : Pretty,
    Bar                : Pretty,
    Underscore         : Pretty,
    Lambda             : Pretty,
    The                : Pretty,
    If                 : Pretty,
    Then               : Pretty,
    Else               : Pretty,
    Case               : Pretty,
    Empty              : Pretty,
    Comma              : Pretty,
    LP                 : Pretty,
    RP                 : Pretty,
    LCurly             : Pretty,
    RCurly             : Pretty,
    LBrack             : Pretty,
    RBrack             : Pretty
   }

  %% ========================================================================

  op ppList : [T] (T -> Pretty) -> (Pretty * Pretty * Pretty) -> List T -> Pretty

  op ppListPath : [T] List Nat -> (List Nat  * T -> Pretty) -> (Pretty * Pretty * Pretty) -> List T -> Pretty

  %% ========================================================================

  op alwaysPrintQualifiers?: Bool = false

  def ppAsciiId (Qualified (qualifier, id) : QualifiedId) = 
   string (if ~alwaysPrintQualifiers?
             && (qualifier = UnQualified  ||
                   %% TODO:  What if there is an unqualified Nat as well as Nat.Nat ?
                   %%        Perhaps that should be disallowed. (It is now).
                   qualifier = "Nat"        || 
                   qualifier = "String"     ||
                   qualifier = "Integer"    ||
                   qualifier = "IntegerAux" || 
                   qualifier = "General"    ||
                   qualifier = "Char"       ||
                   qualifier = "List"       ||
                   qualifier = "Bool")
             then 
               id
           else
             qualifier^"."^id)

  %% def ppAsciiPId (idi : IdInfo) =
  %%     let def f idi =
  %%         case idi
  %%           of []       -> ""
  %%            | [id]     -> id
  %%            | id::idi2 -> id^"."^(f idi2) in
  %%     string (f idi)

  def asciiPrinter : ATermPrinter = 
   {
    ppOpId             = ppAsciiId,
    ppPOpId            = ppAsciiId,
    ppTypeId           = ppAsciiId,
    ppPTypeId          = ppAsciiId,
    ppDefaultQualifier = string,
    fromString         = string,
    ppOp               = string,
    ppType             = string,
    ppFormulaDesc      = string,
    Spec               = string "spec ",
    EndSpec            = string "end-spec",
    Module             = string "module ",
    EndModule          = string "end-module",
    Type               = string "type",
    Axiom              = string "axiom",
    Theorem            = string "theorem",
    Conjecture         = string "conjecture",
    Is                 = string "is",
    Import             = string "import ",
    Op                 = string "op ",
    Of                 = string "of ",
    Def                = string "def ",
    Refine             = string "refine ",
    Arrow              = string " -> ",
    Let                = string "let ",
    In                 = string "in ",
    Not                = string "~",
    And                = string "&&",
    Or                 = string "||",
    Implies            = string "=>",
    Iff                = string "<=>",
    Equals             = string "=",
    NotEquals          = string "~=",
    DefEquals          = string "=" ,
    LetDeclsAnd        = string " and ",  
    Fa                 = string "fa",
    Ex                 = string "ex",
    Ex1                = string "ex1",
    Where              = string "where",
    Product            = string " * ",
    Bar                = string " | ",
    Underscore         = string "_",
    Lambda             = string "fn ",
    The                = string "the ",
    If                 = string "if ",
    Then               = string " then ",
    Else               = string "else ",
    Case               = string "case ",
    Empty              = string "",
    Comma              = string ", ",
    LCurly             = string "{",
    RCurly             = string "}",
    LBrack             = string "[",
    RBrack             = string "]",
    LP                 = string "(",
    RP                 = string ")"
   } 


  def XSymbolPrinter : ATermPrinter = 
   {
    ppOpId             = ppAsciiId,
    ppPOpId            = ppAsciiId,
    ppTypeId           = ppAsciiId,
    ppPTypeId          = ppAsciiId,
    ppDefaultQualifier = string,
    fromString         = string,
    ppOp               = string,
    ppType             = string,
    ppFormulaDesc      = string,
    Spec               = string "spec ",
    EndSpec            = string "end-spec",
    Module             = string "module ",
    EndModule          = string "end-module",
    Type               = string "type",
    Axiom              = string "axiom",
    Theorem            = string "theorem",
    Conjecture         = string "conjecture",
    Is                 = string "is",
    Import             = string "import ",
    Op                 = string "op ",
    Of                 = string "of ",
    Def                = string "def ",
    Refine             = string "refine ",
    Arrow              = lengthString(3, " \\_rightarrow "),
    Let                = string "let ",
    In                 = string "in ",
    Not                = lengthString(1, "\\_not"),
    And                = lengthString(1, "\\_and"),
    Or                 = lengthString(1, "\\_or"),
    Implies            = lengthString(1, "\\_Rightarrow"),
    Iff                = lengthString(3, " \\_Leftrightarrow "),
    Equals             = string "=",
    NotEquals          = lengthString(1, "\\_noteq"),
    DefEquals          = string "=" ,
    LetDeclsAnd        = string " and ",  
    Fa                 = lengthString(1, "\\_forall"),
    Ex                 = lengthString(1, "\\_exists"),
    Ex1                = string "ex1",
    Where              = string "where",
    Product            = lengthString(3, " \\_times "),
    Bar                = string " | ",
    Underscore         = string "_",
    Lambda             = lengthString(2, "\\_lambda "),
    The                = string "the ",
    If                 = string "if ",
    Then               = string " then ",
    Else               = string "else ",
    Case               = string "case ",
    Empty              = string "",
    Comma              = string ", ",
    LCurly             = string "{",
    RCurly             = string "}",
    LBrack             = string "[",
    RBrack             = string "]",
    LP                 = string "(",
    RP                 = string ")"
   } 


  def latexString s =
   if Char.isAlphaNum(s@0) then
     string s
   else 
     % Ad hoc treatment for LaTeX
     let s = String.translate (fn #^ -> "++" | ## -> "\\#" | #_ -> "\\_" | #& -> "\\&" | ch -> show ch) s in % "
     %   if String.sub(s,0) = #^
     %   then lengthString (2,"{\\tt ++}")
     %   else
     lengthString (String.length s,"\\mbox{{\\tt "^s^"}}")

  def latexNat s = 
   case s of
    | "*"   -> lengthString (1, "$\\cdot$") 
    | ">"   -> lengthString (1, "$>$")
    | "<"   -> lengthString (1, "$<$")
    | ">= " -> lengthString (1, "$\\geq$")
    | "<= " -> lengthString (1, "$\\leq$")
    | _     -> string s

  %  op latexInt: String -> Pretty
  def latexInt s = latexNat s

  def ppLatexId (Qualified (qualifier, id) : QualifiedId) = 
   if qualifier = UnQualified then
     latexString id 
   else
     case qualifier of
      | "Nat"     -> latexNat     id
      | "Integer" -> latexInt     id
      | _         -> prettysNone [string (qualifier^"."), latexString id]

  %%  def ppLatexPId (idi : IdInfo) = 
  %%      let def f idi =
  %%          case idi
  %%            of []       -> ""
  %%             | [id]     -> id
  %%             | id::idi2 -> id^"."^(f idi2) in
  %%      latexString (f idi)

  def latexPrinter : ATermPrinter = 
   {
    ppOpId             = ppLatexId,
    ppPOpId            = ppLatexId,
    ppTypeId           = ppLatexId,
    ppPTypeId          = ppLatexId,
    ppDefaultQualifier = string,
    ppOp               = latexString,
    ppType             = latexString,
    fromString         = latexString,
    ppFormulaDesc      = fn s -> lengthString (String.length s, "{\\tt "^s^"}" ),
    Spec               = lengthString (5, "\\SWspec\\ "          ),
    EndSpec            = lengthString (8, "\\SWendspec "         ),
    Module             = lengthString (7, "{\\bf module}\\ "     ),
    EndModule          = lengthString (9, "{\\bf end-module}\\ " ),
    Type               = lengthString (4, "\\SWtype "            ),
    Axiom              = lengthString (6, "\\SWaxiom\\ "         ),
    Theorem            = lengthString (8, "\\SWtheorem\\ "       ),
    Conjecture         = lengthString (8, "{\\bf conjecture}\\ " ),
    Is                 = lengthString (2, "{\\bf is}\\ "         ),
    Import             = lengthString (7, "\\SWimport "          ),
    Op                 = lengthString (2, "\\SWop "              ),
    Of                 = lengthString (3, "\\SWof "              ),
    Def                = lengthString (4, "\\SWdef "             ),
    Refine             = lengthString (7, "\\SWrefine "             ),
    Arrow              = lengthString (3, " $\\rightarrow$ "     ),
    Let                = lengthString (4, "\\SWlet\\ "           ),
    In                 = lengthString (3, "\\ {\\bf in}"         ),
    Not                = lengthString (1, "$\\neg$"              ),
    And                = lengthString (1, "$\\&$"                ),
    Or                 = lengthString (2, "\\SWor\\ "            ),
    Implies            = lengthString (1, "$\\Rightarrow$"       ),
    Iff                = lengthString (2, "$\\Leftrightarrow$"   ),
    Equals             = lengthString (3, "\\ = \\ "             ),
    NotEquals          = lengthString (1, "$\\neg$\\=\\"         ), % TODO: this is just a guess
    DefEquals          = lengthString (3, "\\ = \\ "             ),
    LetDeclsAnd        = lengthString (3, "\\ \\SWand\\ "        ),
    Fa                 = lengthString (1, "\\SWfa "              ),
    Ex                 = lengthString (1, "\\SWex "              ),
    Ex1                = lengthString (1, "\\SWexOne "           ),
    Where              = lengthString (4, "{\\bf where} "        ),
    Product            = lengthString (3,  " $\\times$ "         ), 
    RCurly             = lengthString (1, "$\\}$"                ),
    LCurly             = lengthString (1, "$\\{$"                ),
    Bar                = lengthString (3, " {\\tt |} "           ),
    Underscore         = lengthString (1, "{\\tt \\_}"           ),
    Lambda             = lengthString (3, "$\\lambda$ "          ),
    The                = lengthString (3, "\\SWthe "             ),
    If                 = lengthString (3, "\\SWif "              ),
    Then               = lengthString (6, " \\SWthen "           ),
    Else               = lengthString (5, "\\SWelse "            ),
    Case               = lengthString (6, "\\SWcase "            ),
    Comma              = string ", ",
    Empty              = string "",
    LBrack             = string "[",
    RBrack             = string "]",
    LP                 = string "(",
    RP                 = string ")"
   }

  def pdfId (spc, nameSpace) (Qualified (qualifier, id) : QualifiedId) = 
   if qualifier = UnQualified then
     prettysNone [lengthString (0, "\\pdfannotlink goto name {"^spc^":"^nameSpace^":"^id^"}"^newlineString()),
                  latexString id,
                  lengthString (0,"\\pdfendlink\\ ")
                 ]
   else
     case qualifier of
      | "Nat"     -> latexNat     id
      | "Integer" -> latexInt     id
      | _         -> prettysNone [lengthString (0,
                                                "\\pdfannotlink goto name {"^qualifier^":"^nameSpace^":"^id^"}"^
                                                newlineString()),
                                  string (qualifier^"."),
                                  latexString id,
                                  lengthString (0,"\\pdfendlink\\ ")]  

  def pdfIdDecl (spc, nameSpace) s = 
   prettysNone [lengthString (0,
                              "\\pdfdest name {"^spc^":"^nameSpace^":"^
                              s^"} fitbh%"^newlineString()),
                latexString s ]  
 
  %%  def pdfPId (_(* spc *),_(* nameSpace*)) (idi : IdInfo) =
  %%      let def f idi =
  %%          case idi
  %%            of []       -> ""
  %%             | [id]     -> id
  %%             | id::idi2 -> id^"."^(f idi2) in
  %%      latexString (f idi)

  def pdfPrinter (counter, spc : String) : ATermPrinter = 
   {
    ppOpId             = pdfId (spc, "Op"),
    ppPOpId            = pdfId (spc, "Op"),
    ppTypeId           = pdfId (spc, "Type"),
    ppPTypeId          = pdfId (spc, "Type"),
    ppDefaultQualifier = string,
    ppOp               = pdfIdDecl (spc,"Op"),
    ppType             = pdfIdDecl (spc,"Type"),
    ppFormulaDesc      = fn s -> (counter State.:= (State.! counter) + 1;
                                  prettysNone [lengthString (0,
                                                             "\\pdfdest num "^(Nat.show (State.! counter))^
                                                             " fitbh%"^newlineString()),
                                               lengthString (String.length s, "{\\tt "^s^"}" )
                                              ]),
    fromString         = latexString,
    Spec               = lengthString ( 5, "\\SWspec\\ "           ),
    EndSpec            = lengthString ( 8, "\\SWendspec "          ),
    Type               = lengthString ( 4, "\\SWtype "             ),
    Module             = lengthString ( 7, "{\\bf module}\\ "      ),
    EndModule          = lengthString ( 9, "{\\bf end-module}\\ "  ),
    Axiom              = lengthString ( 6, "\\SWaxiom\\ "          ),
    Theorem            = lengthString ( 8, "\\SWtheorem\\ "        ),
    Conjecture         = lengthString (11, "{\\bf conjecture}\\ "  ),
    Is                 = lengthString ( 2, "{\\bf is}\\ "          ),
    Import             = lengthString ( 7, "\\SWimport "           ),
    Op                 = lengthString ( 2, "\\SWop "               ),
    Of                 = lengthString ( 3, "\\SWof "               ),
    Def                = lengthString ( 4, "\\SWdef "              ),
    Refine             = lengthString ( 7, "\\SWrefine "              ),
    Arrow              = lengthString ( 3, " $\\rightarrow$ "      ),
    Let                = lengthString ( 4, "\\SWlet\\ "            ),
    In                 = lengthString ( 3, "\\ {\\bf in}"          ),
    Not                = lengthString ( 1, "$\\neg$"               ),
    And                = lengthString ( 1, "$\\&$"                 ),
    Or                 = lengthString ( 2, "\\SWor\\ "             ),
    Implies            = lengthString ( 1, "$\\Rightarrow$"        ),
    Iff                = lengthString ( 2, "$\\Leftrightarrow$"    ),
    Equals             = lengthString ( 3, "\\ = \\ "              ),
    NotEquals          = lengthString ( 1, "$\\neg$\\=\\"          ), % TODO: this is just a guess
    DefEquals          = lengthString ( 3, "\\ = \\ "              ),
    LetDeclsAnd        = lengthString ( 3, "\\ \\SWand\\ "         ),
    Fa                 = lengthString ( 1, "\\SWfa "               ),
    Ex                 = lengthString ( 1, "\\SWex "               ),
    Ex1                = lengthString ( 1, "\\SWexOne "            ),
    Where              = lengthString ( 4, "{\\bf where} "         ),
    Product            = lengthString ( 3,  " $\\times$ "          ), 
    RCurly             = lengthString ( 1, "$\\}$"                 ),
    LCurly             = lengthString ( 1, "$\\{$"                 ),
    Bar                = lengthString ( 3, " {\\tt |} "            ),
    Underscore         = lengthString ( 1, "{\\tt \\_}"            ),
    Lambda             = lengthString ( 3, "$\\lambda$ "           ),
    The                = lengthString ( 3, "\\SWthe "              ),
    If                 = lengthString ( 3, "\\SWif "               ),
    Then               = lengthString ( 6, " \\SWthen "            ),
    Else               = lengthString ( 5, "\\SWelse "             ),
    Case               = lengthString ( 6, "\\SWcase "             ),
    Comma              = string ", ",
    Empty              = string "",
    LBrack             = string "[",
    RBrack             = string "]",
    LP                 = string "(",
    RP                 = string ")"
   }
    
  def htmlPrinter () : ATermPrinter = 
   let nameMap : Ref (StringMap String) = Ref (StringMap.empty) in
   let counter : Ref Nat = Ref 0 in
   let def nameNumber s =
        case StringMap.find (State.! nameMap, s) of
         | None -> let n = State.! counter in
                   let ns = Nat.show n in
                   (nameMap State.:= StringMap.insert (State.! nameMap, s, ns);
                    counter State.:= n + 1; 
                    ns)
         | Some ns -> ns
   in                  
   let def ppQid (Qualified (qualifier, id) : QualifiedId) = 
        if qualifier = UnQualified then
          lengthString (String.length id,
                        "<a href = #"^nameNumber id^">"^id^"</a>") % "
        else
          case qualifier of
           | "Nat"     -> string id
           | _         -> prettysNone [lengthString (String.length qualifier,
                                                     "<a href = "^qualifier^".html>"^qualifier^"</a>"),
                                       string ".",
                                       string id]      
   %%            def ppPQid (idi : IdInfo) = 
   %%             let def f idi =
   %%                 case idi
   %%                   of []       -> ""
   %%                    | [id]     -> id
   %%                    | id::idi2 -> id^"."^(f idi2) in
   %%             string (f idi)  
   in   
   let 
     def ppOp s = 
      lengthString (String.length s,
                    "<a name = "^nameNumber(s)^">"^s^"</a>")
     def ppType s = 
      lengthString (String.length s,
                    "<a name = "^nameNumber(s)^">"^s^"</a>")
   in
   {
    ppOpId             = ppQid,
    ppPOpId            = ppQid,
    ppTypeId           = ppQid, 
    ppPTypeId          = ppQid, 
    ppDefaultQualifier = string,
    fromString         = string,
    ppOp               = ppOp,
    ppType             = ppType,
    ppFormulaDesc      = string,
    Spec               = lengthString ( 5, "<b>spec </b>"        ),
    EndSpec            = lengthString ( 7, "<b>end-spec</b>"      ),
    Module             = lengthString ( 7, "<b>module </b>"      ),
    EndModule          = lengthString ( 9, "<b>end-module </b>"  ),
    Type               = lengthString ( 4, "<b>type</b>"         ),
    Axiom              = lengthString ( 6, "<b>axiom </b>"       ),
    Conjecture         = lengthString (11, "<b>conjecture </b>"  ),
    Is                 = lengthString (11, "<b>is </b>"          ), % TODO: length 11 ???
    Theorem            = lengthString ( 8, "<b>theorem </b>"     ), 
    Import             = lengthString ( 7, "<b>import </b>"      ),
    Op                 = lengthString ( 2, "<b>op</b>"           ), % TODO: why is this length 2
    Of                 = lengthString ( 2, "<b>of </b>"          ), % TODO: if this is also length 2 ???
    Def                = lengthString ( 3, "<b>def </b>"         ),
    Refine             = lengthString ( 6, "<b>refine </b>"      ),
    Arrow              = lengthString ( 4, " -> "                ),
    Let                = lengthString ( 3, "<b>let </b>"         ),
    In                 = lengthString ( 2, "<b> in</b>"          ),
    Not                = lengthString ( 1, "<b>~</b>"            ), % TODO: guessing...
    And                = lengthString ( 2, "<b>&&</b>"           ), % TODO: guessing...
    Or                 = lengthString ( 2, "<b>||</b>"           ), % TODO: guessing...
    Implies            = lengthString ( 2, "<b>=></b>"           ), % TODO: guessing...
    Iff                = lengthString ( 2, "<b>&lt;=></b>"       ), % TODO: guessing...
    Equals             = lengthString ( 2, "<b>=</b>"            ), % TODO: why was this length 2 instead of 1?
    NotEquals          = lengthString ( 2, "<b>~=</b>"           ), % TODO: guessing...
    DefEquals          = lengthString ( 2, "<b>=</b>"            ),
    LetDeclsAnd        = lengthString ( 3, "<b> and </b>"        ),
    Fa                 = lengthString ( 2, "<b>fa</b>"           ),
    Ex                 = lengthString ( 2, "<b>ex</b>"           ),
    Ex1                = lengthString ( 2, "<b>ex!</b>"          ),
    Product            = lengthString ( 3, "<b> * </b>"          ), 
    RCurly             = lengthString ( 1, "<b>}</b>"            ),
    LCurly             = lengthString ( 1, "<b>{</b>"            ),
    Bar                = lengthString ( 3, "<b> | </b>"          ),
    Underscore         = lengthString ( 1, "<b>_</b>"            ),
    Lambda             = lengthString ( 3, "<b>fn</b> "          ),
    The                = lengthString ( 3, "<b>the</b> "         ),
    If                 = lengthString ( 3, "<b>if </b>"          ),
    Then               = lengthString ( 6, "<b> then </b>"       ),
    Else               = lengthString ( 5, "<b>else </b>"        ),
    Case               = lengthString ( 6, "<b>case </b>"        ),
    Where              = lengthString ( 4, "<b>where</b>"        ),
    Comma              = string ", ",
    Empty              = string "",
    LBrack             = string "[",
    RBrack             = string "]",
    LP                 = string "(",
    RP                 = string ")"            
   }

  % Customized ppList which takes a string pretty printer as argument.

  def ppList f (left, sep, right) ps = 
   prettysNone [left,
                prettysLinear (addSeparator sep (map f ps)),
                right]


  def ppListPath path f (left, sep, right) ps = 
   prettysNone [
     left,
     prettysLinear (
       addSeparator sep 
         (mapWithIndex (fn (i, x) -> f (Cons (i, path), x)) ps)),
     right]
end-spec

