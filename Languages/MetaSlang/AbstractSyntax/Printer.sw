(*
 * MetaSlang pretty printer.
 * This module contains utilities for printing terms, sorts, and patterns to 
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

AnnTermPrinter qualifying spec {
  import /Library/PrettyPrinter/BjornerEspinosa
  import AnnTerm

  import /Library/Legacy/DataStructures/ListUtilities
  import /Library/Legacy/DataStructures/StringMap

  %% ========================================================================

  %% Dispatchable pretty printers.
  sort ATermPrinter = 
   {
    ppOpId             : QualifiedId -> Pretty,
    ppPOpId            : QualifiedId -> Pretty,
    ppSortId           : QualifiedId -> Pretty,
    ppPSortId          : QualifiedId -> Pretty,
    ppDefaultQualifier : String -> Pretty,
    fromString         : String -> Pretty,
    ppOp               : String -> Pretty,
    ppSort             : String -> Pretty,
    ppFormulaDesc      : String -> Pretty,
    Spec               : Pretty,
    EndSpec            : Pretty,
    Module             : Pretty,
    EndModule          : Pretty,
    Sort               : Pretty,
    Axiom              : Pretty,
    Theorem            : Pretty,
    Conjecture         : Pretty,
    Is                 : Pretty,
    Import             : Pretty,
    Op                 : Pretty,
    Of                 : Pretty,
    Def                : Pretty,
    Arrow              : Pretty,
    And                : Pretty,
    Fa                 : Pretty,
    Ex                 : Pretty,
    Where              : Pretty,
    Let                : Pretty,
    In                 : Pretty,
    Equals             : Pretty,
    DefEquals          : Pretty,
    Product            : Pretty,
    Bar                : Pretty,
    Underscore         : Pretty,
    Lambda             : Pretty,
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

  op ppList : fa(T) (T -> Pretty) -> (Pretty * Pretty * Pretty) -> List T -> Pretty

  op ppListPath : fa(T) List Nat -> (List Nat  * T -> Pretty) -> (Pretty * Pretty * Pretty) -> List T -> Pretty

  %% ========================================================================

  def ppAsciiId (Qualified (qualifier, id) : QualifiedId) = 
   string (if qualifier = UnQualified or
	      qualifier = "Nat"       or 
	      qualifier = "Boolean"   or
	      qualifier = "String"    or
	      qualifier = "Integer"   or 
	      qualifier = "General"   or
	      qualifier = "Char"      or
	      qualifier = "List"     
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
    ppSortId           = ppAsciiId,
    ppPSortId          = ppAsciiId,
    ppDefaultQualifier = string,
    fromString         = string,
    ppOp               = string,
    ppSort             = string,
    ppFormulaDesc      = string,
    Spec               = string "spec ",
    EndSpec            = string "end-spec",
    Module             = string "module ",
    EndModule          = string "end-module",
    Sort               = string "sort",
    Axiom              = string "axiom",
    Theorem            = string "theorem",
    Conjecture         = string "conjecture",
    Is	               = string "is",
    Import             = string "import ",
    Op                 = string "op",
    Of                 = string "of ",
    Def                = string "def ",
    Arrow              = string " -> ",
    Let 	       = string "let ",
    In 	               = string "in ",
    Equals             = string "=" ,
    DefEquals          = string "=" ,
    And 	       = string " and ",
    Fa	               = string "fa",
    Ex	               = string "ex",
    Where	       = string "where",
    Product            = string " * ",
    Bar                = string " | ",
    Underscore         = string "_",
    Lambda             = string "fn ",
    If 	               = string "if ",
    Then 	       = string " then ",
    Else 	       = string "else ",
    Case 	       = string "case ",
    Empty              = string "",
    Comma	       = string ", ",
    LCurly 	       = string "{",
    RCurly 	       = string "}",
    LBrack 	       = string "[",
    RBrack 	       = string "]",
    LP	               = string "(",
    RP	               = string ")"
   } 

  def latexString s =
   if Char.isAlphaNum(String.sub(s,0)) then
     string s
   else 
     % Ad hoc treatment for LaTeX
     let s = String.translate (fn #^ -> "++" | ## -> "\\#" | #_ -> "\\_" | #& -> "\\&" | ch -> Char.toString ch) s in
     %   if String.sub(s,0) = #^
     %   then lengthString (2,"{\\tt ++}")
     %   else
     lengthString (String.length s,"\\mbox{{\\tt "^s^"}}")

  def latexBoolean s = 
   case s of
    | "&"   -> lengthString (1, "$\\&$")
    | " =>" -> lengthString (1, "$\\Rightarrow$")
    | "or"  -> lengthString (2, "\\SWor\\ ")
    | "<=>" -> lengthString (2, "$\\Leftrightarrow$")
    | "~"   -> lengthString (1, "$\\neg$")
    | _     -> string s	 	 

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
      | "Boolean" -> latexBoolean id
      | _         -> prettysNone [string (qualifier^"."), latexString id]

  %%  def ppLatexPId (idi : IdInfo) = 
  %%      let def f idi =
  %%          case idi
  %%            of []       -> ""
  %%	     | [id]     -> id
  %%             | id::idi2 -> id^"."^(f idi2) in
  %%      latexString (f idi)

  def latexPrinter : ATermPrinter = 
   {
    ppOpId             = ppLatexId,
    ppPOpId            = ppLatexId,
    ppSortId           = ppLatexId,
    ppPSortId          = ppLatexId,
    ppDefaultQualifier = string,
    ppOp 	      = latexString,
    ppSort	      = latexString,
    fromString         = latexString,
    ppFormulaDesc      = fn s -> lengthString (String.length s, "{\\tt "^s^"}" ),
    Spec 	      = lengthString (5, "\\SWspec\\ "          ),
    EndSpec 	      = lengthString (8, "\\SWendspec "         ),
    Module             = lengthString (7, "{\\bf module}\\ "     ),
    EndModule          = lengthString (9, "{\\bf end-module}\\ " ),
    Sort 	      = lengthString (4, "\\SWsort "            ),
    Axiom 	      = lengthString (6, "\\SWaxiom\\ "         ),
    Theorem	      = lengthString (8, "\\SWtheorem\\ "       ),
    Conjecture	      = lengthString (8, "{\\bf conjecture}\\ " ),
    Is		      = lengthString (2, "{\\bf is}\\ "         ),
    Import	      = lengthString (7, "\\SWimport "          ),
    Op		      = lengthString (2, "\\SWop "              ),
    Of 		      = lengthString (3, "\\SWof "              ),
    Def		      = lengthString (4, "\\SWdef "             ),
    Arrow	      = lengthString (3, " $\\rightarrow$ "     ),
    Let		      = lengthString (4, "\\SWlet\\ "           ),
    In		      = lengthString (3, "\\ {\\bf in}"         ),
    Equals	      = lengthString (3, "\\ = \\ "             ),
    DefEquals	      = lengthString (3, "\\ = \\ "             ),
    And		      = lengthString (3, "\\ \\SWand\\ "        ),
    Fa		      = lengthString (1, "\\SWfa "              ),
    Ex		      = lengthString (1, "\\SWex "              ),
    Where	      = lengthString (4, "{\\bf where} "        ),
    Product	      = lengthString (3,  " $\\times$ "         ), 
    RCurly 	      = lengthString (1, "$\\}$"                ),
    LCurly 	      = lengthString (1, "$\\{$"                ),
    Bar		      = lengthString (3, " {\\tt |} "           ),
    Underscore	      = lengthString (1, "{\\tt \\_}"           ),
    Lambda	      = lengthString (3, "$\\lambda$ "          ),
    If		      = lengthString (3, "\\SWif "              ),
    Then 	      = lengthString (6, " \\SWthen "           ),
    Else 	      = lengthString (5, "\\SWelse "            ),
    Case 	      = lengthString (6, "\\SWcase "            ),
    Comma	      = string ", ",
    Empty   	      = string "",
    LBrack 	      = string "[",
    RBrack 	      = string "]",
    LP		      = string "(",
    RP		      = string ")"
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
      | "Boolean" -> latexBoolean id
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
  %%	     | [id]     -> id
  %%             | id::idi2 -> id^"."^(f idi2) in
  %%      latexString (f idi)

  def pdfPrinter (counter, spc : String) : ATermPrinter = 
   {
    ppOpId             = pdfId (spc, "Op"),
    ppPOpId            = pdfId (spc, "Op"),
    ppSortId           = pdfId (spc, "Sort"),
    ppPSortId          = pdfId (spc, "Sort"),
    ppDefaultQualifier = string,
    ppOp 	       = pdfIdDecl (spc,"Op"),
    ppSort	       = pdfIdDecl (spc,"Sort"),
    ppFormulaDesc      = fn s -> (counter State.:= (State.! counter) + 1;
				  prettysNone [lengthString (0,
							     "\\pdfdest num "^(Nat.toString (State.! counter))^
							     " fitbh%"^newlineString()),
					       lengthString (String.length s, "{\\tt "^s^"}" )
					      ]),
    fromString         = latexString,
    Spec 	       = lengthString ( 5, "\\SWspec\\ "           ),
    EndSpec 	       = lengthString ( 8, "\\SWendspec "          ),
    Sort 	       = lengthString ( 4, "\\SWsort "             ),
    Module             = lengthString ( 7, "{\\bf module}\\ "      ),
    EndModule          = lengthString ( 9, "{\\bf end-module}\\ "  ),
    Axiom 	       = lengthString ( 6, "\\SWaxiom\\ "          ),
    Theorem	       = lengthString ( 8, "\\SWtheorem\\ "        ),
    Conjecture         = lengthString (11, "{\\bf conjecture}\\ "  ),
    Is		       = lengthString ( 2, "{\\bf is}\\ "          ),
    Import	       = lengthString ( 7, "\\SWimport "           ),
    Op		       = lengthString ( 2, "\\SWop "               ),
    Of 		       = lengthString ( 3, "\\SWof "               ),
    Def		       = lengthString ( 4, "\\SWdef "              ),
    Arrow	       = lengthString ( 3, " $\\rightarrow$ "      ),
    Let		       = lengthString ( 4, "\\SWlet\\ "            ),
    In		       = lengthString ( 3, "\\ {\\bf in}"          ),
    Equals	       = lengthString ( 3, "\\ = \\ "              ),
    DefEquals	       = lengthString ( 3, "\\ = \\ "              ),
    And		       = lengthString ( 3, "\\ \\SWand\\ "         ),
    Fa		       = lengthString ( 1, "\\SWfa "               ),
    Ex		       = lengthString ( 1, "\\SWex "               ),
    Where	       = lengthString ( 4, "{\\bf where} "         ),
    Product	       = lengthString ( 3,  " $\\times$ "          ), 
    RCurly 	       = lengthString ( 1, "$\\}$"                 ),
    LCurly 	       = lengthString ( 1, "$\\{$"                 ),
    Bar		       = lengthString ( 3, " {\\tt |} "            ),
    Underscore	       = lengthString ( 1, "{\\tt \\_}"            ),
    Lambda	       = lengthString ( 3, "$\\lambda$ "           ),
    If		       = lengthString ( 3, "\\SWif "               ),
    Then 	       = lengthString ( 6, " \\SWthen "            ),
    Else 	       = lengthString ( 5, "\\SWelse "             ),
    Case 	       = lengthString ( 6, "\\SWcase "             ),
    Comma	       = string ", ",
    Empty   	       = string "",
    LBrack 	       = string "[",
    RBrack 	       = string "]",
    LP		       = string "(",
    RP		       = string ")"
   }
    

  def htmlPrinter () : ATermPrinter = 
   let nameMap : Ref (StringMap String) = ref (StringMap.empty) in
   let counter : Ref Nat = ref 0 in
   let def nameNumber s =
        case StringMap.find (State.! nameMap, s) of
	 | None    -> let n = State.! counter in
	              let ns = Nat.toString n in
		      (nameMap State.:= StringMap.insert (State.! nameMap, s, ns);
		       counter State.:= n + 1; 
		       ns)
	 | Some ns -> ns
   in		  
   let def ppQid (Qualified (qualifier, id) : QualifiedId) = 
        if qualifier = UnQualified then
	  lengthString (String.length id,
			"<a href = #"^nameNumber id^">"^id^"</a>") 
	else
	  case qualifier of
           | "Nat"     -> string id
	   | "Boolean" -> string id
	   | _         -> prettysNone [lengthString (String.length qualifier,
						     "<a href = "^qualifier^".html>"^qualifier^"</a>"),
				       string ".",
				       string id]      
   %%   	 def ppPQid (idi : IdInfo) = 
   %%             let def f idi =
   %%		 case idi
   %%		   of []       -> ""
   %%		    | [id]     -> id
   %%		    | id::idi2 -> id^"."^(f idi2) in
   %%	     string (f idi)  
   in   
   let def ppOp s = 
        lengthString (String.length s,
		      "<a name = "^nameNumber(s)^">"^s^"</a>")
   in
   {
    ppOpId	       = ppQid,
    ppPOpId	       = ppQid,
    ppSortId	       = ppQid, 
    ppPSortId	       = ppQid, 
    ppDefaultQualifier = string,
    fromString         = string,
    ppOp               = ppOp,
    ppSort	       = ppOp,
    ppFormulaDesc      = string,
    Spec 	       = lengthString ( 5, "<b>spec </b>"        ),
    EndSpec  	       = lengthString ( 7, "<b>end-spec</b>"     ),
    Module 	       = lengthString ( 7, "<b>module </b>"      ),
    EndModule 	       = lengthString ( 9, "<b>end-module </b>"  ),
    Sort 	       = lengthString ( 4, "<b>sort</b>"         ),
    Axiom 	       = lengthString ( 6, "<b>axiom </b>"       ),
    Conjecture         = lengthString (11, "<b>conjecture </b>"  ),
    Is   	       = lengthString (11, "<b>is </b>"          ),
    Theorem	       = lengthString ( 8, "<b>theorem </b>"     ),
    Import	       = lengthString ( 7, "<b>import </b>"      ),
    Op		       = lengthString ( 2, "<b>op</b>"           ),
    Of 		       = lengthString ( 2, "<b>of </b>"          ),
    Def		       = lengthString ( 3, "<b>def </b>"         ),
    Arrow	       = lengthString ( 4, " -> "                ),
    Let		       = lengthString ( 3, "<b>let </b>"         ),
    In		       = lengthString ( 2, "<b> in</b>"          ),
    Equals	       = lengthString ( 2, "<b>=</b>"            ),
    DefEquals	       = lengthString ( 2, "<b>=</b>"            ),
    And		       = lengthString ( 3, "<b> and </b>"        ),
    Fa		       = lengthString ( 2, "<b>fa</b>"           ),
    Ex		       = lengthString ( 2, "<b>ex</b>"           ),
    Product	       = lengthString ( 3, "<b> * </b>"          ), 
    RCurly 	       = lengthString ( 1, "<b>}</b>"            ),
    LCurly 	       = lengthString ( 1, "<b>{</b>"            ),
    Bar		       = lengthString ( 3, "<b> | </b>"          ),
    Underscore	       = lengthString ( 1, "<b>_</b>"            ),
    Lambda	       = lengthString ( 3, "<b>fn</b> "          ),
    If		       = lengthString ( 3, "<b>if </b>"          ),
    Then 	       = lengthString ( 6, "<b> then </b>"       ),
    Else 	       = lengthString ( 5, "<b>else </b>"        ),
    Case 	       = lengthString ( 6, "<b>case </b>"        ),
    Where	       = lengthString ( 4, "<b>where</b>"        ),
    Comma	       = string ", ",
    Empty   	       = string "",
    LBrack 	       = string "[",
    RBrack 	       = string "]",
    LP		       = string "(",
    RP		       = string ")"    	
   }

  % Customized ppList which takes a string pretty printer as argument.

  def ppList f (left, sep, right) ps = 
   prettysNone [left,
		prettysLinear (addSeparator sep (map f ps)),
		right]


  def ppListPath path f (left, sep, right) ps = 
   prettysNone [left,
		prettysLinear (addSeparator sep 
			       (ListUtilities.mapWithIndex (fn (i, x) -> f (cons (i, path), x)) 
		                                           ps)),
		right]
}
