(* Copyright 2015 Kestrel Institute. See file LICENSE.text for license details *)

(* Definition of the exception type

These are the exceptions that one might raise. This refines the abstract
type under \UnitId{/Library/Structures/Data/Monad/Exception}

Ideally the exception type should be defined
compositionally ... specs that need an exception should be able to extend
the type.  We need exceptions for things like:

\begin{itemize}
\item environment: failing to find an op or type id etc.
\item typechecking: 
\item io: can't open file, permisssions, etc
\item parsing
\end{itemize}

The thought was that \Op{Fail} would be an exception that cannot
be caught.  As such it will take one to the lisp debugger. This needs
thought.

Many of the exceptions have a field which gives the location (in the
current file) where the error occurred. Putting the position here rather
than directly in the error message means that all error messages display
the position in a uniform way and can more easily be conveyed to the UI.
On the other hand, it seems there are places where the exception is
raised but where the position information is unavailable. Needs thought.

A \Op{SyntaxError} is one that is raised at the toplevel when the user
enters something bad. A \Op{ParserError} is raised when the file parser fails.
*)

SpecCalc qualifying spec
  import /Library/Structures/Data/Monad/Exception
  import /Library/Legacy/Utilities/System

  import /Languages/SpecCalculus/AbstractSyntax/UnitId
  import /Languages/MetaSlang/Specs/Position

  type AnnSpec.Spec

  type Monad.Exception =
    | Fail                String 
    | FileNotFound        Position * RelativeUID
    | UIDNotFound         Position * RelativeUID
    | TypeCheck           Position * String
    | TypeCheckErrors     List(String * Position) * Spec
    %% OldTypeCheck is a temporary hack to avoid gratuitous 0.0-0.0 for position
    | OldTypeCheck        String              
    | Unsupported         Position * String
    | SyntaxError         String
    | ParserError         String   % Here the string is the filename.
    | DiagError           Position * String
    | SpecError           Position * String
    | MorphError          Position * String
    | QualifyError        Position * String
    | TranslationError    String * Position
    | ColimitError        Position * String
    | SubstError          Position * String
    | CircularDefinition  UnitId
    | Proof               Position * String
    | TransformError      Position * String
    | UndefinedGlobalVar  String
    | CollectedExceptions List Monad.Exception
    | Warning             Position * String
    | Escape  % Control flow mechanism - see IsoMorphism.sw

  op decodeException : Exception -> (Option (Position * Bool)) * String 
  def decodeException except =
    case except of
      | Fail str                       -> (None,              "Fail: " ^ str)
      | FileNotFound        (pos, uid) -> (Some (pos, true),  "Unknown unit " ^ (showRelativeUID uid))
      | UIDNotFound         (pos, uid) -> (Some (pos, true),  "Unknown unit " ^ (showRelativeUID uid))
      | TypeCheck           (pos, msg) -> (Some (pos, false), "Type error: "              ^ msg)
      | TypeCheckErrors     (pairs, err_spc) -> (None,        printTypeErrors pairs)
      | Unsupported         (pos, msg) -> (Some (pos, false), "Unsupported operation: "   ^ msg)
      | SyntaxError         msg        -> (None,              "Syntax error: "            ^ msg)
      | ParserError         fileName   -> (None,              "Syntax error in file "     ^ fileName)
      | DiagError           (pos, msg) -> (Some (pos, false), "Diagram error: "           ^ msg)
      | SpecError           (pos, msg) -> (Some (pos, false), "in specification: "  ^ msg)
      | MorphError          (pos, msg) -> (Some (pos, false), "in morphism: "       ^ msg)
      | QualifyError        (pos, msg) -> (Some (pos, false), "in qualify: "        ^ msg)
      | TranslationError    (msg, pos) -> (Some (pos, false), "in translation: "    ^ msg)
      | ColimitError        (pos, msg) -> (Some (pos, false), "in colimit: "      ^ msg)
      | SubstError          (pos, msg) -> (Some (pos, false), "in substitution: " ^ msg)
      | CircularDefinition  uid        -> (None,              "Circular definition: " ^ showUnitId uid)
      | Proof               (pos, msg) -> (Some (pos, false), "Proof error: "             ^ msg)
      | TransformError      (pos, msg) -> (Some (pos, false), "in transform: "      ^ msg)
      | UndefinedGlobalVar  name       -> (None,              "Undefined global var: "    ^ name)
      | CollectedExceptions exceptions -> (None,              printExceptions exceptions)
      | mystery                        -> (None,              "Unknown exception: " ^ (anyToString mystery))

  op printException (except : Exception) : String =
   ("ERROR: " ^  %% New, so we can grep for this string and find all the exceptions.
    (case decodeException except of
      | (None,             msg) -> msg
      | (Some (pos, ref?), msg) -> 
       msg ^ (if ref? then "\n referenced from " else "\n found in ") ^ (printAll pos)))

  op  numberOfTypeErrorsToPrint: Nat
  def numberOfTypeErrorsToPrint = 10

  op  numberOfExceptionsToPrint: Nat
  def numberOfExceptionsToPrint = 12

  op printTypeErrors : List(String * Position) -> String
  def printTypeErrors errs =
    if length errs = 0 then "" else
    let def printErr((result,lastfilename),(msg,pos)) =
          let filename = (case pos of
			    | File (filename, left, right) -> filename
			    | _ -> "")
          in (result
	      ^ (if filename = lastfilename then
		   print pos 
		 else
		   "Errors in " ^ (printAll pos))
	      ^ "\t: " ^ msg ^ "\n",
	      filename)
    in
    (foldl printErr ("","") (firstN(errs,numberOfTypeErrorsToPrint))).1
     ^ (if (length errs) <= numberOfTypeErrorsToPrint then
	   ""
	 else 
	   "...  (" ^ Nat.show(length errs - numberOfTypeErrorsToPrint) ^ " additional type errors)")

  op printExceptions : List Monad.Exception -> String
  def printExceptions exceptions =
    case exceptions of 
      | [] -> ""
      | _ ->
        let def print_exception ((result, opt_lastfilename), exception) =
	     (case decodeException exception of
		| (None, msg) ->
		  (printException exception,
		   None)
                | (Some (pos, ref?), msg) ->
		  let filename = (case pos of
				    | File (filename, left, right) -> filename
				    | _ -> "")
		  in 
		  let same_file? = case opt_lastfilename of
				     | None -> false
				     | Some lastfilename -> filename = lastfilename
		  in
		  let msg = (result ^ 
			     (if same_file? then
				"  " ^ print pos 
			      else
				"Errors in " ^ (printAll pos))
				^ "\t: " ^ msg ^ "\n")
		  in
		    (msg, Some filename))
      in
	(foldl print_exception ("",None) (firstN (reverse exceptions, numberOfExceptionsToPrint))).1
	^ 
	(if (length exceptions) <= numberOfExceptionsToPrint then
	   ""
	 else 
	   "...  (" ^ Nat.show(length exceptions - numberOfExceptionsToPrint) ^ " additional exceptions)")


  op  firstN: [a] List a * Nat -> List a
  def firstN(l,n) =
    if n = 0 then []
    else
    case l of
      | [] -> []
      | x::r -> Cons(x,firstN(r,n-1))

end-spec
