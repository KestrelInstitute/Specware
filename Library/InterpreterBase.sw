(* Copyright 2015 Kestrel Institute. See file LICENSE for license details *)

%%% This adds definitions to some ops in the Base that have handwritten lisp definitions

ExecutableList    = morphism Base/List    -> Base/List_Executable    {}

% ExecutableStringList = Base/String_Executable [ExecutableList]

ExecutableString  = morphism Base/String  -> Base/String_Executable  {}
ExecutableInteger = morphism Base/Integer -> Base/Integer_Executable {}

InterpreterBase   = Base [ExecutableInteger] [ExecutableString] [ExecutableList]

(* The following almostduplicates def in String_Executable
 * InterpreterBase = refine InterpreterBase0 by {
 * 
 *   (* The following def's have been commented out because they are now present in
 *   the base library spec String. Once we make sure that everything works fine,
 *   the following commented-out def's should be removed altogether. *)
 * 
 * (*
 *   def String.all p s = List.all p (explode s)
 *   def String.map f s = implode(List.map f (explode s))
 *   def String.exists p s = List.exists p (explode s)
 *   def String.concatList ss = case ss of
 *                                | []     -> ""
 *                                | s::ss1 -> s ^ (concatList ss1)
 *   def String.translate subst s = concatList(map subst (explode s))
 *   def String.newline = "\n"
 *   def Integer.intToString = Integer.toString
 *   def Integer.stringToInt s = let firstchar::_ = explode s in
 * 			       if firstchar = #-
 * 				 then -(stringToNat(substring(s,1,length s)))
 * 			       else stringToNat s
 *   def Nat.natToString = Nat.toString
 *  *)
 * 
 *   def Nat.stringToNat s =
 *        (let def charToDigit (c : (Char | isNum)) : Nat =
 * 	case c of
 * 	  | #0 -> 0
 * 	  | #1 -> 1
 * 	  | #2 -> 2
 * 	  | #3 -> 3
 * 	  | #4 -> 4
 * 	  | #5 -> 5
 * 	  | #6 -> 6
 * 	  | #7 -> 7
 * 	  | #8 -> 8
 * 	  | #9 -> 9 in
 * 	  let def stringToNatAux (chars : {chars : List Char | forall? isNum chars},
 * 				  res : Nat) : Nat =
 * 	        case chars of
 * 		  | []     -> res
 * 		  | hd::tl -> stringToNatAux (tl, res * 10 + charToDigit hd)
 * 	  in
 * 	    stringToNatAux(explode s, 0))
 * }
 *)
