(* Copyright 2015 Kestrel Institute. See file LICENSE for license details *)

\section{Abstract Pretty Printer}

We want to postpone committing to one pretty printer or the other. The
Wadler/Lindig pretty printer has the advantage of being much simpler
and better documented.  The Bjorner/Espinosa printer is complex, has a
poor interface and there is no documentation. It has the advantage that
the coverage of MetaSlang is better. Also, it is probably less likely
to get a stack overflow.

There might be a problem finding a refinement from the following to
the Bjorner/Espinosa printer as many of its operators require indent
information. The Bjorner/Espinosa printer also has more control over
layout.

Also a pretty printer can benefit from state (recording context and
layout information). There might be a win in placing the pretty printer
in the state monad.

### This needs fixing. The qualifier should be generic and
not WadlerLindig.

\begin{spec}
WadlerLindig qualifying spec
  type Doc

  op ppString : String -> Doc
  op ppNewline : Doc
  op ppBreak : Doc
  op ppConcat : List Doc -> Doc
  op ppSep : Doc -> List Doc -> Doc
  op ppIndent : Doc -> Doc
  op ppNil : Doc
  op ppCons : Doc -> Doc -> Doc
  op ppGroup : Doc -> Doc

  op ppFormat : Doc -> String

  op String.pp : String -> Doc
  def String.pp = ppString

  op Nat.pp : Nat -> Doc
  def Nat.pp n = pp (Nat.show n)

  op Integer.pp : Int -> Doc
  def Integer.pp n = pp (Integer.show n)

  op Bool.pp : Bool -> Doc
  def Bool.pp n = pp (Bool.show n)

  op Char.pp : Char -> Doc
  def Char.pp n = pp (Char.show n)
endspec
\end{spec}
