\section{List show function}

The natural place for this is in \verb|List|. However, \verb|String|
depends on \verb|List| and with the following, we have \verb|List|
depending on \verb|String|.  An alternative is to factor out the
signatures of \verb|String| and \verb|List| but this seems even
more unnatural. Then again, perhaps \verb+PrimitiveSorts+ should
be renamed \verb|PrimitiveSignature| and contain just enough sort and
op definitions to break the dependencies.

\begin{spec}
spec {
  import PrimitiveSorts
  import List
  import String
\end{spec}

Render a list as a string. The first argument is the separator between
elements. The second is a list of strings.  For example,
\verb|show ":" (map Integer.show [1,2,3])|
yields \verb|1:2:3|.

\begin{spec}
  op List.show : String -> List String -> String
  def List.show sep l =
    case l of
      | [] -> ""
      | x::[] -> x 
      | x::rest ->
           x
         ^ sep
         ^ (List.show sep rest)

  op Option.show : fa (a) (a -> String) -> Option a -> String
  def Option.show showX opt =
    case opt of
      | None -> "None"
      | Some x ->
          "(Some "
          ^ (showX x)
          ^ ")"
}
\end{spec}
