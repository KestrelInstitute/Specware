\section{Categories}

This is the base specs for a category. That is, a model of this
spec is a category. It does not include a sort for category.\footnote{Do we 
need dependent types to do this in terms of homsets?}

\begin{spec}
spec {
  import /Library/Structures/Data/Pretty

  sort Object
  sort Arrow
  sort Composable = {(g,f) : Arrow * Arrow | dom g = cod f}
  
  op dom : Arrow -> Object
  op cod : Arrow -> Object
  op ident : Object -> Arrow
  op compose : Composable -> Arrow  

  op ppObject : Object -> Doc
  op ppArrow : Arrow -> Doc
  
  axiom dom_ident is dom o ident = id
  axiom cod_ident is cod o ident = id
  
  axiom dom_compose is fa(f,g) (dom o compose)(g,f) = dom f
  axiom cod_compose is fa(f,g) (cod o compose)(g,f) = cod g
  axiom assoc is fa(f,g,h) compose (h,compose (g,f)) = compose (compose (h,g),f)
  axiom right_unit is fa(f) compose (f,(ident o dom) f) = f
  axiom left_unit is fa(f) compose ((ident o cod) f,f) = f
}
\end{spec}

This spec can be obtained by refinement.
Define the following import to \verb+Cat+:
\begin{verbatim}
  def Cat-Import = translateSpec ReflexiveGraph
    ["Node"   |-> "Object",
     "Edge"   |-> "Arrow"]
\end{verbatim}
and then omit the sorts \verb+Object+ and \verb+Arrow+ and the operator
\verb+ident+.

