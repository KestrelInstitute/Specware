\section{Finite Endo-Maps}

These are maps when the domain and codomain are the same.

\begin{spec}
spec
   import translate (translate Finite
     by {Dom._ +-> Elem._, Cod._ +-> Elem._})
     by {Elem.Dom +-> Elem.Elem, Elem.Cod +-> Elem.Elem}
\end{spec}

Endo maps can be composed.

\begin{spec}
  op o infixl 24 : Map * Map -> Map
\end{spec}

We give the "axiom" for composition in terms of a definition. This is
problematic. Maps do not have an explicit domain.  So if a key of a given
sort is absent, the function is not defined on that element. However, for
the op \Op{prefix}, defined below, is motivated by a different assumption.
If a key is absent then the element maps to itself. In the latter case,
the definition of composition below is wrong if \Op{fold} is interpreted as
the function that iterates only over those parts of the map that
differ from the identity.

These cases need to be distinguished. One option is to have a two 
families of fold functions for delta maps. Those that iterate over
the entire domain, and those that iterate only over where the map
differs from the identity.

\begin{spec}
   def o (m2,m1) =
     fold (fn (new, (k1,v1)) ->
       case evalPartial (m2,v1) of
         | None -> new
         | Some v2 -> update (new, k1, v2), empty, m1)
\end{spec}

We include the operator \Op{prefix}. This is a generalization of
\Op{update}. It prefixes the map in its first argument with
the map in its second argument.

This helps the case when one is working with "delta" maps. These are maps
where it is assumed that, in the absence of a mapping for an element,
the element maps to itself.

Having a separate function means that one can have rules such as
\Expr{prefix empty m = m}. The advantage is that, in many case we
can avoid iterating when constructing delta maps.

\begin{spec}
   op prefix : Map -> Map -> Map
\end{spec}

The following represents the law for \Op{prefix}.

\begin{verbatim}
   def prefix orig updates =
     fold (fn map -> fn (key,value) -> update (ma, key, value)) orig updates
\end{verbatim}

\begin{spec}
endspec
\end{spec}
