\section{Initial Data Type for Polymorphic Categories}

Here we define an explicit sort for categories. This is 
a refinement of Cats where a category is represented by a record. 

\begin{spec}
spec {
  import /Library/Structures/Data/Categories/Polymorphic

  sort Cat (O,A) = {
    ident : O -> A,
    dom : A -> O,
    cod : A -> O,
    % composable? : A -> A -> Boolean,
    compose : A -> A -> A,
    ppObj : O -> Pretty,
    ppArr : A -> Pretty
  }

  def ident cat = cat.ident
  def dom cat = cat.dom
  def cod cat = cat.cod
  % def composable? cat = cat.composable?
  def compose cat = cat.compose
  def ppObj cat = cat.ppObj
  def ppArr cat = cat.ppArr
}
\end{spec}

Should we add ppObj and ppArrow to the record for pretty printing
objects and arrows respectively?
