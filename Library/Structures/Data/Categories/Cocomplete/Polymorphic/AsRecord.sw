(* Copyright 2015 Kestrel Institute. See file LICENSE.text for license details *)

\section{Concrete Type for Cocomplete Cats as Record}

\begin{spec}
Cat qualifying spec {
  import ../Polymorphic

  type Cocone (O,A) = {
      diagram : Diagram (O,A),
      apex : O,
      natTrans : NatTrans (O,A)
    }

  def diagram cocone = cocone.diagram
  def apex cocone = cocone.apex
  def natTrans cocone = cocone.natTrans

  def emptyCocone targetCat = {
      diagram = emptyDiagram targetCat,
      apex = initialObject targetCat,
      natTrans = emptyNatTrans targetCat
   }

  type InitialCocone (O,A) = {
      cocone : Cocone (O,A),
      universal : Cocone (O,A) -> A
    }

  def cocone initCocone = initCocone.cocone
  def universal initCocone = initCocone.universal

  def emptyInitialCocone targetCat = {
      cocone = emptyCocone targetCat,
      universal = fn _ (* cocone *) -> ident targetCat (initialObject targetCat)
    }

  type Cat.Cat (O,A) = {
      ident : O -> A,
      dom : A -> O,
      cod : A -> O,
      % composable? : A -> A -> Bool,
      compose : A -> A -> A,
      % For now, use option to indicate errors. A monad would be nicer.
      colimit : Diagram (O,A) -> Option (InitialCocone (O,A)) * Option String,
      initialObject : O,
      ppObj : O -> WLPretty,
      ppArr : A -> WLPretty
    }

%  op ident: fa(O,A) Cat(O,A) -> O -> A
%  op dom: fa(O,A) Cat(O,A) -> A -> O
%  op cod: fa(O,A) Cat(O,A) -> A -> O
%  % op composable?: fa(O,A) Cat (O,A)  -> A -> A -> Bool
%  op compose: fa(O,A) Cat(O,A) -> A -> A -> A 
%  op colimit: fa(O,A) Cat(O,A) -> Diagram (O,A) -> InitialCocone (O,A)
%  op ppObj: fa(O,A) Cat(O,A) -> O -> WLPretty
%  op ppArr: fa(O,A) Cat(O,A) -> A -> WLPretty

  def Cat.ident cat = cat.ident 
  def Cat.dom cat = cat.dom
  def Cat.cod cat = cat.cod
  % def composable? cat = cat.composable?
  def Cat.compose cat = cat.compose
  def Cat.ppObj cat = cat.ppObj
  def Cat.ppArr cat = cat.ppArr

  def colimit cat = cat.colimit
  def initialObject cat = cat.initialObject
}
\end{spec}

Should we add ppObj and ppArrow to the record for pretty printing
objects and arrows respectively?
