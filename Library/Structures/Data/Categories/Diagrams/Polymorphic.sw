\section{Diagrams in a Polymorphic Category}

Polymorphic diagrams. Shapes are sketches though at present sketches
are just graphs.

Note that the functors appearing here are those whose domain is freely
generated from the shape.

\begin{spec}
let Sketches =
 /Library/Structures/Data/Categories/Sketches/Monomorphic/Sketches in
let Functors =
  /Library/Structures/Data/Categories/Functors/FreeDomain/Polymorphic
in
spec
  import Functors
  import Sketches
  import /Library/PrettyPrinter/WadlerLindig

%   sort Diagram (O,A) = {
%     shape : Sketch,
%     functor : Functor (O,A)
%   }

  sort Diagram (O,A)
  op shape : fa (O,A) Diagram (O,A) -> Sketch
  op functor : fa (O,A) Diagram (O,A) -> Functor (O,A)

%   op ppDiagram : fa (O,A) Diagram (O,A) -> Pretty
%   def ppDiagram diag =
%     ppBlockAll [
%       ppString "Shape=",
%       ppIndent 2 (ppSketch (shape diag)),
%       ppString "Functor=",
%       ppIndent 2 (ppFunctor (functor diag))
%     ]
end
\end{spec}

The pretty printing functions need a rethink.  Perhaps the pretty printer
should be made part of the sort above.

What is omitted from this is the requirement that the domain of the functor
is same as the shape of the diagram.

So the sort above should be subsorted by the following:
(shape diag) = dom (functor diag).
