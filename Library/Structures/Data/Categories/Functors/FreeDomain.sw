(* Copyright 2015 Kestrel Institute. See file LICENSE for license details *)

%% Functors with free domain and fixed (monomorphic) target category

%% This is a spec for mono functors where the domain is the free
%% category generated from a category presentation (ie sketch). This spec is
%% meant mainly defining systems. A key distinction between
%% this spec and the more general polymorphic functor spec is that the effect
%% of the functor is determined by what the maps do on the vertices
%% and edges of the graph underlying the sketch.

%% Note the following. In
%% \UnitId{Library/Structures/Data/Categories/Functors/Polymorphic},
%% the type Functor is defined over 4 type variables. The first two are
%% the types of the objects and arrows in the domain category. The other
%% two for the codomain category. In contrast, here there are only type
%% variables characterizing the objects and arrows in the codomain.

%% An alternative to including the generator is simply to define the
%% functor from the free category. The problem is that by doing so, we
%% lose the ability to enumerate (fold) over the vertices and edges
%% in the generating graph, since as a rule, whereas the number of edges
%% in the generating graph may be finite, there may not be a finite number
%% of paths in the free category.

%% The names of some of these operators clash with Cats and Graphs.

Functor qualifying spec
  import /Library/Structures/Data/Pretty
  import Shape qualifying /Library/Structures/Data/Categories/Sketches
  import /Library/Structures/Math/Cat
  import EdgeMap qualifying (translate (translate /Library/Structures/Data/Maps/Finite by {
      KeyValue._ +-> EdgeCat._,
      Dom._ +-> Edge._,
      Cod._ +-> Cat._
    }) by {
      Edge.Dom +-> Edge.Edge,
      Cat.Cod +-> Cat.Arrow
    })

  import VertexMap qualifying (translate (translate /Library/Structures/Data/Maps/Finite by {
      KeyValue._ +-> VertexCat._,
      Dom._ +-> Vertex._,
      Cod._ +-> Cat._
    }) by {
      Vertex.Dom +-> Vertex.Vertex,
      Cat.Cod +-> Cat.Object
    })

  type Functor

  op dom : Functor -> Sketch
  op vertexMap : Functor -> VertexMap.Map
  op edgeMap : Functor -> EdgeMap.Map 

  op empty : Functor
  op make : Sketch -> VertexMap.Map -> EdgeMap.Map -> Functor


%% When pretty printing a functor, we don't print the domain or codomain. 
%% Printing the domain (generator) is not unreasonable.

  op pp : Functor -> Doc
  def pp functor = 
    ppConcat [
      pp "Vertex Map =",
      ppNewline,
      pp "  ",
      ppIndent (pp (vertexMap functor)),
      ppNewline,
      pp "Edge Map =",
      ppNewline,
      pp "  ",
      ppIndent (pp (edgeMap functor))
   ]

end-spec

%% Perhaps we should define the free category construction. Can we also
%% describe what happens on graph homomorphisms? Ie can we define a functor?
%% Perhaps not since this requires the category of categories. Needs thought.
