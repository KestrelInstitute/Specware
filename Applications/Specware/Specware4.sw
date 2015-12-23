(* Copyright 2015 Kestrel Institute. See file LICENSE for license details *)

(* Specware 4 Toplevel Specification *)

%%% This constructs Specware and refines various abstract types.

spec 
  import /Applications/Specware/SpecwareShell
  import /Languages/SpecCalculus/Semantics/Specware
  import /Languages/SpecCalculus/Semantics/Evaluate/NoOther

  import /Provers/ToIsabelle/IsaPrinter
  import /Provers/ToCoq/CoqPrinter
  import /Languages/SpecCalculus/AbstractSyntax/ASW_Printer
  import /Languages/SpecCalculus/AbstractSyntax/XMLPrinter

  import Sketch  qualifying /Library/Structures/Data/Maps/Monomorphic/AsLists

  % import PolyMap qualifying /Library/Structures/Data/Maps/Polymorphic/AsLists
  % import                    /Library/Structures/Data/Categories/Cocomplete/Polymorphic/AsRecord
  % import Functor qualifying /Library/Structures/Data/Categories/Functors/FreeDomain/Polymorphic/AsRecord
  % import Cat     qualifying /Library/Structures/Data/Categories/Diagrams/Polymorphic/AsRecord
  % import Sketch  qualifying /Library/Structures/Data/Categories/Sketches/Monomorphic/AsRecord

  % The renaming below should match that in /Library/Structures/Data/Graphs.sw
  import translate (Vertex qualifying /Library/Structures/Data/Sets/Monomorphic/AsLists) by {
      Elem.Elem +-> Vertex.Elem,
      Elem.pp   +-> Vertex.ppElem,
      Vertex.pp +-> Vertex.ppSet
    }
  import translate (Edge qualifying /Library/Structures/Data/Sets/Monomorphic/AsLists) by {
      Elem.Elem +-> Edge.Elem,
      Elem.pp   +-> Edge.ppElem,
      Edge.pp   +-> Edge.ppSet
    }

  % import Sketch   qualifying /Library/Structures/Data/Maps/Monomorphic/AsLists
  % import NatTrans qualifying /Library/Structures/Data/Categories/NatTrans/FreeFunctorDomain/Polymorphic/AsRecord

end-spec
