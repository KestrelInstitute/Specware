let
  Specware4 = spec {
      import /Languages/SpecCalculus/Semantics/Specware
      import PolyMap qualifying /Library/Structures/Data/Maps/Polymorphic/AsLists
      % import /Library/Structures/Data/Categories/Diagrams/Polymorphic/AsRecord
    } 
in
  generate lisp Specware4
