let
  Specware4 = spec {
      % import /Languages/MetaSlang/Specs/Printer
      % import /Languages/MetaSlang/Specs/Elaborate/TypeChecker
      % import /Library/Structures/Data/Categories/Diagrams/Polymorphic/AsRecord
      import /Languages/SpecCalculus/Semantics/Specware
      import PolyMap qualifying /Library/Structures/Data/Maps/Polymorphic/AsLists
    } 
  % S = printF Specware4
in
  generate lisp Specware4
