spec

  (* This spec collects all the library specs used by the proof checker
  spec. This spec is systematically imported into every spec (in this
  directory) that would not otherwise import any other spec, which guarantees
  the library specs to be available in every spec. *)

  import Libs/Predicates,
         Libs/Assertions,
         Libs/PartialFunctions,
         Libs/Sets,
         Libs/FiniteSets,
         Libs/Maps,
         Libs/FiniteMaps,
         Libs/FiniteSequences,
         Libs/StructureConversions

  (* The library specs in Type.sw are not imported here because they are meant
  to be imported (and translated) on demand where needed, as opposed to
  providing certain utility types and ops, like the specs imported above. *)
         
endspec
