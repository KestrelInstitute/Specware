spec

  (* This spec collects all the library specs used by the proof checker
  spec. This spec is systematically imported into every spec that would not
  otherwise import any other spec, which guarantees the library specs to be
  available in every spec. *)

  import /Library/General/Assert,
         /Library/General/FiniteStructures
         
endspec
