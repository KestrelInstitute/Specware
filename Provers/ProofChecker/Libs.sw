(* Copyright 2015 Kestrel Institute. See file LICENSE.text for license details *)

spec

  (* This spec collects all the library specs used by the proof checker. This
  spec is systematically imported into all other specs in this directory,
  directly or indirectly. Therefore, this spec isolates the proof checker from
  certain changes in the libraries. For instance, if we changed the name of
  the library spec FiniteStructures and if several specs in this directory
  directly referenced FiniteStructures, then all those specs would have to be
  updated, as opposed to just updating this single spec). *)

  import /Library/General/Order
  import /Library/General/FiniteMap
  import /Library/General/Assert
  import /Library/Structures/Data/Maps/SimpleAsAlist
  import IntegerExt
  import StateAndExceptionMonads
         
endspec
