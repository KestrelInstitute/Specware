spec

  import Libs/MyBase   % systematically imported (see README.txt)

  (* Positions of syntactic entities (e.g. types and expressions) within
  larger syntactic entities can be identified by sequences of natural numbers
  that describe paths down the trees that represent the syntactic entities in
  question. *)

  type Position = FSeq Nat

endspec
