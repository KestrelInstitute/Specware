spec

  import (spec import Proofs, Provability endspec)
         [PrimitivesAsStringsMorphism]
         [/Library/General/FiniteStructuresAsListsMorphism]


  type Text = List Char

  type Token =
    | rule InferenceRule
    | string String
    | natural Nat
    | positive PosNat
    | openParen
    | closeParen

  type TokenizedText = List Token

  op tokenize : Text -> Option TokenizedText


endspec


(*
Proof
Proofs
Proof?s
TypeName
Operation
AxiomName
TypeVariable
Variable
Variable?
Constructor
Constructors
Field
Fields
Position = FSeq Nat
Nat
FSeq Nat
PosNat

*
Option
FSeq

Nat/PosNat
TypeName
Operation
AxiomName
TypeVariable
Variable
Constructor
Field

tokens:
- rules
- names (7)
- (
- )
- 0
- positive natural
*)
