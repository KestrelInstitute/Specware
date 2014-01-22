
(*** An approach to representing Specs with inductive types ***)

(* A glorified record type *)
Inductive SpecType : Type :=
| SpecType_Nil : SpecType
| SpecType_Cons (A : Type) : (A -> SpecType) -> SpecType
.

(* An element of a SpecType *)
Inductive SpecElem : SpecType -> Type :=
| SpecElem_Nil : SpecElem SpecType_Nil
| SpecElem_Cons A B a : SpecElem (B a) -> SpecElem (SpecType_Cons A B)
.

(* A partial element of a SpecType *)
Inductive PartialElem : SpecType -> Type :=
| Part_Nil : PartialElem SpecType_Nil
| Part_ConsNone A B : (forall a, PartialElem (B a)) -> PartialElem (SpecType_Cons A B)
| Part_ConsSome A B a : PartialElem (B a) -> PartialElem (SpecType_Cons A B)
.

(* A partial element can "complete" to an element *)
Inductive CompletesTo : forall T, PartialElem T -> SpecElem T -> Prop :=
| CompletesTo_Nil : CompletesTo _ Part_Nil SpecElem_Nil
| CompletesTo_ConsNone A B a pelem elem :
    CompletesTo (B a) (pelem a) elem ->
    CompletesTo (SpecType_Cons A B) (Part_ConsNone A B pelem)
                (SpecElem_Cons A B a elem)
| CompletesTo_ConsSome A B a pelem elem :
    CompletesTo (B a) pelem elem ->
    CompletesTo (SpecType_Cons A B) (Part_ConsSome A B a pelem)
                (SpecElem_Cons A B a elem)
.
