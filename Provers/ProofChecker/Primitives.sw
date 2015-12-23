(* Copyright 2015 Kestrel Institute. See file LICENSE for license details *)

MetaslangProofChecker qualifying
spec

  % API public all

  import Libs  % systematically imported

  (* In LD, names are primitive in the sense that they are not defined in
  terms of other concepts. The only requirements are that there are infinite
  names and that there exist certain distinguished names, used as fields of
  products types (the "pi" names) and as bound variables of expression
  abbreviations (the "gamma", "psi", and "phi" names). The whole logic is
  parameterized over names.

  Here, we differentiate those names according to their syntactic purpose
  (i.e. type names, type variables, etc.), by postulating various primitive
  meta types instead of just one. The reasons for this distinction are
  enhanced clarity and enforcement of separation (e.g. so that a type variable
  cannot be accidentally used as a type name, because otherwise a
  type-checking error would occur).

  While in LD axioms and lemmas have no names, here they do, in order to
  provide a simple way to refer to them (e.g. in proofs).

  Instead of postulating meta types for fields and variables along with ops to
  denote the distinguished fields and variables ("pi" fields etc.), we
  postulate meta types for the fields and variables that differ from the
  distinguished ones and then we add the distinguished ones via meta type sums
  (in spec TypesAndExpressions). We prepend the primitive meta type names for
  fields and variables with "User", to convey the idea that they only contain
  fields and variables provided by the user, while the distinguished fields
  and variables are machine-generated, by expansions of abbreviations.

  The proof checker is parameterized over this spec. The primitives postulated
  here can be instantiated (i.e. refined) in different ways, obtaining
  different instances of the proof checker. *)

  import translate /Library/General/Type#Infinite by {X +-> TypeName}
  import translate /Library/General/Type#Infinite by {X +-> Operation}
  import translate /Library/General/Type#Infinite by {X +-> TypeVariable}
  import translate /Library/General/Type#Infinite by {X +-> UserVariable}
  import translate /Library/General/Type#Infinite by {X +-> UserField}
  import translate /Library/General/Type#Infinite by {X +-> AxiomName}
  import translate /Library/General/Type#Infinite by {X +-> LemmaName}

endspec
