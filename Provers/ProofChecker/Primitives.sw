spec

  import Libs   % systematically imported

  (* In LD, names are primitive in the sense that they are not defined in
  terms of other concepts; the only requirements are that there are infinite
  names and that there are distinguished projection names indexed by the
  natural numbers. The whole logic is parameterized over names.

  Here, we differentiate those names according to their syntactic purpose
  (i.e. type names, type variables, etc.), by postulating various primitive
  meta types instead of just one. The reason for this distinction is clarity
  and enforcement of separation (e.g. so that a type variable cannot be
  accidentally used as a type name).

  While in LD axioms have no names, here they do, in order to provide a simple
  way to refer to them (e.g. in proofs).

  Here we do not postulate any projection names because we model product types
  explicitly, as opposed to LD where product types are modeled as
  abbreviations of record types with the postulated projection names as
  fields.

  The overall spec of the proof checker is parameterized over this spec. The
  primitives postulated here can be instantiated (i.e. refined) in different
  ways, obtaining different instances of the proof checker.

  In order to impose the infinity requirement on the meta types we postulate,
  we use the library spec for infinite types. *)

  import translate /Library/General/Type#Infinite by {X +-> TypeName}
  import translate /Library/General/Type#Infinite by {X +-> Operation}
  import translate /Library/General/Type#Infinite by {X +-> TypeVariable}
  import translate /Library/General/Type#Infinite by {X +-> Variable}
  import translate /Library/General/Type#Infinite by {X +-> Field}
  import translate /Library/General/Type#Infinite by {X +-> Constructor}
  import translate /Library/General/Type#Infinite by {X +-> AxiomName}

endspec
