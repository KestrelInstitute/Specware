(* Copyright 2015 Kestrel Institute. See file LICENSE.text for license details *)

(* In Specware, any spec S that does not import any other spec explicitly,
imports spec /Library/Base implicitly. Unless S resides under the
Specware4/Library/Base/ directory, in which case it has no implicit imports. The
latter exception prevents some of the base specs from attempting to import
themselves through the implicit importing of spec Base.

This Empty spec is useful in those rare occasions in which a user might want to
not import (implicitly) any of the base specs. By import Empty, a spec
effectively starts as a clean slate, without the base specs. *)


spec

proof Isa ThyMorphism Main
end-proof
endspec
