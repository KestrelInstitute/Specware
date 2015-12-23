(* Copyright 2015 Kestrel Institute. See file LICENSE for license details *)

(* This spec is implicitly imported by any spec S that does not explicitly
import any other spec. Unless S resides under the Specware4/Library/Base/
directory, in which case it has no implicit imports. The latter exception
prevents some of the base specs from attempting to import themselves through the
implicit importing of spec Base.

The seemingly unnecessary importing of spec Empty ensures that, when Specware
starts up and loads the base library specs, spec Empty is loaded and cached as
well. *)

spec

import Base/Empty
import Base/String

endspec
