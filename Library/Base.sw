(* This spec is implicitly imported by any spec S that does not explicitly
import any other spec. Unless S resides under the Specware4/Library/Base/
directory, in which case it has no implicit imports. The latter exception
prevents some of the base specs from attempting to import themselves through the
implicit importing of spec Base. *)

spec

  import Base/Empty                     % Must be cached for it to be useful
  import Base/String
  import Base/System

endspec
