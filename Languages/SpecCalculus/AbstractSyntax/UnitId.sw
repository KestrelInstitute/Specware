(* Copyright 2015 Kestrel Institute. See file LICENSE for license details *)

SpecCalc qualifying spec {

 %% The support for UnitId's is somewhat simplistic but hopefully sufficient
 %% for now.  A user may specify a unitId that is relative to the current unitId
 %% (ie relative to the object making the reference) or relative to a path
 %% in the SPECPATH environment variable. In the current syntax, the
 %% latter are indicated by an opening "/". In additon, each unitId evaluates
 %% to a full canonical system path. The latter cannot be directly entered
 %% by the user. My apologies for the long constructor names. A relative UnitId
 %% resolves to a canonical UnitId. The latter in turn resolves to an absolute
 %% path in the file system. Recall that file may contain a single anonymous
 %% term or a list of bindings. Thus a canonical UnitId may resolve to two
 %% possible path names. Later we may want to have UIDs with network addresses.

 type UnitIds = List UnitId
 type UnitId = {
		path       : List   String,
		hashSuffix : Option String
	       }

 type RelativeUID =
   | UnitId_Relative   UnitId  % relative to current unit id
   | SpecPath_Relative UnitId  % relative to SPECPATH

 op showUnitId      : UnitId      -> String
 op showRelativeUID : RelativeUID -> String

}
