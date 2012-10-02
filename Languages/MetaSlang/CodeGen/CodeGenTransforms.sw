... deprecated ...

(**
 * this spec contains code generation related transformations that are performed
 * before the actual code generation step
 *)

CodeGenTransforms qualifying spec

import Poly2Mono
import AddMissingFromBase
import LetWildPatToSeq
import SubstBaseSpecs
import IdentifyIntTypes
import AddEqOpsToSpec
import AddTypeConstructorsToSpec
import ConformOpDecls 
import AdjustAppl

endspec
