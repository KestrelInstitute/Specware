LispGen qualifying spec

import /Languages/MetaSlang/Transformations/SliceSpec

op builtInLispOp?   (qid : QualifiedId) : Bool = 
 printPackageId(qid, "") in? SpecToLisp.SuppressGeneratedDefuns

op builtInLispType? (qid : QualifiedId) : Bool = 
 false

op SpecTransform.sliceSpecForLisp (spc             : Spec)
                                  (root_ops        : QualifiedIds)
                                  (root_types      : QualifiedIds)
 : Spec =
 sliceSpecForCode (spc, root_ops, root_types, builtInLispOp?, builtInLispType?)


end-spec
