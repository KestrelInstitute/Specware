
    SpecTransform                    Lisp      C   Java
    -------------------------------  ----     --   ----

 get executable fragment:

     substBaseSpecs                    1        1                 introduces executable version of base ops
    
 transform into simpler subset of metaslang:
    
     normalizeTopLevelLambdas          2        2                 simplify top-level lambdas -- may introduce case expressions, so precedes translateMatch
     instantiateHOFns                  3        3                 may inline local functions -- should preceed lambdaLift, removeCurrying
                                                                  calls simplify?
     removeCurrying                             4                 removes curried functions -- must follow instantiateHOFns
                                                                  
     liftUnsupportedPatterns                    5                 introduces local functions, so should preceed lambdaLift (but orthogonal to instantiateHOFns)

     translateMatch                    6        6                 removes case expressions, introduces local functions, so should preceded lambdaLift
                                                                  removes types?                  
    
     lambdaLift                       -7-       7                 removes local functions
    
     expandRecordMerges                8        8                 replaces << with explicit record constructions

     letWildPatToSeq                            9                 removes wild patterns, introduces sequences  [maybe pointless?]

 introduce options that simplify code generation:

     etaExpansion                     10
     arityNormalize                   11       
     conformOpDecls                            12
     encapsulateProductArgs                    13                 compose tuple of args into a single arg when op has a single parameter 

     introduceRecordMerges                     14                 opposite of expandRecordMerges above -- replaces record constructions with << (useful for setf)
    
     expandTypeDefs                            15                 ??
    
     reviseTypesForGenXXX                      16                 todo: replace with introduceCanonicalTypes ? [create appropriate subtypes of Nat8, Nat16, etc.]

     addEqOpsToSpec                            17                 todo: fold into routines that introduce calls to thse
     addTypeConstructorsToSpec                 18                 todo: ??
    
     sliceSpecforXXX                  19       19                 remove ops not executably reachable [XXX = Lisp, C, Java] 

Note:
 subtractSpec is deprecated                     

   % removeTheorems                    2        2                 todo: is this necessary?
   % simplifySpec                              15                 ?? overkill ??
   % poly2monoAndDropPoly                      19                 todo: is this necessary?
   % sliceSpecforXXX                  [3]      20                 remove ops not executably reachable [XXX = Lisp, C, Java] 

     
