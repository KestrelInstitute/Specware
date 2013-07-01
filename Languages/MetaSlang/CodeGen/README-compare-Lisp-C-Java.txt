
    SpecTransform                    Lisp      C   Java
    -------------------------------  ----     --   ----

 get executable fragment:

     substBaseSpecs                    1        1                 adds executable versions of base ops
    
 transform into simpler subset of metaslang:
    
     normalizeTopLevelLambdas          2        2                 removes cases from top-level lambdas -- moves cases into lambda body, must preceed translateMatch

     instantiateHOFns                  3        3                 removes some calls to HO functions and inlines some local function -- must preceed removeCurrying, lambdaLift
                                                                     TODO: why does it call simplify?

     removeCurrying                             4                 removes curried functions -- must follow instantiateHOFns

     liftUnsupportedPatterns                    5                 removes type restrictions -- adds case expressions, so should preceed translateMatch

     translateMatch                    6        6                 removes case expressions  -- adds local functions,  so should preceded lambdaLift
                                                                  removes types?                  
    
     lambdaLift                       -7-       7                 removes local functions   -- adds top-level functions
    
     expandRecordMerges                8        8                 removes <<                -- adds explicit record constructions

     letWildPatToSeq                            9                 removes wild patterns     -- adds sequences  [is this pointless?]

 options that simplify code generation:

     etaExpansion                     10                          
     arityNormalize                   11                          
     conformOpDecls                            12                 
     encapsulateProductArgs                    13                 compose tuple of args into a single arg when op has a single parameter 

     introduceRecordMerges                     14                 opposite of expandRecordMerges above -- replaces record constructions with << (useful for setf)
    
     expandTypeDefs                            15                 ??
    
     reviseTypesForGen<Target>                 16                 revise types to be subtypes native to <target> language: Nat8, Int32, etc.

     addEqOpsToSpec                            17                 todo: fold into routines that introduce calls to thse
     addTypeConstructors                       18                 todo: ??
    
     sliceSpecfor<Target>             19       19                 remove ops not executably reachable [<Target> = Lisp, C, Java] 

Note:
 subtractSpec is deprecated                     

   % removeTheorems                    2        2                 todo: is this necessary?
   % simplifySpec                              15                 ?? overkill ??
   % poly2monoAndDropPoly                      19                 todo: is this necessary?

     
