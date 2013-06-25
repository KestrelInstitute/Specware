
    SpecTransform                    Lisp      C   Java
    -------------------------------  ----     --   ----

 get executable fragment:

     substBaseSpecs                    1        1                 introduces various stuff
     sliceSpecforXXX                  (3)       3                 XXX = Lisp, C, Java
     addEqOpsToSpec                            14                 ugh
     addTypeConstructorsToSpec                 16                 
    
 transform into simpler subset of metaslang:
    
     removeCurrying                   (4)       4                 do not introduce new curried functions after this
     normalizeTopLevelLambdas          5        5                 ??
     instantiateHOFns                  6        6                 do not introduce new HO functions after this
                                                                  simplifies?
    
     translateMatch                    8        8                 introduces local functions
                                                                  removes types?                  
    
     lambdaLift                       (7)       7                 do not introduce local functions after this
    
     expandRecordMerges                9        9                 
     letWildPatToSeq                           10                 cosmetic

 introduce options that simplify code generation:

     introduceRecordMerges                      9A                simplifies record constructions to be updates 
                                                                  of pre-existing records (useful for setf)
    
     poly2monoAndDropPoly                      12                 ??
    
     arityNormalize                   10       
     conformOpDecls                            17
     adjustAppl                                18
    
     sliceSpecforXXX                  (3)       3                 XXX = Lisp, C, Java   [??]

     simplifySpec                              13                 ?? overkill ??
     removeTheorems                    2        2                 not needed for code
     removeNonNatSubtypesAndBaseDefs           11                 well-formed specs, but losing ability to prove
     
    
Note:
 subtractSpec is deprecated                     
