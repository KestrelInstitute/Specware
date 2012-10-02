
                                 Lisp       C      Java
                                 ----     ----     ----
 subtractSpec                     ...      (0)     (4)
 substBaseSpecs                   (1)      (1)B    (1,6)SJ
 sliceSpec                        ...
 addMissingFromBase                        (2)     (5)
 removeCurrying                   ...      (3)
 normalizeTopLevelLambdas         (2)      (4)     (2)
 instantiateHOFns                 (3)      (5)     (3)
 lambdaToInner                             ...
 lambdaLift                       ...      (6)     (7)
 unfoldSortAliases                                 (8)
 specStripSubsortsAndBaseDefs              (7) 
 identifyIntTypes                                 (10)*
 poly2mono                                 (8)    (11)
 letWildPatToSeq                           (9)    (12)
 translateMatch                   (4)     (10)    (13)J
 translateRecordMergeInSpec       (5)     (11)     (9)
 simplifySpec                             (12)    (14)
 addEqOpsToSpec                           [13]
 addSortConstructorsToSpec                (14)
 arityNormalize                   (6)     (15)    (15)
 distinctVariable                                 (16)


similar:
  arityNormalize
  etaExpandDefs
  conformOpDecls ; adjustAppl
