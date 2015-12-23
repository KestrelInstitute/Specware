(* Copyright 2015 Kestrel Institute. See file LICENSE for license details *)

StandardSpec qualifying spec
 import AnnSpec
 import /Library/Legacy/DataStructures/NatMapSplay  % for metaTyVars - should be abstracted
 import /Library/Legacy/DataStructures/StringMapSplay % for makeTyVarMap

 type TypeMap      = ATypeMap        StandardAnnotation
 type OpMap        = AOpMap          StandardAnnotation

% type Property     = AProperty       StandardAnnotation

 type Specs        = ASpecs          StandardAnnotation
 % type Types        = ATypes          StandardAnnotation
 % type Ops          = AOps            StandardAnnotation

 op addTypeDef(spc: Spec, qid as Qualified(q,id): QualifiedId, dfn: MSType): Spec =
   spc << {types = insertAQualifierMap(spc.types, q, id, {names = [qid], dfn = dfn}),
           elements = spc.elements ++ [TypeDef(qid,noPos)]}

 op addOpDef(spc: Spec, qid as Qualified(q,id): QualifiedId, fixity: Fixity, dfn: MSTerm): Spec =
   spc << {ops = insertAQualifierMap(spc.ops, q, id, 
                                     {names = [qid], dfn = dfn, fixity = fixity, fullyQualified? = false}),
           elements = spc.elements ++ [Op(qid,true,noPos)]}

 type MetaTypeScheme = AMetaTypeScheme StandardAnnotation

 op emptyTypeMap  : TypeMap    
 op emptyOpMap    : OpMap      
 op emptyElements : SpecElements 

 def emptyTypeMap  = emptyATypeMap
 def emptyOpMap    = emptyATypeMap
 def emptyElements = emptyAElements

 type MetaTyVarsContext = {map     : Ref (NatMap.Map String),
                           counter : Ref Nat}
  
 def initializeMetaTyVars() : MetaTyVarsContext =
   { map = (Ref NatMap.empty), counter = (Ref 0)}

 def findTyVar (context : MetaTyVarsContext, uniqueId) : TyVar =
    let mp = ! context.map in
    case NatMap.find(mp,uniqueId) of
       | Some name -> name
       | None -> 
         let number    = ! context.counter in
         let increment = number div 5 in
         let parity    = number mod 5 in
         let prefix = 
             (case parity
                of 0 -> "a" | 1 -> "b" | 2 -> "c" | 3 -> "d" | 4 -> "e")
         in  
         let suffix = if increment = 0 then "" else show increment in
         let name = prefix ^ suffix in name 
 def mapImage (m, vars) = 
     List.map (fn d -> case StringMap.find (m, d) of Some v -> v) vars


 % The following are used in the semantic rules in the parser.

 op abstractType : (String -> TyVar) * List String * MSType -> TyVars * MSType
 def abstractType (fresh, tyVars, srt) = 
  if empty? tyVars then ([], srt) else
  let (m, doType) = makeTyVarMap (fresh, tyVars) in
  let srt = mapType (fn M -> M, doType, fn p -> p) srt in
  (mapImage (m, tyVars), srt)

 op newAbstractType : (String -> TyVar) * List String * MSType -> MSType
 def newAbstractType (fresh, tyVars, srt) = 
  if empty? tyVars then 
    srt
  else
    let (m, doType) = makeTyVarMap (fresh, tyVars) in
    let srt = mapType (fn M -> M, doType, fn p -> p) srt in
    let tvs = mapImage (m, tyVars) in
    maybePiType (tvs, srt)

 op abstractTerm : (String -> TyVar) * List String * MSTerm -> TyVars * MSTerm
 def abstractTerm (fresh, tyVars, trm) = 
  let (m, doType) = makeTyVarMap (fresh, tyVars) in
  let trm = mapTerm (fn M -> M, doType, fn p -> p) trm in
  (mapImage (m, tyVars), trm)

 op newAbstractTerm : (String -> TyVar) * List String * MSTerm -> MSTerm
 def newAbstractTerm (fresh, tyVars, trm) = 
  let (m, doType) = makeTyVarMap (fresh, tyVars) in
  let trm = mapTerm (fn M -> M, doType, fn p -> p) trm in
  let tvs = mapImage (m, tyVars) in
  maybePiTerm (tvs, trm)

 %%
 %% It is important that the order of the type variables is preserved
 %% as this function is used to abstract type in recursive type defintions.
 %% For example, if 
 %% type ListPair(a,b) = | Nil | Cons a * b * ListPair(a,b)
 %% is defined, then abstractType is used to return the pair:
 %% ( (a,b), | Nil | Cons a * b * ListPair(a,b) )
 %%

 op makeTyVarMap: (String -> TyVar) * List String
                 -> StringMap.Map String * (MSType -> MSType)
 def makeTyVarMap (fresh, tyVars) = 
  let def insert (tv, map) = StringMap.insert (map, tv, fresh tv) in
  let m = List.foldr insert StringMap.empty tyVars in
  let doType = 
      fn (srt as (Base (Qualified (_, s), [], pos)) : MSType) -> 
         (case StringMap.find (m, s) of
           | Some tyVar -> (TyVar (tyVar, pos)) : MSType
           | None -> srt) 
       | s -> s
  in
    (m, doType)

 op mkApplyN      : MSTerm * MSTerm                 -> MSTerm
 def mkApplyN (t1, t2) : MSTerm = ApplyN ([t1, t2],       internalPosition)

 op mkListN (terms : MSTerms, pos: Position, element_type: MSType): MSTerm = 
  let list_type  = Base (Qualified ("List", "List"),  [element_type], pos) in
  let list1_type = Base (Qualified ("List", "List1"), [element_type], pos) in
  let cons_type  = Arrow (Product   ([("1", element_type), ("2", list_type)], pos),
                          list1_type, pos) in
  let consFun    = Fun   (Embed     (Qualified("List", "Cons"), true),  cons_type, pos) in
  let empty_list = Fun   (Embed     (Qualified("List", "Nil"),  false), list_type, pos) in
  let def mkCons (x, xs) = ApplyN ([consFun, Record( [("1",x), ("2",xs)], pos)], pos) in
  foldr mkCons empty_list terms

op mkList (terms : MSTerms, pos: Position, element_type: MSType): MSTerm = 
  let list_type  = Base (Qualified ("List", "List"),  [element_type], pos) in
  let list1_type = Base (Qualified ("List", "List1"), [element_type], pos) in
  let cons_type  = Arrow (Product   ([("1", element_type), ("2", list_type)], pos),
                          list1_type, pos) in
  let consFun    = Fun   (Embed     (Qualified("List", "List"), true),  cons_type, pos) in
  let empty_list = Fun   (Embed     (Qualified("List", "Nil"),  false), list_type, pos) in
  let def mkCons (x, xs) = Apply (consFun, Record( [("1",x), ("2",xs)], pos), pos) in
  foldr mkCons empty_list terms


 % ------------------------------------------------------------------------
 %  Recursive constructors of MSPattern's
 % ------------------------------------------------------------------------

 op mkListPattern : MSPatterns            * Position * MSType -> MSPattern
 op mkConsPattern : MSPattern * MSPattern * Position * MSType -> MSPattern

 def mkListPattern (patterns : MSPatterns, pos, element_type) : MSPattern = 
  let list_type  = Base (Qualified("List","List"),  [element_type], pos) in
  let empty_list = EmbedPat (Qualified("List", "Nil"),  None,  list_type, pos) in
  let def mkCons (x, xs) = 
       EmbedPat (Qualified("List", "Cons"), Some (RecordPat ([("1",x), ("2",xs)], pos)), list_type, pos) in
  List.foldr mkCons empty_list patterns

 def mkConsPattern (p1 : MSPattern, p2 : MSPattern, pos, element_type) : MSPattern =
  let list_type  = Base (Qualified("List","List"), [element_type], pos) in
  EmbedPat (Qualified("List", "Cons"), Some (RecordPat ([("1",p1), ("2",p2)], pos)), list_type, pos)

endspec
