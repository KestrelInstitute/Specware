StandardSpec qualifying spec {
 import AnnSpec
 import /Library/Legacy/DataStructures/NatMapSplay  % for metaTyVars - should be abstracted
 import /Library/Legacy/DataStructures/StringMapSplay % for makeTyVarMap


 sort SortMap      = ASortMap        StandardAnnotation
 sort OpMap        = AOpMap          StandardAnnotation

 sort SortInfo     = ASortInfo       StandardAnnotation 
 sort OpInfo       = AOpInfo         StandardAnnotation

 sort Properties   = AProperties     StandardAnnotation
 sort Property     = AProperty       StandardAnnotation

 sort Specs        = ASpecs          StandardAnnotation
 % sort Sorts        = ASorts          StandardAnnotation
 % sort Ops          = AOps            StandardAnnotation

 sort OpSignature  = AOpSignature    StandardAnnotation
 sort SortScheme   = ASortScheme     StandardAnnotation
 sort TermScheme   = ATermScheme     StandardAnnotation
 sort MetaSortScheme  = AMetaSortScheme StandardAnnotation

 op emptySortMap    : SortMap    
 op emptyOpMap      : OpMap      
 op emptyProperties : Properties 

 def emptySortMap    = emptyASortMap
 def emptyOpMap      = emptyASortMap
 def emptyProperties = emptyAProperties

 sort MetaTyVarsContext = {map     : Ref (NatMap.Map String),
                           counter : Ref Nat}
  
 def initializeMetaTyVars() : MetaTyVarsContext =
   { map = (Ref NatMap.empty), counter = (Ref 0)}

 def findTyVar (context : MetaTyVarsContext, uniqueId) : TyVar =
    let mp = ! context.map in
    case NatMap.find(mp,uniqueId) of
       | Some name -> name
       | None -> 
         let number    = ! context.counter   in
         let increment = number Nat.div 5           in
         let parity    = number Nat.rem 5           in
         let prefix = 
             (case parity
                of 0 -> "a" | 1 -> "b" | 2 -> "c" | 3 -> "d" | 4 -> "e")
         in  
         let suffix = if increment = 0 then "" else Nat.toString increment in
         let name = prefix ^ suffix in name 
 def mapImage (m, vars) = 
     List.map (fn d -> case StringMap.find (m, d) of Some v -> v) vars


 % The following are used in the semantic rules in the parser.

 op abstractSort : (String -> TyVar) * List String * MS.Sort -> TyVars * MS.Sort
 def abstractSort (fresh, tyVars, srt) = 
  if null tyVars then ([], srt) else
  let (m, doSort) = makeTyVarMap (fresh, tyVars) in
  let srt = mapSort (fn M -> M, doSort, fn p -> p) srt in
  (mapImage (m, tyVars), srt)

 op abstractTerm : (String -> TyVar) * List String * MS.Term -> TyVars * MS.Term
 def abstractTerm (fresh, tyVars, trm) = 
  let (m, doSort) = makeTyVarMap (fresh, tyVars) in
  let trm = mapTerm (fn M -> M, doSort, fn p -> p) trm in
  (mapImage (m, tyVars), trm)

 %%
 %% It is important that the order of the type variables is preserved
 %% as this function is used to abstract sort in recursive sort defintions.
 %% For example, if 
 %% sort ListPair(a,b) = | Nil | Cons a * b * ListPair(a,b)
 %% is defined, then abstractSort is used to return the pair:
 %% ( (a,b), | Nil | Cons a * b * ListPair(a,b) )
 %%

 op makeTyVarMap: (String -> TyVar) * List String
                 -> StringMap.Map String * (MS.Sort -> MS.Sort)
 def makeTyVarMap (fresh, tyVars) = 
  let def insert (tv, map) = StringMap.insert (map, tv, fresh tv) in
  let m = List.foldr insert StringMap.empty tyVars in
  let doSort = 
      fn (srt as (Base (Qualified (_, s), [], pos)) : MS.Sort) -> 
         (case StringMap.find (m, s) of
           | Some tyVar -> (TyVar (tyVar, pos)) : MS.Sort
           | None -> srt) 
       | s -> s
  in
    (m, doSort)

 op mkApplyN      : MS.Term * MS.Term                 -> MS.Term
 def mkApplyN (t1, t2) : MS.Term = ApplyN ([t1, t2],       internalPosition)

 op mkList        : List MS.Term * Position * MS.Sort -> MS.Term
 def mkList (terms : List MS.Term, pos, element_type) = 
  let list_type  = Base (Qualified ("List", "List"),                                [element_type], pos) in
  let cons_type  = Arrow (Product   ([("1", element_type), ("2", list_type)], pos),  list_type,      pos) in
  let consFun    = Fun   (Embed     ("Cons", true),                                  cons_type,      pos) in
  let empty_list = Fun   (Embed     ("Nil",  false),                                 list_type,      pos) in
  let def mkCons (x, xs) = ApplyN ([consFun, Record( [("1",x), ("2",xs)], pos)], pos) in
  List.foldr mkCons empty_list terms

 % ------------------------------------------------------------------------
 %  Recursive constructors of MS.Pattern's
 % ------------------------------------------------------------------------

 op mkListPattern : List MS.Pattern       * Position * MS.Sort -> MS.Pattern
 op mkConsPattern : MS.Pattern * MS.Pattern * Position * MS.Sort -> MS.Pattern

 def mkListPattern (patterns : List MS.Pattern, pos, element_type) : MS.Pattern = 
  let list_type  = Base (Qualified("List","List"),  [element_type], pos) in
  let empty_list = EmbedPat ("Nil",  None,  list_type, pos) in
  let def mkCons (x, xs) = 
       EmbedPat ("Cons", Some (RecordPat ([("1",x), ("2",xs)], pos)), list_type, pos) in
  List.foldr mkCons empty_list patterns

 def mkConsPattern (p1 : MS.Pattern, p2 : MS.Pattern, pos, element_type) : MS.Pattern =
  let list_type  = Base (Qualified("List","List"), [element_type], pos) in
  EmbedPat ("Cons", Some (RecordPat ([("1",p1), ("2",p2)], pos)), list_type, pos)
}
