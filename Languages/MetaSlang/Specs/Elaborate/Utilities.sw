% Utilities qualifying
spec { 
 import SpecToPosSpec   % for PosSpec's, plus convertSort[Info]ToPSort[Info]
 import ../Printer        % for error messages
 import /Library/Legacy/DataStructures/MergeSort % for combining error messages
 import /Library/Legacy/DataStructures/ListPair  % misc utility

 sort Environment = StringMap Spec
 sort LocalEnv = 
      {importMap  : Environment,
       internal   : PosSpec,
       errors     : Ref(List (String * Position)),
       specName   : String,
       vars       : StringMap PSort,
       firstPass? : Boolean,
       constrs    : StringMap (List PSortScheme),
       file       : String}                        
 
 op initialEnv     : SpecRef * PosSpec * String -> LocalEnv
 op addConstrsEnv  : LocalEnv * PosSpec -> LocalEnv

 op addVariable    : LocalEnv * String * PSort -> LocalEnv
 op secondPass     : LocalEnv                  -> LocalEnv
 op unfoldPSort    : LocalEnv * PSort          -> PSort
 op findVarOrOps   : LocalEnv * Id * Position  -> List PTerm

 op error          : LocalEnv * String * Position -> ()

 % def pos0 = zeroPosition() ... ### defined in ../PosSpec

 (* Auxiliary functions: *)

 % Generate a fresh type variable at a given position.
 op freshMetaTyVar : Position -> PSort
 def counter = (Ref 0) : Ref Nat
 def freshMetaTyVar pos = 
   (counter := 1 + (! counter);
    MetaTyVar (Ref {link = None,uniqueId = ! counter,name = "#fresh"}, pos))
 def initializeMetaTyVar() = counter := 0

 op copySort : PSortScheme -> PMetaSortScheme

 op  unlinkPSort : PSort -> PSort
 %% sjw: Dereferences the link recursively
 def unlinkPSort srt = 
  case srt of
   | MetaTyVar (tv, _) -> 
     (case ! tv of
       | {link = Some srt, name, uniqueId} -> unlinkPSort srt
       | _ -> srt)
   | _ -> srt 

 %% sjw: unused?
 def unlinkMetaTyVar (tv : PMetaTyVar) = 
   case ! tv
     of {link = Some (MetaTyVar (tw, _)), name, uniqueId} -> unlinkMetaTyVar tw
      | _ -> tv

 def copySort (tyVars, srt) = 
   if null tyVars then
     ([],srt)
   else
     let tyVarMap = List.map (fn tv -> (tv, freshMetaTyVar pos0)) tyVars in
     let
        def mapTyVar (tv, tvs, pos) : PSort = 
            case tvs
              of [] -> TyVar(tv,pos)
               | (tv1,s)::tvs -> 
                 if tv = tv1 then s else mapTyVar (tv, tvs, pos)
     in
     let
        def cp (srt : PSort) = 
            case srt
              of TyVar (tv, pos) -> mapTyVar (tv, tyVarMap, pos)
               | srt -> srt
     in
     let srt = mapSort (fn x -> x, cp, fn x -> x) srt                              in
     let metaTyVars = List.map (fn(_, (MetaTyVar (y,_)) : PSort) -> y) tyVarMap in
     (metaTyVars,srt)


  op initPrimitiveSpec : Qualifier -> Id -> List String -> Spec
  def initPrimitiveSpec qualifier id tyvars =
    %% we expect the qualifier to be the same as id, e.g. Boolean.Boolean
    {imports          = emptyImports,
     importedSpec     = None,
     sorts            = insertAQualifierMap (emptyAQualifierMap, qualifier, id,
                                             ([Qualified (qualifier, id)], tyvars, None)),
     ops              = emptyAQualifierMap,
     properties       = emptyProperties
    } 

  def stringSpec  = initPrimitiveSpec "String"  "String"  []
  def charSpec    = initPrimitiveSpec "Char"    "Char"    []
  def boolSpec    = initPrimitiveSpec "Boolean" "Boolean" []
  def listSpec    = initPrimitiveSpec "List"    "List"    ["a"]
  def generalSpec = initPrimitiveSpec "General" "General" ["a"]
  def natSpec     = initPrimitiveSpec "Nat"     "Nat"     []
  def intSpec     = initPrimitiveSpec "Integer" "Integer" []

 %
 % Boot strapping environment
 %        
 def baseSpec : Spec = 
%%%le   let base_op_map =
%%%le       foldr (fn (name, map) -> 
%%%le              insertAQualifierMap(map, "BaseSpecs", name,
%%%le                                 ([Qualified(name,name)], 
%%%le                                  Nonfix, 
%%%le                                  ([], mkBase(["MetaSlang","Spec"], [])), 
%%%le                                  None)))
%%%le             emptyAQualifierMap
%%%le             ["Integer",
%%%le              "Nat",     
%%%le              "Char",    
%%%le              "Boolean", 
%%%le              "String",  
%%%le              "List",    
%%%le              "General", 
%%%le              "TranslationBuiltIn"]
%%%le   in
%%%le     {ops           = base_op_map,
     {imports          = emptyImports,
      importedSpec     = None,
      sorts            = emptyAQualifierMap,
      ops              = emptyAQualifierMap,
      properties       = emptyProperties
     }

 def initialEnv (spec_name, spc, file) = 
   let errs : List (String * Position) = [] in
   let {imports, importedSpec, sorts, ops, properties} = spc in
   let MetaTyVar(tv,_)  = freshMetaTyVar(pos0) in % ?
%%%le    let external = merge(external, "String",    stringEnv)  in
%%%le    let external = merge(external, "Nat",       natEnv)     in
%%%le    let external = merge(external, "Integer",   intEnv)     in
%%%le    let external = merge(external, "Boolean",   boolEnv)    in
%%%le    let external = merge(external, "Char",      charEnv)    in
%%%le    let external = merge(external, "List",      listEnv)    in
%%%le    let external = merge(external, "General",   generalEnv) in
%%%le    let external = merge(external, "BaseSpecs", baseEnv)    in
   %% Try just leaving the immediate imports
%%%le    let imports = %foldr (insert external) [] 
%%%le                  (imports ++ ["String","Nat","Boolean","Integer",
%%%le                               "Char","List","General"])
%%%le    in
%%%le    let importedSpecs = importedSpecsEnv(imports,external) in
   %% importedSpecs is the subset of external used
   %% let importMap = importedSpecs in
   let spc = {imports      = imports,
              importedSpec = importedSpec,
              sorts        = sorts,
              ops          = ops,
              properties   = properties
             } : PosSpec
   in
   let env = {importMap  = StringMap.empty, % importMap,
              specName   = spec_name,
              internal   = spc,
              errors     = Ref errs,
              vars       = StringMap.empty,
              firstPass? = true,
              constrs    = StringMap.empty,
              file       = file
             } : LocalEnv
   in
%%%le    let
%%%le        def importIt(importName) = 
%%%le          case findImportNamed(external,importName)
%%%le            of None -> error(env,"Imported spec "^importName^" has not been defined",pos0)
%%%le             | Some _ -> ()
%%%le    in 
%%%le    let _  = app importIt imports  in          
   env

 def sameCPSort? (s1: PSort, s2: PSort): Boolean =
   case (s1,s2) of
    | (CoProduct(row1,_), CoProduct(row2,_)) ->
      length row1 = length row2
      & all (fn (id1,cs1) ->
             exists (fn (id2,cs2) -> id1 = id2 & cs1 = cs2) row2)
            row1
   | _ -> false

 def addConstrsEnv({importMap, internal, vars, specName, errors, firstPass?,
                    constrs, file},
                   sp) =
   {importMap  = importMap,
    internal   = sp,
    vars       = vars,
    specName   = specName,
    errors     = errors,
    firstPass? = firstPass?,
    constrs    = computeConstrMap(sp), % importMap
    file       = file}

 %% Computes a map from constructor names to set of sorts for them
 def computeConstrMap (spc) : StringMap (List PSortScheme) =
   let sorts = spc.sorts in
   let constrMap : Ref (StringMap (List PSortScheme)) = Ref StringMap.empty 
   in
   let def addConstr (id, tvs, cp_srt) =
         let cMap = ! constrMap in
         case StringMap.find (cMap, id)
           of None -> constrMap := StringMap.insert(cMap, id, [(tvs,cp_srt)])
            | Some srt_prs ->
              if exists (fn(_,o_srt) -> sameCPSort?(o_srt, cp_srt)) srt_prs
               then ()
               else constrMap := StringMap.insert(cMap, id,
                                                  cons((tvs,cp_srt),srt_prs))
   in
   let def addSort (tvs, srt) =
        case srt : PSort of
         | CoProduct (row, _) ->
           app (fn (id,_) -> addConstr (id, tvs, srt)) row
         %% | PBase (Qualified (qid, id), _, _) ->
         %%   (let matching_entries : List(String * QualifiedId * SortInfo) = 
         %%           lookupSortInImports(importMap, qid, id)
         %%       in
         %%       case matching_entries
         %%  of [(_, _, (_, e_tvs, Some e_srt))] ->
         %%     addSort(e_tvs, convertSortToPSort e_srt)
         %%   | _ -> ())
         | _ -> ()
   in
   let _ = appAQualifierMap 
             (fn ((sort_names, tyvars, opt_def)) -> 
              (case opt_def : Option(PSort)
                of None     -> ()
                 | Some srt -> addSort (tyvars, srt)))
             sorts
   in
   %% Look at at all sorts mentioned in spec
   let _ = mapSpec (fn x -> x, fn s -> (addSort([],s);s), fn p -> p) spc 
   in ! constrMap

 op  checkErrors : LocalEnv -> Option String

 def checkErrors(env:LocalEnv) = 
   let errors = env.errors in
   let def comp((l,c),(l2,c2)) = 
         case Nat.compare(l,l2)
           of EQUAL -> Nat.compare(c,c2)
            | c -> c
   in
   let def compare((m1,(l,r)),(m2,(l2,r2))) = 
         case comp(l,l2)
           of EQUAL -> 
              (case comp(r,r2)
                 of EQUAL -> String.compare(m1,m2)
                  | c     -> c)
            | c -> c
   in
   let errors = MergeSort.uniqueSort compare (! errors) in
   let errMsg = (Ref "") : Ref String in
   let def printError(msg,pos) = 
         errMsg := (! errMsg) ^
                   printPosition pos^":"^msg^PrettyPrint.newlineString()
              
   in
   if null(errors) then 
     None
   else
     (let (_,((l,r),_))::_ = errors in
      IO.gotoFilePosition(env.file,l,r);
      app printError errors;
      %               StringMap.app
      %                (fn spc -> MetaSlangPrint.printSpecToTerminal 
      %                                (convertPosSpecToSpec spc)) env.importMap;
      Some(! errMsg)
     )
      
  def error(env as {errors,importMap,internal,specName,vars,
                    firstPass?,constrs,file},
            msg,
            pos) 
    = 
    errors := cons((msg,pos),! errors)


  def addVariable({importMap,internal,vars,specName,errors,
                   firstPass?,constrs,file},
                  id,
                  srt) = 
    {importMap  = importMap,
     internal   = internal,
     vars       = StringMap.insert(vars,id,srt),
     specName   = specName,
     errors     = errors,
     firstPass? = firstPass?,
     constrs    = constrs,
     file       = file
    }
        
  def secondPass({importMap,internal,vars,specName,errors,
                  firstPass?=_,constrs,file}) = 
    {importMap  = importMap,
     internal   = internal,
     vars       = vars,
     specName   = specName,
     errors     = errors,
     firstPass? = false,
     constrs    = constrs,
     file       = file
    }

 (* Unlink and unfold recursive sort declarations *)

 def compareQId (Qualified (q1, id1), Qualified (q2, id2)): Comparison = 
  case String.compare (q1, q2) of
   | EQUAL  -> String.compare (id1, id2)
   | result -> result

 %% sjw: Replace base srt by its instantiated definition
 def unfoldPSort (env,srt) = unfoldPSortRec(env, srt, SplaySet.empty compareQId)

 def unfoldPSortRec (env, srt, qids) : PSort = 
   let unlinked_sort = unlinkPSort srt in
   case unlinked_sort of
    | PBase (qid, ts, pos) -> 
      if SplaySet.member (qids, qid) then
         (error(env,
                "The sort "^(printQualifiedId qid)^" is recursively defined using itself",
                pos);
          unlinked_sort)
      else
        (case findAllSorts (env.internal, qid) of
          | sort_info::r ->
            (case sort_info of
              | (main_qid::_, tvs, None) ->        % sjw: primitive sort
                let l1 = length tvs in
                let l2 = length ts  in
                ((if ~(l1 = l2) then
                    error(env,"Instantiation list does not match argument list",
                          pos)
                  else 
                    ());
                 %% Use the primary name, even if the reference was via some alias.
                 %% This normalizes all references to be via the same name.
                 PBase (main_qid, ts, pos))
              | (aliases, tvs, Some (srt as PBase(_,_,pos))) -> 
                %% A base sort can be defined in terms of another base sort.
                %% So we unfold recursively here.
                unfoldPSortRec(env,
                               instantiateScheme (env, pos, ts, tvs, srt),
                               %% Watch for self-references, even via aliases: 
                               foldl (fn (qid, qids) -> SplaySet.add (qids, qid))
                                     qids
                                     aliases)
              | (aliases, tvs, Some srt) ->
                instantiateScheme(env, pos, ts, tvs, srt))
          | [] -> 
               (error (env, "Could not find definition of sort "^ printQualifiedId qid, pos);
                unlinked_sort))
    | s -> s 

 %% sjw: Returns srt with all  sort variables dereferenced
 def unlinkRec(srt) = 
   mapSort (fn x -> x, 
            fn s -> unlinkPSort s,
            fn x -> x)
           srt
    
 %% findTheFoo2 is just a variant of findTheFoo, 
 %%  but taking Qualifier * Id instead of QualifiedId
 op findTheSort2 : LocalEnv * Qualifier * Id -> Option PSortInfo
 op findTheOp2   : LocalEnv * Qualifier * Id -> Option POpInfo

 def findTheSort2 (env, qualifier, id) =
  %% We're looking for precisely one sort,
  %% which we might have specified as being unqualified.
  %% (I.e., unqualified is not a wildcard here.)
  findAQualifierMap (env.internal.sorts, qualifier, id)

 def findTheOp2 (env, qualifier, id) =
  %% We're looking for precisely one op,
  %% which we might have specified as being unqualified.
  %% (I.e., unqualified is not a wildcard here.)
  findAQualifierMap (env.internal.ops, qualifier, id)

 def findVarOrOps ({errors, importMap, internal, vars, specName, firstPass?, constrs, file}: LocalEnv,
                   id,
                   a)
  =
  let 
     def mkTerm (a, (qids, fixity, (tyvars,srt), _)) = 
      let (_,srt) = copySort(tyvars,srt) in
      case qids of
       | (Qualified (qualifier, id))::misc ->
         Fun (%% Allow (UnQualified, x) through as TwoNames term ...
              %% if qualifier = UnQualified
              %%  then OneName  (           id, fixity) 
              %% else 
              TwoNames (qualifier, id, fixity),
              srt, 
              a)
    def mkTerms infos =
      List.map (fn info -> mkTerm  (a, info)) infos
  in
  case StringMap.find (vars, id) of
   | Some srt -> [Var((id, srt), a)]
   | None     -> mkTerms (wildFindUnQualified (internal.ops, id))


 def instantiateScheme (env, pos, types, type_vars, srt) = 
   if ~(length types = length type_vars) then
     (error (env, "Instantiation list does not match argument list", pos);
      srt)
   else
     let (new_type_vars, new_srt) = copySort (type_vars, srt) in
     (ListPair.app (fn (type, new_type_var) -> 
                    let {uniqueId,name,link} = ! new_type_var in
                    new_type_var := {link     = Some type,
                                     uniqueId = uniqueId,
                                     name     = name})
                   (types, new_type_vars);
      new_srt)


 sort Unification = | NotUnify  PSort * PSort 
                    | Unify List(PSort * PSort)

 op  unifyL : fa(a) PSort * PSort * List(a) * List(a) * List(PSort * PSort) *         
                    (a * a *  List(PSort * PSort) -> Unification) 
                    ->
                        Unification
 def unifyL(srt1,srt2,l1,l2,pairs,unify):Unification = 
   case (l1,l2)
     of ([],[]) -> Unify pairs
      | (e1::l1,e2::l2) -> 
        (case unify(e1,e2,pairs)
           of Unify pairs -> unifyL(srt1,srt2,l1,l2,pairs,unify)
            | notUnify    -> notUnify)
      | _ -> NotUnify(srt1,srt2)

 def unifySorts env s1 s2 =

   (* Unify possibly recursive sorts s1 and s2.
      The auxiliary list "pairs" is a list of pairs of 
      sorts that can be assumed unified. The list avoids
      indefinite expansion of recursive sorts.
           
      Let for instance:

      sort T[x] = A + T[x]
      sort S = A + S

      then T[A] unifies with S
      because (T[A],S) is inserted to the list "pairs" in the
      first recursive invocation of the unification and 
      prevents further recursive calls.

      sort S = A + (A + S)
      sort T = A+T

      These also unify.

      More generally  sorts unify just in case that their
      unfoldings are bisimilar.

      *)

   %%    let _ = String.writeLine "Unifying"     in
   %%    let _ = System.print s1 in
   %%    let _ = System.print s2 in
   %%    let _ = String.writeLine (printSort s1) in
   %%    let _ = String.writeLine (printSort s2) in

   let
       def unifyCP(srt1,srt2,r1,r2,pairs):Unification = 
           unifyL(srt1, srt2, r1, r2, pairs,
                  fn ((id1,s1),(id2,s2),pairs) -> 
                  if id1 = id2 then
                    (case (s1,s2) of
                        | (None,None) -> Unify pairs 
                        | (Some s1,Some s2) -> unify(s1,s2,pairs)
                        | _ -> NotUnify(srt1,srt2))
                  else
                    NotUnify(srt1,srt2))

       def unifyP(srt1,srt2,r1,r2,pairs):Unification = 
           unifyL(srt1,srt2,r1,r2,pairs,
                  fn((id1,s1),(id2,s2),pairs) -> 
                  if id1 = id2 
                  then unify(s1,s2,pairs)
                  else NotUnify(srt1,srt2))
           
       def unify(s1,s2,pairs):Unification = 
         let pos1 = sortAnn(s1) in
         let pos2 = sortAnn(s2) in
         let srt1 = withAnnS(unlinkPSort s1, pos1) in
         let srt2 = withAnnS(unlinkPSort s2, pos2) in
         if equalSort?(srt1,srt2) then 
           Unify pairs 
         else
           case (srt1,srt2)
             of (CoProduct(r1,_),CoProduct(r2,_)) -> 
                unifyCP(srt1,srt2,r1,r2,pairs)
              | (Product(r1,_),Product(r2,_)) -> 
                unifyP(srt1,srt2,r1,r2,pairs)
              | (Arrow(t1,t2,_),Arrow(s1,s2,_)) -> 
                (case unify(t1,s1,pairs)
                   of Unify pairs -> unify(t2,s2,pairs)
                    | notUnify -> notUnify)
              | (Quotient(ty,trm,_),Quotient(ty_,trm_,_)) -> 
                   unify(ty,ty_,pairs)
                   %                 if trm = trm_ 
                   %                     then unify(ty,ty_,pairs) 
                   %                    else NotUnify(srt1,srt2)
                   %               | (Subsort(ty,trm,_),Subsort(ty_,trm_,_)) -> 
                   %                  if trm = trm_ 
                   %                      then unify(ty,ty_,pairs) 
                   %                  else NotUnify(srt1,srt2)
              | (PBase(id,ts,pos1),PBase(id_,ts_,pos2)) -> 
                   if exists (fn (p1,p2) -> 
                              %% p = (srt1,srt2) 
                              %% need predicate that chases metavar links
                              equalSort?(p1, srt1) &
                              equalSort?(p2, srt2))
                              pairs 
                   then
                     Unify pairs
                   else 
                     if id = id_ then
                       unifyL(srt1,srt2,ts,ts_,pairs,unify)
                     else 
                       let s1_ = unfoldPSort(env,srt1) in
                       let s2_ = unfoldPSort(env,srt2) in
                       if equalSort?(s1,s1_) & equalSort?(s2_,s2) then
                         NotUnify (srt1,srt2)
                       else 
                         unify(withAnnS(s1_,pos1),
                               withAnnS(s2_,pos2),
                               cons((s1,s2), pairs))
              | (TyVar(id1,_), TyVar(id2,_)) -> 
                if id1 = id2 
                then Unify pairs
                else NotUnify (srt1,srt2)
              | (MetaTyVar(mtv,_), _) -> 
                 let s2_ = unfoldPSort(env,srt2) in
                 let t = unlinkPSort s2_ in
                 if equalSort?(t,s1)
                     then Unify pairs
                 else
                     if occursRec(mtv,t) 
                         then NotUnify (srt1,srt2)
                     else (linkMetaTyVar mtv (withAnnS(s2,pos2)); Unify pairs)
              | (t, MetaTyVar (mtv, _)) -> 
                let t = unfoldPSort (env, t) in
                let t = unlinkPSort t in
                if equalSort? (t, s2) then
                  Unify pairs
                else
                  if occursRec (mtv, t) then
                    NotUnify (srt1,srt2)
                  else
                    (linkMetaTyVar mtv (withAnnS(s1,pos1)); Unify pairs)
              | (Subsort(ty,_,_),ty2) -> unify(ty,ty2,pairs)
              | (ty,Subsort(ty2,_,_)) -> unify(ty,ty2,pairs)
              | (PBase _,_) -> 
                 let  s1_ = unfoldPSort(env,srt1) in
                if equalSort?(s1,s1_)
                then NotUnify (srt1,srt2)
                else unify(s1_,s2,pairs)
              | (_,PBase _) ->
                let s2_ = unfoldPSort(env,srt2) in
                if equalSort?(s2,s2_)
                then NotUnify (srt1,srt2)
                else unify(s1,s2_,pairs)
              | _ -> NotUnify(srt1,srt2)
   in
     case unify(s1,s2,[])
       of Unify _ -> (true,"")
        | NotUnify(s1,s2) -> (false,printSort s1^" ! = "^printSort s2)

 op consistentSorts?: LocalEnv * PSort * PSort -> Boolean
 def consistentSorts?(env,srt1,srt2) =
   let free_meta_ty_vars = freeTypeVars(srt1) ++ freeTypeVars(srt2) in
   let (val,_) = (unifySorts env srt1 srt2) in
   (clearMetaTyVarLinks free_meta_ty_vars;
    val)

 def clearMetaTyVarLinks meta_ty_vars =
  app (fn mtv -> 
        let {link, uniqueId, name} = ! mtv in
        mtv := {link = None, uniqueId = uniqueId, name = name})
      meta_ty_vars


 def freeTypeVars(srt) = 
   let vars = (Ref []) : Ref(PMetaTyVars) in
   let def vr(srt) = 
         case srt
           of MetaTyVar(tv,pos) -> 
              (case unlinkPSort srt of
                | MetaTyVar(tv,_) -> (vars := cons (tv,! vars); srt)
                | s -> mapSort (fn x -> x,vr,fn x -> x) (withAnnS (s, pos)))
            | _ -> srt
   in
   let _ = mapSort(fn x -> x,vr,fn x -> x) srt in
   ! vars

 def occursRec(v,srt:PSort) =
   case srt
     of CoProduct(row,_)   -> exists (fn (_,Some t) -> occurs(v,t) | _ -> false) row
      | Product(row,_)     -> exists (fn (_,t) -> occurs(v,t)) row
      | Arrow(t1,t2,_)     -> occurs(v,t1) or occurs(v,t2)
      | Quotient(t,pred,_) -> occurs(v,t)  or occursT(v,pred)
      | Subsort(t,pred,_)  -> occurs(v,t)  or occursT(v,pred)
      | PBase(_,srts,_)    -> exists (fn s -> occurs(v,s)) srts
      | TyVar _            -> false 
      | MetaTyVar _        -> (case unlinkPSort srt of
                               | MetaTyVar(w1,_) -> v = w1 
                               | t -> occursRec(v,t))

 def occurs(v: PMetaTyVar,srt: PSort): Boolean = 
   occursRec(v,srt)

 def occursT(v,pred) =
   case pred
     of ApplyN(ms,_)         -> exists (fn M -> occursT(v,M)) ms
      | Record(fields,_)     -> exists (fn (_,M) -> occursT(v,M)) fields
      | Bind(_,vars,body,_)  -> exists (fn (_,s) -> occurs(v,s)) vars or occursT(v,body)
      | IfThenElse(M,N,P,_)  -> occursT(v,M) or occursT(v,N) or occursT(v,P)
      | Var((_,s),_)         -> occurs(v,s)
      | Fun(_,s,_)           -> occurs(v,s)
      | Seq(ms,_)            -> exists (fn M -> occursT(v,M)) ms
      | Let(decls,body,_)    -> occursT(v,body) or exists (fn (p,M) -> occursT(v,M)) decls
      | LetRec(decls,body,_) -> occursT(v,body) or exists (fn (p,M) -> occursT(v,M)) decls
      | Lambda(rules,_)      -> exists (fn (p,c,M) -> occursT(v,M)) rules
      | _                    -> false

 (* Apply substitution as variable linking *)
 op linkMetaTyVar : PMetaTyVar -> PSort -> ()
 def linkMetaTyVar (v:PMetaTyVar) t = 
   let {link,uniqueId,name} = ! v in
   (%%String.writeLine ("Linking "^name^Nat.toString uniqueId^" with "^printSort t);
   v := {link = Some t, uniqueId = uniqueId, name = name})
}
