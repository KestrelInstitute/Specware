snark qualifying spec

  import /Languages/MetaSlang/Specs/Utilities
  import /Languages/MetaSlang/CodeGen/Lisp/SpecToLisp
  import /Languages/MetaSlang/CodeGen/CodeGenTransforms
  import /Languages/MetaSlang/Transformations/ExplicateHiddenAxioms
  import /Languages/MetaSlang/Transformations/OpToAxiom
  import /Languages/SpecCalculus/Semantics/Evaluate/UnitId/Utilities
  import /Languages/SpecCalculus/Semantics/Evaluate/UnitId
%  import /Languages/MetaSlang/Transformations/Match
%  import /Languages/MetaSlang/CodeGen/Lisp/Lisp
%  import /Languages/MetaSlang/Specs/StandardSpec


  op LISP.PPRINT: LispCell -> LispCell

  sort Context = 
      {
       counter  : Ref Nat
      }

  op newContext: Context
  def newContext = { counter = (Ref 0)}

  op snark_assert: LispCell
  def snark_assert = Lisp.symbol("SNARK","ASSERT")

  op snark_assert_rewrite: LispCell
  def snark_assert_rewrite = Lisp.symbol("SNARK","ASSERT-REWRITE")

  op snark_prove: LispCell
  def snark_prove = Lisp.symbol("SNARK","PROVE")

  op snarkSortId: Id -> Id
  def snarkSortId(id) =
    if length(id) = 1
      then "snark_"^id
    else id
  
 def unfoldBaseUnInterp (sp, srt) =
   unfoldBaseUnInterpV (sp, srt, true)

 def unfoldBaseUnInterpV (sp:Spec, srt, verbose) = 
  case srt of
    | Base (qid, srts, a) ->
      (case AnnSpec.findTheSort (sp, qid) of
	 | None -> srt
	 | Some info ->
	   case info.dfn of
	     | []   -> srt
	     | (tvs, srt2)::_ ->
	       let ssrt = substSort (zip (tvs, srts), srt2) in
	       case ssrt of
		 | Product _ -> srt
		 | Arrow _ -> ssrt
		 | TyVar _ -> srt
		 | CoProduct _ -> srt
		 | _ -> unfoldBaseUnInterpV (sp, ssrt, verbose))
    | _ -> srt


  
  def snarkPBaseSort(spc, s:Sort, rng?):LispCell = 
    let s = unfoldBaseUnInterp(spc, s) in
	          case s of
		    | Base(Qualified("Nat","Nat"),_,_) -> Lisp.symbol("SNARK","NUMBER")
		    | Base(Qualified("Nat","PosNat"),_,_) -> Lisp.symbol("SNARK","NUMBER")
		    | Base(Qualified("Integer","Integer"),_,_) -> Lisp.symbol("SNARK","NUMBER")
		    | Boolean _ -> if rng? then Lisp.symbol("SNARK","BOOLEAN") else Lisp.symbol("SNARK","LOGICAL")
		    %| Base(Qualified(qual,id),_,_) -> let res = findPBuiltInSort(spc, Qualified(qual,id), rng?) in
                      %let _ = if specwareDebug? then toScreen("findPBuiltInSort: "^printSort(s)^" returns ") else () in
                      %let _ = if specwareDebug? then  LISP.PPRINT(res) else Lisp.list [] in
		      %let _ = if specwareDebug? then  writeLine("") else () in
		     % res   %findPBuiltInSort(spc, Qualified(qual,id), rng?)
		    | Base(Qualified( _,id),_,_) -> if rng? then Lisp.symbol("SNARK",snarkSortId(id))
                                                       else Lisp.symbol("SNARK",snarkSortId(id))
		    | Subsort(supSrt, _, _) -> snarkPBaseSort(spc, supSrt, rng?)
		    | Product _ -> Lisp.symbol("SNARK","TRUE")
		    | Arrow _ -> Lisp.symbol("SNARK","TRUE")
		    | TyVar _ -> Lisp.symbol("SNARK","TRUE")
		    | _ -> Lisp.symbol("SNARK","TRUE")

  def findPBuiltInSort(spc, qid as Qualified(qual,id), rng?) =
    let optSrt = AnnSpec.findTheSort(spc, qid) in
    case optSrt of
      | Some info ->
        (let
           def builtinSort? s =
	     case s of 
	       | Base (Qualified ("Nat",     "Nat"),     _, _) -> true
	       | Base (Qualified ("Integer", "Integer"), _, _) -> true
	       | Boolean _ -> true 
	       | _ -> false 
	   def builtinSnarkSort s =
	     case s of 
	       | Base (Qualified ("Nat",     "Nat"),     _, _) -> Lisp.symbol ("SNARK", "NUMBER")
	       | Base (Qualified ("Integer", "Integer"), _, _) -> Lisp.symbol ("SNARK", "NUMBER")
	       | Boolean _ -> 
	         if rng? then 
		   Lisp.symbol("SNARK","BOOLEAN") 
		 else 
		   Lisp.symbol ("SNARK", "LOGICAL")
         in
	 let builtinScheme = find (fn (_, srt) -> builtinSort? srt) info.dfn in
	 case builtinScheme of
	   | Some (_, srt) -> builtinSnarkSort srt
	   | _ -> 
	     case info.dfn of
	       | [(_, srt)] -> 
	         (case srt of
		    | Subsort (supSrt, _, _) -> Lisp.symbol ("SNARK", snarkSortId id)
		    | _ -> snarkPBaseSort (spc, srt, rng?))
	       | _ -> Lisp.symbol ("SNARK", snarkSortId id))
      | _ -> Lisp.symbol ("SNARK", snarkSortId id)
    
  def snarkPPBaseSort(_(* sp *):Spec, s:Sort, rng?):LispCell = 
    let res =
    case s of
      | Base(Qualified("Nat","Nat"),_,_) -> Lisp.symbol("SNARK","NUMBER")
      | Base(Qualified("Integer","Integer"),_,_) -> Lisp.symbol("SNARK","NUMBER")
      | Base(Qualified( _,id),_,_) -> if rng? then Lisp.symbol("SNARK",snarkSortId(id))
				      else Lisp.symbol("SNARK",snarkSortId(id))
      | Boolean _ -> Lisp.symbol("SNARK",snarkSortId("Boolean"))
      | Product _ -> Lisp.symbol("SNARK","TRUE")
      | Arrow _ -> Lisp.symbol("SNARK","TRUE")
      | TyVar _ -> Lisp.symbol("SNARK","TRUE") in
    %let _ = if specwareDebug? then writeLine("snarkPBaseSort: "^printSort(s)) else () in
    %let _ = if specwareDebug? then LISP.PPRINT(res) else Lisp.list[] in
    res
  
  def bndrString(bndr) =
    case bndr
      of Forall -> "ALL"
	| Exists -> "EXISTS"

  op snarkVar: Var -> LispCell

  def snarkVar(v as (id, srt)) =
    case srt of
      | Boolean _ -> snarkBoolVarFromId(id)
      | _ -> snarkVarFromId(id)

  op snarkVarFromId: Id -> LispCell

  def snarkVarFromId(id) =  Lisp.symbol("SNARK", "?" ^ id)
  
  op snarkBoolVarFromId: Id -> LispCell

  def snarkBoolVarFromId(id) =  Lisp.symbol("SNARK", "?" ^ id ^ "_Logical")
  
  op snarkVarTerm: Var -> LispCell

  def snarkVarTerm(v as (id, srt)) =
    case srt of
      | Boolean _ -> snarkBoolVarTermFromId(id)
      | _ -> snarkVarFromId(id)

  op snarkVarFmla: Var -> LispCell

  def snarkVarFmla(v as (id, srt)) =
    case srt of
      | Boolean _ -> snarkBoolVarFmlaFromId(id)
      | _ -> snarkVarFromId(id)

  op snarkBoolVarTermFromId: Id -> LispCell

  def snarkBoolVarTermFromId(id) =
    snarkBoolVarFromId(id)
  
  op snarkBoolVarFmlaFromId: Id -> LispCell

  def snarkBoolVarFmlaFromId(id) =
    Lisp.list [Lisp.symbol("SNARK","HOLDS"), snarkBoolVarFromId(id)]
  op snarkBndVar: Spec * Var * Vars -> LispCell

  def snarkBndVar(sp, var, globalVars) =
    let (name, srt) = var in
      if exists (fn (gname, _) -> name = gname) globalVars
	then
	  Lisp.list[snarkVar(var),
		    Lisp.symbol("KEYWORD","SORT"),
		    snarkPBaseSort(sp, srt, false),
		    Lisp.symbol("KEYWORD","GLOBAL"),
		    Lisp.symbol("SNARK", "T")]
      else
	Lisp.list[snarkVar(var),
		  Lisp.symbol("KEYWORD","SORT"),
		  snarkPBaseSort(sp, srt, false)]
  
  op snarkBndVars: Spec * List Var * Vars -> LispCell

  def snarkBndVars(sp, vars, globalVars) =
    let snarkVarList = map (fn (var) -> snarkBndVar(sp, var, globalVars)) vars in
    let res = Lisp.list snarkVarList in
      res
    
  op mkSnarkName: Qualifier * Id -> String

  def mkSnarkName(qual, id) =
    case (qual, id) of
      | ("Nat",     "<=") -> "=<"
      | ("Integer", "<=") -> "=<"
      | ("Nat",     "~") -> "-"
      | ("Integer", "~") -> "-"
      | ("Nat", ">=") -> ">="
      | ("Nat", "+") -> "+"
      | ("Nat", "-") -> "-"
      | ("Nat", "*") -> "*"
      | ("Integer", ">=") -> ">="
      | ("Integer", "+") -> "+"
      | ("Integer", "-") -> "-"
      | ("Integer", "*") -> "*"
      | (_, "hoapply") ->  "HOAPPLY"
      | _ -> if qual = UnQualified
	       then id
	     else qual^"."^id

  op mkSnarkFmlaApp: Context * Spec * String * StringSet.Set * Fun * Sort * MS.Term -> LispCell

  def mkSnarkFmlaApp(context, sp, dpn, vars, f, srt, arg) =
    let args = case arg
                of Record(flds,_) -> map(fn (_, term) -> term) flds
	         | _ -> [arg] in
    case f of
       | Op(Qualified(qual,id),_) ->
	    let snarkArgs = map(fn (arg) -> mkSnarkTerm(context, sp, dpn, vars, arg)) args in
	      Lisp.cons(Lisp.symbol("SNARK",mkSnarkName(qual,id)), Lisp.list snarkArgs)
       | Embedded id ->
	      let def boolArgp(srt) =
	          case srt of		    
		    | Boolean _ -> true
                    | _ -> false in
	      let Arrow (dom,rng,_) = srt in
	      let isfmla = boolArgp(dom) in
	      let snarkArg = if isfmla
	                       then mkSnarkFmla(context,sp,dpn,vars,[],arg)
			     else mkSnarkTerm(context,sp,dpn,vars,arg) in
		 Lisp.cons(Lisp.symbol("SNARK","embed?"), Lisp.list[Lisp.symbol("SNARK",id),snarkArg])

       | Not ->
	 let snarkArgs = map(fn (arg) -> mkSnarkFmla(context, sp, dpn, vars, [], arg)) args in
	 Lisp.cons(Lisp.symbol("SNARK", "NOT"), Lisp.list snarkArgs)
       | And ->
	 let snarkArgs = map(fn (arg) -> mkSnarkFmla(context, sp, dpn, vars, [], arg)) args in
	 Lisp.cons(Lisp.symbol("SNARK", "AND"), Lisp.list snarkArgs)
       | Or ->
	 let snarkArgs = map(fn (arg) -> mkSnarkFmla(context, sp, dpn, vars, [], arg)) args in
	 Lisp.cons(Lisp.symbol("SNARK", "OR"), Lisp.list snarkArgs)
       | Implies ->
	 let snarkArgs = map(fn (arg) -> mkSnarkFmla(context, sp, dpn, vars, [], arg)) args in
	 Lisp.cons(Lisp.symbol("SNARK", "IMPLIES"), Lisp.list snarkArgs)
       | Iff ->
	 let snarkArgs = map(fn (arg) -> mkSnarkFmla(context, sp, dpn, vars, [], arg)) args in
	 Lisp.cons(Lisp.symbol("SNARK", "IFF"), Lisp.list snarkArgs)
       | Equals -> 
	    let def boolArgp(srt) =
	          case srt of
		    | Boolean _ -> true
                    | _ -> false in
	    let [arg1,arg2] = args in
	    let Arrow (dom,rng,_) = srt in
	    let Product(s:List(Id * Sort), _) = dom in
	    let [(_,s1),(_,s2)] = s in
	    let isfmla = boolArgp(s1) or boolArgp(s2) in
	    let snarkArg1 =
	        if isfmla
		  then mkSnarkFmla(context, sp, dpn, vars, [], arg1)
		else mkSnarkTerm(context, sp, dpn, vars, arg1) in
	    let snarkArg2 =
	        if isfmla
		  then mkSnarkFmla(context, sp, dpn, vars, [], arg2)
		else mkSnarkTerm(context, sp, dpn, vars, arg2) in
	      if isfmla 
		then Lisp.cons(Lisp.symbol("SNARK","IFF"), Lisp.list [snarkArg1, snarkArg2])
	      else Lisp.cons(Lisp.symbol("SNARK","="), Lisp.list [snarkArg1, snarkArg2])
       | NotEquals -> 
	    let def boolArgp(srt) =
	          case srt of
		    | Boolean _ -> true
                    | _ -> false in
	    let [arg1,arg2] = args in
	    let Arrow (dom,rng,_) = srt in
	    let Product(s:List(Id * Sort), _) = dom in
	    let [(_,s1),(_,s2)] = s in
	    let isfmla = boolArgp(s1) or boolArgp(s2) in
	    let snarkArg1 =
	        if isfmla
		  then mkSnarkFmla(context, sp, dpn, vars, [], arg1)
		else mkSnarkTerm(context, sp, dpn, vars, arg1) in
	    let snarkArg2 =
	        if isfmla
		  then mkSnarkFmla(context, sp, dpn, vars, [], arg2)
		else mkSnarkTerm(context, sp, dpn, vars, arg2) in
	    Lisp.cons(Lisp.symbol("SNARK", "NOT"), 
		      Lisp.list [if isfmla 
				   then Lisp.cons(Lisp.symbol("SNARK","IFF"), Lisp.list [snarkArg1, snarkArg2])
				 else Lisp.cons(Lisp.symbol("SNARK","="), Lisp.list [snarkArg1, snarkArg2])])


  op mkSnarkFmla: Context * Spec * String * StringSet.Set * Vars * MS.Term -> LispCell

  def mkSnarkFmla(context, sp, dpn, vars, globalVars, fmla) =
    case fmla
      of Bind(bndr, bndVars, term, _) ->
	let snarkBndList = snarkBndVars(sp, bndVars, globalVars) in
	let newVars = map(fn (var, srt) -> specId(var,""))
	                 bndVars in
	let bndVarsPred:MS.Term = (foldl (fn ((var:Id, srt), res) -> Utilities.mkAnd(srtPred(sp, srt, mkVar((var, srt))), res)) (mkTrue()) (bndVars:(List Var))):MS.Term in
	let newTerm = case bndr of
	                | Forall -> Utilities.mkSimpImplies(bndVarsPred, term)
	                | Exists -> Utilities.mkAnd(bndVarsPred, term) in
	let snarkFmla = mkSnarkFmla(context, sp, dpn, StringSet.addList(vars, newVars), globalVars, newTerm) in
	   Lisp.list [Lisp.symbol("SNARK",bndrString bndr),
		      snarkBndList,
		      snarkFmla]
      | Apply(Fun(f, srt, _), arg, _) -> mkSnarkFmlaApp(context, sp, dpn, vars, f, srt, arg)
      | IfThenElse(c, t, e, _) ->
	   Lisp.list [Lisp.symbol("SNARK","IF"),
		      mkSnarkFmla(context, sp, dpn, vars, globalVars, c),
		      mkSnarkFmla(context, sp, dpn, vars, globalVars, t),
		      mkSnarkFmla(context, sp, dpn, vars, globalVars, e)]
      | Fun ((Bool true),  _, _) -> Lisp.symbol("SNARK","TRUE")  % sort of Fun was Boolean, but that was a free var in the pattern! 
      | Fun ((Bool false), _, _) -> Lisp.symbol("SNARK","FALSE") % sort of Fun was Boolean, but that was a free var in the pattern!
      | Var (v, _) -> snarkVarFmla(v)
      | _ -> mkSnarkTerm(context, sp, dpn, vars, fmla)

  op mkSnarkTermAppTop: Context * Spec * String * StringSet.Set * Fun * Sort * MS.Term -> LispCell
  def mkSnarkTermAppTop(context, sp, dpn, vars, f, srt, arg) =
    case arrowOpt(sp, srt) of
      | Some(dom, range) ->
         (case dom of
	    |Base _ ->
	        (case productOpt(sp, dom) of
		   | Some _ -> mkSnarkTermAppRecordArg(context, sp, dpn, vars, f, dom, arg)
		   | _ -> mkSnarkTermApp(context, sp, dpn, vars, f, arg))
	      | _ -> mkSnarkTermApp(context, sp, dpn, vars, f, arg))
      | _ -> mkSnarkTermApp(context, sp, dpn, vars, f, arg)

  op mkSnarkTermAppRecordArg: Context * Spec * String * StringSet.Set * Fun * Sort * MS.Term -> LispCell
  def mkSnarkTermAppRecordArg(context, sp, dpn, vars, f, dom as Base (qid, _ , _), arg) =
    case f of
      | Op(Qualified(qual,id),_) ->
      (case arg of
	 | Record (fields) ->
	 let snarkArg = mkSnarkTermApp(context, sp, dpn, vars, Op(getRecordConstructorOpName(qid), Nonfix), arg) in
	 Lisp.cons(Lisp.symbol("SNARK",mkSnarkName(qual,id)), Lisp.list [snarkArg])
	 | _ -> let snarkArg = mkSnarkTerm(context, sp, dpn, vars, arg) in
	 Lisp.cons(Lisp.symbol("SNARK",mkSnarkName(qual,id)), Lisp.list [snarkArg]))
      | _ -> mkSnarkTermApp(context, sp, dpn, vars, f, arg)


  op mkSnarkTermApp: Context * Spec * String * StringSet.Set * Fun * MS.Term -> LispCell
  def mkSnarkTermApp(context, sp, dpn, vars, f, arg) =
    let args = case arg
                of Record(flds,_) -> map(fn (_, term) -> term) flds
	         | _ -> [arg] in
    case f of
      | Op(Qualified(Integer_, "-"),_) ->
	  let snarkArgs = map(fn (arg) -> mkSnarkTerm(context, sp, dpn, vars, arg)) args in
	      Lisp.cons(Lisp.symbol("SNARK","-"), Lisp.cons(Lisp.nat(0), Lisp.list snarkArgs))
      | Op(Qualified(qual,id),_) ->
          let snarkArgs = map(fn (arg) -> mkSnarkTerm(context, sp, dpn, vars, arg)) args in
	      Lisp.cons(Lisp.symbol("SNARK",mkSnarkName(qual,id)), Lisp.list snarkArgs)
      | Project (id) -> %let _ = if id = "local" then debug("project_local") else () in
	  let snarkArgs = map(fn (arg) -> mkSnarkTerm(context, sp, dpn, vars, arg)) args in
	  let prodSrt = termSort(arg) in
	  let userProdSrt = findMatchingUserTypeOption(sp, prodSrt) in
	  (case userProdSrt of
	     | None -> Lisp.cons(Lisp.symbol("SNARK",mkSnarkName(UnQualified, "project_"^id)), Lisp.list snarkArgs)
	     | Some (Base (Qualified(q, prodSrtId),_, _)) ->
       %%IMPORTANT LOOK AT CODEGENTRANSFORMS FOR CONSISTENCY
	     Lisp.cons(Lisp.symbol("SNARK",mkSnarkName(UnQualified, "project_"^prodSrtId^"_"^id)), Lisp.list snarkArgs))
      | Embed (id, b) -> %let _ = if id = "Cons" then debug("embed_Cons") else () in
	  let snarkArgs = map(fn (arg) -> mkSnarkTerm(context, sp, dpn, vars, arg)) args in
	      Lisp.cons(Lisp.symbol("SNARK",mkSnarkName(UnQualified, "embed_"^id)), Lisp.list snarkArgs)
      | Restrict -> let [tm] = args in mkSnarkTerm(context, sp, dpn, vars, tm)

  op mkSnarkHOTermApp: Context * Spec * String * StringSet.Set * MS.Term * MS.Term -> LispCell

  def mkSnarkHOTermApp(context, sp, dpn, vars, f, arg) =
    let args = case arg
                of Record(flds,_) -> [f]++map(fn (_, term) -> term) flds
	         | _ -> [f, arg] in
    let snarkArgs = map(fn (arg) -> mkSnarkTerm(context, sp, dpn, vars, arg)) args in
     Lisp.cons(Lisp.symbol("SNARK","HOAPPLY"), Lisp.list snarkArgs)

  op mkSnarkTerm: Context * Spec * String * StringSet.Set * MS.Term -> LispCell

  def mkSnarkTerm(context, sp, dpn, vars, term) =
%    let _ = writeLine("Translating to snark: "^printTerm(term)) in
    case term of 
      | Apply(Fun(f, srt, _), arg, _) -> mkSnarkTermAppTop(context, sp, dpn, vars, f, srt, arg)
      | Apply(f, arg, _) -> mkSnarkHOTermApp(context, sp, dpn, vars, f, arg)
      | IfThenElse(c, t, e, _) ->
	   Lisp.list [Lisp.symbol("SNARK","IF"),
		      mkSnarkFmla(context, sp, dpn, vars, [], c),
		      mkSnarkTerm(context, sp, dpn, vars, t),
		      mkSnarkTerm(context, sp, dpn, vars, e)]
      | Fun (Op(Qualified(qual,id),_),_, _) -> Lisp.symbol("SNARK",mkSnarkName(qual, id))
      | Fun ((Nat nat), Nat, _) -> Lisp.nat(nat)
      | Fun (Embed(id, _),_,__) -> Lisp.symbol("SNARK",mkSnarkName(UnQualified,"embed_"^id))
      | Var (v,_) -> snarkVarTerm(v)
      | Record (fields, _) -> mkSnarkTermRecord(context, sp, dpn, vars, term)
      | _ -> mkNewSnarkTerm(context, term) %% Unsupported construct

  op mkSnarkTermRecord: Context * Spec * String * StringSet.Set * MS.Term -> LispCell
  def  mkSnarkTermRecord(context, spc, dpn, vars, term as Record (fields)) =
    let srt = inferTypeFoldRecords(spc,term) in
    case srt of
      | Base (qid, _, _) -> mkSnarkTermApp(context, spc, dpn, vars, Op(getRecordConstructorOpName(qid), Nonfix), term)
      | _ -> mkNewSnarkTerm(context, term)

  op mkNewSnarkTerm: Context * MS.Term -> LispCell

  def mkNewSnarkTerm(context, term) =
    %let _ = debug("mkNewSnarkTerm") in    
    let vars = freeVars term in
    let newFun = mkNewSnarkOp(context) in
    let snarkVars = map (fn (v) -> snarkVar(v)) vars in
      case snarkVars of
	| [] -> newFun
	| _ -> Lisp.cons(newFun, Lisp.list snarkVars)

  op mkNewSnarkOp: Context -> LispCell

  def mkNewSnarkOp(context) =
    let num = State.! context.counter + 1 in
      (context.counter State.:= num;
       Lisp.symbol("SNARK", ("sApply" ++ (Nat.toString num)))
      )

%  op lispFmla: Spec * String * MS.Term -> LispTerm

%  def lispFmla(spc, dpn, fmla) =
%    reduceTerm(mkLFmla(spc, dpn, StringSet.empty, fmla))

  op snarkSubsortProperties: Context * Spec -> List LispCell

  def snarkSubsortProperties(context, spc) =
    let sorts = sortsAsList(spc) in
    let snarkSubsortProps = mapPartial(fn (qual, id, info) ->
				       sortInfoToSnarkSubsortProp(context, spc, id, info))
                                       sorts in
      snarkSubsortProps

  op sortInfoToSnarkSubsortProp: Context * Spec * Id * SortInfo -> Option LispCell
  def sortInfoToSnarkSubsortProp(context, spc, id, info) =
    case info.dfn of
      | [] -> None
      | [(_, srt)] ->
        case srt of
	  | Subsort (supSrt, pred, _) ->
	     let snarkSubSrtId = snarkSortId(id) in
	     let subSrtVar = (snarkSubSrtId, srt) in
	     let snarkBndVar = snarkBndVar(spc, subSrtVar, []) in
	     let subSrtPred = srtPred(spc, srt, mkVar(subSrtVar)) in
	     let snarkSubSrtPred = mkSnarkFmla(context, spc, "SNARK", StringSet.empty, [], subSrtPred) in
	       Some (Lisp.list [snark_assert, Lisp.quote(snarkSubSrtPred),
				Lisp.symbol("KEYWORD","NAME"), Lisp.symbol("KEYWORD","subSort" ^ snarkSubSrtId)])
	  | _ -> None

  op snarkPropertiesFromProperty: Context * Spec * Property -> List LispCell

  def snarkPropertiesFromProperty(context, spc, prop as (ptype, pname as Qualified(qname, name), tyvars, fmla)) =
    %let _ = if name = "filter_Object$1$_$Object$2_def" then debug("embed_cons prop") else () in
    %let liftedFmlas = proverPattern(fmla) in
    let liftedFmlas = [fmla] in
    map (fn (liftedFmla) -> let snarkFmla = mkSnarkFmla(context, spc, "SNARK", StringSet.empty, [], liftedFmla) in
                             Lisp.list [snark_assert, Lisp.quote(snarkFmla),
					Lisp.symbol("KEYWORD","NAME"), Lisp.symbol("KEYWORD",name)])
        liftedFmlas
  
  op snarkProperty: Context * Spec * Property -> LispCell

  def snarkProperty(context, spc, prop as (ptype, pname as Qualified(qname, name), tyvars, fmla)) =
    let snarkFmla = mkSnarkFmla(context, spc, "SNARK", StringSet.empty, [], fmla) in
      Lisp.list [snark_assert, Lisp.quote(snarkFmla),
		 Lisp.symbol("KEYWORD","NAME"), Lisp.symbol("KEYWORD",name)]

  op snarkRewrite: Context * Spec * Property -> LispCell

  def snarkRewrite(context, spc, prop as (ptype, pname as Qualified(qname, name), tyvars, fmla)) =
    let snarkFmla = mkSnarkFmla(context, spc, "SNARK", StringSet.empty, [], fmla) in
      Lisp.list [snark_assert_rewrite, Lisp.quote(snarkFmla),
		 Lisp.symbol("KEYWORD","NAME"), Lisp.symbol("KEYWORD",name)]

  op snarkConjectureRemovePattern: Context * Spec * Property -> LispCell

  def snarkConjectureRemovePattern(context, spc, prop as (ptype, pname as Qualified(qname, name), tyvars, fmla)) =
    %let liftedFmlas = proverPattern(fmla) in
    let liftedFmlas = [fmla] in
    let liftedConjecture = mkConj(liftedFmlas) in
    let snarkFmla = mkSnarkFmla(context, spc, "SNARK", StringSet.empty, [], liftedConjecture) in
      Lisp.list [snark_prove, Lisp.quote(snarkFmla),
		 Lisp.symbol("KEYWORD","NAME"), Lisp.symbol("KEYWORD",name)]

  op snarkConjecture: Context * Spec * Property -> LispCell

  def snarkConjecture(context, spc, prop as (ptype, pname as Qualified(qname, name), tyvars, fmla)) =
    let snarkFmla = mkSnarkFmla(context, spc, "SNARK", StringSet.empty, [], fmla) in
      Lisp.list [snark_prove, Lisp.quote(snarkFmla),
		 Lisp.symbol("KEYWORD","NAME"), Lisp.symbol("KEYWORD",name)]

  op snarkAnswer: Context * Spec * Property * Vars -> LispCell

  def snarkAnswer(context, spc, prop as (ptype, pname as Qualified(qname, name), tyvars, fmla), ansVars) =
    let snarkFmla = mkSnarkFmla(context, spc, "SNARK", StringSet.empty, ansVars, fmla) in
    let snarkAnsVars = map (fn (v) -> snarkVar(v)) ansVars in
    let snarkAnsTerm = Lisp.list ([Lisp.symbol("SNARK","ANS")] ++ snarkAnsVars) in
      Lisp.list [snark_prove, Lisp.quote(snarkFmla),
		 Lisp.symbol("KEYWORD","ANSWER"), Lisp.quote(snarkAnsTerm),
		 Lisp.symbol("KEYWORD","NAME"), Lisp.symbol("KEYWORD",name)]

  op snarkProperties: Spec -> List LispCell

  def snarkProperties(spc) =
    let properties = spc.properties in
    let context = newContext in
    let snarkProperties =
          map(fn (prop) -> snarkProperty(context, spc, prop))
	      properties in
    let snarkSubsortProperties = snarkSubsortProperties(context, spc) in
     snarkSubsortProperties ++ snarkProperties


(*  op snarkOpProperties: Spec -> List LispCell

  def snarkOpProperties(spc) =
    let opsigs = specOps(spc) in
    let snarkOpProperties =
          mapPartial(fn (qname, name, _, srt) -> 
		           snarkOpPropertyPartial(spc, mkSnarkName(qname,name), srt))
                    opsigs in
       snarkOpProperties

  op snarkOpPropertyPartial: Spec * String * Sort -> Option LispCell

  def snarkOpPropertyPartial(spc, name, srt) =
    let prop = snarkOpProperty(spc, name, srt) in
       if null(prop) then None else Some prop

  op snarkOpProperty: Spec * String * Sort -> LispCell

  def snarkOpProperty(spc, name, srt) = snarkFunctionProp(spc, name, srt)

  op snarkFunctionProp: Spec * String * Sort -> LispCell

  def snarkFunctionProp(spc, name, srt) =
    %let _ = toScreen("Generating snark prop for "^name^" with sort: ") in
    %let _ = printSortToTerminal srt in
    (case (curryShapeNum(spc, srt), sortArity(spc, srt))
       of (1,None) ->     %let _ = debug("noArity") in 
	 snarkFunctionNoArityProp(spc, name, srt)
	| (1, Some(_,arity)) -> %let _ = debug("noCurry") in 
	 snarkFunctionNoCurryProp(spc, name, srt, arity)
	| (curryN, None) -> %let _ = debug("CurryNoArity") in 
	 snarkFunctionCurryNoArityProp(spc, name, srt)
	| (curryN, Some (_, arity)) -> %let _ = debug("Curry") in 
	 snarkFunctionCurryProp()
	| _ -> %let _ = debug("Last") in
	 snarkFunctionNoArityProp(spc, name, srt))




  op snarkFunctionNoCurryProp: Spec * String * Sort * Nat -> LispCell

  def snarkFunctionNoCurryProp(spc, name, srt, arity) =
    case arrowOpt(spc, srt) of
      Some (dom, rng) ->
	case rng of
	  | Boolean _ -> snarkPredicateProp(spc, name, dom, arity)
	  | _ ->
	case productOpt(spc, dom) of
	  | Some fields -> 
	    let domSortList = map(fn (id: Id, srt:Sort) -> snarkBaseSort(spc, srt, false))
	                          fields in
	      Lisp.list[declare_function,
			Lisp.quote(Lisp.symbol("SNARK", name)), Lisp.nat(arity),
			Lisp.symbol("KEYWORD","SORT"),
			Lisp.quote(Lisp.cons(snarkBaseSort(spc, rng, true), Lisp.list(domSortList)))]
	  | _ ->
	      let snarkDomSrt = snarkBaseSort(spc, dom, false) in
	        Lisp.list[declare_function,
			  Lisp.quote(Lisp.symbol("SNARK", name)), Lisp.nat(arity),
			  Lisp.symbol("KEYWORD","SORT"),
			  Lisp.quote(Lisp.cons(snarkBaseSort(spc, rng, true), Lisp.list([snarkDomSrt])))]

*)

endspec
