snark qualifying spec

  import /Languages/MetaSlang/Specs/Utilities
  import /Languages/MetaSlang/CodeGen/Lisp/SpecToLisp
  import /Languages/MetaSlang/Transformations/ProverPattern
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

  def snarkPBaseSort(spc, s:Sort, rng?):LispCell = 
	          case s of
		    | Base(Qualified("Nat","Nat"),_,_) -> Lisp.symbol("SNARK","NUMBER")
		    | Base(Qualified("Integer","Integer"),_,_) -> Lisp.symbol("SNARK","NUMBER")
		    | Base(Qualified("Boolean","Boolean"),_,_) -> if rng? then Lisp.symbol("SNARK","BOOLEAN") else Lisp.symbol("SNARK","TRUE")
		    | Base(Qualified(qual,id),_,_) -> let res = findPBuiltInSort(spc, Qualified(qual,id), rng?) in
                      %let _ = if specwareDebug? then toScreen("findPBuiltInSort: "^printSort(s)^" returns ") else () in
                      %let _ = if specwareDebug? then  LISP.PPRINT(res) else Lisp.list [] in
		      %let _ = if specwareDebug? then  writeLine("") else () in
		      res   %findPBuiltInSort(spc, Qualified(qual,id), rng?)
		    | Base(Qualified( _,id),_,_) -> if rng? then Lisp.symbol("SNARK",id)
                                                       else Lisp.symbol("SNARK",id)
		    | Product _ -> Lisp.symbol("SNARK","TRUE")
		    | Arrow _ -> Lisp.symbol("SNARK","TRUE")
		    | TyVar _ -> Lisp.symbol("SNARK","TRUE")
		    | _ -> Lisp.symbol("SNARK","TRUE")

  def findPBuiltInSort(spc, qid as Qualified(qual,id), rng?) =
    let optSrt = findTheSort(spc, qid) in
    case optSrt of
      | Some (names, _, schemes) ->
      (let
        def builtinSort?(s) =
	  case s of 
	    | Base(Qualified("Nat","Nat"),_,_) -> true
	    | Base(Qualified("Integer","Integer"),_,_) -> true
	    | Base(Qualified("Boolean","Boolean"),_,_) -> true 
            | _ -> false in
      let
	def builtinSnarkSort(s) =
	  case s of 
	    | Base(Qualified("Nat","Nat"),_,_) -> Lisp.symbol("SNARK","NUMBER")
	    | Base(Qualified("Integer","Integer"),_,_) -> Lisp.symbol("SNARK","NUMBER")
	    | Base(Qualified("Boolean","Boolean"),_,_) -> if rng? then Lisp.symbol("SNARK","BOOLEAN") else Lisp.symbol("SNARK","TRUE") in
      let builtinScheme = find (fn (_, srt) -> builtinSort?(srt)) schemes in
        (case builtinScheme of
	  | Some (_, srt) -> builtinSnarkSort(srt)
	  | _ -> case schemes of
	           | [(_, srt)] -> 
	              (case srt of
			| Subsort (supSrt, _, _) -> Lisp.symbol("SNARK",id)
			| _ -> snarkPBaseSort(spc, srt, rng?))
	           | _ -> Lisp.symbol("SNARK",id)))
      | _ -> Lisp.symbol("SNARK",id)
    
  def snarkPPBaseSort(_(* sp *):Spec, s:Sort, rng?):LispCell = 
    let res =
    case s of
      | Base(Qualified("Nat","Nat"),_,_) -> Lisp.symbol("SNARK","NUMBER")
      | Base(Qualified("Integer","Integer"),_,_) -> Lisp.symbol("SNARK","NUMBER")
      | Base(Qualified( _,id),_,_) -> if rng? then Lisp.symbol("SNARK",id)
				      else Lisp.symbol("SNARK",id)
      | Product _ -> Lisp.symbol("SNARK","TRUE")
      | Arrow _ -> Lisp.symbol("SNARK","TRUE")
      | TyVar _ -> Lisp.symbol("SNARK","TRUE") in
    let _ = if specwareDebug? then writeLine("snarkPBaseSort: "^printSort(s)) else () in
    let _ = if specwareDebug? then LISP.PPRINT(res) else Lisp.list[] in
    res
  
  def bndrString(bndr) =
    case bndr
      of Forall -> "ALL"
	| Exists -> "EXISTS"

  op snarkVar: Var -> LispCell

  def snarkVar(v as (id, _)) = Lisp.symbol("SNARK", "?" ^ id)
  
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
      | ("Boolean", "~") -> "NOT"
      | ("Boolean", "&") -> "AND"
      | ("Boolean", "or") -> "OR"
      | ("Boolean", "=>") -> "IMPLIES"
      | ("Boolean", "<=>") -> "IFF"
      | ("Nat",     "<=") -> "=<"
      | ("Integer",     "<=") -> "=<"
      | ("Nat",     "~") -> "-"
      | ("Integer",     "~") -> "-"
      | _ -> id

  def snarkBoolOp(id) = 
    let name = mkSnarkName("Boolean", id) in
       Lisp.symbol("SNARK", name)

  op mkSnarkFmlaApp: Context * Spec * String * StringSet.Set * Fun * Sort * MS.Term -> LispCell

  def mkSnarkFmlaApp(context, sp, dpn, vars, f, srt, arg) =
    let args = case arg
                of Record(flds,_) -> map(fn (_, term) -> term) flds
	         | _ -> [arg] in
    case f
      of Op(Qualified("Boolean",id),_) ->
	    let snarkArgs = map(fn (arg) -> mkSnarkFmla(context, sp, dpn, vars, [], arg)) args in
	      Lisp.cons(snarkBoolOp(id), Lisp.list snarkArgs)
       | Op(Qualified(qual,id),_) ->
	    let snarkArgs = map(fn (arg) -> mkSnarkTerm(context, sp, dpn, vars, arg)) args in
	      Lisp.cons(Lisp.symbol("SNARK",mkSnarkName(qual,id)), Lisp.list snarkArgs)
       | Embedded id ->
	      let def boolArgp(srt) =
	          case srt of		    | Base(Qualified(q,id),_,_) -> q = "Boolean" or id = "Boolean"
                    | _ -> false in
	      let Arrow (dom,rng,_) = srt in
	      let isfmla = boolArgp(dom) in
	      let snarkArg = if isfmla
	                       then mkSnarkFmla(context,sp,dpn,vars,[],arg)
			     else mkSnarkTerm(context,sp,dpn,vars,arg) in
		 Lisp.cons(Lisp.symbol("SNARK","embed?"), Lisp.list[Lisp.symbol("SNARK",id),snarkArg])
       | Equals -> 
	    let def boolArgp(srt) =
	          case srt of
		    | Base(Qualified(q,id),_,_) -> q = "Boolean" or id = "Boolean"
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


  op proverNatSort: () -> Sort
  
  def proverNatSort() =
    let baseProverSpec = run getBaseProverSpec in
    let optSrt = findTheSort(baseProverSpec, mkUnQualifiedId("ProverNat")) in
    let Some (names, _, [(_, srt)]) = optSrt in
    srt
  
  op getBaseProverSpec : Env Spec
  def getBaseProverSpec = 
    {
     (optBaseUnitId,baseSpec) <- getBase;
     proverBaseUnitId <- pathToRelativeUID "/Library/Base/ProverBase";
     (Spec baseProverSpec,_,_) <- SpecCalc.evaluateUID (Internal "ProverBase") proverBaseUnitId;
     return (subtractSpec baseProverSpec baseSpec)
    }

(*  def getBaseSpec () : SpecCalc.Env Spec =
    getBaseProverSpec()
*)
  op srtPred: Spec * Sort * Var -> MS.Term

  def srtPred(spc, srt, var) =
    let varTerm = mkVar(var) in
    let def topPredBaseSrt(srt) =
         case srt of
	   | Base(Qualified("Nat","Nat"),_,_) -> topPredBaseSrt(proverNatSort())
	   | Base (qid, _, _) -> (Some qid, mkTrue())
	   | Subsort (supSrt, predFn, _) ->
	   let (supBaseSrt, supPred) = topPredBaseSrt(supSrt) in
	   let pred = (simplify spc (mkApply(predFn, varTerm))) in
	     (case supBaseSrt of
		| Some qid -> (Some qid, Utilities.mkAnd(supPred, pred))
	        | _ -> (None, Utilities.mkAnd(supPred, pred))) 
           | _ -> (None, mkTrue()) in
    let (topBaseQId, topPred) = topPredBaseSrt(srt) in
    case topBaseQId of
      | Some topBaseQId ->
      let optSrt = findTheSort(spc, topBaseQId) in
      (case optSrt of
	 | Some (names, _, schemes) ->
	 (case schemes of
	    | [(_, newSrt)] -> Utilities.mkAnd(topPred, srtPred(spc, newSrt, var))
	    | _ -> topPred)
	 | _ -> topPred)
      | _ -> topPred
     

  op mkSnarkFmla: Context * Spec * String * StringSet.Set * Vars * MS.Term -> LispCell

  def mkSnarkFmla(context, sp, dpn, vars, globalVars, fmla) =
    case fmla
      of Bind(bndr, bndVars, term, _) ->
	let snarkBndList = snarkBndVars(sp, bndVars, globalVars) in
	let newVars = map(fn (var, srt) -> specId(var))
	                 bndVars in
	let bndVarsPred:MS.Term = (foldl (fn ((var:Id, srt), res) -> Utilities.mkAnd(srtPred(sp, srt, (var, srt)), res)) (mkTrue()) (bndVars:(List Var))):MS.Term in
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
      | Fun ((Bool true), Boolean, _) -> Lisp.symbol("SNARK","TRUE")
      | Fun ((Bool false), Boolean, _) -> Lisp.symbol("SNARK","FALSE")
      | _ -> mkSnarkTerm(context, sp, dpn, vars, fmla)

  op mkSnarkTermApp: Context * Spec * String * StringSet.Set * Fun * MS.Term -> LispCell

  def mkSnarkTermApp(context, sp, dpn, vars, f, arg) =
    let args = case arg
                of Record(flds,_) -> map(fn (_, term) -> term) flds
	         | _ -> [arg] in
    case f of
      | Op(Qualified(qual,id),_) ->
          let snarkArgs = map(fn (arg) -> mkSnarkTerm(context, sp, dpn, vars, arg)) args in
	      Lisp.cons(Lisp.symbol("SNARK",mkSnarkName(qual,id)), Lisp.list snarkArgs)
      | Project (id) ->
	  let snarkArgs = map(fn (arg) -> mkSnarkTerm(context, sp, dpn, vars, arg)) args in
	      Lisp.cons(Lisp.symbol("SNARK",mkSnarkName("","project_"^id)), Lisp.list snarkArgs)
      | Embed (id, b) ->
	  let snarkArgs = map(fn (arg) -> mkSnarkTerm(context, sp, dpn, vars, arg)) args in
	      Lisp.cons(Lisp.symbol("SNARK",mkSnarkName("","embed_"^id)), Lisp.list snarkArgs)

  op mkSnarkTerm: Context * Spec * String * StringSet.Set * MS.Term -> LispCell

  def mkSnarkTerm(context, sp, dpn, vars, term) =
%    let _ = writeLine("Translating to snark: "^printTerm(term)) in
    case term
      of Apply(Fun(f, srt, _), arg, _) -> mkSnarkTermApp(context, sp, dpn, vars, f, arg)
      | IfThenElse(c, t, e, _) ->
	   Lisp.list [Lisp.symbol("SNARK","IF"),
		      mkSnarkTerm(context, sp, dpn, vars, c),
		      mkSnarkTerm(context, sp, dpn, vars, t),
		      mkSnarkTerm(context, sp, dpn, vars, e)]
      | Fun (Op(Qualified(qual,id),_),_, _) -> Lisp.symbol("SNARK",mkSnarkName(qual, id))
      | Fun ((Nat nat), Nat, _) -> Lisp.nat(nat)
      | Fun (Embed(id, _),_,__) -> Lisp.symbol("SNARK",mkSnarkName("","embed_"^id))
      | Var (v,_) -> snarkVar(v)
      | _ -> mkNewSnarkTerm(context, term) %% Unsupported construct

  op mkNewSnarkTerm: Context * MS.Term -> LispCell

  def mkNewSnarkTerm(context, term) =
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

  op snarkPropertiesFromProperty: Context * Spec * Property -> List LispCell

  def snarkPropertiesFromProperty(context, spc, prop as (ptype, name, tyvars, fmla)) =
    let liftedFmlas = proverPattern(fmla) in
    map (fn (liftedFmla) -> let snarkFmla = mkSnarkFmla(context, spc, "SNARK", StringSet.empty, [], liftedFmla) in
                             Lisp.list [snark_assert, Lisp.quote(snarkFmla),
					Lisp.symbol("KEYWORD","NAME"), Lisp.symbol("KEYWORD",name)])
        liftedFmlas
  
  op snarkProperty: Context * Spec * Property -> LispCell

  def snarkProperty(context, spc, prop as (ptype, name, tyvars, fmla)) =
    let snarkFmla = mkSnarkFmla(context, spc, "SNARK", StringSet.empty, [], fmla) in
      Lisp.list [snark_assert, Lisp.quote(snarkFmla),
		 Lisp.symbol("KEYWORD","NAME"), Lisp.symbol("KEYWORD",name)]

  op snarkRewrite: Context * Spec * Property -> LispCell

  def snarkRewrite(context, spc, prop as (ptype, name, tyvars, fmla)) =
    let snarkFmla = mkSnarkFmla(context, spc, "SNARK", StringSet.empty, [], fmla) in
      Lisp.list [snark_assert_rewrite, Lisp.quote(snarkFmla),
		 Lisp.symbol("KEYWORD","NAME"), Lisp.symbol("KEYWORD",name)]

  op snarkConjectureRemovePattern: Context * Spec * Property -> LispCell

  def snarkConjectureRemovePattern(context, spc, prop as (ptype, name, tyvars, fmla)) =
    let liftedFmlas = proverPattern(fmla) in
    let liftedConjecture = mkConj(liftedFmlas) in
    let snarkFmla = mkSnarkFmla(context, spc, "SNARK", StringSet.empty, [], liftedConjecture) in
      Lisp.list [snark_prove, Lisp.quote(snarkFmla),
		 Lisp.symbol("KEYWORD","NAME"), Lisp.symbol("KEYWORD",name)]
  
  op snarkConjecture: Context * Spec * Property -> LispCell

  def snarkConjecture(context, spc, prop as (ptype, name, tyvars, fmla)) =
    let snarkFmla = mkSnarkFmla(context, spc, "SNARK", StringSet.empty, [], fmla) in
      Lisp.list [snark_prove, Lisp.quote(snarkFmla),
		 Lisp.symbol("KEYWORD","NAME"), Lisp.symbol("KEYWORD",name)]

  op snarkAnswer: Context * Spec * Property * Vars -> LispCell

  def snarkAnswer(context, spc, prop as (ptype, name, tyvars, fmla), ansVars) =
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
     snarkProperties

endspec
