spec {

  import /Languages/MetaSlang/Specs/Utilities
  import /Languages/MetaSlang/CodeGen/Lisp/SpecToLisp
%  import /Languages/MetaSlang/Transformations/Match
%  import /Languages/MetaSlang/CodeGen/Lisp/Lisp
%  import /Languages/MetaSlang/Specs/StandardSpec


   sort Context = 
      {
       counter  : Ref Nat
      }

  op newContext: Context
  def newContext = { counter = (Ref 0)}

  op snark_assert: LispCell
  def snark_assert = Lisp.symbol("SNARK","ASSERT")

  op snark_prove: LispCell
  def snark_prove = Lisp.symbol("SNARK","PROVE")

  def snarkPBaseSort(s:Sort, rng?):LispCell = 
	          case s of
		    | Base(Qualified("Nat","Nat"),_,_) -> Lisp.symbol("SNARK","NATURAL")
		    | Base(Qualified("Integer","Integer"),_,_) -> Lisp.symbol("SNARK","INTEGER")
		    | Base(Qualified( _,id),_,_) -> if rng? then Lisp.symbol("SNARK",id)
                                                     else Lisp.symbol("SNARK",id)
		    | Product _ -> Lisp.symbol("SNARK","TRUE")
		    | Arrow _ -> Lisp.symbol("SNARK","TRUE")
		    | TyVar _ -> Lisp.symbol("SNARK","TRUE")
  
  def bndrString(bndr) =
    case bndr
      of Forall -> "ALL"
	| Exists -> "EXISTS"
  
  op snarkBndVar: Var -> LispCell

  def snarkBndVar(var) =
    let (name, srt) = var in
      Lisp.list[Lisp.symbol("SNARK",name),
		Lisp.symbol("KEYWORD","SORT"),
		snarkPBaseSort(srt, false)]
  
  op snarkBndVars: List Var -> LispCell

  def snarkBndVars(vars) =
    let snarkVarList = map snarkBndVar vars in
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
      | _ -> id

  def snarkBoolOp(id) = 
    let name = mkSnarkName("Boolean", id) in
       Lisp.symbol("SNARK", name)

  op mkSnarkFmlaApp: Context * Spec * String * StringSet.Set * Fun * Sort * Term -> LispCell

  def mkSnarkFmlaApp(context, sp, dpn, vars, f, srt, arg) =
    let args = case arg
                of Record(flds,_) -> map(fn (_, term) -> term) flds
	         | _ -> [arg] in
    case f
      of Op(Qualified("Boolean",id),_) ->
	    let snarkArgs = map(fn (arg) -> mkSnarkFmla(context, sp, dpn, vars, arg)) args in
	      Lisp.cons(snarkBoolOp(id), Lisp.list snarkArgs)
       | Op(Qualified(qual,id),_) ->
	    let snarkArgs = map(fn (arg) -> mkSnarkTerm(context, sp, dpn, vars, arg)) args in
	      Lisp.cons(Lisp.symbol("SNARK",mkSnarkName(qual,id)), Lisp.list snarkArgs)
       | Equals -> 
	    let def boolArgp(arg, srt) =
	          case srt of
		    | Base(Qualified(q,id),_,_) -> q = "Boolean" or id = "Boolean"
                    | _ -> false in
	    let [arg1,arg2] = args in
	    let Arrow (dom,rng,_) = srt in
	    let Product(s:List(Id * Sort), _) = dom in
	    let [(_,s1),(_,s2)] = s in
	    let isfmla = boolArgp(arg1, s1) or boolArgp(arg2, s2) in
	    let snarkArg1 =
	        if isfmla
		  then mkSnarkFmla(context, sp, dpn, vars, arg1)
		else mkSnarkTerm(context, sp, dpn, vars, arg1) in
	    let snarkArg2 =
	        if isfmla
		  then mkSnarkFmla(context, sp, dpn, vars, arg2)
		else mkSnarkTerm(context, sp, dpn, vars, arg2) in
	      if isfmla 
		then Lisp.cons(Lisp.symbol("SNARK","IFF"), Lisp.list [snarkArg1, snarkArg2])
	      else Lisp.cons(Lisp.symbol("SNARK","="), Lisp.list [snarkArg1, snarkArg2])


  op mkSnarkFmla: Context * Spec * String * StringSet.Set * Term -> LispCell

  def mkSnarkFmla(context, sp, dpn, vars, fmla) =
    case fmla
      of Bind(bndr, bndVars, term, _) ->
	let snarkBndList = snarkBndVars(bndVars) in
	let newVars = map(fn (var, srt) -> specId(var))
	                 bndVars in
	let snarkFmla = mkSnarkFmla(context, sp, dpn, StringSet.addList(vars, newVars), term) in
	   Lisp.list [Lisp.symbol("SNARK",bndrString bndr),
		      snarkBndList,
		      snarkFmla]
      | Apply(Fun(f, srt, _), arg, _) -> mkSnarkFmlaApp(context, sp, dpn, vars, f, srt, arg)
      | IfThenElse(c, t, e, _) ->
	   Lisp.list [Lisp.symbol("SNARK","IF"),
		      mkSnarkFmla(context, sp, dpn, vars, c),
		      mkSnarkFmla(context, sp, dpn, vars, t),
		      mkSnarkFmla(context, sp, dpn, vars, e)]
      | Fun ((Bool true), Boolean, _) -> Lisp.symbol("SNARK","TRUE")
      | Fun ((Bool false), Boolean, _) -> Lisp.symbol("SNARK","FALSE")
      | _ -> mkSnarkTerm(context, sp, dpn, vars, fmla)

  op mkSnarkTermApp: Context * Spec * String * StringSet.Set * Fun * Sort * Term -> LispCell

  def mkSnarkTermApp(context, sp, dpn, vars, f, srt, arg) =
    let args = case arg
                of Record(flds,_) -> map(fn (_, term) -> term) flds
	         | _ -> [arg] in
    case f
      of Op(Qualified(qual,id),_) ->
	   let snarkArgs = map(fn (arg) -> mkSnarkTerm(context, sp, dpn, vars, arg)) args in
	      Lisp.cons(Lisp.symbol("SNARK",mkSnarkName(qual,id)), Lisp.list snarkArgs)

  op mkSnarkTerm: Context * Spec * String * StringSet.Set * Term -> LispCell

  def mkSnarkTerm(context, sp, dpn, vars, term) =
%    let _ = writeLine("Translating to snark: "^printTerm(term)) in
    case term
      of Apply(Fun(f, srt, _), arg, _) -> mkSnarkTermApp(context, sp, dpn, vars, f, srt, arg)
      | IfThenElse(c, t, e, _) ->
	   Lisp.list [Lisp.symbol("SNARK","IF"),
		      mkSnarkTerm(context, sp, dpn, vars, c),
		      mkSnarkTerm(context, sp, dpn, vars, t),
		      mkSnarkTerm(context, sp, dpn, vars, e)]
      | Fun (Op(Qualified(qual,id),_),_, _) -> Lisp.symbol("SNARK",mkSnarkName(qual, id))
      | Fun ((Nat nat), Nat, _) -> Lisp.nat(nat)
      | Var ((id,srt),_) -> Lisp.symbol("SNARK",id)
      | _ -> mkNewSnarkTerm(context, term) %% Unsupported construct

  op mkNewSnarkTerm: Context * Term -> LispCell

  def mkNewSnarkTerm(context, term) =
    let vars = freeVars term in
    let newFun = mkNewSnarkOp(context) in
    let snarkVars = map (fn (v as (id,_)) -> Lisp.symbol("SNARK", id)) vars in
      case snarkVars of
	| [] -> newFun
	| _ -> Lisp.cons(newFun, Lisp.list snarkVars)

  op mkNewSnarkOp: Context -> LispCell

  def mkNewSnarkOp(context) =
    let num = State.! context.counter + 1 in
      (context.counter State.:= num;
       Lisp.symbol("SNARK", ("sApply" ++ (Nat.toString num)))
      )

%  op lispFmla: Spec * String * Term -> LispTerm

%  def lispFmla(spc, dpn, fmla) =
%    reduceTerm(mkLFmla(spc, dpn, StringSet.empty, fmla))

  op snarkProperty: Context * Spec * Property -> LispCell

  def snarkProperty(context, spc, prop as (ptype, name, tyvars, fmla)) =
    let snarkFmla = mkSnarkFmla(context, spc, "SNARK", StringSet.empty, fmla) in
      Lisp.list [snark_assert, Lisp.quote(snarkFmla),
		 Lisp.symbol("KEYWORD","NAME"), Lisp.symbol("KEYWORD",name)]

  op snarkConjecture: Context * Spec * Property -> LispCell

  def snarkConjecture(context, spc, prop as (ptype, name, tyvars, fmla)) =
    let snarkFmla = mkSnarkFmla(context, spc, "SNARK", StringSet.empty, fmla) in
      Lisp.list [snark_prove, Lisp.quote(snarkFmla),
		 Lisp.symbol("KEYWORD","NAME"), Lisp.symbol("KEYWORD",name)]

  op snarkProperties: Spec -> List LispCell

  def snarkProperties(spc) =
    let properties = spc.properties in
    let context = newContext in
    let snarkProperties =
          map(fn (prop) -> snarkProperty(context, spc, prop))
	      properties in
     snarkProperties
}