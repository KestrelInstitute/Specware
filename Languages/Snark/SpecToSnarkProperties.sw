spec {

  import /Languages/MetaSlang/CodeGen/Lisp/SpecToLisp
%  import /Languages/MetaSlang/Transformations/Match
%  import /Languages/MetaSlang/CodeGen/Lisp/Lisp
%  import /Languages/MetaSlang/Specs/StandardSpec


  op snark_assert: LispCell
  def snark_assert = Lisp.symbol("SNARK","ASSERT")

  op snark_prove: LispCell
  def snark_prove = Lisp.symbol("SNARK","PROVE")

  def snarkPBaseSort(s:Sort, rng?):LispCell = 
	          case s of
		     Base(Qualified( _,id),_,_) -> if rng? then Lisp.symbol("SNARK",id)
                                                     else Lisp.symbol("SNARK",id)
		    | Product _ -> Lisp.bool true
		    | Arrow _ -> Lisp.bool true
		    | TyVar _ -> Lisp.bool true
  
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
    
  def snarkBoolOp(id) = Lisp.symbol("SNARK",id)

  op mkSnarkFmlaApp: Spec * String * StringSet.Set * Fun * Sort * Term -> LispCell

  def mkSnarkFmlaApp(sp, dpn, vars, f, srt, arg) =
    let args = case arg
                of Record(flds,_) -> map(fn (_, term) -> term) flds
	         | _ -> [arg] in
    case f
      of Op(Qualified("Boolean",id),_) ->
	    let snarkArgs = map(fn (arg) -> mkSnarkFmla(sp, dpn, vars, arg)) args in
	      Lisp.cons(snarkBoolOp(id), Lisp.list snarkArgs)
       | Op(Qualified(_,id),_) ->
	    let snarkArgs = map(fn (arg) -> mkSnarkTerm(sp, dpn, vars, arg)) args in
	      Lisp.cons(Lisp.symbol("SNARK",id), Lisp.list snarkArgs)
       | Equals -> 
     	    let snarkArgs = map(fn (arg) -> mkSnarkTerm(sp, dpn, vars, arg)) args in
	       Lisp.cons(Lisp.symbol("SNARK","="), Lisp.list snarkArgs)


  op mkSnarkFmla: Spec * String * StringSet.Set * Term -> LispCell

  def mkSnarkFmla(sp, dpn, vars, fmla) =
    case fmla
      of Bind(bndr, bndVars, term, _) ->
	let snarkBndList = snarkBndVars(bndVars) in
	let newVars = map(fn (var, srt) -> specId(var))
	                 bndVars in
	let snarkFmla = mkSnarkFmla(sp, dpn, StringSet.addList(vars, newVars), term) in
	   Lisp.list [Lisp.symbol("SNARK",bndrString bndr),
		      snarkBndList,
		      snarkFmla]
      | Apply(Fun(f, srt, _), arg, _) -> mkSnarkFmlaApp(sp, dpn, vars, f, srt, arg)
      | IfThenElse(c, t, e, _) ->
	   Lisp.list [Lisp.symbol("SNARK","IF"),
		      mkSnarkFmla(sp, dpn, vars, c),
		      mkSnarkFmla(sp, dpn, vars, t),
		      mkSnarkFmla(sp, dpn, vars, e)]
      | _ -> mkSnarkTerm(sp, dpn, vars, fmla)

  op mkSnarkTermApp: Spec * String * StringSet.Set * Fun * Sort * Term -> LispCell

  def mkSnarkTermApp(sp, dpn, vars, f, srt, arg) =
    let args = case arg
                of Record(flds,_) -> map(fn (_, term) -> term) flds
	         | _ -> [arg] in
    case f
      of Op(Qualified(_,id),_) ->
	   let snarkArgs = map(fn (arg) -> mkSnarkTerm(sp, dpn, vars, arg)) args in
	      Lisp.cons(Lisp.symbol("SNARK",id), Lisp.list snarkArgs)

  op mkSnarkTerm: Spec * String * StringSet.Set * Term -> LispCell

  def mkSnarkTerm(sp, dpn, vars, term) =
    case term
      of Apply(Fun(f, srt, _), arg, _) -> mkSnarkTermApp(sp, dpn, vars, f, srt, arg)
      | IfThenElse(c, t, e, _) ->
	   Lisp.list [Lisp.symbol("SNARK","IF"),
		      mkSnarkTerm(sp, dpn, vars, c),
		      mkSnarkTerm(sp, dpn, vars, t),
		      mkSnarkTerm(sp, dpn, vars, e)]
      | Fun (Op(Qualified(_,id),_),_, _) -> Lisp.symbol("SNARK",id)
      | Var ((id,srt),_) -> Lisp.symbol("SNARK",id)

%  op lispFmla: Spec * String * Term -> LispTerm

%  def lispFmla(spc, dpn, fmla) =
%    reduceTerm(mkLFmla(spc, dpn, StringSet.empty, fmla))

  op snarkProperty: Spec * Property -> LispCell

  def snarkProperty(spc, prop as (ptype, name, tyvars, fmla)) =
    let snarkFmla = mkSnarkFmla(spc, "SNARK", StringSet.empty, fmla) in
      Lisp.list [snark_assert, Lisp.quote(snarkFmla),
		 Lisp.symbol("KEYWORD","NAME"), Lisp.symbol("KEYWORD",name)]

  op snarkConjecture: Spec * Property -> LispCell

  def snarkConjecture(spc, prop as (ptype, name, tyvars, fmla)) =
    let snarkFmla = mkSnarkFmla(spc, "SNARK", StringSet.empty, fmla) in
      Lisp.list [snark_prove, Lisp.quote(snarkFmla),
		 Lisp.symbol("KEYWORD","NAME"), Lisp.symbol("KEYWORD",name)]

  op snarkProperties: Spec -> List LispCell

  def snarkProperties(spc) =
    let properties = spc.properties in
    let snarkProperties =
          map(fn (prop) -> snarkProperty(spc, prop))
	      properties in
     snarkProperties
}