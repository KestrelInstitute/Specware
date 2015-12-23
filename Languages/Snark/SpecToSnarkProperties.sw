(* Copyright 2015 Kestrel Institute. See file LICENSE for license details *)

snark qualifying spec

  import /Languages/MetaSlang/Specs/Utilities
  import /Languages/MetaSlang/CodeGen/Lisp/SpecToLisp    % specId uses Lisp conventions, in particular for specId
  import /Languages/MetaSlang/CodeGen/CodeGenUtilities
  import /Languages/MetaSlang/Transformations/ExplicateHiddenAxioms
  import /Languages/MetaSlang/Transformations/OpToAxiom
  import /Languages/SpecCalculus/Semantics/Evaluate/UnitId/Utilities
  import /Languages/SpecCalculus/Semantics/Evaluate/UnitId
%  import /Languages/MetaSlang/Transformations/Match
%  import /Languages/MetaSlang/CodeGen/Lisp/Lisp
%  import /Languages/MetaSlang/Specs/StandardSpec
  import /Languages/MetaSlang/Specs/MSTerm


  op simpApplies: MSTerm -> MSTerm
(*  def simpApplies(tm) =
    case tm of
      | Apply(Lambda([pat, cond, body], _), arg) ->
        let patArgs 
*)
  
  op LISP.PPRINT: LispCell -> LispCell

  type Context = 
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
      (case AnnSpec.findTheType (sp, qid) of
	 | None -> srt
	 | Some info ->
	   if ~ (definedTypeInfo? info) then
	     srt
	   else
	     let (tvs, srt2) = unpackFirstTypeDef info in
	     let ssrt = if length tvs = length srts
                          then substType (zip (tvs, srts), srt2)
                          else srt2     % Not sure what this means in general
             in
	     case ssrt of
	       | Product   _ -> srt
	       | Arrow     _ -> ssrt
	       | TyVar     _ -> srt
	       | CoProduct _ -> srt
	       | _ -> unfoldBaseUnInterpV (sp, ssrt, verbose))
    | _ -> srt
  
  def snarkPBaseSort(spc, s:MSType, rng?):LispCell = 
    let s = unfoldBaseUnInterp(spc, s) in
	          case s of
		   %| Base(Qualified("Nat",    "Nat"),   _,_) -> Lisp.symbol("SNARK","NUMBER")
		   %| Base(Qualified("Nat",    "PosNat"),_,_) -> Lisp.symbol("SNARK","NUMBER")
		    | Base(Qualified("Integer","Int"),   _,_) -> Lisp.symbol("SNARK","NUMBER")
		    | Boolean _ -> if rng? then Lisp.symbol("SNARK","BOOLEAN") else Lisp.symbol("SNARK","LOGICAL")
		   %| Base(Qualified(qual,id),_,_) -> let res = findPBuiltInSort(spc, Qualified(qual,id), rng?) in
                      %let _ = if specwareDebug? then toScreen("findPBuiltInSort: "^printType(s)^" returns ") else () in
                      %let _ = if specwareDebug? then  LISP.PPRINT(res) else Lisp.list [] in
		      %let _ = if specwareDebug? then  writeLine("") else () in
		     % res   %findPBuiltInType(spc, Qualified(qual,id), rng?)
		    | Base(Qualified( _,id),_,_) -> if rng? then 
                                                      Lisp.symbol("SNARK",snarkSortId(id))
                                                    else 
                                                      Lisp.symbol("SNARK",snarkSortId(id))
		    | Subtype (supSrt, _, _) -> snarkPBaseSort(spc, supSrt, rng?)
		    | Quotient(supSrt, _, _) -> snarkPBaseSort(spc, supSrt, rng?)
		    | Product _ -> Lisp.symbol("SNARK","TRUE")
		    | Arrow   _ -> Lisp.symbol("SNARK","TRUE")
		    | TyVar   _ -> Lisp.symbol("SNARK","TRUE")
		    | _         -> Lisp.symbol("SNARK","TRUE")

  def findPBuiltInSort(spc, qid as Qualified(qual,id), rng?) =
    let optSrt = AnnSpec.findTheType(spc, qid) in
    case optSrt of
      | Some info ->
        (let
           def builtinType? s =
	     case s of 
	       | Base (Qualified ("Nat",     "Nat"), _, _) -> true
	       | Base (Qualified ("Integer", "Int"), _, _) -> true
	       | Boolean _ -> true 
	       | _ -> false 
	   def builtinSnarkSort s =
	     case s of 
	       | Base (Qualified ("Nat",     "Nat"), _, _) -> Lisp.symbol ("SNARK", "NUMBER")
	       | Base (Qualified ("Integer", "Int"), _, _) -> Lisp.symbol ("SNARK", "NUMBER")
	       | Boolean _ -> 
	         if rng? then 
		   Lisp.symbol("SNARK","BOOLEAN") 
		 else 
		   Lisp.symbol ("SNARK", "LOGICAL")
         in
	 let defs = typeInfoDefs info in
	 let builtinType = findLeftmost builtinType? defs in
	 case builtinType of
	   | Some srt -> builtinSnarkSort srt
	   | _ -> 
	     case defs of
	       | [dfn] -> 
	         (let (_, srt) = unpackType dfn in
		  case srt of
		    | Subtype (supSrt, _, _) -> Lisp.symbol ("SNARK", snarkSortId id)
		    | Quotient (supSrt, _, _) -> Lisp.symbol ("SNARK", snarkSortId id)
		    | _ -> snarkPBaseSort (spc, srt, rng?))
	       | _ -> Lisp.symbol ("SNARK", snarkSortId id))
      | _ -> Lisp.symbol ("SNARK", snarkSortId id)
    
  def snarkPPBaseSort(_(* sp *):Spec, s:MSType, rng?):LispCell = 
    let res =
    case s of
      | Base(Qualified("Nat",    "Nat"),_,_) -> Lisp.symbol("SNARK","NUMBER")
      | Base(Qualified("Integer","Int"),_,_) -> Lisp.symbol("SNARK","NUMBER")
      | Base(Qualified( _,id),_,_) -> if rng? then Lisp.symbol("SNARK",snarkSortId(id))
				      else Lisp.symbol("SNARK",snarkSortId(id))
      | Boolean _ -> Lisp.symbol("SNARK",snarkSortId("Boolean"))
      | Product _ -> Lisp.symbol("SNARK","TRUE")
      | Arrow _ -> Lisp.symbol("SNARK","TRUE")
      | TyVar _ -> Lisp.symbol("SNARK","TRUE") in
    %let _ = if specwareDebug? then writeLine("snarkPBaseSort: "^printType(s)) else () in
    %let _ = if specwareDebug? then LISP.PPRINT(res) else Lisp.list[] in
    res
  
  def bndrString(bndr) =
    case bndr
      of Forall -> "ALL"
	| Exists -> "EXISTS"

  op snarkVar: MSVar -> LispCell

  def snarkVar(v as (id, srt)) =
    case srt of
      | Boolean _ -> snarkBoolVarFromId(id)
      | _ -> snarkVarFromId(id)

  op snarkVarFromId: Id -> LispCell

  def snarkVarFromId(id) =  Lisp.symbol("SNARK", "?" ^ id)
  
  op snarkBoolVarFromId: Id -> LispCell

  def snarkBoolVarFromId(id) =  Lisp.symbol("SNARK", "?" ^ id ^ "_Logical")
  
  op snarkVarTerm: MSVar -> LispCell

  def snarkVarTerm(v as (id, srt)) =
    case srt of
      | Boolean _ -> snarkBoolVarTermFromId(id)
      | _ -> snarkVarFromId(id)

  op snarkVarFmla: MSVar -> LispCell

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
  op snarkBndVar: Spec * MSVar * MSVars -> LispCell

  def snarkBndVar(sp, var, globalVars) =
    let (name, srt) = var in
      if exists? (fn (gname, _) -> name = gname) globalVars
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
  
  op snarkBndVars: Spec * MSVars * MSVars -> LispCell

  def snarkBndVars(sp, vars, globalVars) =
    let snarkVarList = map (fn (var) -> snarkBndVar(sp, var, globalVars)) vars in
    let res = Lisp.list snarkVarList in
      res
    
  op mkSnarkName: Qualifier * Id -> String

  def mkSnarkName(qual, id) =
    case (qual, id) of
      | ("Nat",     "<=")   -> "=<"
      | ("Nat",     "~")    -> "-"
      | ("Nat",     ">=")   -> ">="
      | ("Nat",     "+")    -> "+"
      | ("Nat",     "-")    -> "-"
      | ("Nat",     "*")    -> "*"
      | ("Integer", "+")    -> "+"
      | ("Integer", "-")    -> "-"
      | ("Integer", "~")    -> "-"
      | ("Integer", "*")    -> "*"
      | ("Integer", "<=")   -> "=<"
      | ("Integer", "<")    -> "<"
      | ("Integer", ">=")   -> ">="
      | ("Integer", ">")    -> ">"
      | ("Integer", "zero") -> "0"
      | ("Integer", "one")  -> "1"
      | (_, "hoapply") ->  "HOAPPLY"
      | _ -> if qual = UnQualified
	       then id
	     else qual^"."^id

  op mkSnarkFmlaApp: Context * Spec * String * StringSet.Set * MSFun * MSType * MSTerm -> LispCell

  def mkSnarkFmlaApp(context, sp, dpn, vars, f, srt, arg) =
    let args = case arg
                of Record(flds,_) -> map(fn (_, term) -> term) flds
	         | _ -> [arg] in
    case f of
       | Op(Qualified(qual,id),_) ->
	    let snarkArgs = map(fn (arg) -> mkSnarkTerm(context, sp, dpn, vars, arg)) args in
	      Lisp.cons(Lisp.symbol("SNARK",mkSnarkName(qual,id)), Lisp.list snarkArgs)
       | Embedded (Qualified(_, id)) ->
	      let Arrow (dom,rng,_) = srt in
	      let unfoldDomSrt = unfoldBaseUnInterp(sp, dom) in
	      let isfmla = boolType?(unfoldDomSrt) in
	      let snarkArg = if isfmla
	                       then mkSnarkFmla(context,sp,dpn,vars,[],arg)
			     else mkSnarkTerm(context,sp,dpn,vars,arg) in
		 Lisp.cons(Lisp.symbol("SNARK","embed?"), Lisp.list[Lisp.symbol("SNARK",id),snarkArg])
       | Choose _ -> 
	      (case args of
		| [f, a] -> let tm = simplifiedApply(f, a, sp) in
			    mkSnarkFmla(context, sp, dpn, vars, [], tm)
	        | _ -> mkSnarkFmla(context, sp, dpn, vars, [], arg))
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
	    let [arg1,arg2] = args in
	    let Arrow (dom,rng,_) = srt in
	    let Product(s:List(Id * MSType), _) = dom in
	    let [(_,s1),(_,s2)] = s in
	    (case s1 of
	       | Quotient(qsup, eqv, _) -> mkSnarkFmla(context, sp, dpn, vars, [], mkApplication(eqv, [arg1, arg2]))
	       | _ ->
	    let unfoldS1 = unfoldBaseUnInterp(sp, s1) in
	    let unfoldS2 = unfoldBaseUnInterp(sp, s2) in
	    let isfmla = boolType?(unfoldS1) || boolType?(unfoldS2) in
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
	      else Lisp.cons(Lisp.symbol("SNARK","="), Lisp.list [snarkArg1, snarkArg2]))
       | NotEquals -> 
	    let [arg1,arg2] = args in
	    let Arrow (dom,rng,_) = srt in
	    let Product(s:List(Id * MSType), _) = dom in
	    let [(_,s1),(_,s2)] = s in
	    (case s1 of
	       | Quotient(qsup, eqv, _) -> Lisp.cons(Lisp.symbol("SNARK", "NOT"), 
						     Lisp.list [mkSnarkFmla(context, sp, dpn, vars, [], mkApplication(eqv, [arg1, arg2]))])
	       | _ ->
	    let unfoldS1 = unfoldBaseUnInterp(sp, s1) in
	    let unfoldS2 = unfoldBaseUnInterp(sp, s2) in
	    let isfmla = boolType?(unfoldS1) || boolType?(unfoldS2) in
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
				 else Lisp.cons(Lisp.symbol("SNARK","="), Lisp.list [snarkArg1, snarkArg2])]))


  op mkSnarkFmla: Context * Spec * String * StringSet.Set * MSVars * MSTerm -> LispCell

  def mkSnarkFmla(context, sp, dpn, vars, globalVars, fmla) =
    case containsTheTerm fmla of
      | Some(the_tm as The(v,bod,pos)) ->
        %% p(the(x) q x) <=> (ex(x) p x && q x) given uniqueness of the
        let subst_fmla = mapTerm ((fn st -> if st = the_tm then Var(v,pos) else st),id,id) fmla in
        let ex_fmla = Bind(Exists,[v],Utilities.mkAnd(subst_fmla,bod),pos) in
        mkSnarkFmla(context, sp, dpn, vars, globalVars, ex_fmla)
      | _ ->
    case fmla of
      | Bind(bndr, bndVars, term, a) ->
        if bndr = Exists1
	  then mkSnarkFmla(context, sp, dpn, vars, globalVars, expandExists1(head bndVars,term,a))
	else
	let snarkBndList = snarkBndVars(sp, bndVars, globalVars) in
	let newVars = map(fn (var, srt) -> specId(var,""))
	                 bndVars in
	let bndVarsPred = foldl (fn (res, (var:Id, srt)) -> Utilities.mkAnd(srtPred(sp, srt, mkVar((var, srt))), res))
			    (mkTrue()) bndVars in
	let newTerm = case bndr of
	                | Forall -> Utilities.mkSimpImplies(bndVarsPred, term)
	                | Exists -> Utilities.mkAnd(bndVarsPred, term)
	in
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
      | Fun ((Bool true),  _, _) -> Lisp.symbol("SNARK","TRUE")  % type of Fun was Bool, but that was a free var in the pattern! 
      | Fun ((Bool false), _, _) -> Lisp.symbol("SNARK","FALSE") % type of Fun was Bool, but that was a free var in the pattern!
      | Var (v, _) -> snarkVarFmla(v)
      | _ -> mkSnarkTerm(context, sp, dpn, vars, fmla)

  op  containsTheTerm: MSTerm -> Option(MSTerm)
  def containsTheTerm tm =
    case tm of
      | The _ -> Some tm
      | Bind _ -> None			% Will get caught on recursive call to mkSnarkFmla
      | Apply(Fun(f, srt, _), arg, _) ->
        (case f of
	   | Not -> None
	   | And -> None
	   | Or -> None
	   | Implies -> None
	   | Iff -> None
	   | NotEquals -> None
	   | _ -> containsTheTerm arg)
      | Apply(f,arg,_) ->
        (case containsTheTerm f of
	   | None -> containsTheTerm arg
	   | r -> r)
      | IfThenElse(c, t, e, _) ->
        (case containsTheTerm c of
	  | None ->
	    (case containsTheTerm t of
	      | None -> containsTheTerm e
	      | r -> r)
	   | r -> r)
      | Record(prs,_) ->
	foldl (fn (result,(_,tm)) ->
	       case result of
		 | None -> containsTheTerm tm
		 | r -> r)
	  None prs
      | Let(bnds,bod,_) ->
	foldl (fn (result,(_,tm)) ->
	       case result of
		 | None -> containsTheTerm tm
		 | r -> r)
	  (containsTheTerm bod) bnds
      | LetRec(_,bod,_) -> containsTheTerm bod
      | TypedTerm(stm,_,_) -> containsTheTerm stm
      | _ -> None

  op  expandExists1: MSVar * MSTerm * Position -> MSTerm
  def expandExists1(v as (vn,s), bod, pos) =
    let v1 = (vn ^ "__exists1",s) in
    let v1_tm = Var(v1,pos) in
    let v_tm =  Var(v, pos) in
    let v1_bod = substitute(bod,[(v,v1_tm)]) in
    Bind(Exists,[v],MS.mkAnd(bod, Bind(Forall,[v1],mkImplies(v1_bod,mkEquality(s,v1_tm,v_tm)),pos)),pos)

  op mkSnarkTermAppTop: Context * Spec * String * StringSet.Set * MSFun * MSType * MSTerm -> LispCell
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

  op mkSnarkTermAppRecordArg: Context * Spec * String * StringSet.Set * MSFun * MSType * MSTerm -> LispCell
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


  op mkSnarkTermApp: Context * Spec * String * StringSet.Set * MSFun * MSTerm -> LispCell
  def mkSnarkTermApp(context, sp, dpn, vars, f, arg) =
    let args = case arg
                of Record(flds,_) -> map(fn (_, term) -> term) flds
	         | _ -> [arg] in
    case f of
      | Op(Qualified("IntegerAux", "-"),_) ->
	  let snarkArgs = map(fn (arg) -> mkSnarkTerm(context, sp, dpn, vars, arg)) args in
	      Lisp.cons(Lisp.symbol("SNARK","-"), Lisp.cons(Lisp.nat(0), Lisp.list snarkArgs))
      | Op(Qualified(qual,id),_) ->
          let snarkArgs = map(fn (arg) -> mkSnarkTerm(context, sp, dpn, vars, arg)) args in
	      Lisp.cons(Lisp.symbol("SNARK",mkSnarkName(qual,id)), Lisp.list snarkArgs)
      | Project (id) -> %let _ = if id = "local" then debug("project_local") else () in
	  let snarkArgs = map(fn (arg) -> mkSnarkTerm(context, sp, dpn, vars, arg)) args in
	  if isNum (id@0)
	    then
	      if id = "1" then Lisp.cons(Lisp.symbol("CL","CAR"),Lisp.list snarkArgs)
	      else 
	      Lisp.cons(Lisp.symbol("CL","NTH"),
			Lisp.list [head snarkArgs, Lisp.nat((stringToNat id) - 1)])
	  else
	  let prodSrt = termType(arg) in
	  let userProdSrt = findMatchingUserTypeOption(sp, prodSrt) in
	  (case userProdSrt of
	     | None -> Lisp.cons(Lisp.symbol("SNARK",mkSnarkName(UnQualified, "project_"^id)),
				 Lisp.list snarkArgs)
	     | Some (Base (Qualified(q, prodSrtId),_, _)) ->
       %%IMPORTANT LOOK AT CODEGENTRANSFORMS FOR CONSISTENCY
	     Lisp.cons(Lisp.symbol("SNARK",mkSnarkName(UnQualified, "project_"^prodSrtId^"_"^id)), Lisp.list snarkArgs))
      | Embed (Qualified(_, id), b) -> %let _ = if id = "Cons" then debug("embed__Cons") else () in
	  let snarkArgs = map(fn (arg) -> mkSnarkTerm(context, sp, dpn, vars, arg)) args in
	      Lisp.cons(Lisp.symbol("SNARK",mkSnarkName(UnQualified, "embed__"^id)), Lisp.list snarkArgs)
      | Restrict -> let [tm] = args in mkSnarkTerm(context, sp, dpn, vars, tm)
      | Choose _ -> 
	      (case args of
		| [f, a] -> let tm = simplifiedApply(f, a, sp) in
			    mkSnarkTerm(context, sp, dpn, vars, tm)
	        | _ -> mkSnarkTerm(context, sp, dpn, vars, arg))
      | Quotient _ -> mkSnarkTerm(context, sp, dpn, vars, arg)

  op mkSnarkHOTermApp: Context * Spec * String * StringSet.Set * MSTerm * MSTerm -> LispCell

  def mkSnarkHOTermApp(context, sp, dpn, vars, f, arg) =
    let args = case arg
                of Record(flds,_) -> [f]++map(fn (_, term) -> term) flds
	         | _ -> [f, arg] in
    let snarkArgs = map(fn (arg) -> mkSnarkTerm(context, sp, dpn, vars, arg)) args in
     Lisp.cons(Lisp.symbol("SNARK","HOAPPLY"), Lisp.list snarkArgs)

  op mkSnarkTerm: Context * Spec * String * StringSet.Set * MSTerm -> LispCell

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
      | Fun (Embed(Qualified(_, id), _),_, _) -> Lisp.symbol("SNARK",mkSnarkName(UnQualified,"embed__"^id))
      | Var (v,_) -> snarkVarTerm(v)
      | Record (fields, _) -> mkSnarkTermRecord(context, sp, dpn, vars, term)
      | _ -> mkNewSnarkTerm(context, term) %% Unsupported construct

  op mkSnarkTermRecord: Context * Spec * String * StringSet.Set * MSTerm -> LispCell
  def  mkSnarkTermRecord(context, spc, dpn, vars, term as Record (fields,_)) =
    let srt = inferTypeFoldRecords(spc,term) in
    case srt of
      | Base (qid, _, _) -> mkSnarkTermApp(context, spc, dpn, vars,
					   Op(getRecordConstructorOpName(qid), Nonfix), term)
      | _ -> Lisp.cons(Lisp.symbol("CL","LIST"),
		       Lisp.list (map (fn (_,fldval) ->
				        mkSnarkTerm(context, spc, dpn, vars, fldval))
				    fields)) 

  op mkNewSnarkTerm: Context * MSTerm -> LispCell

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
       Lisp.symbol("SNARK", ("sApply" ^ (Nat.show num)))
      )

%  op lispFmla: Spec * String * MSTerm -> LispTerm

%  def lispFmla(spc, dpn, fmla) =
%    reduceTerm(mkLFmla(spc, dpn, StringSet.empty, fmla))

  op snarkSubsortProperties(context: Context, spc: Spec): List LispCell =
    let types = typesAsList(spc) in
    let snarkSubsortProps = mapPartial(fn (qual, id, info) ->
				       typeInfoToSnarkSubsortProp(context, spc, id, info))
                                       types in
      snarkSubsortProps

  op typeInfoToSnarkSubsortProp: Context * Spec * Id * TypeInfo -> Option LispCell
  def typeInfoToSnarkSubsortProp(context, spc, id, info) =
    if ~ (definedTypeInfo? info) then
      None
    else
      let srt = firstTypeDefInnerType info in
      case srt of
	| Subtype (supSrt, pred, _) | false -> % Not sure what this is supposed to be but it is currently wrong
	  let snarkSubSrtId = snarkSortId(id) in
	  let subSrtVar = (snarkSubSrtId, srt) in
	  let snarkBndVar = snarkBndVar(spc, subSrtVar, []) in
	  let subSrtPred = srtPred(spc, srt, mkVar(subSrtVar)) in
         % let _ = writeLine("subSrtPred: "^printTerm subSrtPred^" for var "^printTerm (mkVar(subSrtVar))) in
	  let snarkSubSrtPred = mkSnarkFmla(context, spc, "SNARK", StringSet.empty, [], subSrtPred) in
	  Some (Lisp.list [snark_assert, Lisp.quote(snarkSubSrtPred),
			   Lisp.symbol("KEYWORD","NAME"), Lisp.symbol("KEYWORD","subSort" ^ snarkSubSrtId)])
	| _ -> None

  op snarkPropertiesFromProperty: Context * Spec * Property -> List LispCell

  def snarkPropertiesFromProperty(context, spc, prop as (ptype, pname as Qualified(qname, name), tyvars, fmla, _)) =
    %let _ = if name = "filter_Object$1$_$Object$2_def" then debug("embed__cons prop") else () in
    %let liftedFmlas = proverPattern(fmla) in
    let liftedFmlas = [fmla] in
    map (fn (liftedFmla) -> let snarkFmla = mkSnarkFmla(context, spc, "SNARK", StringSet.empty, [], liftedFmla) in
                             Lisp.list [snark_assert, Lisp.quote(snarkFmla),
					Lisp.symbol("KEYWORD","NAME"), Lisp.symbol("KEYWORD",name)])
        liftedFmlas
  
  op snarkProperty: Context * Spec * Property -> LispCell

  def snarkProperty(context, spc, prop as (ptype, pname as Qualified(qname, name), tyvars, fmla, _)) =
    let snarkFmla = mkSnarkFmla(context, spc, "SNARK", StringSet.empty, [], fmla) in
      Lisp.list [snark_assert, Lisp.quote(snarkFmla),
		 Lisp.symbol("KEYWORD","NAME"), Lisp.symbol("KEYWORD",name)]

  op snarkRewrite: Context * Spec * Property -> LispCell

  def snarkRewrite(context, spc, prop as (ptype, pname as Qualified(qname, name), tyvars, fmla, _)) =
    let snarkFmla = mkSnarkFmla(context, spc, "SNARK", StringSet.empty, [], fmla) in
      Lisp.list [snark_assert_rewrite, Lisp.quote(snarkFmla),
		 Lisp.symbol("KEYWORD","NAME"), Lisp.symbol("KEYWORD",name)]

  op snarkConjectureRemovePattern: Context * Spec * Property -> LispCell

  def snarkConjectureRemovePattern(context, spc, prop as (ptype, pname as Qualified(qname, name),
                                                          tyvars, fmla, _)) =
    %let liftedFmlas = proverPattern(fmla) in
    let liftedFmlas = [fmla] in
    let liftedConjecture = mkConj(liftedFmlas) in
    let snarkFmla = mkSnarkFmla(context, spc, "SNARK", StringSet.empty, [], liftedConjecture) in
      Lisp.list [snark_prove, Lisp.quote(snarkFmla),
		 Lisp.symbol("KEYWORD","NAME"), Lisp.symbol("KEYWORD",name)]

  op snarkConjecture: Context * Spec * Property -> LispCell

  def snarkConjecture(context, spc, prop as (ptype, pname as Qualified(qname, name), tyvars, fmla, _)) =
    let snarkFmla = mkSnarkFmla(context, spc, "SNARK", StringSet.empty, [], fmla) in
      Lisp.list [snark_prove, Lisp.quote(snarkFmla),
		 Lisp.symbol("KEYWORD","NAME"), Lisp.symbol("KEYWORD",name)]

  op snarkAnswer: Context * Spec * Property * MSVars -> LispCell

  def snarkAnswer(context, spc, prop as (ptype, pname as Qualified(qname, name), tyvars, fmla, _), ansVars) =
    %% ansVars don't have to be global in newer versions of SNARK
    let snarkFmla = mkSnarkFmla(context, spc, "SNARK", StringSet.empty, [], fmla) in
    let snarkAnsVars = map (fn (v) -> snarkVar(v)) ansVars in
    let snarkAnsTerm = Lisp.list ([Lisp.symbol("SNARK","ANS")] ++ snarkAnsVars) in
      Lisp.list [snark_prove, Lisp.quote(snarkFmla),
		 Lisp.symbol("KEYWORD","ANSWER"), Lisp.quote(snarkAnsTerm),
		 Lisp.symbol("KEYWORD","NAME"), Lisp.symbol("KEYWORD",name)]

  op snarkProperties: Spec -> List LispCell

  def snarkProperties(spc) =
    % let properties = spc.properties in
    let context = newContext in
    let snarkProperties =
        foldrSpecElements
	  (fn (el,result) ->
	   case el of
	     | Property prop ->
	       Cons(snarkProperty(context, spc, prop),result)
	     | _ -> result)
	  [] spc.elements
    in
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

  op snarkOpPropertyPartial: Spec * String * MSType -> Option LispCell

  def snarkOpPropertyPartial(spc, name, srt) =
    let prop = snarkOpProperty(spc, name, srt) in
       if null(prop) then None else Some prop

  op snarkOpProperty: Spec * String * MSType -> LispCell

  def snarkOpProperty(spc, name, srt) = snarkFunctionProp(spc, name, srt)

  op snarkFunctionProp: Spec * String * MSType -> LispCell

  def snarkFunctionProp(spc, name, srt) =
    %let _ = toScreen("Generating snark prop for "^name^" with sort: ") in
    %let _ = printTypeToTerminal srt in
    (case (curryShapeNum(spc, srt), typeArity(spc, srt))
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




  op snarkFunctionNoCurryProp: Spec * String * MSType * Nat -> LispCell

  def snarkFunctionNoCurryProp(spc, name, srt, arity) =
    case arrowOpt(spc, srt) of
      Some (dom, rng) ->
	case rng of
	  | Boolean _ -> snarkPredicateProp(spc, name, dom, arity)
	  | _ ->
	case productOpt(spc, dom) of
	  | Some fields -> 
	    let domSortList = map(fn (id: Id, srt:MSType) -> snarkBaseSort(spc, srt, false))
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
