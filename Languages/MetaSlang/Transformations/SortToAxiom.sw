Prover qualifying spec
 import ../Specs/Environment
 import ../Specs/Utilities
 import DefToAxiom

  op axiomFromSortDefTop: Spec * Qualifier * Id * SortInfo -> Properties
  def axiomFromSortDefTop(spc, qname, name, sortDecl) =
    case sortDecl of
      | (sortNames, sortTyVars, [(defTyVars, srtDef)]) ->
          let localSorts = spc.importInfo.localSorts in
          if memberQualifiedId(qname, name, localSorts) then
	    let pos = sortAnn(srtDef) in
	    let sortName = mkQualifiedId(qname, name) in
	    let axioms = case srtDef of
	                  | CoProduct _ -> axiomFromCoProductDefTop(spc, sortName, srtDef)
	                  | Subsort _ -> axiomFromSubSortDefTop(spc, sortName, srtDef)
	                  | Product _ -> axiomFromProductDefTop(spc, sortName, srtDef)
	                  | _ -> [] in
               axioms
	else %let _ = writeLine(name^": in axiomFromSortDef Def part is not local") in
	  %let _ = debug("not local sort") in
	     []
      | _ -> %let _ = writeLine(name^": in axiomFromSortDef NOT def part") in
	       []

  op axiomFromSubSortDefTop: Spec * QualifiedId * Sort -> Properties
  def axiomFromSubSortDefTop(spc, name, srt as Subsort (supSort, subSortTerm, b)) =
    []

  op axiomFromProductDefTop: Spec * QualifiedId * Sort -> Properties
  def axiomFromProductDefTop(spc, name, srt as Product (fields, b)) =
    let projectAxioms = mkProjectAxioms(spc, name, srt, fields) in
%    let constructAxiom = mkConstructAxiom(spc, name, fields) in
%    Cons(constructAxiom, projectAxioms)
    projectAxioms

  op mkProjectAxioms: Spec * QualifiedId * Sort * Fields -> Properties
  def mkProjectAxioms(spc, name, srt, fields) =
    let recordArg as Record(resFields, _) =  mkRecordTerm(spc, name, srt) in
    ListPair.map (fn (field, res) -> mkProjectAxiom(spc, name, srt, field, recordArg, res)) (fields, resFields)

  op mkProjectAxiom: Spec * QualifiedId * Sort * Field * MS.Term * (Id * MS.Term) -> Property
  def mkProjectAxiom(spc, name as Qualified(prodQ, prodSrtId), srt, field as (fId, fSrt), arg, (_, res)) =
    let projQid as Qualified(projQ,projId) = getAccessorOpName(prodSrtId,name,fId) in
    let lhs = mkProjectTerm(spc, name, srt, field, arg) in
    let rhs = res in
    let eql = mkEquality(fSrt, lhs, rhs) in
    let bndVars = freeVars(eql) in
    let fmla = mkBind(Forall, bndVars, eql) in
    (Axiom, mkQualifiedId(prodQ, prodSrtId^"_def"), [], fmla)

  op mkRecordTerm: Spec * QualifiedId * Sort -> MS.Term
  def  mkRecordTerm(spc, srtName, srt as Product (fields, b)) =
    let opqid as Qualified(opq,opid) = getRecordConstructorOpName(srtName) in
    let codom:Sort  = Base(srtName,[],b) in
    let opsrt = Arrow(srt,codom,b) in
    let termsrt = Arrow(srt,codom,b) in
    let pat = patternFromSort(Some srt,b) in
    let cond = mkTrue() in
    let funterm = Fun(Op(opqid, Nonfix),termsrt,b) in
    recordTermFromSort(srt, b)

  op mkProjectTerm: Spec * QualifiedId * Sort * Field * MS.Term -> MS.Term
  def mkProjectTerm(spc, srtName, srt, field as (fId, fSrt), arg) =
    let b = noPos in
    let Qualified(_, srtId) = srtName in
    let opqid as Qualified(opq,opid) = getAccessorOpName(srtId,srtName,fId) in
    %let _ = writeLine("  op "^(printQualifiedId opqid)) in
    let codom:Sort  = Base(srtName,[],b) in
    let opsrt = Arrow(codom,fSrt,b) in
    Apply(Fun(Op(opqid, Nonfix), opsrt, b), arg, b)

(*
    let termsrt = Arrow(codom,srt,b) in
    let pat = patternFromSort(Some srt,b) in
    let cond = mkTrue() in
    let funterm = Fun(Project(fId),termsrt,b) in
    argTermFromSort(Some srt,funterm,b)
*)

  op mkConstructAxiom: Spec * QualifiedId * Fields -> Property
    
    
  
  op axiomFromCoProductDefTop: Spec * QualifiedId * Sort -> Properties
  def axiomFromCoProductDefTop(spc, name, srt as CoProduct (fields, b)) =
    let disEqAxioms = mkDisEqsForFields(spc, srt, name, fields) in
    let exhaustAxiom = exhaustAxiom(spc, srt, name, fields) in
    Cons(exhaustAxiom, disEqAxioms)

  op exhaustAxiom: Spec * Sort * QualifiedId * List (Id * Option Sort) -> Property
  def exhaustAxiom(spc, srt, name as Qualified(qname, id), fields) =
    let newVar = (id^"_Var", mkBase(name, [])) in
    let disjuncts = mkEqFmlasForFields(srt, newVar, fields) in
    let tm = mkSimpOrs(disjuncts) in
    let fmla = mkBind(Forall, [newVar], tm) in
      (Axiom, mkQualifiedId(qname, id^"_def"), [], fmla)

  op mkEqFmlasForFields: Sort * Var * List (Id * Option Sort) -> List MS.Term
  def mkEqFmlasForFields(srt, var, fields) =
    case fields of
      | [] -> []
      | (id, optSrt):: restFields ->
        let constrTerm = mkConstructorTerm(srt, id, optSrt) in
	let eql = mkEquality(srt, mkVar(var), constrTerm) in
	let restEqls = mkEqFmlasForFields(srt, var, restFields) in
	Cons(eql, restEqls)

  op mkDisEqsForFields: Spec * Sort * QualifiedId * List (Id * Option Sort) -> Properties
  def mkDisEqsForFields(spc, srt, name, fields) =
    case fields of
      | [] -> []
      | (id, optSrt)::restFields ->
        let diseqs = mkDisEqsForIdAndRest(id, srt, name, optSrt, restFields) in
	let restDisEqs = mkDisEqsForFields(spc, srt, name, restFields) in
	diseqs++restDisEqs

  op mkDisEqsForIdAndRest: Id * Sort * QualifiedId * Option Sort * List (Id * Option Sort) -> Properties
  def mkDisEqsForIdAndRest(id, srt, name, optSrt, restFields) =
    foldr
    (fn ((id2, optSrt2), props) ->
     let disEq = mkDisEqForTwoConstructors(id, srt, name, optSrt, id2, optSrt2) in
     Cons(disEq, props))
    [] restFields

  op mkDisEqForTwoConstructors: Id * Sort * QualifiedId * Option Sort * Id * Option Sort -> Property
  def mkDisEqForTwoConstructors(id1, srt, name, optSrt1, id2, optSrt2) =
    let tm1 = mkConstructorTerm(srt, id1, optSrt1) in
    let tm2 = mkConstructorTerm(srt, id2, optSrt2) in
    let eql = mkEquality(srt, tm1, tm2) in
    let disEql = mkNot(eql) in
    let vars = freeVars(eql) in
    let fmla = withAnnT(mkBind(Forall, vars, disEql), sortAnn(srt)) in
    let Qualified (qual, id) = name in
%    (Axiom, mkQualifiedId(qual, id^"_"^id1^"_notEq_"^id2), [], fmla)
    (Axiom, mkQualifiedId(qual, id^"_def"), [], fmla)

  op mkConstructorTerm: Sort * Id * Option Sort -> MS.Term
  def mkConstructorTerm(srt, id, optSrt) =
    case optSrt of
      | None -> Fun (Embed (id, false), srt, noPos)
      | Some (Product (args, _)) ->
      let recordFields = map (fn (aid, asrt) -> (aid, mkVar((aid^"_var", asrt)))) args in
      let args = mkRecord(recordFields) in
      Apply (Fun (Embed (id, true), srt, noPos), args, noPos)
      | Some aSrt ->
      let arg = mkVar(("constr_var_arg", aSrt)) in
      Apply (Fun (Embed (id, true), srt, noPos), arg, noPos)

endspec
