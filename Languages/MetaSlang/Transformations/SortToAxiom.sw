Prover qualifying spec
 import ../Specs/Environment
 import ../Specs/Utilities
 import DefToAxiom

 op  axiomFromSortDefTop: Spec * QualifiedId * SortInfo -> SpecElements
 def axiomFromSortDefTop (spc, sort_name, info) =
   if definedSortInfo? info then
     let srt_def = firstSortDefInnerSort info in
%     let localSorts = spc.importInfo.localSorts in
%     if memberQualifiedId (q, id, localSorts) then
       let axioms = 
	   case srt_def of
	     | CoProduct _ -> axiomFromCoProductDefTop (spc, sort_name, srt_def)
	     | Subsort   _ -> axiomFromSubSortDefTop   (spc, sort_name, srt_def)
	     | Product   _ -> axiomFromProductDefTop   (spc, sort_name, srt_def)
	     | _ -> [] 
       in
	 axioms
      %else 
       %let _ = writeLine(name^": in axiomFromSortDef Def part is not local") in
       %let _ = debug("not local sort") in
      % []
   else
     %let _ = writeLine(name^": in axiomFromSortDef NOT def part") in
     []

 op  axiomFromSubSortDefTop: Spec * QualifiedId * Sort -> SpecElements
 def axiomFromSubSortDefTop (spc, name, srt as Subsort (supSort, subSortTerm, b)) =
    []

 op  axiomFromProductDefTop: Spec * QualifiedId * Sort -> SpecElements
 def axiomFromProductDefTop (spc, name, srt as Product (fields, b)) =
    let projectAxioms = mkProjectAxioms(spc, name, srt, fields) in
    let equalityAxiom = mkProdEqualityAxiom(spc, name, srt, fields) in
    %    let constructAxiom = mkConstructAxiom(spc, name, fields) in
    %    Cons(constructAxiom, projectAxioms)
    Cons(Property equalityAxiom, projectAxioms)

 op  mkProdEqualityAxiom: Spec * QualifiedId * Sort * Fields -> Property
 def mkProdEqualityAxiom(spc, name as Qualified (prodQ, prodSrtId), srt, fields) =
   let rec1 as Record(fields1, _) = mkRecordTerm(spc, name, srt, "x") in
   let rec2 as Record(fields2, _) = mkRecordTerm(spc, name, srt, "y") in
   %let _ = writeLine("Record1 is: "^printTerm(rec1)) in
   %let _ = writeLine("Record2 is: "^printTerm(rec2)) in
   let recEq = mkEquality(srt, rec1, rec2) in
   %let _ = writeLine("recEq is: "^printTerm(recEq)) in
   let fieldEqs = ListPair.map 
       (fn ((_, f1 as Var ((_, fsrt), _)), (_, f2)) -> mkEquality(fsrt, f1, f2))
       (fields1, fields2) in
   let fieldEqsConj = mkSimpConj(fieldEqs) in
   %let _ = writeLine("conj is: "^printTerm(fieldEqsConj)) in
   let term = mkSimpImplies(recEq, fieldEqsConj) in
   %let _ = writeLine("impl is: "^printTerm(term)) in
   let bndVars = freeVars(term) in
   let fmla = mkBind(Forall, bndVars, term) in
   %let _ = writeLine("fmla is: "^printTerm(fmla)) in
   (Axiom, mkQualifiedId(prodQ, prodSrtId^"_def"), [], fmla)

 op  mkProjectAxioms: Spec * QualifiedId * Sort * Fields -> SpecElements
 def mkProjectAxioms(spc, name, srt, fields) =
   let recordArg as Record(resFields, _) =  mkRecordTerm(spc, name, srt, "") in
   ListPair.map (fn (field, res) -> mkProjectAxiom(spc, name, srt, field, recordArg, res)) (fields, resFields)

 op  mkProjectAxiom: Spec * QualifiedId * Sort * Field * MS.Term * (Id * MS.Term) -> SpecElement
 def mkProjectAxiom(spc, name as Qualified(prodQ, prodSrtId), srt, field as (fId, fSrt), arg, (_, res)) =
   let projQid as Qualified(projQ,projId) = getAccessorOpName(prodSrtId,name,fId) in
   let lhs = mkProjectTerm(spc, name, srt, field, arg) in
   let rhs = res in
   let eql = mkEquality(fSrt, lhs, rhs) in
   let bndVars = freeVars(eql) in
   let fmla = mkBind(Forall, bndVars, eql) in
   Property(Axiom, mkQualifiedId(prodQ, prodSrtId^"_def"), [], fmla)

 op  mkRecordTerm: Spec * QualifiedId * Sort * String -> MS.Term
 def  mkRecordTerm(spc, srtName, srt as Product (fields, b), prefix) =
   (*  let opqid as Qualified(opq,opid) = getRecordConstructorOpName(srtName) in
       let dom  = Base(srtName,[],b) in
       let opsrt = Arrow(srt,dom,b) in
       let termsrt = Arrow(srt,dom,b) in
       let funterm = Fun(Op(opqid, Nonfix),termsrt,b) in *)
  let
    def mkVarTerm (id, srt) =
      Var ((id, srt), b)
  in
      let term = 
        case srt of
	  | Product (fields, _) ->
	    if productfieldsAreNumbered fields && prefix = "" then
	      Record (List.map (fn (id, srt) -> (id, mkVarTerm ("x"^id, srt))) fields, b)
	    else 
	      Record (List.map (fn (id, srt) -> (id, mkVarTerm (prefix^id, srt))) fields, b)
	  | _ -> mkVarTerm ("x", srt)
      in term

 op  mkProjectTerm: Spec * QualifiedId * Sort * Field * MS.Term -> MS.Term
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

 op  mkConstructAxiom: Spec * QualifiedId * Sort * Fields -> Property
 def mkConstructAxiom(spc, name as Qualified(srtQ, srtId), srt, fields) =
   let b = noPos in
   let varId = srtId^"_Rec_Var" in
   let varTerm = mkVar(varId, srt) in
   let projArgs = map (fn (field) -> mkProjectTerm(spc,  name, srt, field, varTerm)) fields in
   let argsSrt = mapWithIndex (fn (i, (_,fSrt)) -> (toString(i), fSrt)) fields in
   let opqid as Qualified(opq,opid) = getRecordConstructorOpName(name) in
   let dom = Product(argsSrt, b) in
   let opsrt = Arrow(dom,srt,b) in
   let opFun = mkOp(opqid, opsrt) in
   let lhs = mkAppl(opFun, projArgs) in
   let rhs = varTerm in
   let eql = mkEquality(srt, lhs, rhs) in
   let fmla = mkBind(Forall, [(varId, srt)], eql) in
   (Axiom, mkQualifiedId(srtQ, srtId^"_def"), [], fmla)
    
  
 op  axiomFromCoProductDefTop: Spec * QualifiedId * Sort -> SpecElements
 def axiomFromCoProductDefTop(spc, name, srt as CoProduct (fields, b)) =
   let disEqAxioms = mkDisEqsForFields(spc, srt, name, fields) in
   let exhaustAxioms = exhaustAxioms(spc, srt, name, fields) in
   exhaustAxioms++disEqAxioms

 op  exhaustAxioms: Spec * Sort * QualifiedId * List (Id * Option Sort) -> SpecElements
 def exhaustAxioms(spc, srt, name as Qualified(qname, id), fields) =
   let newVar = (id^"_Var", mkBase(name, [])) in
   let eqDisjuncts = mkEqFmlasForFields(srt, newVar, fields) in
   let eqTm = mkSimpOrs(eqDisjuncts) in
   let eqFmla = mkBind(Forall, [newVar], eqTm) in
   let predDisjuncts = mkPredFmlasForFields(srt, newVar, fields) in
   let predTm = mkSimpOrs(predDisjuncts) in
   let predFmla = mkBind(Forall, [newVar], predTm) in
   [Property(Axiom, mkQualifiedId(qname, id^"_def"), [], eqFmla),
    Property(Axiom, mkQualifiedId(qname, id^"_def"), [], predFmla)]

 op  mkEqFmlasForFields: Sort * Var * List (Id * Option Sort) -> List MS.Term
 def mkEqFmlasForFields(srt, var, fields) =
   case fields of
     | [] -> []
     | (id, optSrt):: restFields ->
       let constrTerm = mkConstructorTerm(srt, id, optSrt) in
       let eql = mkEquality(srt, mkVar(var), constrTerm) in
       let existVars = freeVars(constrTerm) in
       let eqlFmla = mkBind(Exists, existVars, eql) in
       let restEqls = mkEqFmlasForFields(srt, var, restFields) in
       Cons(eqlFmla, restEqls)

 op  mkPredFmlasForFields: Sort * Var * List (Id * Option Sort) -> List MS.Term
 def mkPredFmlasForFields(srt, var, fields) =
   case fields of
     | [] -> []
     | (id, _):: restFields ->
       let predFmla = mkEmbedPred(srt, id, var) in
       let restPreds = mkPredFmlasForFields(srt, var, restFields) in
       Cons(predFmla, restPreds)

 op  mkDisEqsForFields: Spec * Sort * QualifiedId * List (Id * Option Sort) -> SpecElements
 def mkDisEqsForFields(spc, srt, name, fields) =
   case fields of
     | [] -> []
     | (id, optSrt)::restFields ->
       let diseqs = mkDisEqsForIdAndRest(id, srt, name, optSrt, restFields) in
       let restDisEqs = mkDisEqsForFields(spc, srt, name, restFields) in
	diseqs++restDisEqs

 op  mkDisEqsForIdAndRest: Id * Sort * QualifiedId * Option Sort * List (Id * Option Sort) -> SpecElements
 def mkDisEqsForIdAndRest(id, srt, name, optSrt, restFields) =
   foldr (fn ((id2, optSrt2), props) ->
	  let disEq = mkDisEqForTwoConstructors(id, srt, name, optSrt, id2, optSrt2) in
	  Cons(Property disEq, props))
         [] 
	 restFields

 op  mkDisEqForTwoConstructors: Id * Sort * QualifiedId * Option Sort * Id * Option Sort -> Property
 def mkDisEqForTwoConstructors(id1, srt, name, optSrt1, id2, optSrt2) =
   let tm1 = mkConstructorTerm(srt, id1, optSrt1) in
   let tm2 = mkConstructorTerm(srt, id2, optSrt2) in
   let eql = mkEquality(srt, tm1, tm2) in
   let disEql = mkNot(eql) in
   let vars = freeVars(eql) in
   let fmla = withAnnT(mkBind(Forall, vars, disEql), sortAnn(srt)) in
   let Qualified (qual, id) = name in
   % (Axiom, mkQualifiedId(qual, id^"_"^id1^"_notEq_"^id2), [], fmla)
   (Axiom, mkQualifiedId(qual, id^"_def"), [], fmla)

 op  mkConstructorTerm: Sort * Id * Option Sort -> MS.Term
 def mkConstructorTerm(srt, id, optSrt) =
   case optSrt of
     | None -> Fun (Embed (id, false), srt, noPos)
     | Some (Product (args, _)) ->
       let recordFields = map (fn (aid, asrt) -> (aid, mkVar(("var_"^aid, asrt)))) args in
       let args = mkRecord(recordFields) in
       Apply (Fun (Embed (id, true), srt, noPos), args, noPos)
     | Some aSrt ->
       let arg = mkVar(("constr_var_arg", aSrt)) in
       Apply (Fun (Embed (id, true), srt, noPos), arg, noPos)

 op  mkEmbedPred: Sort * Id * Var -> MS.Term
 def mkEmbedPred(srt, id, var) =
   mkApply((mkEmbedded(id, srt)), mkVar(var))

endspec
