spec

import UnitId
import UnitId/Utilities                                % for uidToString, if used...
import Spec/CoerceToSpec
import /Languages/MetaSlang/Specs/Categories/AsRecord
import /Languages/Snark/SpecToSnark
import /Library/Legacy/DataStructures/ListPair

op SNARK.ANSWER: Boolean -> LispCell

op answerVarsFromSnark: () -> List Id

def answerVarsFromSnark () =
  let snarkAnswer = SNARK.ANSWER(true) in
  let lispAnswerVars = (cdr snarkAnswer) in
  let answerVars = uncell(lispAnswerVars) in
  let answerStrings =  List.map (fn (lv) -> LispString(lv)) answerVars in
  %%let _ = debug("getting answers") in
    answerStrings

def SpecCalc.evaluateExtendMorph term = {
  unitId <- getCurrentUnitId;
  print (";;; Extending Morphisms for " ^ (uidToString unitId) ^ "\n");
  (value, time_stamp, depUnitIds) <- SpecCalc.evaluateTermInfo term;
  (optBaseUnitId,baseSpec) <- getBase;
  case value of
      | Morph sm -> {
          newMorph <- return (extendMorphism (sm,baseSpec));
          return (Morph newMorph, time_stamp, depUnitIds)}
      | _ -> raise (Unsupported (positionOf term, "Can only extend morphisms"))
   }

op extendMorphism: Morphism * Spec -> Morphism

def extendMorphism(morph, base_spc) =
  let baseHypothesis = base_spc.properties in
  let dom = morph.dom in
  let cod = morph.cod in
  let opMap = morph.opMap in
  let properties = dom.properties in
  let axioms = filter (fn (propType,_,_,_) -> propType = Axiom) properties in
  let axiomFmlas = map (fn (_,_,_,fmla) -> fmla) axioms in
  let newAxiomFmlas = map (fn (fmla) -> substOpMap(opMap, fmla)) axiomFmlas in
  let incompleteAxioms = filter (fn (fmla) -> termOpsInSpec?(fmla, dom)) newAxiomFmlas in
  let _ = if specwareDebug? then map (fn (f:MS.Term) -> printTermToTerminal(f)) incompleteAxioms else [()] in
  let testAxiom = hd incompleteAxioms in
  let _ = if specwareDebug? then printTermToTerminal(testAxiom) else () in
  let (existentialTest, ansVars) = mkExistential(dom, testAxiom) in
  let succ = proveForAns(ansVars, existentialTest, subtractSpec cod base_spc, baseHypothesis, base_spc, [Lisp.list []], "foo.log") in
    if succ 
      then extendMorphismWithAnswer(morph, ansVars)
    else morph

op extendMorphismWithAnswer: Morphism * Vars -> Morphism

def extendMorphismWithAnswer(morph, domVars) =
  let dom = morph.dom in
  let cod = morph.cod in
  let opMap = morph.opMap in
  let srtMap = morph.sortMap in
  let codIds = answerVarsFromSnark() in
  let domIds = map (fn (id,_) -> id) domVars in
  let newOpMap = foldl (fn (domId, codId, map) -> (update map (mkUnQualifiedId(domId)) (mkUnQualifiedId(codId)))) opMap (domIds, codIds) in
  let _ = if specwareDebug? then map (fn (id) -> System.print("domOp: " ^ id ^ "\n")) domIds else [""] in
  let _ = if specwareDebug? then map (fn (id) -> System.print("codOp: " ^ id ^ "\n")) codIds else [""] in
  %%let _ = if specwareDebug? then printTermToTerminal(domIds) else () in
  %%let _ = if specwareDebug? then printMapToTerminal(newOpMap) else () in
    makeMorphism(dom, cod, srtMap, newOpMap, morph.sm_tm)

op mkExistential: Spec * MS.Term -> Property * Vars

def mkExistential (spc, term) =
  let opsToQuantify = termOpsInSpec(term, spc) in
  let newVars = map (fn (Fun (Op (Qualified (q, id), _), srt, a)) -> (id, srt))
                    opsToQuantify in
  let opToVarMap = ListPair.foldl (fn (Fun (Op (qid, _), _, _), var, map)
			       -> (update map qid var))
                         emptyMap (opsToQuantify, newVars) in
  let
    def substVarForOp (term) =
      case term of
	| Fun        (Op (qid,f),           srt,  a) ->
	  (let newVar = evalPartial opToVarMap qid in
	     case newVar of
	       | Some newVar -> mkVar newVar
	       | None -> term)
	| _ -> term in
        
  let newTerm = mapTerm (fn(trm) -> substVarForOp(trm), fn(s) -> s, fn(p) -> p) term in
  let existTerm = Bind (Exists, newVars, newTerm, noPos) in
  let _ = if specwareDebug? then printTermToTerminal(existTerm) else () in
    ((Conjecture, mkUnQualifiedId("morphismExistential"), [], existTerm), newVars)

op termOpsInSpec?: MS.Term * Spec -> Boolean

def termOpsInSpec?(term, spc) =
  let 
   def mapT(spc, term) =
     case term of
       | Fun        (Op (qid, fixity),          srt,  a) ->
	  (case AnnSpec.findTheOp(spc, qid) of
	    | Some _ -> true
	    | _ -> false)

       | Fun        (top,                  srt,  a) -> false

       | Var        ((id,                  srt), a) -> false

       | Let        (decls, bdy, a) -> 
	 let res = mapRec bdy in res

       | LetRec     (decls, bdy, a) -> 
	 let res = mapRec bdy in res

       | Record     (row, a) -> 
	 let res = foldl (fn ((_, trm), res) -> res or (mapRec trm)) false row in
	   res

       | IfThenElse (       t1,        t2,        t3, a) -> 
	 let resT1 = mapRec t1 in
	 let resT2 = mapRec t2 in
	 let resT3 = mapRec t3 in
	   resT1 or resT2 or resT3

       | Lambda     (match, a) -> 
         let resMatch = foldl (fn ((pat, cond, trm), res) -> res or (mapRec trm)) false match in
	   resMatch

       | Bind       (bnd, vars, trm, a) -> 
	 let resTrm = mapRec trm in
	   resTrm

       | Apply      (       t1,        t2,  a) ->
	 let resT1 = mapRec t1 in
	 let resT2 = mapRec t2 in
	   resT1 or resT2

       | Seq        (                terms, a) -> 
	 let resTerms = foldl (fn (trm, res) -> res or (mapRec trm)) false terms in
	   resTerms

       | ApplyN     (                terms, a) -> 
	 let resTerms = foldl (fn (trm, res) -> res or (mapRec trm)) false terms in
	   resTerms

       | SortedTerm (       trm,                  srt, a) -> 
	 let resTrm = mapRec trm in
	   resTrm

   def mapRec term = 
     %% apply map to leaves, then apply map to result
     mapT (spc, term)
  in
    mapRec term

op termOpsInSpec: MS.Term * Spec -> List MS.Term

def termOpsInSpec(term, spc) =
  let 
   def mapT(spc, term) =
     case term of
       | Fun        (Op (qid, fixity),          srt,  a) ->
	  (case AnnSpec.findTheOp(spc, qid) of
	    | Some _ -> [term]
	    | _ -> [])

       | Fun        (top,                  srt,  a) -> []

       | Var        ((id,                  srt), a) -> []

       | Let        (decls, bdy, a) -> 
	 let res = mapRec bdy in res

       | LetRec     (decls, bdy, a) -> 
	 let res = mapRec bdy in res

       | Record     (row, a) -> 
	 let res = foldl (fn ((_, trm), res) -> res ++ (mapRec trm)) [] row in
	   res

       | IfThenElse (       t1,        t2,        t3, a) -> 
	 let resT1 = mapRec t1 in
	 let resT2 = mapRec t2 in
	 let resT3 = mapRec t3 in
	   resT1 ++ resT2 ++ resT3

       | Lambda     (match, a) -> 
         let resMatch = foldl (fn ((pat, cond, trm), res) -> res ++ (mapRec trm)) [] match in
	   resMatch

       | Bind       (bnd, vars, trm, a) -> 
	 let resTrm = mapRec trm in
	   resTrm

       | Apply      (       t1,        t2,  a) ->
	 let resT1 = mapRec t1 in
	 let resT2 = mapRec t2 in
	   resT1 ++ resT2

       | Seq        (                terms, a) -> 
	 let resTerms = foldl (fn (trm, res) -> res ++ (mapRec trm)) [] terms in
	   resTerms

       | ApplyN     (                terms, a) -> 
	 let resTerms = foldl (fn (trm, res) -> res ++ (mapRec trm)) [] terms in
	   resTerms

       | SortedTerm (       trm,                  srt, a) -> 
	 let resTrm = mapRec trm in
	   resTrm

   def mapRec term = 
     %% apply map to leaves, then apply map to result
     mapT (spc, term)
  in
    mapRec term

op substOpMap: MorphismOpMap * MS.Term -> MS.Term

def substOpMap (opMap, term) =
  %%
  %% traversal of term with post-order applications of opMap
  %%
  %% i.e. recursively apply opMap to result of mapping over term
  %%
  %% i.e. term will be revised using opMap on its components,
  %% then opMap will be applied to the revised term.
  %%
  let 
   def mapT (opMap, term) = 
    case term of
      | Fun        (Op (qid,f),           srt,  a) ->
	  (let newQid = evalPartial opMap qid in
	     case newQid of
	       | Some qid -> Fun(Op (qid, f), srt,  a)
	       | None -> term)

       | Fun        (top,                  srt,  a) -> term

       | Var        ((id,                  srt), a) ->
	 term

       | Let        (decls, bdy, a) -> 
	 let newDecls = decls in
	 let newBdy = mapRec bdy in
	 if decls = newDecls & bdy = newBdy then term
	   else Let (newDecls, newBdy, a)

       | LetRec     (decls, bdy, a) -> 
	 let newDecls = decls in
	 let newBdy = mapRec bdy in
	 if decls = newDecls & bdy = newBdy then term
	   else LetRec(newDecls, newBdy, a)

       | Record     (row, a) -> 
	 let newRow = map (fn (id,trm) -> (id, mapRec trm)) row in
	 if row = newRow then term
	   else Record(newRow,a)

       | IfThenElse (       t1,        t2,        t3, a) -> 
	 let newT1 = mapRec t1 in
	 let newT2 = mapRec t2 in
	 let newT3 = mapRec t3 in
	 if newT1 = t1 & newT2 = t2 & newT3 = t3 then term
	   else IfThenElse (newT1, newT2, newT3, a)

       | Lambda     (match, a) -> 
         let newMatch = map (fn (pat, cond, trm) ->
			       (pat, mapRec cond, mapRec trm))
	                    match in
	 if match = newMatch then term
	   else Lambda (newMatch, a)

       | Bind       (bnd, vars, trm, a) -> 
	 let newVars = vars in
	 let newTrm = mapRec trm in
	 if vars = newVars & trm = newTrm then term
	   else Bind (bnd, newVars, newTrm, a)

       | Apply      (       t1,        t2,  a) ->
	 let newT1 = mapRec t1 in
	 let newT2 = mapRec t2 in
	 if newT1 = t1 & newT2 = t2 then term
	  else Apply(mapRec newT1, mapRec newT2,  a)

       | Seq        (                terms, a) -> 
	 let newTerms = map mapRec terms in
	 if newTerms = terms then term
	   else Seq(newTerms, a)

       | ApplyN     (                terms, a) -> 
	 let newTerms = map mapRec terms in
	 if newTerms = terms then term
	   else ApplyN (newTerms, a)

       | SortedTerm (       trm,                  srt, a) -> 
	 let newTrm = mapRec trm in
         let newSrt = srt in
	 if newTrm = trm & srt = newSrt then term
	   else SortedTerm (newTrm, newSrt, a)

   def mapRec term = 
     %% apply map to leaves, then apply map to result
     mapT (opMap, term)
  in
    mapRec term


(*
 (Spec baseProverSpec,_,_) <- SpecCalc.evaluateUID (Internal "ProverBase")
                                                       (SpecPath_Relative {path = ["Library","Base","ProverBase"],
									   hashSuffix = None});
*)
 
 op proveForAns: Vars * Property * Spec * List Property * Spec * List LispCell * String -> Boolean

 def proveForAns(ansVars, claim, spc, base_hypothesis, base_spc, prover_options, snarkLogFileName) =
   let (_ (* claim_type *),claim_name,_,_) = claim in
   %% let def claimType(ct) = 
   %%       case ct of
   %%	     | Conjecture -> "Conjecture" 
   %%	     | Theorem -> "Theorem" 
   %%	     | Axiom -> "Axiom" in
   %% let claim_type = claimType(claim_type) in
   let snarkSortDecls = snarkSorts(spc) in
   let snarkOpDecls = snarkOpDecls(spc) in
   let context = newContext in
   let snarkBaseHypothesis = map (fn (prop) -> snarkProperty(context, base_spc, prop))
                                 base_hypothesis in
   let hypothesis = spc.properties in
   let snarkHypothesis = map (fn (prop) -> snarkProperty(context, spc, prop)) hypothesis in
   let snarkConjecture = snarkAnswer(context, spc, claim, ansVars) in
   let snarkEvalForm = makeSnarkAnsEvalForm(prover_options, snarkSortDecls, snarkOpDecls, snarkBaseHypothesis, snarkHypothesis, snarkConjecture, snarkLogFileName) in
     let _ = if specwareDebug? then writeLine("Calling Snark by evaluating: ") else () in
     let _ = if specwareDebug? then LISP.PPRINT(snarkEvalForm) else Lisp.list [] in
     let result = Lisp.apply(Lisp.symbol("CL","FUNCALL"),
			[Lisp.list [Lisp.symbol("SNARK","LAMBDA"),Lisp.nil(),snarkEvalForm]]) in
     let proved = ":PROOF-FOUND" = anyToString(result) in
     %%let _ = displayProofResult(proof_name, claim_type, claim_name, spec_name, proved, snarkLogFileName) in
       proved

 op makeSnarkAnsEvalForm: List Lisp.LispCell * List Lisp.LispCell * List Lisp.LispCell * List Lisp.LispCell * List Lisp.LispCell * Lisp.LispCell * String -> Lisp.LispCell

 def makeSnarkAnsEvalForm(prover_options, snarkSortDecl, snarkOpDecls, snarkBaseHypothesis, snarkHypothesis, snarkConjecture, snarkLogFileName) =
   %%let _ = if specwareDebug? then toScreen("Proving snark fmla: ") else () in
   %%let _ = if specwareDebug? then LISP.PPRINT(snarkConjecture) else Lisp.list [] in
   %%let _ = if specwareDebug? then writeLine(" using: ") else () in
   %%let _ = if specwareDebug? then LISP.PPRINT(Lisp.list(snarkHypothesis)) else Lisp.list [] in

   	 Lisp.list 
	 [Lisp.symbol("CL-USER","WITH-OPEN-FILE"),
	  Lisp.list [Lisp.symbol("CL-USER","LOGFILE"),
		     Lisp.string(snarkLogFileName),
		     Lisp.symbol("KEYWORD","DIRECTION"),
		     Lisp.symbol("KEYWORD","OUTPUT"),
		     Lisp.symbol("KEYWORD","IF-EXISTS"),
		     Lisp.symbol("KEYWORD","SUPERSEDE")],
	  Lisp.list
	  [
	   Lisp.symbol("CL","LET"),
	   Lisp.list [
		      %%Lisp.list [Lisp.symbol("CL-USER","*ERROR-OUTPUT*"),
			%%	 Lisp.symbol("CL-USER","LOGFILE")],
		      %%Lisp.list [Lisp.symbol("CL-USER","*STANDARD-OUTPUT*"),
			%%	 Lisp.symbol("CL-USER","LOGFILE")] %)
		     ],
	   Lisp.list([Lisp.symbol("SNARK","INITIALIZE")]),
	   Lisp.list([Lisp.symbol("SNARK","RUN-TIME-LIMIT"), Lisp.nat(60)]),
           Lisp.list([Lisp.symbol("SNARK","USE-LISP-TYPES-AS-SORTS"), Lisp.bool(true)]),
           Lisp.list([Lisp.symbol("SNARK","USE-CODE-FOR-NUMBERS"), Lisp.bool(true)]),
	   Lisp.list([Lisp.symbol("SNARK","USE-RESOLUTION"), Lisp.bool(true)])
	  ]
	  Lisp.++ (Lisp.list prover_options)
	  Lisp.++ (Lisp.list snarkSortDecl)
	  Lisp.++ (Lisp.list snarkOpDecls)
	  Lisp.++ (Lisp.list snarkBaseHypothesis)
	  Lisp.++ (Lisp.list baseAxioms)
	  Lisp.++ (Lisp.list snarkHypothesis)
	  Lisp.++ (Lisp.list [snarkConjecture])]

endspec
