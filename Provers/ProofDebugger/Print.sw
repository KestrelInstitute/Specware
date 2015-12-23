(* Copyright 2015 Kestrel Institute. See file LICENSE.text for license details *)

ProofDebugger qualifying
spec

  import ExtPrinter

  op printProof: Proof -> String
  def printProof(prf) =
    printProofAux(prf, 0)

  op ind: Nat -> String
  def ind n =
    let
      def ind0(n) = if n=0 then "" else " "^(ind0(n-1))
    in
      %"["^Nat.toString(n)^"]"^
      ind0(n)

  op succind: Nat -> Nat
  def succind(n) = n+2

  op printProofsAux: Proofs * Nat -> String
  def printProofsAux(ps, n) =
    let sep = "\n"^(ind n) in
    if empty?(ps)
      then ""
    else printProofAux(head ps, n)^sep^printProofsAux(tail ps, n)

  op printProofAux: Proof * Nat -> String
  def printProofAux(prf, n) =
    let sn = succind n in
    let pSep = "\n"^(ind sn) in
    let sep = " " in
    case prf of
    | cxMT -> "(cxMT)"
    | cxTdec(p,tn, i) -> "(cxTdec"^sep^printTypeName(tn)^sep^printInt(i)^pSep^printProofAux(p, sn)^")"
    | cxOdec(p, p2, oper) -> "(cxOdec"^sep^printOperation(oper)^pSep^printProofAux(p, sn)^pSep^printProofAux(p2, sn)^")"
    | cxAx(p, p2, an) -> "(cxAx"^sep^printAxiomName(an)^pSep^printProofAux(p, sn)^pSep^printProofAux(p2, sn)^")"
    | cxLem(p, p2, ln) -> "(cxLem"^sep^printLemmaName(ln)^pSep^printProofAux(p, sn)^pSep^printProofAux(p2, sn)^")"
    | cxTVdec(p, tv) -> "(cxTVdec"^sep^printTypeVariable(tv)^pSep^printProofAux(p, sn)^")"
    | cxVdec(p, p2, v) -> "(cxVdec"^sep^printVariable(v)^pSep^printProofAux(p, sn)^pSep^printProofAux(p2, sn)^")"
    % well-formed specs ("spec" is disallowed):
    | speC(p) -> "(speC"^pSep^printProofAux(p, sn)^")"
    % well-formed types:
    | tyBool(p) -> "(tyBool"^pSep^printProofAux(p, sn)^")"
    | tyVar(p, tv) -> "(tyVar"^sep^printTypeVariable(tv)^pSep^printProofAux(p, sn)^")"
    | tyInst(p, ps, tn) -> "(tyInst"^sep^printTypeName(tn)^pSep^printProofAux(p, sn)^printProofsAux(ps, sn)^")"
    | tyArr(p, p2) -> "(tyArr"^pSep^printProofAux(p, sn)^pSep^printProofAux(p2, sn)^")"
    | tyRec(p, ps, flds) -> "(tyRec"^sep^printFields(flds)^pSep^printProofAux(p, sn)^pSep^printProofsAux(ps, sn)^")"
    | tyRestr(p) -> "(tyRestr"^pSep^printProofAux(p, sn)^")"
    % subtyping:
    | stRestr(p) -> "(stRestr"^pSep^printProofAux(p, sn)^")"
    | stRefl(p, v) -> "(stRefl"^sep^printVariable(v)^pSep^printProofAux(p, sn)^")"
    | stArr(p, p2, v, v2) -> "(stArr"^sep^printVariable(v)^sep^printVariable(v2)^pSep^printProofAux(p, sn)^")"
    | stRec(p, ps, v, prm) -> "(stRec"^sep^printVariable(v)^pSep^printProofsAux(p |> ps, sn)^pSep^printInts(prm)^")"
    % well-typed expressions:
    | exVar(p, v) -> "(exVar"^sep^printVariable(v)^pSep^printProofAux(p, sn)^")"
    | exOp(p, ps, oper) -> "(exOp"^sep^printOperation(oper)^pSep^printProofsAux(p |> ps, sn)^")"
    | exApp(p, p2) -> "(exApp"^pSep^printProofAux(p, sn)^pSep^printProofAux(p2, sn)^")"
    | exAbs(p,p2) -> "(exAbs"^pSep^printProofsAux(p |> single(p2), sn)^")"
    | exEq(p, p2) -> "(exEq"^pSep^printProofAux(p, sn)^pSep^printProofAux(p2, sn)^")"
    | exIf(p, p2, p3, p4) -> "(exIf"^pSep^printProofsAux(p |> p2 |> p3 |> single(p4), sn)^")"
    | exThe(p) -> "(exThe"^pSep^printProofAux(p, sn)^")"
    | exProj(p, fld) -> "(exProj"^sep^printField(fld)^pSep^printProofAux(p, sn)^")"
    | exSuper(p, p2) -> "(exSuper"^pSep^printProofAux(p, sn)^pSep^printProofAux(p2, sn)^")"
    | exSub(p, p2, p3) -> "(exSub"^pSep^printProofsAux(p |> p2 |> single(p3), sn)^")"
    | exAbsAlpha(p, v) -> "(exAbsAlpha"^sep^printVariable(v)^pSep^printProofAux(p, sn)^")"
    % theorems:
    | thAx(p, ps, an) -> "(thAx"^sep^printAxiomName(an)^pSep^printProofAux(p, sn)^")"
    | thRefl(p) -> "(thRefl"^pSep^printProofAux(p, sn)^")"
    | thSymm(p) -> "(thSymm"^pSep^printProofAux(p, sn)^")"
    | thTrans(p, p2) -> "(thTrans"^pSep^printProofAux(p, sn)^pSep^printProofAux(p2, sn)^")"
    | thAppSubst(p, p2, p3) -> "(thAppSubst"^pSep^printProofsAux(p |> p2 |> single(p3), sn)^")"
    | thEqSubst(p, p2, p3) -> "(thEqSubst"^pSep^printProofsAux(p |> p2 |> single(p3), sn)^")"
    | thIfSubst(p, p2, p3, p4) -> "(thIfSubst"^pSep^printProofsAux(p |> p2 |> p3 |> single(p4), sn)^")"
    | thSubst(p, p2) -> "(thSubst"^pSep^printProofAux(p, sn)^pSep^printProofAux(p2, sn)^")"
    | thBool(p, v, v2) -> "(thBool"^sep^printVariable(v)^sep^printVariable(v2)^pSep^printProofAux(p, sn)^")"
    | thExt(p, v, v2, v3) -> "(thExt"^sep^printVariable(v)^sep^printVariable(v2)^sep^printVariable(v3)^pSep^printProofAux(p, sn)^")"
    | thAbs(p) -> "(thAbs"^pSep^printProofAux(p, sn)^")"
    | thIf(p, p2, p3) -> "(thIf"^pSep^printProofsAux(p |> p2 |> single(p3), sn)^")"
    | thThe(p) -> "(thThe"^pSep^printProofAux(p, sn)^")"
    | thRec(p, v, v2) -> "(thRec"^sep^printVariable(v)^sep^printVariable(v2)^pSep^printProofAux(p, sn)^")"
    | thProjSub(p, v, fld) -> "(thProjSub"^sep^printVariable(v)^sep^printField(fld)^pSep^printProofAux(p, sn)^")"
    | thSub(p, p2) -> "(thSub"^pSep^printProofAux(p, sn)^pSep^printProofAux(p2, sn)^")"
    % assumptions:
    | assume(jdgmnt) -> "(assume"^sep^(printJudgement(jdgmnt))^")"

    | _ -> fail "printProof"

  op countProof: Proof -> Nat
  def countProof(prf) =
    let hash: FMap(Proof, Nat) = empty in

  let def countProofsAux(ps: Proofs) =
    if empty?(ps)
      then (hash, 0)
    else 
      let (hash, res1) = countProofAux(head ps) in
      let (hash , res2) = countProofsAux(tail ps) in
      (hash, res1 + res2)

   def countProofAux(prf: Proof):(FMap(Proof, Nat) * Nat) =
     let def countProofAuxInt(pi) = let (h, r) = countProofAux(pi) in r in
     let def countProofsAuxInt(pi) = let (h, r) = countProofsAux(pi) in r in
    let found = hash @@ prf in
    case found of
      | Some n -> (hash, n)
      | _ -> let res =
    case prf of
    | cxMT -> 1
    | cxTdec(p,tn, i) -> 1 + countProofAuxInt(p)
    | cxOdec(p, p2, oper) -> 1 + countProofAuxInt(p) + countProofAuxInt(p2)
    | cxAx(p, p2, an) -> 1 + countProofAuxInt(p) + countProofAuxInt(p2)
    | cxLem(p, p2, ln) -> 1 + countProofAuxInt(p) + countProofAuxInt(p2)
    | cxTVdec(p, tv) -> 1 + countProofAuxInt(p)
    | cxVdec(p, p2, v) -> 1 + countProofAuxInt(p) + countProofAuxInt(p2)
    % well-formed specs ("spec" is disallowed):
    | speC(p) -> countProofAuxInt(p)
    % well-formed types:
    | tyBool(p) -> countProofAuxInt(p)
    | tyVar(p, tv) -> countProofAuxInt(p)
    | tyInst(p, ps, tn) -> countProofAuxInt(p) + countProofsAuxInt(ps)
    | tyArr(p, p2) -> countProofAuxInt(p) + countProofAuxInt(p2)
    | tyRec(p, ps, flds) -> countProofAuxInt(p) + countProofsAuxInt(ps)
    | tyRestr(p) -> countProofAuxInt(p)
    % subtyping:
    | stRestr(p) -> countProofAuxInt(p)
    | stRefl(p, v) -> countProofAuxInt(p)
    | stArr(p, p2, v, v2) -> countProofAuxInt(p) + countProofAuxInt(p2)
    | stRec(p, ps, v, prm) -> countProofAuxInt(p) + countProofsAuxInt(ps)
    % well-typed expressions:
    | exVar(p, v) -> countProofAuxInt(p)
    | exOp(p, ps, oper) -> countProofAuxInt(p) + countProofsAuxInt(ps)
    | exApp(p, p2) -> countProofAuxInt(p) + countProofAuxInt(p2)
    | exAbs(p,p2) -> countProofAuxInt(p) + countProofAuxInt(p2)
    | exEq(p, p2) -> countProofAuxInt(p) + countProofAuxInt(p2)
    | exIf(p, p2, p3, p4) -> countProofAuxInt(p) + countProofAuxInt(p2) + countProofAuxInt(p3) + countProofAuxInt(p4)
    | exThe(p) -> countProofAuxInt(p)
    | exProj(p, fld) -> countProofAuxInt(p)
    | exSuper(p, p2) -> countProofAuxInt(p) + countProofAuxInt(p2)
    | exSub(p, p2, p3) -> countProofAuxInt(p) + countProofAuxInt(p2) + countProofAuxInt(p3)
    | exAbsAlpha(p, v) -> countProofAuxInt(p)
    % theorems:
    | thAx(p, ps, an) -> countProofAuxInt(p) + countProofsAuxInt(ps)
    | thRefl(p) -> countProofAuxInt(p)
    | thSymm(p) -> countProofAuxInt(p)
    | thTrans(p, p2) -> countProofAuxInt(p) + countProofAuxInt(p2)
    | thAppSubst(p, p2, p3) -> countProofAuxInt(p) + countProofAuxInt(p2) + countProofAuxInt(p3)
    | thEqSubst(p, p2, p3) -> countProofAuxInt(p) + countProofAuxInt(p2) + countProofAuxInt(p3)
    | thIfSubst(p, p2, p3, p4) -> countProofAuxInt(p) + countProofAuxInt(p2) + countProofAuxInt(p3) + countProofAuxInt(p4)
    | thSubst(p, p2) -> countProofAuxInt(p) + countProofAuxInt(p2)
    | thBool(p, v, v2) -> countProofAuxInt(p)
    | thExt(p, v, v2, v3) -> countProofAuxInt(p)
    | thAbs(p) -> countProofAuxInt(p)
    | thIf(p, p2, p3) -> countProofAuxInt(p) + countProofAuxInt(p2) + countProofAuxInt(p3)
    | thThe(p) -> countProofAuxInt(p)
    | thRec(p, v, v2) -> countProofAuxInt(p)
    | thProjSub(p, v, fld) -> countProofAuxInt(p)
    | thSub(p, p2) -> countProofAuxInt(p) + countProofAuxInt(p2)
    % assumptions:
    | assume(jdgmnt) -> 1

    | _ -> fail "countProof" in
    
    (update hash prf res, res) in
   
    let (_, r) = countProofAux(prf) in r



endspec

