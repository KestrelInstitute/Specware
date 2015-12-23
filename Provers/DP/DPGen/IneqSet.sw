(* Copyright 2015 Kestrel Institute. See file LICENSE.text for license details *)

IneqSet qualifying spec

  import Inequality

  type IneqSet = List Ineq

  op IneqSet.hdVar: IneqSet -> Var
  def IneqSet.hdVar(ineqSet) =
    hdVar(hd(ineqSet))
  
  op IneqSet.hdVarOpt: IneqSet -> Option Var
  def IneqSet.hdVarOpt(ineqSet) =
    hdVarOpt(hd(ineqSet))
  
  op normalize: IneqSet -> M IneqSet
  def normalize(ineqSet) =
    if member(contradictIneqGt, ineqSet) ||
      member(contradictIneqGtEq, ineqSet) ||
      member(contradictIneqGtZero, ineqSet)
      then return ([falseIneq])
    else
      {
       ineqSet <- mapSeq normalize ineqSet;
       return (sortIneqSet ineqSet)
      }

  
  op sortIneqSet: IneqSet -> IneqSet
  def sortIneqSet(ineqSet) =
    let res = uniqueSort compare ineqSet in
    %let _ = writeLine("sortIneqSet:") in
    %let _ = writeIneqSet(res) in
    res

  op neqs: IneqSet -> IneqSet
  def neqs(ineqSet) =
    filter (fn (ineq) -> isNeq?(ineq)) ineqSet

  op eqs: IneqSet -> IneqSet
  def eqs(ineqSet) =
    filter (fn (ineq) -> isEq?(ineq)) ineqSet

  op gtEqs: IneqSet -> IneqSet
  def gtEqs(ineqSet) =
    filter (fn (ineq) -> isGtEq?(ineq)) ineqSet

  op writeIneqSet: IneqSet -> ()
  def writeIneqSet(ineqs) =
    let _ = map (fn (ineq) -> writeLine(Ineq.print(ineq))) ineqs in
    ()
    


endspec
