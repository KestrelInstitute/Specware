IneqSet qualifying spec

  import Inequality

  type IneqSet = List Ineq

  op IneqSet.hdVar: IneqSet -> Var
  def IneqSet.hdVar(ineqSet) =
    hdVar(hd(ineqSet))
  
  op IneqSet.hdVarOpt: IneqSet -> Option Var
  def IneqSet.hdVarOpt(ineqSet) =
    hdVarOpt(hd(ineqSet))
  
  op normalize: IneqSet -> IneqSet
  def normalize(ineqSet) =
    if member(contradictIneqGt, ineqSet) or
      member(contradictIneqGtEq, ineqSet) or
      member(contradictIneqGtZero, ineqSet)
      then [falseIneq]
    else
      let ineqSet = map normalize ineqSet in
      sortIneqSet ineqSet

  
  op sortIneqSet: IneqSet -> IneqSet
  def sortIneqSet ineqSet =
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
    let _ = map (fn (ineq) -> writeLine(print(ineq))) ineqs in
    ()
    


endspec
