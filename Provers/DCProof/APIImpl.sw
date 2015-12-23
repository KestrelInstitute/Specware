(* Copyright 2015 Kestrel Institute. See file LICENSE.text for license details *)

Prover qualifying spec

  import API

  type GoalStatus = | Discharged | False | Attempted | Pending
  type GoalContext = {spc: Spec, prop: Property, autoProps: AutomaticProperties}
  type AutomaticProperties = {autoRewrites: Properties, autoDefs: Properties, groundFacts: List MSTerm}
  type Goal = {sequent: Sequent, parent: Option Goal, subGoals: List Goal, status: GoalStatus, contex: GoalContext}
  type Sequent = {hypothesis: SequentFmlas, conclusions: SequentFmlas}
  type SequentFmlas = List SequentFmla
  type SequentFmla = {fmla: MS.Term, index: Int0, label: FmlaLabel, path: FmlaPath}
  type FmlaLabel = String
  type FmlaPath = List Int % A fmla path indicates the history of the fmla.
    % e.g. If the fmla is the second conjuct of splitting the first proof goal,
    % the path would be 1.2
    % I'm not sure about all the details at this time, but am including it here
    % in the hope it will be useful.

endspec
