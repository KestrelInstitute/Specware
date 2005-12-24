Prover qualifying spec

  import /Languages/MetaSlang/Specs/StandardSpec

  type GoalStatus
  type GoalContext
  type AutomaticProperties
  type Goal
  type GoalContent
  type Sequent
  type SequentFmlas = List SequentFmla
  type SequentFmla = {fmla: MS.Term, index: NonZeroInteger, label: FmlaLabel, path: FmlaPath}
  type FmlaLabel = String
  type FmlaPath = List Integer % A fmla path indicates the history of the fmla.
    % e.g. If the fmla is the second conjuct of splitting the first proof goal,
    % the path would be 1.2
    % I'm not sure about all the details at this time, but am including it here
    % in the hope it will be useful.

  op goal.sequent: Goal -> Sequent
  op goalContent.sequent: GoalContent -> Sequent
  op goalContent: Goal -> GoalContent
  axiom goalSequent is fa (goal:Goal) sequent(goal) = sequent(goalContent(goal))

  op sequent.obviouslyTrue: Sequent -> Boolean
  op goalContent.obviouslyTrue: GoalContent -> Boolean
  op goal.obviouslyTrue: Goal -> Boolean
  axiom obviouslyTrueGoal is
    fa(g: Goal) obviouslyTrue g <=> obviouslyTrue(goalContent g)
  axiom obviouslyTrueGoalContent is
    fa(gc: GoalContent) obviouslyTrue gc <=> obviouslyTrue(sequent(gc))

  conjecture obviouslyTrueSequent is
    fa(g: Goal) obviouslyTrue g <=> obviouslyTrue(sequent(g))
  
  op nextGoal: Goal -> Option Goal
  op lastGoal?: Goal -> Boolean
  def lastGoal(g) = nextGoal g = None
  op previousGoal: Goal -> Option Goal
  axiom prevLastGoal is fa (g: Goal) lastGoal?(g) => previousGoal(g) = None

  op parent: Goal -> Option Goal
  op subGoals: Goal -> List Goal
  op leaves: Goal -> List Goal
  type proofTree = {g: Goal | parent g = None}

  type Leaf = {g: Goal | subGoals(g) = []}
  op dischargedLeaf: Goal -> Boolean

  op discharged: Goal -> Boolean
  op discharge: Goal -> Goal
  axiom dischargedGoal is
    fa (g: Goal) subGoals(g) = [] && dischargedLeaf(g) ||
                 (fa (sg: Goal) member(sg, subGoals(g)) => discharged(sg))

  type ProofCommand = GoalContent -> PCResult
  type PCResult
  type ProofEffect = | UnChanged | Discharged | Modified

  op subGoalsPC: PCResult -> List GoalContent
  op effectPC: PCResult -> ProofEffect

  op pcDischarges: ProofCommand * GoalContent -> Boolean
  op pcUnchanges: ProofCommand * GoalContent -> Boolean
  op pcModifies: ProofCommand * GoalContent -> Boolean

  axiom dischargeProofCommand is
    fa (pc: ProofCommand, g: GoalContent) pcDischarges(pc, g) <=> subGoalsPC(pc g) = []

  

endspec
