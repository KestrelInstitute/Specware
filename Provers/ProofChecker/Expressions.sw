spec

  import Libs/FiniteSequences

  import Types

  (* Since expressions are defined in terms of patterns, we declare a type for
  patterns, which is defined in spec `Patterns'. When this spec and spec
  `Patterns' are imported together, union semantics ensures that the type
  declared here is the same defined there. *)

  type Pattern

  (* Unlike LD, we model all expression abbreviations (such as universal and
  existential quantification) explicitly. *)

  type VariableExpr = Name

  type OpInstance = {opp    : Name,
                     tyArgs : FSeq Type}

  type FunctionApplication = {func: Expression,
                              arg : Expression}

  type LambdaAbstraction = {arg     : Name,
                            argType : Type,
                            body    : Expression}

  type Equation = {left  : Expression,
                   right : Expression}

  type IfThenElse = {cond : Expression,
                     thn  : Expression,
                     els  : Expression}

  type RecordExprComponent = {field : Name,
                              expr  : Expression}

  type RecordExpr = {comps : FSeq RecordExprComponent |
                     (let fields = map (project field, comps) in
                      noRepetitions? fields)}

  type RecordProjection = {rec   : Expression,
                           field : Name}

  type RecordUpdate = {updatee : Expression,
                       updater : Expression}

  type Embedder = {typ    : SumType,
                   constr : Name}

  type Relaxator = Expression

  type RestrictExpr = {pred : Expression,
                       arg  : Expression}

  type Quotienter = Expression

  type ChooseExpr = {pred : Expression,
                     arg  : Expression}

  type CaseBranch = {pat    : Pattern,
                     result : Expression}

  type CaseExpr = {target   : Expression,
                   branches : FSeq CaseBranch}

  type LetRecBinding = {var  : Name,
                        typ  : Type,
                        expr : Expression}

  type LetRecExpr = {binds : {binds : FSeq LetRecBinding |
                              (let vars = map (project var, binds) in
                               noRepetitions? vars)},
                     body  : Expression}

  type NotExpr = Expression

  type AndExpr = {left  : Expression,
                  right : Expression}

  type OrExpr = {left  : Expression,
                 right : Expression}

  type ImpliesExpr = {antec  : Expression,
                      conseq : Expression}

  type IffExpr = {left  : Expression,
                  right : Expression}

  type Inequation = {left  : Expression,
                     right : Expression}

  type ForAllExpr = {var     : Name,
                     varType : Type,
                     body    : Expression}

  type ExistsExpr = {var     : Name,
                     varType : Type,
                     body    : Expression}

  type Exists1Expr = {var     : Name,
                      varType : Type,
                      body    : Expression}

  type LetExpr = {pat   : Pattern,
                  expr  : Expression,
                  body  : Expression}

  type TupleExpr = {comps : FSeq Expression | length comps >= 2}

  type TupleProjection = {tup   : Expression,
                          field : PosNat}   % like record projection
                                            % but number instead of name

  type Expression =
    | var   VariableExpr
    | opi   OpInstance
    | app   FunctionApplication
    | abs   LambdaAbstraction
    | eq    Equation
    | ifte  IfThenElse
    | rec   RecordExpr
    | rproj RecordProjection
    | rupd  RecordUpdate
    | emb   Embedder
    | relx  Relaxator
    | restr RestrictExpr
    | quot  Quotienter
    | choos ChooseExpr
    | cas   CaseExpr
    | letr  LetRecExpr
    | trueExpr
    | falseExpr
    | neg   NotExpr
    | conj  AndExpr
    | disj  OrExpr
    | impl  ImpliesExpr
    | iff   IffExpr
    | neq   Inequation
    | fall  ForAllExpr
    | exis  ExistsExpr
    | exis1 Exists1Expr
    | tup   TupleExpr
    | tproj TupleProjection

  (* We leave out the last four abbreviations for multiple quantifiers in
  LD (e.g. fa(v1:T1,...,vn:Tn) e). *)

endspec
