(* This file contains stuff that has been written but then eliminated. It is
kept around (in this file) for a while in case it later turns out to be useful
again. *)


%%% functional version of positional type substitution:

  (* In LD, type substitutions at positions are formalized via a relation. Here,
  we use a function that corresponds to that relation, using an `Option' type
  to model the fact that the substitution is disallowed (e.g. because the
  position is not valid. *)

  op typeSubstInTypeAt : Type       * Type * Type * Position -> Option Type
  op typeSubstInExprAt : Expression * Type * Type * Position -> Option Expression
  op typeSubstInPattAt : Pattern    * Type * Type * Position -> Option Pattern

  def typeSubstInTypeAt(t,t1,t2,pos) =
    if pos = empty
    then if t = t1
         then Some t2
         else None
    else let i = first pos in
         case t of
           | instance(n,types) ->
             if i < length types
             then (case typeSubstInTypeAt (types elem i, t1, t2, rtail pos) of
                     | Some newTi -> Some (instance (n, update(types,i,newTi)))
                     | None       -> None)
             else None
           % TO BE CONTINUED.............


%%% more verbose def of types:

  type VariableType = Name

  type InstanceType = {typ  : Name,
                       args : FSeq Type}

  type ArrowType = {dom : Type,
                    cod : Type}

  type RecordTypeComponent = {field : Name,
                              typ   : Type}

  type RecordType = {comps : FSeq RecordTypeComponent |
                     (let fields = map (project field, comps) in
                      noRepetitions? fields)}

  type SumTypeComponent = {constr : Name, % constr(uctor)
                           typ    : Type}

  type ProductType = {comps : FSeq Type | length comps >= 2}

  type SumType = {comps : FSeqNE SumTypeComponent |
                  (let constrs = map (project constr, comps) in
                  noRepetitions? constrs)}

  type SubType = {base : Type,
                  pred : Expression}

  type QuotientType = {base : Type,
                       pred : Expression}

  type Type =
    | booleanType
    | var  VariableType
    | inst InstanceType
    | arr  ArrowType
    | rec  RecordType
    | prod ProductType
    | sum  SumType
    | sub  SubType
    | quot QuotientType


%%% more verbose def of expressions:


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
