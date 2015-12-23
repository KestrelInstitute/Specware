(* Copyright 2015 Kestrel Institute. See file LICENSE for license details *)

Base qualifying
spec

  % API private default

  import ProofChecker#Spec

  (* This spec consists of ops that convert judgements, failures, and all
  their syntactic components, to strings. These conversions enable printing
  such syntactic entities in a human-readable form.

  Since primitives can be any strings, it is easy to imagine situations in
  which a printed-out string is ambiguous or unclear. However, if only
  "reasonable" strings are used as primitives, the printing defined in this
  spec should produce unambiguous and clear strings. *)

  % polymorphic op to print sequence of things with given separator:
  op printSeq : [a] (a -> String) -> String -> List a -> String
  def printSeq printElem separator seq =
    if empty? seq then ""
    else if ofLength? 1 seq then printElem (theElement seq)
    else printElem (head seq) ^ separator
      ^ printSeq printElem separator (tail seq)

  % synonym, for uniformity with the other ops in this spec:
  op printInt : Int -> String
  def printInt = intToString

  op printInts : List Int -> String
  def printInts = printSeq printInt ","

  op printTypeName : TypeName -> String
  def printTypeName = id

  op printOperation : Operation -> String
  def printOperation = project 1

  op printTypeVariable : TypeVariable -> String
  def printTypeVariable = id

  op printTypeVariables : TypeVariables -> String
  def printTypeVariables = printSeq printTypeVariable ","

  op printUserVariable : UserVariable -> String
  def printUserVariable = id

  op printUserField : UserField -> String
  def printUserField = id

  op printAxiomName : AxiomName -> String
  def printAxiomName = id

  op printLemmaName : LemmaName -> String
  def printLemmaName = id

  op printField : Field -> String
  def printField = fn
    | user f -> printUserField f
    | prod i -> printInt i

  op printFields : Fields -> String
  def printFields = printSeq printField ","

  op printVariable : Variable -> String
  def printVariable = fn
    | user v -> printUserVariable v
    | abbr i -> "V[" ^ printInt i ^ "]"  % e.g. abbr 3 -> V[3]

  op printType       : Type       -> String  % defined below
  op printExpression : Expression -> String  % defined below

  op printTypes : Types -> String
  def printTypes = printSeq printType ","

  op printTypeInstance : TypeName * Types -> String
  def printTypeInstance (tn,tS) =
    if empty? tS then printTypeName tn  % avoid "[]" if no type arguments
                 else printTypeName tn ^ "[" ^ printTypes tS ^ "]"

  op printArrowType : Type * Type -> String
  def printArrowType (t1,t2) =
    "(" ^ printType t1 ^ " -> " ^ printType t2 ^ ")"

  op printRecordTypeComponent : Field * Type -> String
  def printRecordTypeComponent (f,t) =
    printField f ^ ":" ^ printType t

  op printRecordType : Fields * Types -> String
  def printRecordType (fS,tS) =
    let n:Nat = min (length fS, length tS) in
    let fS = prefix (fS, n) in
    let tS = prefix (tS, n) in
    "{" ^ printSeq printRecordTypeComponent ", " (zip(fS,tS)) ^ "}" ^
    % if there are extra fields or component types (if the record type is
    % not well-formed), append them to record type printout between "#":
    (if length fS <= n then ""
     else "#" ^ printFields (removePrefix(fS,n)) ^ "#") ^
    (if length tS <= n then ""
     else "#" ^ printTypes (removePrefix(tS,n)) ^ "#")

  op printRestrictionType : Type * Expression -> String
  def printRestrictionType (t,r) =
   "(" ^ printType t ^ " | " ^ printExpression r ^ ")"

  def printType = fn
    | BOOL         -> "Boolean"
    | VAR tv       -> printTypeVariable tv
    | TYPE tn_tS   -> printTypeInstance tn_tS
    | ARROW t1_t2  -> printArrowType t1_t2
    | RECORD fS_tS -> printRecordType fS_tS
    | RESTR t_r    -> printRestrictionType t_r

  op printOpInstance : Operation * Types -> String
  def printOpInstance (o,tS) =
    if empty? tS then printOperation o  % avoid "[]" if no type arguments
                 else printOperation o ^ "[" ^ printTypes tS ^ "]"

  op printApplication : Expression * Expression -> String
  def printApplication (e1,e2) =
    printExpression e1 ^ " " ^ printExpression e2

  op printAbstraction : Variable * Type * Expression -> String
  def printAbstraction (v,t,e) =
   "(fn (" ^ printVariable v ^ ":" ^ printType t ^ ") -> "
   ^ printExpression e ^ ")"

  op printEquality : Expression * Expression -> String
  def printEquality (e1,e2) =
    "(" ^ printExpression e1 ^ " = " ^ printExpression e2 ^ ")"

  op printConditional : Expression * Expression * Expression -> String
  def printConditional (e0,e1,e2) =
    "if (" ^ printExpression e0 ^ ") then ("
           ^ printExpression e1 ^ ") else ("
           ^ printExpression e2 ^ ")"

  op printDescriptor : Type -> String
  def printDescriptor t =
    "the[" ^ printType t ^ "]"

  op printProjector : Type * Field -> String
  def printProjector (t,f) =
    "project[" ^ printType t ^ "," ^ printField f ^ "]"

  def printExpression = fn
    | VAR v       -> printVariable v
    | OPI o_tS    -> printOpInstance o_tS
    | APPLY e1_e2 -> printApplication e1_e2
    | FN v_t_e    -> printAbstraction v_t_e
    | EQ e1_e2    -> printEquality e1_e2
    | IF e0_e1_e2 -> printConditional e0_e1_e2
    | IOTA t      -> printDescriptor t
    | PROJECT t_f -> printProjector t_f

  op printTypeDeclaration : TypeName * Int -> String
  def printTypeDeclaration (tn,n) =
    "type " ^ printTypeName tn ^ ":" ^ printInt n ^ newline

  op printOpDeclaration : Operation * TypeVariables * Type -> String
  def printOpDeclaration (o,tvS,t) =
    "op " ^ printOperation o ^ " : {" ^ printTypeVariables tvS ^
    "} " ^ printType t ^ newline

  op printAxiom : AxiomName * TypeVariables * Expression -> String
  def printAxiom (an,tvS,e) =
    "axiom " ^ printAxiomName an ^ " is {" ^ printTypeVariables tvS ^
    "} " ^ printExpression e ^ newline

  op printLemma : LemmaName * TypeVariables * Expression -> String
  def printLemma (ln,tvS,e) =
    "axiom " ^ printLemmaName ln ^ " is {" ^ printTypeVariables tvS ^
    "} " ^ printExpression e ^ newline

  op printTypeVarDeclaration : TypeVariable -> String
  def printTypeVarDeclaration tv =
    "var " ^ printTypeVariable tv ^ newline

  op printVarDeclaration : Variable * Type -> String
  def printVarDeclaration (v,t) =
    "var " ^ printVariable v ^ " : " ^ printType t ^ newline

  op printContextElement : ContextElement -> String
  def printContextElement = fn
    | typeDeclaration tn_n    -> printTypeDeclaration tn_n
    | opDeclaration o_tvS_t   -> printOpDeclaration o_tvS_t
    | axioM an_tvS_e          -> printAxiom an_tvS_e
    | lemma ln_tvS_e          -> printLemma ln_tvS_e
    | typeVarDeclaration tv   -> printTypeVarDeclaration tv
    | varDeclaration v_t      -> printVarDeclaration v_t
    % each context element is printed in its own line

  op printContext : Context -> String
  def printContext cx =
    "[#" ^ newline ^ foldl (^) "" (map printContextElement cx) ^
    "#]" ^ newline
    % context consists of one line for each element, between "[#" and "#]"

  op printContexts : Contexts -> String
  def printContexts = printSeq printContext ""

  op turnStyle : String
  def turnStyle = " |---" ^ newline  % in its own line

  op printWellFormedContext : Context -> String
  def printWellFormedContext cx =
    turnStyle ^ printContext cx ^ " : CONTEXT" ^ newline

  op printWellFormedSpec : Context -> String
  def printWellFormedSpec cx =
    turnStyle ^ printContext cx ^ " : SPEC" ^ newline

  op printWellFormedType : Context * Type -> String
  def printWellFormedType (cx,t) =
    printContext cx ^ turnStyle ^ printType t ^ " : TYPE" ^ newline

  op printSubType : Context * Type * Expression * Type -> String
  def printSubType (cx,t1,r,t2) =
    printContext cx ^ turnStyle ^
    printType t1 ^ " <[" ^ printExpression r ^ "] " ^ printType t2 ^ newline

  op printWellTypedExpr : Context * Expression * Type -> String
  def printWellTypedExpr (cx,e,t) =
    printContext cx ^ turnStyle ^
    printExpression e ^ " : " ^ printType t ^ newline

  op printTheorem : Context * Expression -> String
  def printTheorem (cx,e) =
    printContext cx ^ turnStyle ^
    printExpression e ^ newline

  % API public
  op printJudgement : Judgement -> String
  def printJudgement = fn
    | wellFormedContext cx     -> printWellFormedContext cx
    | wellFormedSpec cx        -> printWellFormedSpec cx
    | wellFormedType cx_t      -> printWellFormedType cx_t
    | subType cx_t1_r_t2       -> printSubType cx_t1_r_t2
    | wellTypedExpr cx_e_t     -> printWellTypedExpr cx_e_t
    | theoreM cx_e             -> printTheorem cx_e

  % API public
  op printFailure : Failure -> String
  def printFailure = fn
    | badPermutation prm ->
      "bad permutation: " ^ printInts prm ^ newline
    | wrongPermutationLength prm ->
      "wrong permutation length: " ^ printInts prm ^ newline
    | fieldNotFound (f, fS, tS) ->
      "field " ^ printField f ^
      " not found in " ^ printRecordType(fS,tS) ^ newline
    | typeNotDeclared (cx, tn) ->
      "type " ^ printTypeName tn ^
      " not declared in" ^ newline ^ printContext cx
    | opNotDeclared (cx, o) ->
      "op " ^ printOperation o ^
      " not declared in" ^ newline ^ printContext cx
    | axiomNotDeclared (cx, an) ->
      "axiom " ^ printAxiomName an ^
      " not declared in" ^ newline ^ printContext cx
    | lemmaNotDeclared (cx, ln) ->
      "lemma " ^ printLemmaName ln ^
      " not declared in" ^ newline ^ printContext cx
    | typeVarNotDeclared (cx, tv) ->
      "type variable " ^ printTypeVariable tv ^
      " not declared in" ^ newline ^ printContext cx
    | varNotDeclared (cx, v) ->
      "variable " ^ printVariable v ^
      " not declared in" ^ newline ^ printContext cx
    | typeAlreadyDeclared (cx, tn) ->
      "type " ^ printTypeName tn ^
      " already declared in" ^ newline ^ printContext cx
    | opAlreadyDeclared (cx, o) ->
      "op " ^ printOperation o ^
      " already declared in" ^ newline ^ printContext cx
    | axiomAlreadyDeclared (cx, an) ->
      "axiom " ^ printAxiomName an ^
      " already declared in" ^ newline ^ printContext cx
    | lemmaAlreadyDeclared (cx, ln) ->
      "lemma " ^ printLemmaName ln ^
      " already declared in" ^ newline ^ printContext cx
    | typeVarAlreadyDeclared (cx, tv) ->
      "type variable " ^ printTypeVariable tv ^
      " already declared in" ^ newline ^ printContext cx
    | varAlreadyDeclared (cx, v) ->
      "variable " ^ printVariable v ^
      " already declared in" ^ newline ^ printContext cx
    | typeVarInSpec cx ->
      "spec contains type variable:" ^ newline ^ printContext cx
    | varInSpec cx ->
      "spec contains variable:" ^ newline ^ printContext cx
    | negativeTypeArity (tn, i) ->
      "type " ^ printTypeName tn ^ " has negative arity " ^
      printInt i ^ newline
    | wrongTypeArity (tn, rightArity, wrongArity) ->
      "type " ^ printTypeName tn ^ " has arity " ^
      printInt wrongArity ^ " instead of " ^
      printInt rightArity ^ newline
    | badTypeSubstitution (tvS, tS) ->
      "bad type substitution: " ^ printTypeVariables tvS ^ " <- " ^
      printTypes tS ^ newline
    | badSubstitution (v, e) ->
      "bad substitution: " ^ printVariable v ^ " <- " ^
      printExpression e ^ newline
    | notWFContext jdg ->
      "judgement is not well-formed context:" ^ newline ^
      printJudgement jdg
    | notWFType jdg ->
      "judgement is not well-formed type:" ^ newline ^
      printJudgement jdg
    | notSubtype jdg ->
      "judgement is not subtype:" ^ newline ^
      printJudgement jdg
    | notWTExpr jdg ->
      "judgement is not well-typed expression:" ^ newline ^
      printJudgement jdg
    | notTheorem jdg ->
      "judgement is not theorem:" ^ newline ^
      printJudgement jdg
    | notBool t ->
      "not boolean type: " ^ printType t ^ newline
    | notTypeInstance t ->
      "not type instance: " ^ printType t ^ newline
    | notArrowType t ->
      "not arrow type: " ^ printType t ^ newline
    | notRecordType t ->
      "not record type: " ^ printType t ^ newline
    | notRestrictionType t ->
      "not restriction type: " ^ printType t ^ newline
    | notOpInstance e ->
      "not op instance: " ^ printExpression e ^ newline
    | notApplication e ->
      "not application: " ^ printExpression e ^ newline
    | notAbstraction e ->
      "not abstraction: " ^ printExpression e ^ newline
    | notEquality e ->
      "not equality: " ^ printExpression e ^ newline
    | notConditional e ->
      "not conditional: " ^ printExpression e ^ newline
    | notDescriptor e ->
      "not descriptor: " ^ printExpression e ^ newline
    | notProjector e ->
      "not projector: " ^ printExpression e ^ newline
    | notForall e ->
      "not universal quantifier: " ^ printExpression e ^ newline
    | notExists1 e ->
      "not unique existential quantifier: " ^ printExpression e ^ newline
    | badRecordType (fS, tS) ->
      "bad record type: " ^ printRecordType (fS, tS) ^ newline
    | badRestrictionType (t, r) ->
      "bad restriction type: " ^ printRestrictionType (t, r) ^ newline 
    | wrongContext (rightCx, wrongCx) ->
      "found context" ^ newline ^ printContext wrongCx ^
      "instead of" ^ newline ^ printContext rightCx
    | notEqualContexts cxS ->
      "not all equal contexts:" ^ newline ^ printContexts cxS
    | notPrefixContext (cx1, cx2) ->
      "context" ^ newline ^ printContext cx1 ^
      "is not a prefix of" ^ newline ^ printContext cx2 ^ newline
    | notAllTypeVarDecls cx ->
      "not all type variables:" ^ newline ^ printContext cx
    | contextNotEndingInVar cx ->
      "context does not end with variable:" ^ newline ^ printContext cx
    | contextNotEndingInAxiom cx ->
      "context does not end with axiom:" ^ newline ^ printContext cx
    | wrongType (rightT, wrongT) ->
      "found type " ^ printType wrongT ^
      " instead of " ^ printType rightT ^ newline
    | wrongLeftSubtype (rightT, wrongT) ->
      "found subtype " ^ printType wrongT ^
      " instead of " ^ printType rightT ^ newline
    | wrongLeftSubtypes (rightTS, wrongTS) ->
      "found subtypes " ^ printTypes wrongTS ^
      " instead of " ^ printTypes rightTS ^ newline
    | wrongRightSubtype (rightT, wrongT) ->
      "found supertype " ^ printType wrongT ^
      " instead of " ^ printType rightT ^ newline
    | wrongFields (rightFS, wrongFS) ->
      "found fields " ^ printFields wrongFS ^
      " instead of " ^ printFields rightFS ^ newline
    | wrongExpression (rightE, wrongE) ->
      "found expression " ^ printExpression wrongE ^
      " instead of " ^ printExpression rightE ^ newline
    | wrongTheorem (rightE, wrongE) ->
      "found theorem " ^ printExpression wrongE ^
      " instead of " ^ printExpression rightE ^ newline
    | wrongLeftExpression (rightE, wrongE) ->
      "found left-hand expression " ^ printExpression wrongE ^
      " instead of " ^ printExpression rightE ^ newline
    | wrongLastAxiom (rightE, wrongE) ->
      "found last axiom " ^ printExpression wrongE ^
      " instead of " ^ printExpression rightE ^ newline
    | nonMonomorphicAxiom celem ->
      "not monomorphic axiom:" ^ printContextElement celem
    | nonDistinctFields fS ->
      "fields are not distinct: " ^ printFields fS ^ newline
    | nonDistinctVariables (v1, v2) ->
      "variables " ^ printVariable v1 ^ " and " ^
      printVariable v2 ^ " are not distinct" ^ newline
    | wrongNumberOfProofs ->
      "wrong number of proofs" ^ newline

endspec
