(* Copyright 2015 Kestrel Institute. See file LICENSE for license details *)

ProofDebugger qualifying
spec

  % API private default

  import AbbreviationContractor, Printer

  (* This spec consists of ops that convert judgements, failure, and all their
  syntactic components, to strings. These conversions enable printing such
  syntactic entities in a human-readable form.

  Since primitives can be any strings, it is easy to imagine situations in
  which a printed-out string is ambiguous or unclear. However, if only
  "reasonable" strings are used as primitives, the printing defined in this
  spec should produce unambiguous and clear strings. *)

  % polymorphic op to print sequence of things with given separator:

  op printType       : ExtType       -> String  % defined below
  op printExpression : ExtExpression -> String  % defined below

  op printTypes : ExtTypes -> String
  def printTypes = printSeq printType ","

  op printTypeInstance : TypeName * ExtTypes -> String
  def printTypeInstance (tn,tS) =
    if empty? tS then printTypeName tn  % avoid "[]" if no type arguments
                 else printTypeName tn ^ "[" ^ printTypes tS ^ "]"

  op printArrowType : ExtType * ExtType -> String
  def printArrowType (t1,t2) =
    "(" ^ printType t1 ^ " -> " ^ printType t2 ^ ")"

  op printRecordTypeComponent : Field * ExtType -> String
  def printRecordTypeComponent (f,t) =
    printField f ^ ":" ^ printType t

  op printRecordType : Fields * ExtTypes -> String
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

  op printRestrictionType : ExtType * ExtExpression -> String
  def printRestrictionType (t,r) =
   "(" ^ printType t ^ " | " ^ printExpression r ^ ")"

  op printProductType : ExtTypes -> String
  def printProductType (tS) =
    let n:Nat = length tS in
    "(" ^ printSeq printType ", " tS ^ ")"

  def printType = fn
    | BOOL         -> "Boolean"
    | VAR tv       -> printTypeVariable tv
    | TYPE tn_tS   -> printTypeInstance tn_tS
    | ARROW t1_t2  -> printArrowType t1_t2
    | RECORD fS_tS -> printRecordType fS_tS
    | RESTR t_r    -> printRestrictionType t_r
    | PRODUCT ts   -> printProductType ts

  op printOpInstance : Operation * ExtTypes -> String
  def printOpInstance (o,tS) =
    if empty? tS then printOperation o  % avoid "[]" if no type arguments
                 else printOperation o ^ "[" ^ printTypes tS ^ "]"

  op printApplication : ExtExpression * ExtExpression -> String
  def printApplication (e1,e2) =
    printExpression e1 ^ " " ^ printExpression e2

  op printAbstraction : Variable * ExtType * ExtExpression -> String
  def printAbstraction (v,t,e) =
   "(fn (" ^ (printVariable) v ^ ":" ^ printType t ^ ") -> "
   ^ printExpression e ^ ")"

  op printEquality : ExtExpression * ExtExpression -> String
  def printEquality (e1,e2) =
    "(" ^ printExpression e1 ^ " = " ^ printExpression e2 ^ ")"

  op printConditional : ExtExpression * ExtExpression * ExtExpression -> String
  def printConditional (e0,e1,e2) =
    "if (" ^ printExpression e0 ^ ") then ("
           ^ printExpression e1 ^ ") else ("
           ^ printExpression e2 ^ ")"

  op printDescriptor : ExtType -> String
  def printDescriptor t =
    "the[" ^ printType t ^ "]"

  op printProjector : ExtType * Field -> String
  def printProjector (t,f) =
    "project[" ^ printType t ^ "," ^ printField f ^ "]"

  op printTrue : String
  def printTrue = "true"

  op printFalse : String
  def printFalse = "false"

  op printNot : String
  def printNot = "NOT"

  op printNEGExpression: ExtExpression -> String
  def printNEGExpression(e) =
    "NOT " ^ printExpression(e)

  op printANDExpression : ExtExpression * ExtExpression -> String
  def printANDExpression(e1, e2) =
    printExpression(e1) ^ " AND " ^ printExpression(e2)

  op printORExpression : ExtExpression * ExtExpression -> String
  def printORExpression(e1, e2) =
    printExpression(e1) ^ " OR " ^ printExpression(e2)

  op printIMPLIESExpression : ExtExpression * ExtExpression -> String
  def printIMPLIESExpression(e1, e2) =
    printExpression(e1) ^ " IMPLIES " ^ printExpression(e2)

  op printIFFExpression : String
  def printIFFExpression = "IFF"

  op printEQVExpression : ExtExpression * ExtExpression -> String
  def printEQVExpression(e1, e2) =
    printExpression(e1) ^ " == " ^ printExpression(e2)

  op printNEQExpression: ExtExpression * ExtExpression -> String
  def printNEQExpression(e1, e2) =
    printExpression(e1) ^ " != " ^ printExpression(e2)

  op printTHEExpression: Variable * ExtType * ExtExpression -> String
  def printTHEExpression(v, t, e) =
    "THE " ^ (printVariable(v)) ^ ": " ^ (printType t) ^ "." ^ (printExpression(e))

  op printFAqExpression: ExtType -> String
  def printFAqExpression(t) =
    "FAq " ^ printType(t)

  op printFAExpression: Variable * ExtType * ExtExpression -> String
  def printFAExpression(v, t, e) =
    "FA " ^ (printVariable(v)) ^ ": " ^ (printType(t)) ^ "." ^
    (printExpression(e))

  op printFAAExpression: Variables * ExtTypes * ExtExpression -> String
  def printFAAExpression(vs, ts, e) =
    let vts = zip(vs, ts) in
    "FA (" ^ (printSeq (fn (v, t) -> (printVariable v) ^ ": " ^
    (printType(t))) ", " vts) ^ ")" ^ printExpression(e)

  op printEXqExpression: ExtType -> String
  def printEXqExpression(t) =
    "EXq " ^ printType(t)

  op printEXExpression: Variable * ExtType * ExtExpression -> String
  def printEXExpression(v, t, e) =
    "EX " ^ (printVariable(v)) ^ ": " ^ (printType(t)) ^ "." ^
    (printExpression(e))

  op printEXXExpression: Variables * ExtTypes * ExtExpression -> String
  def printEXXExpression(vs, ts, e) =
    let vts = zip(vs, ts) in
    "EX (" ^ (printSeq (fn (v, t) -> (printVariable v) ^ ": " ^
    (printType(t))) ", " vts) ^ ")" ^ printExpression(e)

  op printEX1qExpression: ExtType -> String
  def printEX1qExpression(t) =
    "EX! " ^ printType(t)

  op printEX1Expression: Variable * ExtType * ExtExpression -> String
  def printEX1Expression(v, t, e) =
    "EX! " ^ (printVariable(v)) ^ ": " ^ (printType(t)) ^ "." ^
    (printExpression(e))

  op printDOTExpression: ExtExpression * ExtType * Field -> String
  def printDOTExpression(e, _(*t*), f) =
    printExpression(e) ^ "." ^ printField(f)

  op printRECCExpression: Fields * ExtTypes -> String
  def printRECCExpression(fs, ts) =
    let fts = zip(fs, ts) in
    "REC(" ^ (printSeq (fn (f, t) -> (printField f) ^ ": " ^ (printType(t))) ", " fts) ^ ")"

  op printRECExpression: Fields * ExtTypes * ExtExpressions -> String
  def printRECExpression(fs, ts, es) =
    let ftes = zip3(fs, ts, es) in
    "<" ^ (printSeq (fn (f, t, e) -> (printField f) ^ ": " ^
    (printType(t)) ^ " := " ^ printExpression(e)) ", " ftes) ^ ">"

  op printTUPLEExpression: ExtTypes * ExtExpressions -> String
  def printTUPLEExpression(_(*ts*), es) =
    "<" ^ (printSeq printExpression ", " es) ^ ">"

  op printRECUPDATERExpression:
     Fields * ExtTypes * Fields * ExtTypes * Fields * ExtTypes -> String
  def printRECUPDATERExpression _(* fs1, ts1, fs2, ts2, fs3, ts3 *) =
    "RECUPDATER"

  op printRECUPDATEExpression:
     Fields * ExtTypes * Fields * ExtTypes * Fields * ExtTypes *
     ExtExpression * ExtExpression -> String
  def printRECUPDATEExpression _(* fs1, ts1, fs2, s2, fs3, ts3, e1, e2 *) =
    "RECUPDATE"

  op printLETSIMPExpression:
     ExtType * Variable * ExtType * ExtExpression * ExtExpression -> String
  def printLETSIMPExpression _(* t1, v, t2, e1, e2 *) =
    "LETSIMP"

  op printCONDExpression: ExtType * ExtBindingBranches -> String
  def printCONDExpression(_(*t*), bbs) =
    "COND(" ^ (printSeq printBindingBranch ";/n" bbs) ^ ")"

  op printBindingBranch:
     Variables * ExtTypes * ExtExpression  * ExtExpression -> String
  def printBindingBranch(vs, ts, e1, e2) =
    let vsts = zip(vs, ts) in
    "(" ^ (printSeq (fn (v, t) -> (printVariable v) ^ ":" ^
    printType t) ", " vsts) ^ " -> " ^ printExpression e1 ^
    " => " ^ printExpression e2 ^ ")"

  op printCASEExpression:
     ExtType * ExtType * ExtExpression * ExtBindingBranches -> String
  def printCASEExpression _(* t1, t2, e, bbs *) =
    "CASE"

  op printLETExpression:
     ExtType * ExtType * Variables * ExtTypes *
     ExtExpression * ExtExpression * ExtExpression -> String
  def printLETExpression _(* t1, t2, vs, ts, e1, e2, e3 *) =
    "LET"
                 
  op printLETDEFExpression:
     ExtType * Variables * ExtTypes * ExtExpressions * ExtExpression -> String
  def printLETDEFExpression _(* t, vs, ts, e1, e2 *) =
    "LETDEF"

  def printExpression(e) =
    case e of
    | VAR v          -> printVariable v
    | OPI o_tS       -> printOpInstance o_tS
    | APPLY e1_e2    -> printApplication e1_e2
    | FN v_t_e       -> printAbstraction v_t_e
    | EQ e1_e2       -> printEquality e1_e2
    | IF e0_e1_e2    -> printConditional e0_e1_e2
    | IOTA t         -> printDescriptor t
    | PROJECT t_f    -> printProjector t_f
    | TRUE           -> printTrue
    | FALSE          -> printFalse
    | NOT            -> printNot
    | NEG (e)        -> printNEGExpression e
    | AND (e1,e2)    -> printANDExpression(e1, e2)
    | OR  (e1,e2)    -> printORExpression(e1, e2)
    | IMPLIES(e1,e2) -> printIMPLIESExpression(e1, e2)
    | IFF            -> printIFFExpression
    | EQV(e1, e2)    -> printEQVExpression(e1, e2)
    | NEQ(e1,e2)     -> printNEQExpression(e1, e2)
    | THE(v,t, e)    -> printTHEExpression(v, t, e)
    | FAq(t)         -> printFAqExpression(t)
    | FA(v, t, e)    -> printFAExpression(v, t, e)
    | FAA(vs, ts, e) -> printFAAExpression(vs, ts, e)
    | EXq(t)         -> printEXqExpression(t)
    | EX(v, t, e)    -> printEXExpression(v, t, e)
    | EXX(vs, ts, e) -> printEXXExpression(vs, ts, e)
    | EX1q(t)        -> printEX1qExpression(t)
    | EX1(v, t, e)   -> printEX1Expression(v, t, e)
    | DOT(e, t, f)   -> printDOTExpression(e, t, f)
    | RECC(fs, ts)   -> printRECCExpression(fs, ts)
    | REC(fs, ts, es)-> printRECExpression(fs, ts, es)
    | TUPLE(ts, es)  -> printTUPLEExpression(ts, es)
    | RECUPDATER(fs, ts, fs1, ts1, fs2, ts2) ->
      printRECUPDATERExpression(fs, ts, fs1, ts1, fs2, ts2)
    | RECUPDATE(fs, ts, fs1, ts1, fs2, ts2, e1, e2) ->
      printRECUPDATEExpression(fs, ts, fs1, ts1, fs2, ts2, e1, e2)
    | LETSIMP(t1, v, t2, e1, e2) -> printLETSIMPExpression(t1, v, t2, e1, e2)
    | COND(t, bbs) -> printCONDExpression(t, bbs)
    | CASE(t1, t2, e, bbs) -> printCASEExpression(t1, t2, e, bbs)
    | LET(t1, t2, vs, ts, e1, e2, e3) ->
      printLETExpression(t1, t2, vs, ts, e1, e2, e3)
    | LETDEF(t, vs, ts, e1, e2) -> printLETDEFExpression(t, vs, ts, e1, e2)

  op printOpDeclaration : Operation * TypeVariables * ExtType -> String
  def printOpDeclaration (o,tvS,t) =
    "op " ^ printOperation o ^ " : {" ^ printTypeVariables tvS ^
    "} " ^ printType t ^ newline

  op printAxiom : AxiomName * TypeVariables * ExtExpression -> String
  def printAxiom (an,tvS,e) =
    "axiom " ^ printAxiomName an ^ " is {" ^ printTypeVariables tvS ^
    "} " ^ printExpression e ^ newline

  op printLemma : LemmaName * TypeVariables * ExtExpression -> String
  def printLemma (ln,tvS,e) =
    "lemma " ^ printLemmaName ln ^ " is {" ^ printTypeVariables tvS ^
    "} " ^ printExpression e ^ newline

  op printVarDeclaration : Variable * ExtType  -> String
  def printVarDeclaration (v,t) =
    "var " ^ printVariable v ^ " : " ^ printType t ^ newline

  op printContextElement : ContextElement -> String
  def printContextElement = fn
    | typeDeclaration tn_n    -> printTypeDeclaration tn_n
    | opDeclaration(o, tvS, t)   -> printOpDeclaration(o, tvS, contractTypeAll t)
    | axioM(an, tvS, e)          -> printAxiom(an, tvS, contractExprAll e)
    | lemma(ln, tvS, e)          -> printLemma(ln, tvS, contractExprAll e)
    | typeVarDeclaration tv   -> printTypeVarDeclaration tv
    | varDeclaration(v, t)      -> printVarDeclaration(v, contractTypeAll t)
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

  op printWellFormedType : Context * ExtType  -> String
  def printWellFormedType (cx,t) =
    printContext cx ^ turnStyle ^ printType t ^ " : TYPE" ^ newline

  op printSubType : Context * ExtType  * ExtExpression * ExtType  -> String
  def printSubType (cx,t1,r,t2) =
    printContext cx ^ turnStyle ^
    printType t1 ^ " <[" ^ printExpression r ^ "] " ^ printType t2 ^ newline

  op printWellTypedExpr : Context * ExtExpression * ExtType  -> String
  def printWellTypedExpr (cx,e,t) =
    printContext cx ^ turnStyle ^
    printExpression e ^ " : " ^ printType t ^ newline

  op printTheorem : Context * Expression -> String
  def printTheorem (cx,e) =
    printContext cx ^ turnStyle ^
    printExpression (contractExprAll e) ^ newline

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
      "not bool type: " ^ printType t ^ newline
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
