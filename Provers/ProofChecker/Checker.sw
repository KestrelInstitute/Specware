spec

  % API private default

  import Substitutions, BasicAbbreviations, ProofCheckerMonad

  (* This spec defines the function, mentioned in specs Proofs and Failures,
  that recursively checks whether a proof is valid, returning a judgement or a
  failure. The function is op check. This op makes use of several auxiliary
  ops, also defined in this spec. Op check and the auxiliary ops are monadic;
  they use the exception monad defined in spec Failures. *)

  (* DAC: 2005/11/07:
   Added State to the checker monad.  Initially the state only includes a simple
   map as Alist to implement memoization.  See check and checkInt comments. *)

  (* Ensure that boolean condition holds. If it does not hold, return the
  failure provided as argument, otherwise return nothing. This op is
  essentially a shortcut for an if-then-else that can be composed via the
  monadic bind operator. *)
  op ensure : Boolean -> Failure -> M ()
  def ensure cond fail =
    if cond then OK () else let _ = (System.fail "ensure") in FAIL fail

  (* Check whether a finite sequence of integers is a permutation (see spec
  FiniteSequences in the Specware library). If it is, return it as a
  permutation, i.e. as a value of type FSeq.Permutation. *)
  op checkPermutation : FSeq Integer -> M Permutation
  def checkPermutation prm =
    % all integers must be non-negative:
    ensure (forall? natural? prm) (badPermutation prm) >> (fn _ ->
    % convert sequence of non-negative integers to sequence of naturals:
    (let prm1 : FSeq Nat = seq (fn(i:Nat) ->
       if i < length prm then Some (prm @ i) else None) in
    % sequence of naturals must form a permutation:
    ensure (permutation? prm1) (badPermutation prm) >> (fn _ ->
    % return result (of type Permutation):
    OK prm1)))

  (* Check whether a type is the boolean type. *)
  op checkBoolean : Type -> M ()
  def checkBoolean = fn
    | BOOL -> OK ()
    | t -> FAIL (notBoolean t)

  (* Check whether a type is a type instance. If it is, return its type name
  and argument types. *)
  op checkTypeInstance : Type -> M (TypeName * Types)
  def checkTypeInstance = fn
    | TYPE (tn, tS) -> OK (tn, tS)
    | t -> FAIL (notTypeInstance t)

  (* Check whether a type is an arrow type. If it is, return its domain and
  range types. *)
  op checkArrowType : Type -> M (Type * Type)
  def checkArrowType = fn
    | ARROW (t1, t2) -> OK (t1, t2)
    | t -> FAIL (notArrowType t)

  (* Check whether a type is a record type with distinct fields and with a
  matching number of component types. If it is, return its fields and
  component types. *)
  op checkRecordType : Type -> M (Fields * Types)
  def checkRecordType = fn
    | RECORD (fS, tS) ->
      ensure (fS equiLong tS && noRepetitions? fS)
             (badRecordType (fS, tS)) >> (fn _ ->
      OK (fS, tS))
    | t -> FAIL (notRecordType t)

 (* Check whether a type is a sum type with non-zero distinct constructors and
 with a matching number of component types. If it is, return its constructors
 and component types. *)
  op checkSumType : Type -> M (Constructors * Types)
  def checkSumType = fn
    | SUM (cS, tS) ->
      ensure (cS equiLong tS && noRepetitions? cS && nonEmpty? cS)
             (badSumType (cS, tS)) >> (fn _ ->
      OK (cS, tS))
    | t -> FAIL (notSumType t)

  (* Check whether a type is a restriction type whose predicate has no free
  variables. If it is, return its base type and predicate. *)
  op checkRestrictionType : Type -> M (Type * Expression)
  def checkRestrictionType = fn
    | RESTR (t, r) ->
      ensure (exprFreeVars r = empty) (badRestrictionType (t, r)) >> (fn _ ->
      OK (t, r))
    | t -> FAIL (notRestrictionType t)

  (* Check whether a type is a quotient type whose predicate has no free
  variables. If it is, return its quotiented type and predicate type. *)
  op checkQuotientType : Type -> M (Type * Expression)
  def checkQuotientType = fn
    | QUOT (t, q) ->
      ensure (exprFreeVars q = empty) (badQuotientType (t, q)) >> (fn _ ->
      OK (t, q))
    | t -> FAIL (notQuotientType t)

  (* Check whether a field appears in a record type (the record type is
  represented by its fields and component types). If it does, return its
  associated component type. *)
  op checkFieldType :
     Field ->
     {(fS,tS) : Fields * Types | noRepetitions? fS && fS equiLong tS} ->
     M Type
  def checkFieldType f (fS,tS) =
    ensure (f in? fS) (fieldNotFound (f, fS, tS)) >> (fn _ ->
    OK (tS @ (positionOf(fS,f))))

  (* Check whether a constructor appears in a sum type (the sum type is
  represented by its constructors and component types). If it does, return its
  associated component type. *)
  op checkConstructorType :
     Constructor ->
     {(cS,tS) : Constructors * Types | noRepetitions? cS && cS equiLong tS} ->
     M Type
  def checkConstructorType c (cS,tS) =
    ensure (c in? cS) (constructorNotFound (c, cS, tS)) >> (fn _ ->
    OK (tS @ (positionOf(cS,c))))

  (* Check whether two types are (syntactically) equal. *)
  op checkSameType : Type -> Type -> M ()
  def checkSameType t1 t2 =
    ensure (t1 = t2) (wrongType (t1, t2))

  (* Check whether an expression is an op instance. If it is, return its
  operation and argument types. *)
  op checkOpInstance : Expression -> M (Operation * Types)
  def checkOpInstance = fn
    | OPI (o, tS) -> OK (o, tS)
    | e -> FAIL (notOpInstance e)

  (* Check whether an expression is an application. If it is, return its
  function and argument expressions. *)
  op checkApplication : Expression -> M (Expression * Expression)
  def checkApplication = fn
    | APPLY (e1, e2) -> OK (e1, e2)
    | e -> FAIL (notApplication e)

  (* Check whether an expression is an abstraction. If it is, return its bound
  variable, type, and body. *)
  op checkAbstraction : Expression -> M (Variable * Type * Expression)
  def checkAbstraction = fn
    | FN (v, t, e) -> OK (v, t, e)
    | e -> FAIL (notAbstraction e)

  (* Check whether an expression is an equality. If it is, return its left-
  and right-hand sides. *)
  op checkEquality : Expression -> M (Expression * Expression)
  def checkEquality = fn
    | EQ (e1, e2) -> OK (e1, e2)
    | e -> FAIL (notEquality e)

  (* Check whether an expression is a conditional, If it is, return its
  condition and branches. *)
  op checkConditional : Expression -> M (Expression * Expression * Expression)
  def checkConditional = fn
    | IF (e0, e1, e2) -> OK (e0, e1, e2)
    | e -> FAIL (notConditional e)

  (* Check whether an expression is a descriptor. If it is, return its
  labeling type. *)
  op checkDescriptor : Expression -> M Type
  def checkDescriptor = fn
    | IOTA t -> OK t
    | e -> FAIL (notDescriptor e)

  (* Check whether an expression is a projector tagged by a record type and
  whose field belongs to the record type. If it is, return the record type
  (represented by its fields and component types) and the field. *)
  op checkProjector : Expression -> M (Fields * Types * Field)
  def checkProjector = fn
    | PROJECT (t, f) ->
      checkRecordType t >> (fn (fS, tS) ->
      ensure (f in? fS) (fieldNotFound (f, fS, tS)) >> (fn _ ->
      OK (fS, tS, f)))
    | e -> FAIL (notProjector e)

  (* Check whether an expression is an embedder tagged by a sum type and whose
  constructor belongs to the sum type. If it is, return the sum type
  (represented by its constructors and component types) and the
  constructor. *)
  op checkEmbedder : Expression -> M (Constructors * Types * Constructor)
  def checkEmbedder = fn
    | EMBED (t, c) ->
      checkSumType t >> (fn (cS, tS) ->
      ensure (c in? cS) (constructorNotFound (c, cS, tS)) >> (fn _ ->
      OK (cS, tS, c)))
    | e -> FAIL (notEmbedder e)

  (* Check whether an expression is a quotienter tagged by a quotient type. If
  it is, return the base type and predicate that constitute the quotient
  type. *)
  op checkQuotienter : Expression -> M (Type * Expression)
  def checkQuotienter = fn
    | QUOT t ->
      checkQuotientType t >> (fn (t, q) ->
      OK (t, q))
    | e -> FAIL (notQuotienter e)

  (* Check whether an expression is a universal quantification. If it is,
  return its bound variable, type, and body. A universal quantification is an
  abbreviation (see spec BasicAbbreviations) consisting of the universal
  quantifier applied to an abstraction with the same variable, type, and body
  as the universal quantification. *)
  op checkUniversal : Expression -> M (Variable * Type * Expression)
  def checkUniversal e =
    % check that e is an application:
    checkApplication e >> (fn (mustBe_FAq, mustBe_FN) ->
    % check that the argument of the application is an abstraction:
    checkAbstraction mustBe_FN >> (fn (v, t, e) ->
    % check that the function is the universal quantifier whose type matches
    % the abstraction's:
    ensure (mustBe_FAq = FAq t) (notForall mustBe_FAq) >> (fn _ ->
    % return bound variable, type, and body:
    OK (v, t, e))))

  (* Like previous op (see explanatory comments for previous op) but check a
  unique existential quantification rather than a universal quantification. *)
  op checkUniqueExistential : Expression -> M (Variable * Type * Expression)
  def checkUniqueExistential e =
    checkApplication e >> (fn (mustBe_EX1q, mustBe_FN) ->
    checkAbstraction mustBe_FN >> (fn (v, t, e) ->
    ensure (mustBe_EX1q = EX1q t) (notExists1 mustBe_EX1q) >> (fn _ ->
    OK (v, t, e))))

  (* Check whether two expressions are (syntactically) equal. *)
  op checkSameExpr : Expression -> Expression -> M ()
  def checkSameExpr e1 e2 =
    ensure (e1 = e2) (wrongExpression (e1, e2))

  (* Check whether a context declares a type with a non-negative arity. If it
  does, return its arity. *)
  op checkTypeDecl : Context -> TypeName -> M Nat
  def checkTypeDecl cx tn =
    ensure (cx ~= empty) (typeNotDeclared (cx, tn)) >> (fn _ ->
    (case first cx of
       | typeDeclaration (tn1, n) ->
         if tn1 = tn then
           ensure (n >= 0) (negativeTypeArity (tn, n)) >> (fn _ ->
           OK n)
         else checkTypeDecl (rtail cx) tn
       | _ -> checkTypeDecl (rtail cx) tn))

  (* Like previous op but also check that the arity coincides with the given
  argument. *)
  op checkTypeDeclWithArity : Context -> TypeName -> Nat -> M ()
  def checkTypeDeclWithArity cx tn n =
    checkTypeDecl cx tn >> (fn(mustBe_n:Nat) ->
    ensure (mustBe_n = n) (wrongTypeArity (tn, mustBe_n, n)))

  (* Check whether a context declares an op. If it does, return its type
  information. *)
  op checkOpDecl : Context -> Operation -> M (TypeVariables * Type)
  def checkOpDecl cx o =
    ensure (cx ~= empty) (opNotDeclared (cx, o)) >> (fn _ ->
    (case first cx of
       | opDeclaration (o1, tvS, t) ->
         if o1 = o then OK (tvS, t)
         else checkOpDecl (rtail cx) o
       | _ -> checkOpDecl (rtail cx) o))

  (* Check whether a context defines a type. If it does, return its definition
  information. *)
  op checkTypeDef : Context -> TypeName -> M (TypeVariables * Type)
  def checkTypeDef cx tn =
    ensure (cx ~= empty) (typeNotDefined (cx, tn)) >> (fn _ ->
    (case first cx of
       | typeDefinition (tn1, tvS, t) ->
         if tn1 = tn then OK (tvS, t)
         else checkTypeDef (rtail cx) tn
       | _ -> checkTypeDef (rtail cx) tn))

  (* Check whether a context defines an op. If it does, return its definition
  information. *)
  op checkOpDef : Context -> Operation -> M (TypeVariables * Expression)
  def checkOpDef cx o =
    ensure (cx ~= empty) (opNotDefined (cx, o)) >> (fn _ ->
    (case first cx of
       | opDefinition (o1, tvS, e) ->
         if o1 = o then OK (tvS, e)
         else checkOpDef (rtail cx) o
       | _ -> checkOpDef (rtail cx) o))

  (* Check whether a context includes a named axiom. If it does, return the
  axiom information. *)
  op checkAxiom : Context -> AxiomName -> M (TypeVariables * Expression)
  def checkAxiom cx an =
    ensure (cx ~= empty) (axiomNotDeclared (cx, an)) >> (fn _ ->
    (case first cx of
       | axioM (an1, tvS, e) ->
         if an1 = an then OK (tvS, e)
         else checkAxiom (rtail cx) an
       | _ -> checkAxiom (rtail cx) an))

  (* Check whether a context declares a variable. If it does, return its
  type. *)
  op checkVarDecl : Context -> Variable -> M Type
  def checkVarDecl cx v =
    ensure (cx ~= empty) (varNotDeclared (cx, v)) >> (fn _ ->
    (case first cx of
       | varDeclaration (v1, t) ->
         if v1 = v then OK t
         else checkVarDecl (rtail cx) v
       | _ -> checkVarDecl (rtail cx) v))

  (* Check whether the given type variables and types form a valid type
  substitution. If they do, return the type substitution (as a value of type
  TypeSubstitution). *)
  op checkTypeSubstitution :
     TypeVariables -> Types -> M TypeSubstitution
  def checkTypeSubstitution tvS tS =
    % type variables must be distinct and be as many as the types:
    ensure (noRepetitions? tvS && tvS equiLong tS)
           (badTypeSubstitution (tvS, tS)) >> (fn _ ->
    % make map from sequences (see op fromSeqs in spec FiniteStructures):
    OK (fromSeqs (tvS, tS)))

  (* Check whether a context consists solely of type variable declarations. If
  it does, return the type variables in the order they are declared. *)
  op checkAllTypeVarDecls : Context -> M TypeVariables
  def checkAllTypeVarDecls cx =
    % auxiliary function that accumulates type variables as it checks the
    % context left-to-right:
    let def aux (cx  : Context,        % residual context to process
                 tvS : TypeVariables)  % accumulator
                : M TypeVariables =
          % if context exhausted, return accumulated type variableS:
          if cx = empty then OK tvS
          % otherwise, keep processing context:
          else case first cx of
                   % if context element is a type variable declaraion,
                   % accumulate type variable and continue with rest of context:
                 | typeVarDeclaration tv -> aux (rtail cx, tvS <| tv)
                   % stop and fail as soon as context element is not
                   % a type variable declaration:
                 | _ -> FAIL (notAllTypeVarDecls cx)
    in
    % use auxiliary function, starting with full context and no accumulated
    % type variables:
    aux (cx, empty)

  (* Check whether cx1 is cx extended with zero or more type variable
  declarations. If it is, return the type variables, in the order they appear
  in cx1. *)
  op checkLastTypeVars : Context -> Context -> M TypeVariables
  def checkLastTypeVars cx cx1 =
    % first check that cx is a prefix of cx1:
    ensure (length cx <= length cx1 && prefix (cx1, length cx) = cx)
           (notPrefixContext (cx, cx1)) >> (fn _ ->
    % then check that the extra portion of cx1 solely consists of type variables:
    checkAllTypeVarDecls (removePrefix (cx1, length cx)))

  (* Check whether a context's last element is a variable declaration (so, the
  context must be non-empty). If it is, return the context minus the variable
  declaration, the variable, and the declared type of the variable. *)
  op checkLastVar : Context -> M (Context * Variable * Type)
  def checkLastVar cx =
    ensure (nonEmpty? cx && embed? varDeclaration (last cx))
           (contextNotEndingInVar cx) >> (fn _ ->
    (let varDeclaration (v, t) = last cx in
    OK (ltail cx, v, t)))

  (* Check whether cx1 is cx extended with an extra axiom with zero type
  variables and e as formula. If it is, return the axiom name. *)
  op checkLastAxiom : Context -> Context -> Expression -> M AxiomName
  def checkLastAxiom cx cx1 e =
    % check that cx1 ends with an axiom:
    ensure (nonEmpty? cx1 && embed? axioM (last cx1))
           (contextNotEndingInAxiom cx1) >> (fn _ ->
    % check that cx is cx1 minus the ending axiom:
    ensure (ltail cx1 = cx) (notPrefixContext (cx, cx1)) >> (fn _ ->
    % extract axiom info:
    (let axioM (an, mustBe_empty, mustBe_e) = last cx1 in
    % check that axiom has zero type variables and the given formula:
    ensure (empty? mustBe_empty) (nonMonomorphicAxiom (last cx1)) >> (fn _ ->
    ensure (mustBe_e = e) (wrongLastAxiom (mustBe_e, e)) >> (fn _ ->
    % return axiom name:
    OK an)))))

  (* Check whether two contexts are equal. *)
  op checkSameContext : Context -> Context -> M ()
  def checkSameContext cx1 cx2 =
    ensure (cx1 = cx2) (wrongContext (cx1, cx2))

  (* Op check is the main op of this spec, the one that recursively checks a
  proof. Op check is mutually recursive with several other auxiliary ops. So,
  we first declare it, then we declare and define the auxiliary ops, and
  finally we define op check itself.

  Op check is memoized for efficiency.  The proofs generated by the
  proof generator are very large when viewed as trees, but due to
  large shared structure are actually quite small when viewed as DAGS.
  Memoiziation allows check to exploit this structure sharing.
  Memoization is accomplished by adding a state variable, Memo to the
  Monad. See State.sw and ProofCheckerMonad.sw.  Op check first checks
  whether the result of checking the proof has been memo'd already.
  If so it returns, otherwise it performs the check (by calling
  checkInt).  It then writes the result to the Memo.  Op runCheck is
  the only public op defined in this spec.  It allows outside
  functions to call the checker, check, but without having to deal
  with the extra state component of the monad. *)

  % API public

  op runCheck: Proof -> Result(Failure, Judgement)
  def runCheck p =
    run check p

  op check : Proof -> M Judgement
  def check(p) =
    checkMemo p >>
    (fn | Some res -> OK res
        | None -> checkInt p >> (fn res -> putMemo(p, res)))

  op checkInt : Proof -> M Judgement   % defined below

  (* Check proof of well-formed context, returning context. *)
  op checkWFContext : Proof -> M Context
  def checkWFContext prf =
    check prf >> (fn wellFormedContext cx -> OK cx
                   | jdg -> FAIL (notWFContext jdg))

  (* Check proof of well-formed type, returning context and type. *)
  op checkWFType : Proof -> M (Context * Type)
  def checkWFType prf =
    check prf >> (fn wellFormedType (cx, t) -> OK (cx, t)
                   | jdg -> FAIL (notWFType jdg))

  (* Like previous op but also check that the context coincides with the
  argument, returning only the type. *)
  op checkWFTypeWithContext : Context -> Proof -> M Type
  def checkWFTypeWithContext cx prf =
    checkWFType prf >> (fn (mustBe_cx, t) ->
    checkSameContext mustBe_cx cx >> (fn _ ->
    OK t))

  (* Check one or more proofs of well-formed types with the same context,
  returning the common context and the types. Note that the requirement of a
  non-zero number of proofs serves to ensure that there is a context to return
  (which would not be the case with zero proofs). (Op allEqualElements? is
  defined in the library spec FiniteSequences.) *)
  op checkWFTypes : (NonEmptyFSeq Proof) -> M (Context * Types)
  def checkWFTypes prfS =
    mapSeq checkWFType prfS >> (fn pairS ->
    let (cxS, tS) = unzip pairS in
    ensure (allEqualElements? cxS) (notEqualContexts cxS) >> (fn _ ->
    OK (first cxS, tS)))

  (* Check proof of well-formed type in a context that extends the given
  context cx with type variables, returning the type variables and the
  type. In other words, check proof of well-formed polymorphic type in cx
  (polymorphic in the returned type variables). *)
  op checkWFPolyType : Context -> Proof -> M (TypeVariables * Type)
  def checkWFPolyType cx prf =
    checkWFType prf >> (fn (cx1, t) ->
    checkLastTypeVars cx cx1 >> (fn tvS ->
    OK (tvS, t)))

  (* Check proofs of well-formed types with given context, returning types.
  (Op mapSeq is defined in the library spec ExceptionMonads.) *)
  op checkWFTypesWithContext : Context -> Proofs -> M Types
  def checkWFTypesWithContext cx prfS =
    mapSeq (checkWFTypeWithContext cx) prfS

  (* Check proof of well-formed type instance, returning context, type name,
  and argument types. *)
  op checkWFTypeInstance : Proof -> M (Context * TypeName * Types)
  def checkWFTypeInstance prf =
    checkWFType prf >> (fn (cx, t) ->
    checkTypeInstance t >> (fn (tn, tS) ->
    OK (cx, tn, tS)))

  (* Check proof of well-formed arrow type, returning context, domain type,
  and range type. *)
  op checkWFArrowType : Proof -> M (Context * Type * Type)
  def checkWFArrowType prf =
    checkWFType prf >> (fn (cx, t) ->
    checkArrowType t >> (fn (t1, t2) ->
    OK (cx, t1, t2)))

  (* Check proof of well-formed record type, returning context, fields, and
  component types. *)
  op checkWFRecordType : Proof -> M (Context * Fields * Types)
  def checkWFRecordType prf =
    checkWFType prf >> (fn (cx, t) ->
    checkRecordType t >> (fn (fS, tS) ->
    OK (cx, fS, tS)))

  (* Check proof of well-formed sum type, returning context, constructors, and
  component types. *)
  op checkWFSumType : Proof -> M (Context * Constructors * Types)
  def checkWFSumType prf =
    checkWFType prf >> (fn (cx, t) ->
    checkSumType t >> (fn (cS, tS) ->
    OK (cx, cS, tS)))

  (* Check proof of well-formed restriction type, returning context, base
  type, and predicate. *)
  op checkWFRestrictionType : Proof -> M (Context * Type * Expression)
  def checkWFRestrictionType prf =
    checkWFType prf >> (fn (cx, t) ->
    checkRestrictionType t >> (fn (t, r) ->
    OK (cx, t, r)))

  (* Check proof of well-formed quotient type, returning context, base type,
  and predicate. *)
  op checkWFQuotientType : Proof -> M (Context * Type * Expression)
  def checkWFQuotientType prf =
    checkWFType prf >> (fn (cx, t) ->
    checkQuotientType t >> (fn (t, q) ->
    OK (cx, t, q)))

  (* Check proof of equivalent types, returning context and types. *)
  op checkTypeEquiv : Proof -> M (Context * Type * Type)
  def checkTypeEquiv prf =
    check prf >> (fn typeEquivalence (cx, t1, t2) -> OK (cx, t1, t2)
                   | jdg -> FAIL (notTypeEquiv jdg))

  (* Like previous op but also check that the context coincides with the
  argument, returning only the types. *)
  op checkTypeEquivWithContext : Context -> Proof -> M (Type * Type)
  def checkTypeEquivWithContext cx prf =
    checkTypeEquiv prf >> (fn (mustBe_cx, t1, t2) ->
    checkSameContext mustBe_cx cx >> (fn _ ->
    OK (t1, t2)))

  (* Like previous op but also check that the left-hand type coincides with
  the argument, returning only the right-hand type. *)
  op checkTypeEquivWithContextAndLeftType : Context -> Type -> Proof -> M Type
  def checkTypeEquivWithContextAndLeftType cx t1 prf =
    checkTypeEquivWithContext cx prf >> (fn (mustBe_t1, t2) ->
    ensure (mustBe_t1 = t1) (wrongLeftType (mustBe_t1, t1)) >> (fn _ ->
    OK t2))

  (* Check one or more proofs of equivalent types with the same context,
  returning the common context and the left- and the right-hand types. Note
  that the requirement of a non-zero number of proofs serves to ensure that
  there is a context to return (which would not be the case with zero proofs).
  (Op allEqualElements? is defined in the library spec FiniteSequences.) *)
  op checkTypeEquivs : (NonEmptyFSeq Proof) -> M (Context * Types * Types)
  def checkTypeEquivs prfS =
    mapSeq checkTypeEquiv prfS >> (fn tripleS ->
    let (cxS, tS, tS1) = unzip3 tripleS in
    ensure (allEqualElements? cxS) (notEqualContexts cxS) >> (fn _ ->
    OK (first cxS, tS, tS1)))

  (* Like previous op but also check that the context coincides with the
  argument, returning only the left- and right-hand types. Since the context
  is given, there is no need to require a non-zero number of proofs. *)
  op checkTypeEquivsWithContext : Context -> Proofs -> M (Types * Types)
  def checkTypeEquivsWithContext cx prfS =
    mapSeq (checkTypeEquivWithContext cx) prfS >> (fn pairS ->
    OK (unzip pairS))

  (* Like previous op but also check that the left-hand types coincide with
  the argument, returning only the right-hand types. *)
  op checkTypeEquivsWithContextAndLeftTypes :
     Context -> Types -> Proofs -> M Types
  def checkTypeEquivsWithContextAndLeftTypes cx tS prfS =
    checkTypeEquivsWithContext cx prfS >> (fn (mustBe_tS, tS1) ->
    ensure (mustBe_tS = tS) (wrongLeftTypes (mustBe_tS, tS)) >> (fn _ ->
    OK tS1))

  (* Check proof of equivalence of the given type to a record type in the
  given context, returning the record type's fields and component types. *)
  op checkRecordTypeEquivWithContextAndLeftType :
     Context -> Type -> Proof -> M (Fields * Types)
  def checkRecordTypeEquivWithContextAndLeftType cx t prf =
    checkTypeEquivWithContextAndLeftType cx t prf >> (fn t1 ->
    checkRecordType t1)

  (* Check proof of equivalence of the given type to a sum type in the given
  context, returning the sum type's constructors and component types. *)
  op checkSumTypeEquivWithContextAndLeftType :
     Context -> Type -> Proof -> M (Constructors * Types)
  def checkSumTypeEquivWithContextAndLeftType cx t prf =
    checkTypeEquivWithContextAndLeftType cx t prf >> (fn t1 ->
    checkSumType t1)

  (* Check proof of equivalence of the given type to a quotient type in the
  given context, returning the quotient type's base type and predicate. *)
  op checkQuotientTypeEquivWithContextAndLeftType :
     Context -> Type -> Proof -> M (Type * Expression)
  def checkQuotientTypeEquivWithContextAndLeftType cx t prf =
    checkTypeEquivWithContextAndLeftType cx t prf >> (fn t1 ->
    checkQuotientType t1)

  (* Check proof of subtype, returning context, subtype, predicate, and
  supertype. *)
  op checkSubtype : Proof -> M (Context * Type * Expression * Type)
  def checkSubtype prf =
    check prf >> (fn subType (cx, t1, r, t2) -> OK (cx, t1, r, t2)
                   | jdg -> FAIL (notSubtype jdg))

  (* Like previous op but also check that the context coincides with the
  argument, returning only the subtype, predicate, and supertype. *)
  op checkSubtypeWithContext : Context -> Proof -> M (Type * Expression * Type)
  def checkSubtypeWithContext cx prf =
    checkSubtype prf >> (fn (mustBe_cx, t1, r, t2) ->
    checkSameContext mustBe_cx cx >> (fn _ ->
    OK (t1, r, t2)))

  (* Like previous op but also check that the subtype (on the left) coincides
  with the argument, returning only the predicate and supertype. *)
  op checkSubtypeWithContextAndLeftType :
     Context -> Type -> Proof -> M (Expression * Type)
  def checkSubtypeWithContextAndLeftType cx t1 prf =
    checkSubtypeWithContext cx prf >> (fn (mustBe_t1, r, t2) ->
    ensure (mustBe_t1 = t1) (wrongLeftSubtype (mustBe_t1, t1)) >> (fn _ ->
    OK (r, t2)))

  (* Like op checkSubtypeWithContext but also check that the supertype (on the
  right) coincides with the argument, returning only the predicate and
  subtype. *)
  op checkSubtypeWithContextAndRightType :
     Context -> Type -> Proof -> M (Type * Expression)
  def checkSubtypeWithContextAndRightType cx t2 prf =
    checkSubtypeWithContext cx prf >> (fn (t1, r, mustBe_t2) ->
    ensure (mustBe_t2 = t2) (wrongRightSubtype (mustBe_t2, t2)) >> (fn _ ->
    OK (t1, r)))

  (* Check proofs of subtypes with the given context, returning the subtypes,
  predicates, and supertypes. *)
  op checkSubtypesWithContext :
     Context -> Proofs -> M (Types * Expressions * Types)
  def checkSubtypesWithContext cx prfS =
    mapSeq (checkSubtypeWithContext cx) prfS >> (fn tripleS ->
    OK (unzip3 tripleS))

  (* Like previous op but also check that the subtypes (on the left) coincide
  with the argument, returning only the predicates and the supertypes. *)
  op checkSubtypesWithContextAndLeftTypes :
     Context -> Types -> Proofs -> M (Expressions * Types)
  def checkSubtypesWithContextAndLeftTypes cx tS prfS =
    checkSubtypesWithContext cx prfS >> (fn (mustBe_tS, rS, tS1) ->
    ensure (mustBe_tS = tS) (wrongLeftSubtypes (mustBe_tS, tS)) >> (fn _ ->
    OK (rS, tS1)))

  (* Check subtype relation between two record types with the same fields in
  the same order, returning the context, fields, subtype's component types,
  predicate, and supertype's component types. *)
  op checkSubtypeRecord :
     Proof -> M (Context * Fields * Types * Expression * Types)
  def checkSubtypeRecord prf =
    checkSubtype prf >> (fn (cx, t, r, t1) ->
    checkRecordType t >> (fn (fS, tS) ->
    checkRecordType t1 >> (fn (mustBe_fS, tS1) ->
    ensure (mustBe_fS = fS) (wrongFields (mustBe_fS, fS)) >> (fn _ ->
    OK (cx, fS, tS, r, tS1)))))

  (* Check subtype relation between two sum types with the same constructors
  in the same order, returning the context, constructors, subtype's component
  types, predicate, and supertype's component types. *)
  op checkSubtypeSum :
     Proof -> M (Context * Constructors * Types * Expression * Types)
  def checkSubtypeSum prf =
    checkSubtype prf >> (fn (cx, t, r, t1) ->
    checkSumType t >> (fn (cS, tS) ->
    checkSumType t1 >> (fn (mustBe_cS, tS1) ->
    ensure (mustBe_cS = cS) (wrongConstructors (mustBe_cS, cS)) >> (fn _ ->
    OK (cx, cS, tS, r, tS1)))))

  (* Check proof of well-typed expression, returning the context, expression,
  and type. *)
  op checkWTExpr : Proof -> M (Context * Expression * Type)
  def checkWTExpr prf =
    check prf >> (fn wellTypedExpr (cx, e, t) -> OK (cx, e, t)
                   | jdg -> fail("notWTExpr")) %FAIL (notWTExpr jdg))

  (* Like previous op but also check that the context coincides with the
  argument, returning only the expression and type. *)
  op checkWTExprWithContext : Context -> Proof -> M (Expression * Type)
  def checkWTExprWithContext cx prf =
    checkWTExpr prf >> (fn (mustBe_cx, t, e) ->
    checkSameContext mustBe_cx cx >> (fn _ ->
    OK (t, e)))

  (* Like previous op but also check that the type coincides with the
  argument, returning only the context and expression. *)
  op checkWTExprWithType : Type -> Proof -> M (Context * Expression)
  def checkWTExprWithType t prf =
   checkWTExpr prf >> (fn (cx, e, mustBe_t) ->
   checkSameType mustBe_t t >> (fn _ ->
   OK (cx, e)))

  (* Like previous op but also check that the context coincides with the
  argument, returning only the expression. *)
  op checkWTExprWithContextAndType :
     Context -> Type -> Proof -> M Expression
  def checkWTExprWithContextAndType cx t prf =
    checkWTExprWithType t prf >> (fn (mustBe_cx, e) ->
    checkSameContext mustBe_cx cx >> (fn _ ->
    OK e))

  (* Check proof of well-typed op instance, returning the context, operation,
  argument types, and type. *)
  op checkWTOpInstance : Proof -> M (Context * Operation * Types * Type)
  def checkWTOpInstance prf =
    checkWTExpr prf >> (fn (cx, e, t) ->
    checkOpInstance e >> (fn (o, tS) ->
    OK (cx, o, tS, t)))

  (* Check proof of well-typed application, returning the context, function,
  argument, and type. *)
  op checkWTApplication : Proof -> M (Context * Expression * Expression * Type)
  def checkWTApplication prf =
    checkWTExpr prf >> (fn (cx, e, t) ->
    checkApplication e >> (fn (e1, e2) ->
    OK (cx, e1, e2, t)))

  (* Check proof of well-typed abstraction, returning the context, bound
  variable, type of the bound variable, body, and type of the abstraction. *)
  op checkWTAbstraction :
     Proof -> M (Context * Variable * Type * Expression * Type)
  def checkWTAbstraction prf =
    checkWTExpr prf >> (fn (cx, e, t1) ->
    checkAbstraction e >> (fn (v, t, e) ->
    OK (cx, v, t, e, t1)))

  (* Check proof of well-typed application of an abstraction to some other
  expression, returning the context, bound variable, type of the bound
  variable, body, argument, and type of the application. *)
  op checkWTApplicationOfAbstraction :
     Proof -> M (Context * Variable * Type * Expression * Expression * Type)
  def checkWTApplicationOfAbstraction prf =
    checkWTExpr prf >> (fn (cx, e, t1) ->
    checkApplication e >> (fn (e, e1) ->
    checkAbstraction e >> (fn (v, t, e) ->
    OK (cx, v, t, e, e1, t1))))

  (* Check proof of well-typed application of descriptor to some other
  expression, returning the context, type (of both the descriptor and the
  application), and argument. *)
  op checkWTApplicationOfDescriptor : Proof -> M (Context * Type * Expression)
  def checkWTApplicationOfDescriptor prf =
    checkWTExpr prf >> (fn (cx, e, t) ->
    checkApplication e >> (fn (e0, e) ->
    checkDescriptor e0 >> (fn mustBe_t ->
    checkSameType mustBe_t t >> (fn _ ->
    OK (cx, t, e)))))

  (* Check proof of well-typed equality, returning the context, left-hand
  side, right-hand side, and type (type of the equality, not of the
  expressions, i.e. BOOL or some type equivalent to it). *)
  op checkWTEquality : Proof -> M (Context * Expression * Expression * Type)
  def checkWTEquality prf =
    checkWTExpr prf >> (fn (cx, e, t) ->
    checkEquality e >> (fn (e1, e2) ->
    OK (cx, e1, e2, t)))

  (* Check proof of well-typed conditional, returning the context, condition,
  branches, and type. *)
  op checkWTConditional :
     Proof -> M (Context * Expression * Expression * Expression *Type)
  def checkWTConditional prf =
    checkWTExpr prf >> (fn (cx, e, t) ->
    checkConditional e >> (fn (e0, e1, e2) ->
    OK (cx, e0, e1, e2, t)))

  (* Check proof of well-typed descriptor, returning the context, type the
  tags the descriptor, and type of the descriptor. *)
  op checkWTDescriptor : Proof -> M (Context * Type * Type)
  def checkWTDescriptor prf =
    checkWTExpr prf >> (fn (cx, e, t1) ->
    checkDescriptor e >> (fn t ->
    OK (cx, t, t1)))

  (* Check proof of well-typed projector, returning the context, fields of the
  record type that tags the projector, component types of the record type that
  tags the projector, field of the projector, and type of the projector. *)
  op checkWTProjector : Proof -> M (Context * Fields * Types * Field * Type)
  def checkWTProjector prf =
    checkWTExpr prf >> (fn (cx, e, t) ->
    checkProjector e >> (fn (fS, tS, f) ->
    OK (cx, fS, tS, f, t)))

  (* Check proof of well-typed embedder, returning the context, constructors
  of the sum type that tags the embedder, component types of the sum type that
  tags the embedder, constructor of the embedder, and type of the embedder. *)
  op checkWTEmbedder :
     Proof -> M (Context * Constructors * Types * Constructor * Type)
  def checkWTEmbedder prf =
    checkWTExpr prf >> (fn (cx, e, t) ->
    checkEmbedder e >> (fn (cS, tS, c) ->
    OK (cx, cS, tS, c, t)))

  (* Check proof of well-typed quotienter, returning the context, base type of
  the quotient type that tags the quotienter, predicate of the quotient type
  that tags the quotienter, and type of the quotienter. *)
  op checkWTQuotienter : Proof -> M (Context * Type * Expression * Type)
  def checkWTQuotienter prf =
    checkWTExpr prf >> (fn (cx, e, t1) ->
    checkQuotienter e >> (fn (t, q) ->
    OK (cx, t, q, t1)))

  (* Check proof of well-formed expression in a context that ends with a
  variable declaration, returning the context minus the variable declaration,
  variable, type of the variable, expression, and type of the expression. In
  other words, it checks a proof of the well-typedness of an abstraction body
  (the variable that the context ends with becomes the variable bound by the
  abstraction); this is used for rule exAbs. *)
  op checkWTAbstractionBody :
     Proof -> M (Context * Variable * Type * Expression * Type)
  def checkWTAbstractionBody prf =
    checkWTExpr prf >> (fn (cx1, e, t1) ->
    checkLastVar cx1 >> (fn (cx, v, t) ->
    OK (cx, v, t, e, t1)))

  (* Check proof of well-typed proposition (i.e. boolean expression),
  returning the context and expression. *)
  op checkWTProposition : Proof -> M (Context * Expression)
  def checkWTProposition prf =
    checkWTExpr prf >> (fn (cx, e, t) ->
    checkBoolean t >> (fn _ ->
    OK (cx, e)))

  (* Check proof of well-typed function (i.e. expression of arrow type),
  returning the context, expression, domain type, and range type. *)
  op checkWTFunction : Proof -> M (Context * Expression * Type * Type)
  def checkWTFunction prf =
    checkWTExpr prf >> (fn (cx, e, t) ->
    checkArrowType t >> (fn (t1, t2) ->
    OK (cx, e, t1, t2)))

  (* Check proof of well-typed predicate (i.e. boolean-valued function),
  returning the context, expression, and domain type. *)
  op checkWTPredicate : Proof -> M (Context * Expression * Type)
  def checkWTPredicate prf =
    checkWTFunction prf >> (fn (cx, e, t, t1) ->
    checkBoolean t1 >> (fn _ ->
    OK (cx, e, t)))

  (* Check proof of well-typed proposition in the given context extended with
  type variable declarations, returning the type variables and expression. In
  other words, it checks a proof of the well-typedness of an axiom (the extra
  type variables become those of the axiom); this is used for tule cxAx. *)
  op checkWTAxiom : Context -> Proof -> M (TypeVariables * Expression)
  def checkWTAxiom cx prf =
    checkWTProposition prf >> (fn (cx1, e) ->
    checkLastTypeVars cx cx1 >> (fn tvS ->
    OK (tvS, e)))

  (* Check proof of well-typed expression in cx extended by the assumption (in
  the form of an axiom) that e0 holds, returning the expression and type. In
  other words, it checks the proof of the well-typedness of the "then" branch
  of a conditional, where e0 is the condition; this is used for tule exIf. *)
  op checkWTIfThenBranch :
     Context -> Expression -> Proof -> M (Expression * Type)
  def checkWTIfThenBranch cx e0 prf =
    checkWTExpr prf >> (fn (cx1, e, t) ->
    checkLastAxiom cx cx1 e0 >> (fn _ ->
    OK (e, t)))

  (* Check proof of well-typed expression of type t in cx extended by the
  assumption (in the form of an axiom) that e0 does not hold, returning the
  expression. In other words, it checks the proof of the well-typedness of the
  "else" branch of a conditional, where e0 is the condition; this is used for
  rule exIf. *)
  op checkWTIfElseBranch :
     Context -> Expression -> Type -> Proof -> M Expression
  def checkWTIfElseBranch cx e0 t prf =
    checkWTExprWithType t prf >> (fn (cx1, e) ->
    checkLastAxiom cx cx1 (~~ e0) >> (fn _ ->
    OK e))

  (* Check proof of theorem, returning context and formula. *)
  op checkTheorem : Proof -> M (Context * Expression)
  def checkTheorem prf =
    check prf >> (fn theoreM (cx, e) -> OK (cx, e)
                   | jdg -> FAIL (notTheorem jdg))

  (* Like previous op but also check that the context coincides with the
  argument, returning only the formula. *)
  op checkTheoremWithContext : Context -> Proof -> M Expression
  def checkTheoremWithContext cx prf =
    checkTheorem prf >> (fn (mustBe_cx, e) ->
    checkSameContext mustBe_cx cx >> (fn _ ->
    OK e))

  (* Like previous op but also check that the formula coincides with the
  argument. *)
  op checkTheoremWithContextAndFormula :
     Context -> Expression -> Proof -> M ()
  def checkTheoremWithContextAndFormula cx e prf =
    checkTheoremWithContext cx prf >> (fn mustBe_e ->
    ensure (mustBe_e = e) (wrongTheorem (mustBe_e, e)) >> (fn _ ->
    OK ()))

  (* Like op checkTheorem but also check that the formula coincides with the
  argument, returning only the context. *)
  op checkTheoremWithFormula : Expression -> Proof -> M Context
  def checkTheoremWithFormula e prf =
    checkTheorem prf >> (fn (cx, mustBe_e) ->
    ensure (mustBe_e = e) (wrongTheorem (mustBe_e, e)) >> (fn _ ->
    OK cx))

  (* Check proof of equality theorem, returning the context and left- and
  right-hand side expressions. *)
  op checkTheoremEquality : Proof -> M (Context * Expression * Expression)
  def checkTheoremEquality prf =
    checkTheorem prf >> (fn (cx, e) ->
    checkEquality e >> (fn (e1, e2) ->
    OK (cx, e1, e2)))

  (* Like previous op but also check that the left-hand expression coincides
  with the argument, returning only the context and right-hand expression. *)
  op checkTheoremEqualityWithLeftExpr :
     Expression -> Proof -> M (Context * Expression)
  def checkTheoremEqualityWithLeftExpr e1 prf =
    checkTheoremEquality prf >> (fn (cx, mustBe_e1, e2) ->
    ensure (mustBe_e1 = e1) (wrongLeftExpression (mustBe_e1, e1)) >> (fn _ ->
    OK (cx, e2)))

  (* Like previous op but also check that the context coincides with the
  argument, returning only the right-hand side expression. *)
  op checkTheoremEqualityWithContextAndLeftExpr :
     Context -> Expression -> Proof -> M Expression
  def checkTheoremEqualityWithContextAndLeftExpr cx e1 prf =
    checkTheoremEqualityWithLeftExpr e1 prf >> (fn (mustBe_cx, e2) ->
    checkSameContext mustBe_cx cx >> (fn _ ->
    OK e2))

  (* Check proof of equality theorem in cx extended with the assumption that d
  holds and such that the left-hand side coincides with e.  In other words, it
  checks a proof of the equality theorems needed for rule thIfSubst, where d
  is either the condition or its negation, and correspondingly e is the "then"
  or "else" branch. *)
  op checkTheoremEqualityIfSubst :
     Context -> Expression -> Expression -> Proof -> M Expression
  def checkTheoremEqualityIfSubst cx d e prf =
    checkTheoremEqualityWithLeftExpr e prf >> (fn (cx1, e1) ->
    checkLastAxiom cx cx1 d >> (fn _ ->
    OK e1))

  (* Check proof of equality theorem in context cx extended with the
  assumption that e0 holds and such that the left-hand side is e1, returning
  the right-hand side expression. In other words, it checks a proof of the
  equality theorem needed for rule thIf, where e0 is the condition and e1 is
  the "then" branch. *)
  op checkTheoremEqualityIfThen :
     Context -> Expression -> Expression -> Proof -> M Expression
  def checkTheoremEqualityIfThen cx e0 e1 prf =
    checkTheoremEqualityWithLeftExpr e1 prf >> (fn (cx1, e) ->
    checkLastAxiom cx cx1 e0 >> (fn _ ->
    OK e))

  (* Check proof of equality theorem that (e2 == e) in context cx extended
  with the assumption that e0 does not hold. In other words, it checks a proof
  of the equality theorem needed for rule thIf, where e0 is the condition, e2
  is the "else" branch, and "e" is the expression that the "then" branch is
  equal to. *)
  op checkTheoremEqualityIfElse :
     Context -> Expression -> Expression -> Expression -> Proof -> M ()
  def checkTheoremEqualityIfElse cx e0 e2 e prf =
    checkTheoremWithFormula (e2 == e) prf >> (fn cx1 ->
    checkLastAxiom cx cx1 (~~ e0) >> (fn _ ->
    OK ()))

  (* Check proof of existence and uniqueness theorem needed for rule cxOdef.
  More precisely, given cx, t, and tvS, check that the proof proves
    theoreM (cx ++ multiTypeVarDecls tvS1,
             EX1 (v, typeSubstInType tsbs t, (VAR v == e)))
  for some tvS1, v, e, and tsbs such that isTypeSubstFrom? (tsbs, tvS, map VAR
  tvS1) holds (cf. cxOdef in spec Provability); return tvS1, v, and e. *)
  op checkTheoremOpDef : Context -> Type -> TypeVariables -> Proof ->
                         M (TypeVariables * Variable * Expression)
  def checkTheoremOpDef cx t tvS prf =
    checkTheorem prf >> (fn (cx1, e) ->
    checkLastTypeVars cx cx1 >> (fn tvS1 ->
    checkTypeSubstitution tvS (map VAR tvS1) >> (fn tsbs ->
    checkUniqueExistential e >> (fn (v, t1, e) ->
    checkSameType t1 (typeSubstInType tsbs t) >> (fn _ ->
    checkEquality e >> (fn (mustBe_v, e) ->
    ensure (mustBe_v = VAR v) (wrongLeftExpression (mustBe_v, VAR v)) >> (fn _ ->
    OK (tvS, v, e))))))))

  (* Check proof of reflexivity theorem needed for rule tyQuot. More
  precisely, check that the proof proves
    theoreM (cx, FA (v, t, q @ PAIR (t, t, VAR v, VAR v)))
  for some cx, v, t, and q; return cx, v, t, and q. *)
  op checkTheoremReflexivity :
     Proof -> M (Context * Variable * Type * Expression)
  def checkTheoremReflexivity prf =
    checkTheorem prf >> (fn (cx, e) ->
    checkUniversal e >> (fn (v, t, e) ->
    checkApplication e >> (fn (q, mustBe_v_v) ->
    checkSameExpr mustBe_v_v (PAIR (t, t, VAR v, VAR v)) >> (fn _ ->
    OK (cx, v, t, q)))))

  (* Check proof of symmetry theorem needed for rule tyQuot. More precisely,
  given cx, t, and q, check that the proof proves
    theoreM (cx, FA2 (v1, t, v2, t,
                      q @ PAIR (t, t, VAR v1, VAR v2) ==>
                      q @ PAIR (t, t, VAR v2, VAR v1)))
  for some distinct v1 and v2. *)
  op checkTheoremSymmetry :
     Context -> Type -> Expression -> Proof -> M ()
  def checkTheoremSymmetry cx t q prf =
    checkTheoremWithContext cx prf >> (fn e ->
    checkUniversal e >> (fn (v1, mustBe_t, e) ->
    checkSameType mustBe_t t >> (fn _ ->
    checkUniversal e >> (fn (v2, mustBe_t, e) ->
    checkSameType mustBe_t t >> (fn _ ->
    ensure (v1 ~= v2) (nonDistinctVariables (v1, v2)) >> (fn _ ->
    checkSameExpr e (q @ PAIR (t, t, VAR v1, VAR v2) ==>
                     q @ PAIR (t, t, VAR v2, VAR v1)) >> (fn _ ->
    OK ())))))))

  (* Check proof of transitivity theorem needed for rule tyQuot. More
  precisely, given cx, t, and q, check that the proof proves
    theoreM (cx, FA3 (v1, t, v2, t, v3, t,
                      q @ PAIR (t, t, VAR v1, VAR v2) &&&
                      q @ PAIR (t, t, VAR v2, VAR v3) ==>
                      q @ PAIR (t, t, VAR v1, VAR v3)))
  for some distinct v1, v2, and v3. *)
  op checkTheoremTransitivity : Context -> Type -> Expression -> Proof -> M ()
  def checkTheoremTransitivity cx t q prf =
    checkTheoremWithContext cx prf >> (fn e ->
    checkUniversal e >> (fn (v1, mustBe_t, e) ->
    checkSameType mustBe_t t >> (fn _ ->
    checkUniversal e >> (fn (v2, mustBe_t, e) ->
    checkSameType mustBe_t t >> (fn _ ->
    checkUniversal e >> (fn (v3, mustBe_t, e) ->
    checkSameType mustBe_t t >> (fn _ ->
    ensure (v1 ~= v2) (nonDistinctVariables (v1, v2)) >> (fn _ ->
    ensure (v2 ~= v3) (nonDistinctVariables (v2, v3)) >> (fn _ ->
    ensure (v3 ~= v1) (nonDistinctVariables (v3, v1)) >> (fn _ ->
    checkSameExpr e (q @ PAIR (t, t, VAR v1, VAR v2) &&&
                     q @ PAIR (t, t, VAR v2, VAR v3) ==>
                     q @ PAIR (t, t, VAR v1, VAR v3))))))))))))

  % we finally define op check:

  def checkInt = fn

    %%%%%%%%%% well-formed contexts:
    | cxMT ->
      OK (wellFormedContext empty)
    | cxTdec (prf, tn, n) ->
      checkWFContext prf >> (fn cx ->
      ensure (~(tn in? contextTypes cx))
             (typeAlreadyDeclared (cx, tn)) >> (fn _ ->
      ensure (n >= 0) (negativeTypeArity (tn, n)) >> (fn _ ->
      OK (wellFormedContext (cx <| typeDeclaration (tn, n))))))
    | cxOdec (prf, prf1, o) ->
      checkWFContext prf >> (fn cx ->
      ensure (~(o in? contextOps cx)) (opAlreadyDeclared (cx, o)) >> (fn _ ->
      checkWFPolyType cx prf1 >> (fn (tvS, t) ->
      OK (wellFormedContext (cx <| opDeclaration (o, tvS, t))))))
    | cxTdef (prf, prf1, tn) ->
      checkWFContext prf >> (fn cx ->
      checkTypeDecl cx tn >> (fn(n:Nat) ->
      ensure (~(contextDefinesType? (cx, tn)))
             (typeAlreadyDefined (cx, tn)) >> (fn _ ->
      checkWFPolyType cx prf1 >> (fn (tvS, t) ->
      ensure (length tvS = n) (wrongTypeArity (tn, n, length tvS)) >> (fn _ ->
      OK (wellFormedContext (cx <| typeDefinition (tn, tvS, t))))))))
    | cxOdef (prf, prf1, o) ->
      checkWFContext prf >> (fn cx ->
      checkOpDecl cx o >> (fn (tvS, t) ->
      ensure (~(contextDefinesOp? (cx, o))) (opAlreadyDefined (cx, o)) >> (fn _ ->
      checkTheoremOpDef cx t tvS prf1 >> (fn (tvS1, v, e) ->
      ensure (~(o in? exprOps e)) (opInOpDefTheorem (o, e)) >> (fn _ ->
      (let e1:Expression = exprSubst v (OPI (o, map VAR tvS1)) e in
      OK (wellFormedContext (cx <| opDefinition (o, tvS1, e1)))))))))
    | cxAx (prf, prf1, an) ->
      checkWFContext prf >> (fn cx ->
      ensure (~(an in? contextAxioms cx))
             (axiomAlreadyDeclared (cx, an)) >> (fn _ ->
      checkWTAxiom cx prf1 >> (fn (tvS, e) ->
      OK (wellFormedContext (cx <| axioM (an, tvS, e))))))
    | cxTVdec (prf, tv) ->
      checkWFContext prf >> (fn cx ->
      ensure (~(tv in? contextTypeVars cx))
             (typeVarAlreadyDeclared (cx, tv)) >> (fn _ ->
      OK (wellFormedContext (cx <| typeVarDeclaration tv))))
    | cxVdec (prf, prf1, v) ->
      checkWFContext prf >> (fn cx ->
      ensure (~(v in? contextVars cx)) (varAlreadyDeclared (cx, v)) >> (fn _ ->
      checkWFTypeWithContext cx prf1 >> (fn t ->
      OK (wellFormedContext (cx <| varDeclaration (v, t))))))

    %%%%%%%%%% well-formed specs:
    | speC prf ->
      checkWFContext prf >> (fn cx ->
      ensure (contextTypeVars cx = empty) (typeVarInSpec cx) >> (fn _ ->
      ensure (contextVars cx = empty) (varInSpec cx) >> (fn _ ->
      OK (wellFormedSpec cx))))

    %%%%%%%%%% well-formed types:
    | tyBool prf ->
      checkWFContext prf >> (fn cx ->
      OK (wellFormedType (cx, BOOL)))
    | tyVar (prf, tv) ->
      checkWFContext prf >> (fn cx ->
      ensure (tv in? contextTypeVars cx) (typeVarNotDeclared (cx, tv)) >> (fn _ ->
      OK (wellFormedType (cx, VAR tv))))
    | tyInst (prf, prfS, tn) ->
      checkWFContext prf >> (fn cx ->
      checkTypeDeclWithArity cx tn (length prfS) >> (fn _ ->
      checkWFTypesWithContext cx prfS >> (fn tS ->
      OK (wellFormedType (cx, TYPE (tn, tS))))))
    | tyArr (prf1, prf2) ->
      checkWFType prf1 >> (fn (cx, t1) ->
      checkWFTypeWithContext cx prf2 >> (fn t2 ->
      OK (wellFormedType (cx, t1 --> t2))))
    | tyRec (prf, prfS, fS) ->
      checkWFContext prf >> (fn cx ->
      ensure (length prfS = length fS) wrongNumberOfProofs >> (fn _ ->
      ensure (noRepetitions? fS) (nonDistinctFields fS) >> (fn _ ->
      checkWFTypesWithContext cx prfS >> (fn tS ->
      OK (wellFormedType (cx, RECORD (fS, tS)))))))
    | tySum (prfS, cS) ->
      ensure (length prfS = length cS) wrongNumberOfProofs >> (fn _ ->
      ensure (noRepetitions? cS) (nonDistinctConstructors cS) >> (fn _ ->
      ensure (nonEmpty? cS) noConstructors >> (fn _ ->
      checkWFTypes prfS >> (fn (cx, tS) ->
      OK (wellFormedType (cx, SUM (cS, tS)))))))
    | tyRestr prf ->
      checkWTPredicate prf >> (fn (cx, r, t) ->
      ensure (exprFreeVars r = empty) (badRestrictionType (t, r)) >> (fn _ ->
      OK (wellFormedType (cx, t\r))))
    | tyQuot (prf1, prf2, prf3) ->
      checkTheoremReflexivity prf1 >> (fn (cx, v, t, q) ->
      checkTheoremSymmetry cx t q prf2 >> (fn _ ->
      checkTheoremTransitivity cx t q prf3 >> (fn _ ->
      ensure (exprFreeVars q = empty) (badQuotientType (t, q)) >> (fn _ ->
      OK (wellFormedType (cx, t/q))))))

    %%%%%%%%%% type equivalence:
    | teDef (prf, prfS, tn) ->
      checkWFContext prf >> (fn cx ->
      checkTypeDef cx tn >> (fn (tvS, t) ->
      checkWFTypesWithContext cx prfS >> (fn tS ->
      checkTypeSubstitution tvS tS >> (fn tsbs ->
      OK (typeEquivalence (cx, TYPE (tn, tS), typeSubstInType tsbs t))))))
    | teRefl prf ->
      checkWFType prf >> (fn (cx, t) ->
      OK (typeEquivalence (cx, t, t)))
    | teSymm prf ->
      checkTypeEquiv prf >> (fn (cx, t1, t2) ->
      OK (typeEquivalence (cx, t2, t1)))
    | teTrans (prf1, prf2) ->
      checkTypeEquiv prf1 >> (fn (cx, t1, t2) ->
      checkTypeEquivWithContextAndLeftType cx t2 prf2 >> (fn t3 ->
      OK (typeEquivalence (cx, t1, t3))))
    | teInst (prf, prfS) ->
      checkWFTypeInstance prf >> (fn (cx, tn, tS) ->
      checkTypeEquivsWithContextAndLeftTypes cx tS prfS >> (fn tS1 ->
      OK (typeEquivalence (cx, TYPE (tn, tS), TYPE (tn, tS1)))))
    | teArr (prf1, prf2) ->
      checkTypeEquiv prf1 >> (fn (cx, t1, s1) ->
      checkTypeEquivWithContext cx prf2 >> (fn (t2, s2) ->
      OK (typeEquivalence (cx, t1 --> t2, s1 --> s2))))
    | teRec (prf, prfS, fS) ->
      checkWFContext prf >> (fn cx ->
      ensure (length prfS = length fS) wrongNumberOfProofs >> (fn _ ->
      ensure (noRepetitions? fS) (nonDistinctFields fS) >> (fn _ ->
      checkTypeEquivsWithContext cx prfS >> (fn (tS, tS1) ->
      OK (typeEquivalence (cx, RECORD (fS, tS), RECORD (fS, tS1)))))))
    | teSum (prfS, cS) ->
      ensure (length prfS = length cS) wrongNumberOfProofs >> (fn _ ->
      ensure (noRepetitions? cS) (nonDistinctConstructors cS) >> (fn _ ->
      ensure (nonEmpty? cS) noConstructors >> (fn _ ->
      checkTypeEquivs prfS >> (fn (cx, tS, tS1) ->
      OK (typeEquivalence (cx, SUM (cS, tS), SUM (cS, tS1)))))))
    | teRestr (prf1, prf2, prf3) ->
      checkWFRestrictionType prf1 >> (fn (cx, t, r) ->
      checkTypeEquivWithContextAndLeftType cx t prf2 >> (fn t1 ->
      checkTheoremEqualityWithContextAndLeftExpr cx r prf3 >> (fn r1 ->
      OK (typeEquivalence (cx, t\r, t1\r1)))))
    | teQuot (prf1, prf2, prf3) ->
      checkWFQuotientType prf1 >> (fn (cx, t, q) ->
      checkTypeEquivWithContextAndLeftType cx t prf2 >> (fn t1 ->
      checkTheoremEqualityWithContextAndLeftExpr cx q prf3 >> (fn q1 ->
      OK (typeEquivalence (cx, t/q, t1/q1)))))
    | teRecOrd (prf, prm) ->
      checkWFRecordType prf >> (fn (cx, fS, tS) ->
      checkPermutation prm >> (fn(prm1:Permutation) ->
      ensure (length prm1 = length fS) (wrongPermutationLength prm) >> (fn _ ->
      OK (typeEquivalence (cx, RECORD (fS, tS),
                               RECORD (permute(fS,prm1), permute(tS,prm1)))))))
    | teSumOrd (prf, prm) ->
      checkWFSumType prf >> (fn (cx, cS, tS) ->
      checkPermutation prm >> (fn(prm1:Permutation) ->
      ensure (length prm1 = length cS) (wrongPermutationLength prm) >> (fn _ ->
      OK (typeEquivalence (cx, SUM (cS, tS),
                               SUM (permute(cS,prm1), permute(tS,prm1)))))))

    %%%%%%%%%% subtyping:
    | stRestr prf ->
      checkWFRestrictionType prf >> (fn (cx, t, r) ->
      OK (subType (cx, t\r, r, t)))
    | stRefl (prf, v) ->
      checkWFType prf >> (fn (cx, t) ->
      let r:Expression = FN (v, t, TRUE) in
      OK (subType (cx, t, r, t)))
    | stArr (prf, prf1, v, v1) ->
      checkWFType prf >> (fn (cx, t) ->
      checkSubtypeWithContext cx prf1 >> (fn (t1, r, t2) ->
      ensure (v ~= v1) (nonDistinctVariables (v, v1)) >> (fn _ ->
      (let r1:Expression = FN (v, t --> t2, FA (v1, t, r @ (VAR v @ VAR v1))) in
      OK (subType (cx, t --> t1, r1, t --> t2))))))
    | stRec (prf, prfS, v) ->
      checkWFRecordType prf >> (fn (cx, fS, tS) ->
      checkSubtypesWithContextAndLeftTypes cx tS prfS >> (fn (rS, tS1) ->
      (let conjuncts:Expressions = seq (fn(i:Nat) ->
        if i < length fS then Some ((rS@i) @ DOT (VAR v, RECORD(fS,tS1), fS@i))
        else None) in
      let r:Expression = FN (v, RECORD (fS, tS1), ANDn conjuncts) in
      OK (subType (cx, RECORD (fS, tS), r, RECORD (fS, tS1))))))
    | stSum (prf, prfS, v, v1) ->
      checkWFSumType prf >> (fn (cx, cS, tS) ->
      checkSubtypesWithContextAndLeftTypes cx tS prfS >> (fn (rS, tS1) ->
      (let disjuncts:Expressions = seq (fn(i:Nat) ->
        if i < length cS then
          Some (EX (v1, tS1@i, VAR v == EMBED (SUM(cS,tS1), cS@i) @ VAR v1
                               &&& rS@i @ VAR v1))
        else None) in
      ensure (v ~= v1) (nonDistinctVariables (v, v1)) >> (fn _ ->
      (let r:Expression = FN (v, SUM (cS, tS1), ORn disjuncts) in
      OK (subType (cx, SUM (cS, tS), r, SUM (cS, tS1))))))))
    | stTE (prf, prf1, prf2) ->
      checkSubtype prf >> (fn (cx, t1, r, t2) ->
      checkTypeEquivWithContextAndLeftType cx t1 prf1 >> (fn s1 ->
      checkTypeEquivWithContextAndLeftType cx t2 prf2 >> (fn s2 ->
      OK (subType (cx, s1, r, s2)))))

    %%%%%%%%%% well-typed expressions:
    | exVar (prf, v) ->
      checkWFContext prf >> (fn cx ->
      checkVarDecl cx v >> (fn t ->
      OK (wellTypedExpr (cx, VAR v, t))))
    | exOp (prf, prfS, o) ->
      checkWFContext prf >> (fn cx ->
      checkOpDecl cx o >> (fn (tvS, t) ->
      checkWFTypesWithContext cx prfS >> (fn tS ->
      checkTypeSubstitution tvS tS >> (fn tsbs ->
      OK (wellTypedExpr (cx, OPI (o, tS), typeSubstInType tsbs t))))))
    | exApp (prf, prf1) ->
      checkWTFunction prf >> (fn (cx, e1, t1, t2) ->
      checkWTExprWithContextAndType cx t1 prf1 >> (fn e2 ->
      OK (wellTypedExpr (cx, e1 @ e2, t2))))
    | exAbs prf ->
      checkWTAbstractionBody prf >> (fn (cx, v, t, e, t1) ->
      OK (wellTypedExpr (cx, FN (v, t, e), t --> t1)))
    | exEq (prf1, prf2) ->
      checkWTExpr prf1 >> (fn (cx, e1, t) ->
      checkWTExprWithContextAndType cx t prf2 >> (fn e2 ->
      OK (wellTypedExpr (cx, e1 == e2, BOOL))))
    | exIf (prf0, prf1, prf2) ->
      checkWTProposition prf0 >> (fn (cx, e0) ->
      checkWTIfThenBranch cx e0 prf1 >> (fn (e1, t) ->
      checkWTIfElseBranch cx e0 t prf2 >> (fn e2 ->
      OK (wellTypedExpr (cx, IF (e0, e1, e2), t)))))
    | exIf0 (prf0, prf1, prf2) ->
      checkWTProposition prf0 >> (fn (cx, e0) ->
      checkWTExprWithContext cx prf1 >> (fn (e1, t) ->
      checkWTExprWithContextAndType cx t prf2 >> (fn e2 ->
      OK (wellTypedExpr (cx, IF (e0, e1, e2), t)))))
    | exThe prf ->
      checkWFType prf >> (fn (cx, t) ->
      OK (wellTypedExpr (cx, IOTA t, ((t --> BOOL) \ EX1q t) --> t)))
    | exProj (prf, f) ->
      checkWFRecordType prf >> (fn (cx, fS, tS) ->
      checkFieldType f (fS, tS) >> (fn t ->
      OK (wellTypedExpr (cx, PROJECT (RECORD(fS,tS), f),
                             RECORD(fS,tS) --> t))))
    | exEmbed (prf, c) ->
      checkWFSumType prf >> (fn (cx, cS, tS) ->
      checkConstructorType c (cS, tS) >> (fn t ->
      OK (wellTypedExpr (cx, EMBED (SUM(cS,tS), c), t --> SUM (cS, tS)))))
    | exQuot prf ->
      checkWFQuotientType prf >> (fn (cx, t, q) ->
      OK (wellTypedExpr (cx, QUOT (t/q), t --> t/q)))
    | exSuper (prf1, prf2) ->
      checkWTExpr prf1 >> (fn (cx, e, t) ->
      checkSubtypeWithContextAndLeftType cx t prf2 >> (fn (r, t1) ->
      OK (wellTypedExpr (cx, e, t1))))
    | exSub (prf1, prf2, prf3) ->
      checkWTExpr prf1 >> (fn (cx, e, t1) ->
      checkSubtypeWithContextAndRightType cx t1 prf2 >> (fn (t, r) ->
      checkTheoremWithContextAndFormula cx (r @ e) prf3 >> (fn _ ->
      OK (wellTypedExpr (cx, e, t)))))
    | exAbsAlpha (prf, v1) ->
      checkWTAbstraction prf >> (fn (cx, v, t, e, t1) ->
      ensure (v1 nin? (exprFreeVars e \/ captVars v e))
             (badSubstitution (v, VAR v1)) >> (fn _ ->
      OK (wellTypedExpr (cx, FN (v1, t, exprSubst v (VAR v1) e), t1))))

    %%%%%%%%%% theorems:
    | thAx (prf, prfS, an) ->
      checkWFContext prf >> (fn cx ->
      checkAxiom cx an >> (fn (tvS, e) ->
      checkWFTypesWithContext cx prfS >> (fn tS ->
      checkTypeSubstitution tvS tS >> (fn tsbs ->
      OK (theoreM (cx, typeSubstInExpr tsbs e))))))
    | thDef (prf, prfS, o) ->
      checkWFContext prf >> (fn cx ->
      checkOpDef cx o >> (fn (tvS, e) ->
      checkWFTypesWithContext cx prfS >> (fn tS ->
      checkTypeSubstitution tvS tS >> (fn tsbs ->
      OK (theoreM (cx, OPI (o, tS) == typeSubstInExpr tsbs e))))))
    | thRefl prf ->
      checkWTExpr prf >> (fn (cx, e, _) ->
      OK (theoreM (cx, e == e)))
    | thSymm prf ->
      checkTheoremEquality prf >> (fn (cx, e1, e2) ->
      OK (theoreM (cx, e2 == e1)))
    | thTrans (prf1, prf2) ->
      checkTheoremEquality prf1 >> (fn (cx, e1, e2) ->
      checkTheoremEqualityWithContextAndLeftExpr cx e2 prf2 >> (fn e3 ->
      OK (theoreM (cx, e1 == e3))))
    | thOpSubst (prf, prfS) ->
      checkWTOpInstance prf >> (fn (cx, o, tS, _) ->
      checkTypeEquivsWithContextAndLeftTypes cx tS prfS >> (fn tS1 ->
      OK (theoreM (cx, OPI (o, tS) == OPI (o, tS1)))))
    | thAppSubst (prf, prf1, prf2) ->
      checkWTApplication prf >> (fn (cx, e1, e2, _) ->
      checkTheoremEqualityWithContextAndLeftExpr cx e1 prf1 >> (fn d1 ->
      checkTheoremEqualityWithContextAndLeftExpr cx e2 prf2 >> (fn d2 ->
      OK (theoreM (cx, e1 @ e2 == d1 @ d2)))))
    | thAbsSubst (prf1, prf2, prf3) ->
      checkWTAbstraction prf1 >> (fn (cx, v, t, e, _) ->
      checkTypeEquivWithContextAndLeftType cx t prf2 >> (fn t1 ->
      (let cx1 = cx <| varDeclaration (v, t) in
      checkTheoremEqualityWithContextAndLeftExpr cx1 e prf3 >> (fn e1 ->
      OK (theoreM (cx, FN (v, t, e) == FN (v, t1, e1)))))))
    | thEqSubst (prf, prf1, prf2) ->
      checkWTEquality prf >> (fn (cx, e1, e2, _) ->
      checkTheoremEqualityWithContextAndLeftExpr cx e1 prf1 >> (fn d1 ->
      checkTheoremEqualityWithContextAndLeftExpr cx e2 prf2 >> (fn d2 ->
      OK (theoreM (cx, (e1 == e2) == (d1 == d2))))))
    | thIfSubst (prf, prf0, prf1, prf2) ->
      checkWTConditional prf >> (fn (cx, e0, e1, e2, _) ->
      checkTheoremEqualityWithContextAndLeftExpr cx e0 prf0 >> (fn d0 ->
      checkTheoremEqualityIfSubst cx     e0  e1 prf1 >> (fn d1 ->
      checkTheoremEqualityIfSubst cx (~~ e0) e2 prf2 >> (fn d2 ->
      OK (theoreM (cx, IF (e0, e1, e2) == IF (d0, d1, d2)))))))
    | thTheSubst (prf1, prf2) ->
      checkWTDescriptor prf1 >> (fn (cx, t, _) ->
      checkTypeEquivWithContextAndLeftType cx t prf2 >> (fn t1 ->
      OK (theoreM (cx, IOTA t == IOTA t1))))
    | thProjSubst (prf1, prf2) ->
      checkWTProjector prf1 >> (fn (cx, fS, tS, f, _) ->
      checkRecordTypeEquivWithContextAndLeftType cx (RECORD(fS,tS)) prf2 >>
        (fn (fS1, tS1) ->
      OK (theoreM (cx, PROJECT (RECORD(fS,tS), f) ==
                       PROJECT (RECORD(fS1,tS1), f)))))
    | thEmbedSubst (prf1, prf2) ->
      checkWTEmbedder prf1 >> (fn (cx, cS, tS, c, _) ->
      checkSumTypeEquivWithContextAndLeftType cx (SUM(cS,tS)) prf2 >>
        (fn (cS1, tS1) ->
      OK (theoreM (cx, EMBED (SUM(cS,tS), c) ==
                       EMBED (SUM(cS1,tS1), c)))))
    | thQuotSubst (prf1, prf2) ->
      checkWTQuotienter prf1 >> (fn (cx, t, q, _) ->
      checkQuotientTypeEquivWithContextAndLeftType cx (t/q) prf2 >>
        (fn (t1, q1) ->
      OK (theoreM (cx, QUOT (t/q) == QUOT (t1/q1)))))
    | thSubst (prf1, prf2) ->
      checkTheorem prf1 >> (fn (cx, e) ->
      checkTheoremEqualityWithContextAndLeftExpr cx e prf2 >> (fn e1 ->
      OK (theoreM (cx, e1))))
    | thBool (prf, v, v1) ->
      checkWFContext prf >> (fn cx ->
      ensure (v ~= v1) (nonDistinctVariables (v, v1)) >> (fn _ ->
      OK (theoreM (cx, FA (v, BOOL --> BOOL,
                           VAR v @ TRUE &&& VAR v @ FALSE
                           <==>
                           FA (v1, BOOL, VAR v @ VAR v1))))))
    | thExt (prf, v, v1, v2) ->
      checkWFArrowType prf >> (fn (cx, t, t1) ->
      ensure (v  ~= v1) (nonDistinctVariables (v,  v1)) >> (fn _ ->
      ensure (v1 ~= v2) (nonDistinctVariables (v1, v2)) >> (fn _ ->
      ensure (v2 ~= v)  (nonDistinctVariables (v2, v))  >> (fn _ ->
      OK (theoreM (cx, FA2 (v, t --> t1, v1, t --> t1,
                            VAR v == VAR v1
                            <==>
                            FA (v2, t, VAR v @ VAR v2 == VAR v1 @ VAR v2))))))))
    | thAbs prf ->
      checkWTApplicationOfAbstraction prf >> (fn (cx, v, t, e, e1, _) ->
      ensure (exprSubstOK? v e1 e) (badSubstitution (v, e1)) >> (fn _ ->
      OK (theoreM (cx, FN (v, t, e) @ e1 == exprSubst v e1 e))))
    | thIf (prf0, prf1, prf2) ->
      checkWTConditional prf0 >> (fn (cx, e0, e1, e2, _) ->
      checkTheoremEqualityIfThen cx e0 e1 prf1 >> (fn e ->
      checkTheoremEqualityIfElse cx e0 e2 e prf2 >> (fn _ ->
      OK (theoreM (cx, IF (e0, e1, e2) == e)))))
    | thThe prf ->
      checkWTApplicationOfDescriptor prf >> (fn (cx, t, e) ->
      OK (theoreM (cx, e @ ((IOTA t) @ e))))
    | thRec (prf, v, v1) ->
      checkWFRecordType prf >> (fn (cx, fS, tS) ->
      ensure (v ~= v1) (nonDistinctVariables (v, v1)) >> (fn _ ->
      (let conjuncts:Expressions = seq (fn(i:Nat) ->
        if i < length fS then
          Some (DOT (VAR v, RECORD(fS,tS), fS@i) ==
                DOT (VAR v1, RECORD(fS,tS), fS@i))
        else None) in
      OK (theoreM (cx, FA2 (v, RECORD(fS,tS), v1, RECORD(fS,tS),
                            ANDn conjuncts ==> VAR v == VAR v1))))))
    | thEmbSurj (prf, v, v1) ->
      checkWFSumType prf >> (fn (cx, cS, tS) ->
      ensure (v ~= v1) (nonDistinctVariables (v, v1)) >> (fn _ ->
      (let disjuncts:Expressions = seq (fn(i:Nat) ->
        if i < length cS then
          Some (EX (v1, tS@i, VAR v == EMBED (SUM(cS,tS), cS@i) @ VAR v1))
        else
          None) in
      OK (theoreM (cx, FA (v, SUM(cS,tS), ORn disjuncts))))))
    | thEmbDist (prf, cj, ck, vj, vk) ->
      checkWFSumType prf >> (fn (cx, cS, tS) ->
      checkConstructorType cj (cS, tS) >> (fn tj ->
      checkConstructorType ck (cS, tS) >> (fn tk ->
      ensure (vj ~= vk) (nonDistinctVariables (vj, vk)) >> (fn _ ->
      OK (theoreM (cx, FA2 (vj, tj, vk, tk,
                            EMBED (SUM(cS,tS), cj) @ VAR vj ~==
                            EMBED (SUM(cS,tS), ck) @ VAR vk)))))))
    | thEmbInj (prf, c, v, v1) ->
      checkWFSumType prf >> (fn (cx, cS, tS) ->
      ensure (v ~= v1) (nonDistinctVariables (v, v1)) >> (fn _ ->
      checkConstructorType c (cS, tS) >> (fn t ->
      OK (theoreM (cx, FA2 (v, t, v1, t,
                            VAR v ~== VAR v1 ==>
                            EMBED (SUM(cS,tS), c) @ VAR v ~==
                            EMBED (SUM(cS,tS), c) @ VAR v1))))))
    | thQuotSurj (prf, v, v1) ->
      checkWFQuotientType prf >> (fn (cx, t, q) ->
      ensure (v ~= v1) (nonDistinctVariables (v, v1)) >> (fn _ ->
      OK (theoreM (cx, FA (v, t/q,
                           EX (v1, t, QUOT (t/q) @ VAR v1 == VAR v))))))
    | thQuotEqCls (prf, v, v1) ->
      checkWFQuotientType prf >> (fn (cx, t, q) ->
      ensure (v ~= v1) (nonDistinctVariables (v, v1)) >> (fn _ ->
      OK (theoreM (cx, FA2 (v, t, v1, t,
                            q @ PAIR (t, t, VAR v, VAR v1) <==>
                            QUOT (t/q) @ VAR v == QUOT (t/q) @ VAR v1)))))
    | thProjSub (prf, v, f) ->
      checkSubtypeRecord prf >> (fn (cx, fS, tS, _, tS1) ->
      OK (theoreM (cx, FA (v, RECORD(fS,tS),
                           PROJECT (RECORD(fS,tS),  f) @ VAR v ==
                           PROJECT (RECORD(fS,tS1), f) @ VAR v))))
    | thEmbSub (prf, v, c) ->
      checkSubtypeSum prf >> (fn (cx, cS, tS, _, tS1) ->
      checkConstructorType c (cS, tS) >> (fn t ->
      OK (theoreM (cx, FA (v, t, EMBED (SUM(cS,tS),  c) @ VAR v ==
                                 EMBED (SUM(cS,tS1), c) @ VAR v)))))
    | thSub (prf1, prf2) ->
      checkSubtype prf1 >> (fn (cx, t, r, t1) ->
      checkWTExprWithContextAndType cx t prf2 >> (fn e ->
      OK (theoreM (cx, r @ e))))

    %%%%%%%%%% assumptions:
    | assume jdg ->
      OK jdg

endspec
