
(* FIXME HERE: document this! It is somewhat like Oleg's finally tagless
interpreters *)

C_DSL qualifying spec
  import C


  (* Expression combinators, which have type Monad Value *)

  (* Variables *)
  op VAR (id:Identifier) : Monad Value =
    lookupIdentifierValue id

  (* Integer constants *)
  (* FIXME HERE: do the actual type assignment of C for ints *)
  op ICONST (n : Nat) : Monad Value =
    if n in? rangeOfIntegerType T_sint then
      evaluateIntegerConstant (T_sint, n)
    else error

  (* Unary operators *)
  type Operator1 = Monad Value -> Monad Value
  op liftOperator1 (f : Value -> Monad Value) : Operator1 =
    fn m -> {val <- m; f val}

  op STAR : Operator1 = liftOperator1 readPtrValue
  op PLUS : Operator1 = liftOperator1 operator_PLUS
  op MINUS : Operator1 = liftOperator1 operator_MINUS
  op NOT : Operator1 = liftOperator1 operator_NOT
  op NEG : Operator1 = liftOperator1 operator_NEG

  (* Binary operators *)
  type Operator2 = Monad Value * Monad Value -> Monad Value
  op liftOperator2 (f : Value * Value -> Monad Value) : Operator2 =
    fn (m1,m2) -> {val1 <- m1; val2 <- m2; f (val1, val2)}

  op MUL : Operator2 = liftOperator2 operator_MUL
  op DIV : Operator2 = liftOperator2 operator_DIV
  op REM : Operator2 = liftOperator2 operator_REM
  op ADD : Operator2 = liftOperator2 operator_ADD
  op SUB : Operator2 = liftOperator2 operator_SUB
  op SHL : Operator2 = liftOperator2 operator_SHL
  op SHR : Operator2 = liftOperator2 operator_SHR
  op LT : Operator2 = liftOperator2 operator_LT
  op GT : Operator2 = liftOperator2 operator_GT
  op LE : Operator2 = liftOperator2 operator_LE
  op GE : Operator2 = liftOperator2 operator_GE
  op EQ : Operator2 = liftOperator2 operator_EQ
  op NE : Operator2 = liftOperator2 operator_NE
  op AND : Operator2 = liftOperator2 operator_AND
  op XOR : Operator2 = liftOperator2 operator_XOR
  op IOR : Operator2 = liftOperator2 operator_IOR

  op LAND : Operator2 = operator_LAND
  op LOR : Operator2 = operator_LOR

  (* Array subscripting *)
  op SUBSCRIPT : Operator2 = fn (m1,m2) -> STAR (ADD (m1,m2))


  (* LValue combinators, which have type Monad (Type * ObjectDesignator) *)

  type LValue = Type * ObjectDesignator

  op LVAR (id:Identifier) : Monad LValue =
    {(tp,ptr) <- lookupIdentifier id;
     case ptr of
       | ObjPointer d -> return (tp,d)
       | _ -> error}

  op ADDR (e : Monad LValue) : Monad Value =
    {(tp,d) <- e;
     return (V_pointer (tp, ObjPointer d))}

  op LSTAR (m : Monad Value) : Monad LValue =
    {val <- m;
     case val of
       | V_pointer (tp, ObjPointer d) -> return (tp, d)
       | _ -> error}

  (* Array subscripting *)
  op LSUBSCRIPT (arr : Monad Value, ind : Monad Value) : Monad LValue =
    LSTAR (ADD (arr, ind))


  (* Statement combinators, which have type Monad () *)

  (* Assignment, which takes expressions lhs and rhs and performs *lhs = rhs *)
  op ASSIGN (lhs : Monad LValue, rhs : Monad Value) : Monad () =
    {(tp, d) <- lhs; rhs_val <- rhs;
     assignValue (Res_pointer (tp, ObjPointer d), rhs_val)}

  (* If-then-else statements *)
  op IFTHENELSE (expr : Monad Value,
                 then_branch : Monad (), else_branch : Monad ()) : Monad () =
    {condition <- expr;
     isZero <- zeroScalarValue? condition;
     if ~ isZero then then_branch else else_branch}

  (* While statements *)
  op WHILE (expr : Monad Value, body : Monad ()) : Monad () =
    mfix (fn recurse -> fn unit ->
          {condition <- expr;
           isZero <- zeroScalarValue? condition;
           if isZero then return () else
             {_ <- body; recurse ()}}) ()

  (* Statement blocks, with new bound variables at the beginning. The body gets
     passed *pointers to* these new variables, not their values, to enable
     assignment; for instance,

     BLOCK ([("x",T_sint)], fn [x] -> ASSIGN (x, INT 1))

     represents the C code

     { int x; *(&x) = 1; }
    *)
  op BLOCK (vars : List (Identifier * Type), body : List (Monad ())) : Monad () =
    {var_addrs <- mapM (fn (id,tp) ->
                          addLocalBinding (id, V_undefined tp)) vars;
     _ <- mapM id body;
     return ()}


  (* Function combinator *)
  op FUNCTION (retType : Type, params : List (Identifier * Type),
               body : List Value -> Monad ()) : CFunction =
    makeCFunction (retType, params,
                   {var_addrs <- mapM (fn (id,_) -> lookupIdentifierAddr id) params;
                    body var_addrs})

end-spec
