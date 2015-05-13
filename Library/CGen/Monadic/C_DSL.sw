
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
  op BLOCK (vars : List (TypeName * Identifier), body : List (Monad ())) : Monad () =
    {var_addrs <- mapM (fn (tp_name,id) ->
                          {tp <- expandTypeNameM tp_name;
                           addLocalBinding (id, V_undefined tp)}) vars;
     _ <- mapM id body;
     return ()}


  (* Function combinator *)
  op FUNCTION (retType : Type, params : List (Identifier * Type),
               body : List Value -> Monad ()) : CFunction =
    makeCFunction (retType, params,
                   {var_addrs <- mapM (fn (id,_) -> lookupIdentifierAddr id) params;
                    body var_addrs})


  (*** Theorems ***)

  (** Expressions **)

  theorem VAR_correct is
    fa (id) VAR id = expressionValueM (evaluate (E_ident id))

  theorem ICONST_correct is
    fa (n) ICONST n = expressionValueM (evaluate (E_const (T_sint, n)))

  (* Unary operators *)

  theorem STAR_correct is
    fa (e)
      STAR (expressionValueM (evaluate e))
      = expressionValueM (evaluate (E_unary (UOp_STAR, e)))

  theorem PLUS_correct is
    fa (e)
      PLUS (expressionValueM (evaluate e))
      = expressionValueM (evaluate (E_unary (UOp_PLUS, e)))

  theorem MINUS_correct is
    fa (e)
      MINUS (expressionValueM (evaluate e))
      = expressionValueM (evaluate (E_unary (UOp_MINUS, e)))

  theorem NOT_correct is
    fa (e)
      NOT (expressionValueM (evaluate e))
      = expressionValueM (evaluate (E_unary (UOp_NOT, e)))

  theorem NEG_correct is
    fa (e)
      NEG (expressionValueM (evaluate e))
      = expressionValueM (evaluate (E_unary (UOp_NEG, e)))

  (* Binary operators *)

  theorem MUL_correct is
    fa (e1,e2)
      MUL (expressionValueM (evaluate e1),
           expressionValueM (evaluate e2))
      = expressionValueM (evaluate (E_binary (e1, BinOp_MUL, e2)))

  theorem DIV_correct is
    fa (e1,e2)
      DIV (expressionValueM (evaluate e1),
           expressionValueM (evaluate e2))
      = expressionValueM (evaluate (E_binary (e1, BinOp_DIV, e2)))

  theorem REM_correct is
    fa (e1,e2)
      REM (expressionValueM (evaluate e1),
           expressionValueM (evaluate e2))
      = expressionValueM (evaluate (E_binary (e1, BinOp_REM, e2)))

  theorem ADD_correct is
    fa (e1,e2)
      ADD (expressionValueM (evaluate e1),
           expressionValueM (evaluate e2))
      = expressionValueM (evaluate (E_binary (e1, BinOp_ADD, e2)))

  theorem SUB_correct is
    fa (e1,e2)
      SUB (expressionValueM (evaluate e1),
           expressionValueM (evaluate e2))
      = expressionValueM (evaluate (E_binary (e1, BinOp_SUB, e2)))

  theorem SHL_correct is
    fa (e1,e2)
      SHL (expressionValueM (evaluate e1),
           expressionValueM (evaluate e2))
      = expressionValueM (evaluate (E_binary (e1, BinOp_SHL, e2)))

  theorem SHR_correct is
    fa (e1,e2)
      SHR (expressionValueM (evaluate e1),
           expressionValueM (evaluate e2))
      = expressionValueM (evaluate (E_binary (e1, BinOp_SHR, e2)))

  theorem LT_correct is
    fa (e1,e2)
      LT (expressionValueM (evaluate e1),
          expressionValueM (evaluate e2))
      = expressionValueM (evaluate (E_binary (e1, BinOp_LT, e2)))

  theorem GT_correct is
    fa (e1,e2)
      GT (expressionValueM (evaluate e1),
          expressionValueM (evaluate e2))
      = expressionValueM (evaluate (E_binary (e1, BinOp_GT, e2)))

  theorem LE_correct is
    fa (e1,e2)
      LE (expressionValueM (evaluate e1),
          expressionValueM (evaluate e2))
      = expressionValueM (evaluate (E_binary (e1, BinOp_LE, e2)))

  theorem GE_correct is
    fa (e1,e2)
      GE (expressionValueM (evaluate e1),
          expressionValueM (evaluate e2))
      = expressionValueM (evaluate (E_binary (e1, BinOp_GE, e2)))

  theorem EQ_correct is
    fa (e1,e2)
      EQ (expressionValueM (evaluate e1),
          expressionValueM (evaluate e2))
      = expressionValueM (evaluate (E_binary (e1, BinOp_EQ, e2)))

  theorem NE_correct is
    fa (e1,e2)
      NE (expressionValueM (evaluate e1),
          expressionValueM (evaluate e2))
      = expressionValueM (evaluate (E_binary (e1, BinOp_NE, e2)))

  theorem AND_correct is
    fa (e1,e2)
      AND (expressionValueM (evaluate e1),
           expressionValueM (evaluate e2))
      = expressionValueM (evaluate (E_binary (e1, BinOp_AND, e2)))

  theorem XOR_correct is
    fa (e1,e2)
      XOR (expressionValueM (evaluate e1),
           expressionValueM (evaluate e2))
      = expressionValueM (evaluate (E_binary (e1, BinOp_XOR, e2)))

  theorem IOR_correct is
    fa (e1,e2)
      IOR (expressionValueM (evaluate e1),
           expressionValueM (evaluate e2))
      = expressionValueM (evaluate (E_binary (e1, BinOp_IOR, e2)))

  theorem LAND_correct is
    fa (e1,e2)
      LAND (expressionValueM (evaluate e1),
            expressionValueM (evaluate e2))
      = expressionValueM (evaluate (E_binary (e1, BinOp_LAND, e2)))

  theorem LOR_correct is
    fa (e1,e2)
      LOR (expressionValueM (evaluate e1),
           expressionValueM (evaluate e2))
      = expressionValueM (evaluate (E_binary (e1, BinOp_LOR, e2)))

  (* Array subscripts *)
  theorem SUBSCRIPT_correct is
    fa (e1,e2)
      SUBSCRIPT (expressionValueM (evaluate e1),
                 expressionValueM (evaluate e2))
      = expressionValueM (evaluate (E_subscript (e1, e2)))


  (** LValues **)

  op ExpressionResult2LValueM (m:Monad ExpressionResult) : Monad LValue =
    {res <- m;
     case res of
       | Res_pointer (tp, ObjPointer d) -> return (tp, d)
       | _ -> error}

  theorem LVAR_correct is
    fa (id) LVAR id = ExpressionResult2LValueM (evaluate (E_ident id))

  theorem ADDR_correct is
    fa (e)
      ADDR (ExpressionResult2LValueM (evaluate e))
      = expressionValueM (evaluate (E_unary (UOp_ADDR, e)))

  theorem LSTAR_correct is
    fa (e)
      LSTAR (expressionValueM (evaluate e))
      = ExpressionResult2LValueM (evaluate (E_unary (UOp_STAR, e)))

  theorem LSUBSCRIPT_correct is
    fa (e1,e2)
      LSUBSCRIPT (expressionValueM (evaluate e1),
                  expressionValueM (evaluate e2))
      = ExpressionResult2LValueM (evaluate (E_subscript (e1, e2)))


  (** Statements **)

  theorem ASSIGN_correct is
    fa (e1,e2)
      ASSIGN (ExpressionResult2LValueM (evaluate e1),
              expressionValueM (evaluate e2))
      = evalStatement (S_assign (e1, e2))

  theorem IFTHENELSE_correct is
    fa (e,s1,s2)
      IFTHENELSE (expressionValueM (evaluate e),
                  evalStatement s1, evalStatement s2)
      = evalStatement (S_if (e, s1, Some s2))

  theorem WHILE_correct is
    fa (e,body)
      WHILE (expressionValueM (evaluate e), evalStatement body)
      = evalStatement (S_while (e, body))

  theorem BLOCK_correct is
    fa (decls,stmts)
      BLOCK (decls, map evalStatement stmts)
      = evalStatement (S_block
                         (map BlockItem_declaration decls
                            ++ map BlockItem_statement stmts))

end-spec
