
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


  (* External declarations, which have type XUMonad (Option ObjectFileBinding) *)

  type ExtDecl = XUMonad (Option ObjectFileBinding)

  (* Function combinator *)
  op FUNCTION (retTypeName : TypeName, name : Identifier,
               paramDecls : List (TypeName * Identifier),
               body : Monad ()) : ExtDecl =
    {retType <- expandTypeNameXU retTypeName;
     params <- mapM_XU evalParameterDeclaration paramDecls;
     xenv <- xu_get;
     return
       (Some (name,
              ObjFile_Function
                (makeCFunction
                   (retType, params,
                    localR (fn r -> makeGlobalR (xenv, r.r_functions)) body),
                 (retType, (unzip params).2))))}


  (*** Theorems ***)

  (** Expressions **)

  op evalRValue (e : Expression) : Monad Value = expressionValueM (evaluate e)

  theorem VAR_correct is
    fa (id) VAR id = evalRValue (E_ident id)

  theorem ICONST_correct is
    fa (n) ICONST n = evalRValue (E_const (T_sint, n))

  (* Unary operators *)

  theorem STAR_correct is
    fa (e) STAR (evalRValue e) = evalRValue (E_unary (UOp_STAR, e))

  theorem PLUS_correct is
    fa (e) PLUS (evalRValue e) = evalRValue (E_unary (UOp_PLUS, e))

  theorem MINUS_correct is
    fa (e) MINUS (evalRValue e) = evalRValue (E_unary (UOp_MINUS, e))

  theorem NOT_correct is
    fa (e) NOT (evalRValue e) = evalRValue (E_unary (UOp_NOT, e))

  theorem NEG_correct is
    fa (e) NEG (evalRValue e) = evalRValue (E_unary (UOp_NEG, e))

  (* Binary operators *)

  theorem MUL_correct is
    fa (e1,e2)
      MUL (evalRValue e1, evalRValue e2)
      = evalRValue (E_binary (e1, BinOp_MUL, e2))

  theorem DIV_correct is
    fa (e1,e2)
      DIV (evalRValue e1, evalRValue e2)
      = evalRValue (E_binary (e1, BinOp_DIV, e2))

  theorem REM_correct is
    fa (e1,e2)
      REM (evalRValue e1, evalRValue e2)
      = evalRValue (E_binary (e1, BinOp_REM, e2))

  theorem ADD_correct is
    fa (e1,e2)
      ADD (evalRValue e1, evalRValue e2)
      = evalRValue (E_binary (e1, BinOp_ADD, e2))

  theorem SUB_correct is
    fa (e1,e2)
      SUB (evalRValue e1, evalRValue e2)
      = evalRValue (E_binary (e1, BinOp_SUB, e2))

  theorem SHL_correct is
    fa (e1,e2)
      SHL (evalRValue e1, evalRValue e2)
      = evalRValue (E_binary (e1, BinOp_SHL, e2))

  theorem SHR_correct is
    fa (e1,e2)
      SHR (evalRValue e1, evalRValue e2)
      = evalRValue (E_binary (e1, BinOp_SHR, e2))

  theorem LT_correct is
    fa (e1,e2)
      LT (evalRValue e1, evalRValue e2)
      = evalRValue (E_binary (e1, BinOp_LT, e2))

  theorem GT_correct is
    fa (e1,e2)
      GT (evalRValue e1, evalRValue e2)
      = evalRValue (E_binary (e1, BinOp_GT, e2))

  theorem LE_correct is
    fa (e1,e2)
      LE (evalRValue e1, evalRValue e2)
      = evalRValue (E_binary (e1, BinOp_LE, e2))

  theorem GE_correct is
    fa (e1,e2)
      GE (evalRValue e1, evalRValue e2)
      = evalRValue (E_binary (e1, BinOp_GE, e2))

  theorem EQ_correct is
    fa (e1,e2)
      EQ (evalRValue e1, evalRValue e2)
      = evalRValue (E_binary (e1, BinOp_EQ, e2))

  theorem NE_correct is
    fa (e1,e2)
      NE (evalRValue e1, evalRValue e2)
      = evalRValue (E_binary (e1, BinOp_NE, e2))

  theorem AND_correct is
    fa (e1,e2)
      AND (evalRValue e1, evalRValue e2)
      = evalRValue (E_binary (e1, BinOp_AND, e2))

  theorem XOR_correct is
    fa (e1,e2)
      XOR (evalRValue e1, evalRValue e2)
      = evalRValue (E_binary (e1, BinOp_XOR, e2))

  theorem IOR_correct is
    fa (e1,e2)
      IOR (evalRValue e1, evalRValue e2)
      = evalRValue (E_binary (e1, BinOp_IOR, e2))

  theorem LAND_correct is
    fa (e1,e2)
      LAND (evalRValue e1, evalRValue e2)
      = evalRValue (E_binary (e1, BinOp_LAND, e2))

  theorem LOR_correct is
    fa (e1,e2)
      LOR (evalRValue e1, evalRValue e2)
      = evalRValue (E_binary (e1, BinOp_LOR, e2))

  (* Array subscripts *)
  theorem SUBSCRIPT_correct is
    fa (e1,e2)
      SUBSCRIPT (evalRValue e1,
                 evalRValue e2)
      = evalRValue (E_subscript (e1, e2))


  (** LValues **)

  op evalLValue (e : Expression) : Monad LValue =
    {res <- evaluate e;
     case res of
       | Res_pointer (tp, ObjPointer d) -> return (tp, d)
       | _ -> error}

  theorem LVAR_correct is
    fa (id) LVAR id = evalLValue (E_ident id)

  theorem ADDR_correct is
    fa (e) ADDR (evalLValue e) = evalRValue (E_unary (UOp_ADDR, e))

  theorem LSTAR_correct is
    fa (e) LSTAR (evalRValue e) = evalLValue (E_unary (UOp_STAR, e))

  theorem LSUBSCRIPT_correct is
    fa (e1,e2)
      LSUBSCRIPT (evalRValue e1, evalRValue e2)
      = evalLValue (E_subscript (e1, e2))


  (** Statements **)

  theorem ASSIGN_correct is
    fa (e1,e2)
      ASSIGN (evalLValue e1, evalRValue e2)
      = evalStatement (S_assign (e1, e2))

  theorem IFTHENELSE_correct is
    fa (e,s1,s2)
      IFTHENELSE (evalRValue e, evalStatement s1, evalStatement s2)
      = evalStatement (S_if (e, s1, Some s2))

  theorem WHILE_correct is
    fa (e,body)
      WHILE (evalRValue e, evalStatement body)
      = evalStatement (S_while (e, body))

  theorem BLOCK_correct is
    fa (decls,stmts)
      BLOCK (decls, map evalStatement stmts)
      = evalStatement (S_block
                         (map BlockItem_declaration decls
                            ++ map BlockItem_statement stmts))


  (* External Declarations *)
  theorem FUNCTION_correct is
    fa (retTypeName, name, params, body)
      FUNCTION (retTypeName, name, params, evalStatement body)
      = compile1XU (EDecl_function {FDef_retType  = retTypeName,
                                    FDef_name     = name,
                                    FDef_params   = params,
                                    FDef_body     = Some body,
                                    FDef_isExtern = false})

  theorem FUNCTION_correct_2 is
    fa (retTypeName, name, params, body, d, m)
     d = EDecl_function {FDef_retType  = retTypeName,
                         FDef_name     = name,
                         FDef_params   = params,
                         FDef_body     = Some body,
                         FDef_isExtern = false}
       && m = evalStatement body
   => compile1XU d
      = FUNCTION (retTypeName, name, params, m)



end-spec
