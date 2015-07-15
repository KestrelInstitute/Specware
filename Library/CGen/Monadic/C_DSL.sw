
(* FIXME HERE: document this! It is somewhat like Oleg's finally tagless
interpreters *)

C_DSL qualifying spec
  import C

  (* Expression combinators, which have type Monad Value *)

  (* Variables *)
  op VAR (id:Identifier) : Monad C.Value =
    lookupIdentifierValue id

  (* Integer constants *)
  op ICONST (str : IntegerConstant) : Monad C.Value =
    evaluateIntegerConstant str

  (* Unary operators *)
  type Operator1 = Monad C.Value -> Monad C.Value
  op liftOperator1 (f : C.Value -> Monad C.Value) : Operator1 =
    fn m -> {val <- m; f val}

  op STAR : Operator1 = liftOperator1 readPtrValue
  op PLUS : Operator1 = liftOperator1 operator_PLUS
  op MINUS : Operator1 = liftOperator1 operator_MINUS
  op NOT : Operator1 = liftOperator1 operator_NOT
  op NEG : Operator1 = liftOperator1 operator_NEG

  (* Binary operators *)
  type Operator2 = Monad C.Value * Monad C.Value -> Monad C.Value
  op liftOperator2 (f : C.Value * C.Value -> Monad C.Value) : Operator2 =
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


  (* LValue combinators, which have type Monad LValueRes *)

  op LVAR (id:Identifier) : Monad LValueResult = lookupIdentifier id

  op ADDR (e : Monad LValueResult) : Monad C.Value =
    {res <- e; return (V_pointer res)}

  op LSTAR (m : Monad C.Value) : Monad LValueResult =
    {val <- m; dereferencePointer val}

  (* Array subscripting *)
  op LSUBSCRIPT (arr : Monad C.Value, ind : Monad C.Value) : Monad LValueResult =
    LSTAR (ADD (arr, ind))


  (* Statement combinators, which have type Monad () *)

  (* Assignment, which takes expressions lhs and rhs and performs *lhs = rhs *)
  op ASSIGN (lhs : Monad LValueResult, rhs : Monad C.Value) : Monad () =
    {res <- lhs; rhs_val <- rhs;
     assignValue (res, rhs_val)}

  (* If-then-else statements *)
  op IFTHENELSE (expr : Monad C.Value,
                 then_branch : Monad (), else_branch : Monad ()) : Monad () =
    {condition <- expr;
     isZero <- zeroScalarValue? condition;
     if ~ isZero then then_branch else else_branch}

  (* While statements *)
  op WHILE (expr : Monad C.Value, body : Monad ()) : Monad () =
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
  op BLOCK_helper (vars : List (C.TypeName * Identifier), body : List (Monad ())) : Monad () =
    {var_addrs <- mapM (fn (tp_name,id) ->
                          {tp <- expandTypeNameM tp_name;
                           addLocalBinding (id, V_undefined tp)}) vars;
     _ <- mapM id body;
     return ()}

  op BLOCK (vars : List (C.TypeName * Identifier), body : List (Monad ())) : Monad () =
    withFreshLocalBindings empty (BLOCK_helper (vars, body))


  (* External declarations, which have type XUMonad (Option ObjectFileBinding) *)

  type ExtDecl = XUMonad (Option ObjectFileBinding)

  (* Function combinator *)
  op FUNCTION (retTypeName : C.TypeName, name : Identifier,
               paramDecls : List (C.TypeName * Identifier),
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

  theorem VAR_correct is
    fa (id,e) e = E_lvalue (LV_ident id) => evaluate e = VAR id

  theorem ICONST_correct is
    fa (str,e)
      e = E_strict (E_const str) =>
      evaluate e = ICONST str

  (* Unary operators *)

  theorem STAR_correct is
    fa (e1,rv1,e)
      e = E_lvalue (LV_star e1) && evaluate e1 = rv1
      =>
      evaluate e = STAR rv1

  theorem PLUS_correct is
    fa (e1,rv1,e)
      e = E_strict (E_unary (UOp_PLUS, e1)) && evaluate e1 = rv1
      =>
      evaluate e = PLUS rv1

  theorem MINUS_correct is
    fa (e1,rv1,e)
      e = E_strict (E_unary (UOp_MINUS, e1)) && evaluate e1 = rv1
      =>
      evaluate e = MINUS rv1

  theorem NOT_correct is
    fa (e1,rv1,e)
      e = E_strict (E_unary (UOp_NOT, e1)) && evaluate e1 = rv1
      =>
      evaluate e = NOT rv1

  theorem NEG_correct is
    fa (e1,rv1,e)
      e = E_strict (E_unary (UOp_NEG, e1)) && evaluate e1 = rv1
      =>
      evaluate e = NEG rv1

  (* Binary operators *)

  theorem MUL_correct is
    fa (e1,e2,rv1,rv2,e)
      e = E_strict (E_binary (e1, BinOp_MUL, e2)) &&
      evaluate e1 = rv1 && evaluate e2 = rv2
      =>
      evaluate e = MUL (rv1, rv2)

  theorem DIV_correct is
    fa (e1,e2,rv1,rv2,e)
      e = E_strict (E_binary (e1, BinOp_DIV, e2)) &&
      evaluate e1 = rv1 && evaluate e2 = rv2
      =>
      evaluate e = DIV (rv1, rv2)

  theorem REM_correct is
    fa (e1,e2,rv1,rv2,e)
      e = E_strict (E_binary (e1, BinOp_REM, e2)) &&
      evaluate e1 = rv1 && evaluate e2 = rv2
      =>
      evaluate e = REM (rv1, rv2)

  theorem ADD_correct is
    fa (e1,e2,rv1,rv2,e)
      e = E_strict (E_binary (e1, BinOp_ADD, e2)) &&
      evaluate e1 = rv1 && evaluate e2 = rv2
      =>
      evaluate e = ADD (rv1, rv2)

  theorem SUB_correct is
    fa (e1,e2,rv1,rv2,e)
      e = E_strict (E_binary (e1, BinOp_SUB, e2)) &&
      evaluate e1 = rv1 && evaluate e2 = rv2
      =>
      evaluate e = SUB (rv1, rv2)

  theorem SHL_correct is
    fa (e1,e2,rv1,rv2,e)
      e = E_strict (E_binary (e1, BinOp_SHL, e2)) &&
      evaluate e1 = rv1 && evaluate e2 = rv2
      =>
      evaluate e = SHL (rv1, rv2)

  theorem SHR_correct is
    fa (e1,e2,rv1,rv2,e)
      e = E_strict (E_binary (e1, BinOp_SHR, e2)) &&
      evaluate e1 = rv1 && evaluate e2 = rv2
      =>
      evaluate e = SHR (rv1, rv2)

  theorem LT_correct is
    fa (e1,e2,rv1,rv2,e)
      e = E_strict (E_binary (e1, BinOp_LT, e2)) &&
      evaluate e1 = rv1 && evaluate e2 = rv2
      =>
      evaluate e = LT (rv1, rv2)

  theorem GT_correct is
    fa (e1,e2,rv1,rv2,e)
      e = E_strict (E_binary (e1, BinOp_GT, e2)) &&
      evaluate e1 = rv1 && evaluate e2 = rv2
      =>
      evaluate e = GT (rv1, rv2)

  theorem LE_correct is
    fa (e1,e2,rv1,rv2,e)
      e = E_strict (E_binary (e1, BinOp_LE, e2)) &&
      evaluate e1 = rv1 && evaluate e2 = rv2
      =>
      evaluate e = LE (rv1, rv2)

  theorem GE_correct is
    fa (e1,e2,rv1,rv2,e)
      e = E_strict (E_binary (e1, BinOp_GE, e2)) &&
      evaluate e1 = rv1 && evaluate e2 = rv2
      =>
      evaluate e = GE (rv1, rv2)

  theorem EQ_correct is
    fa (e1,e2,rv1,rv2,e)
      e = E_strict (E_binary (e1, BinOp_EQ, e2)) &&
      evaluate e1 = rv1 && evaluate e2 = rv2
      =>
      evaluate e = EQ (rv1, rv2)

  theorem NE_correct is
    fa (e1,e2,rv1,rv2,e)
      e = E_strict (E_binary (e1, BinOp_NE, e2)) &&
      evaluate e1 = rv1 && evaluate e2 = rv2
      =>
      evaluate e = NE (rv1, rv2)

  theorem AND_correct is
    fa (e1,e2,rv1,rv2,e)
      e = E_strict (E_binary (e1, BinOp_AND, e2)) &&
      evaluate e1 = rv1 && evaluate e2 = rv2
      =>
      evaluate e = AND (rv1, rv2)

  theorem XOR_correct is
    fa (e1,e2,rv1,rv2,e)
      e = E_strict (E_binary (e1, BinOp_XOR, e2)) &&
      evaluate e1 = rv1 && evaluate e2 = rv2
      =>
      evaluate e = XOR (rv1, rv2)

  theorem IOR_correct is
    fa (e1,e2,rv1,rv2,e)
      e = E_strict (E_binary (e1, BinOp_IOR, e2)) &&
      evaluate e1 = rv1 && evaluate e2 = rv2
      =>
      evaluate e = IOR (rv1, rv2)

  theorem LAND_correct is
    fa (e1,e2,rv1,rv2,e)
      e = E_strict (E_binary (e1, BinOp_LAND, e2)) &&
      evaluate e1 = rv1 && evaluate e2 = rv2
      =>
      evaluate e = LAND (rv1, rv2)

  theorem LOR_correct is
    fa (e1,e2,rv1,rv2,e)
      e = E_strict (E_binary (e1, BinOp_LOR, e2)) &&
      evaluate e1 = rv1 && evaluate e2 = rv2
      =>
      evaluate e = LOR (rv1, rv2)

  (* Array subscripts *)
  theorem SUBSCRIPT_correct is
    fa (e1,e2,e,rv1,rv2)
      e = E_lvalue (LV_subscript (e1, e2)) && evaluate e1 = rv1 && evaluate e2 = rv2
      =>
      evaluate e = SUBSCRIPT (rv1, rv2)


  (** LValues **)

  theorem LVAR_correct is
    fa (id,lv)
      lv = LV_ident id => evaluateLValue lv = LVAR id

  theorem ADDR_correct is
    fa (lv1,res1,e)
      e = E_strict (E_addr lv1) && evaluateLValue lv1 = res1
      =>
      evaluate e = ADDR res1

  theorem LSTAR_correct is
    fa (e1,rv1,e)
      e = LV_star e1 && evaluate e1 = rv1
      =>
      evaluateLValue e = LSTAR rv1

  theorem LSUBSCRIPT_correct is
    fa (e1,e2,expr,rv1,rv2)
      expr = LV_subscript (e1, e2) && evaluate e1 = rv1 && evaluate e2 = rv2
      =>
      evaluateLValue expr = LSUBSCRIPT (rv1, rv2)


  (** Statements **)

  theorem ASSIGN_correct is
    fa (e1,e2,stmt,lv,rv)
      stmt = S_assign (e1, e2) && evaluateLValue e1 = lv && evaluate e2 = rv
      =>
      evalStatement stmt = ASSIGN (lv, rv)

  theorem IFTHENELSE_correct is
    fa (e,s1,s2,rv,m1,m2,stmt)
      stmt = S_if (e, s1, Some s2) && evaluate e = rv &&
      evalStatement s1 = m1 && evalStatement s2 = m2
      =>
      evalStatement stmt = IFTHENELSE (rv, m1, m2)

  theorem WHILE_correct is
    fa (e,body,rv,m,stmt)
      stmt = S_while (e, body) && evaluate e = rv && evalStatement body = m
      =>
      evalStatement stmt = WHILE (rv, m)

  theorem BLOCK_correct is
    fa (decls,ms,stmt,blockitems)
      stmt = S_block blockitems &&
      evalBlockItems blockitems = BLOCK_helper (decls, ms)
      =>
      evalStatement stmt = BLOCK (decls, ms)

  theorem BLOCK_helper_correct1 is
    fa (decl,decls,ms,blockitems,blockitems')
      blockitems = (BlockItem_declaration decl) :: blockitems' &&
      evalBlockItems blockitems' = BLOCK_helper (decls, ms)
      =>
      evalBlockItems blockitems = BLOCK_helper (decl::decls, ms)

  theorem BLOCK_helper_correct2 is
    fa (stmt,m,ms,blockitems,blockitems')
      blockitems = (BlockItem_statement stmt) :: blockitems' &&
      evalStatement stmt = m &&
      evalBlockItems blockitems' = BLOCK_helper ([], ms)
      =>
      evalBlockItems blockitems = BLOCK_helper ([], m::ms)

  theorem BLOCK_helper_correct3 is
    fa (blockitems)
      blockitems = []
      =>
      evalBlockItems blockitems = BLOCK_helper ([], [])


  (* External Declarations *)
  theorem FUNCTION_correct is
    fa (retTypeName, name, params, body, d, m)
      d = EDecl_function {FDef_retType  = retTypeName,
                          FDef_name     = name,
                          FDef_params   = params,
                          FDef_body     = Some body,
                          FDef_isExtern = false}
      && evalStatement body = m
      =>
      compile1XU d = FUNCTION (retTypeName, name, params, m)

end-spec
