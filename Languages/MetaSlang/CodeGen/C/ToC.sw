\section{C Code Generator}

\begin{spec}
spec {
  import /Languages/MetaSlang/Specs/AnnSpec
  import /Languages/MetaSlang/Specs/StandardSpec
  import /Languages/MetaSlang/Specs/Printer
  import /Languages/C/AbstractSyntax/Types
  import /Languages/C/AbstractSyntax/Printer

  op specToC : Spec -> CSpec
  def specToC spc =
    let cSpec = emptyCSpec in
    let cSpec = generateCTypes cSpec spc in
    let cSpec = generateCVars cSpec spc in
    let cSpec = generateCFunctions cSpec spc in
    let stmt = Block ([],map (fn (type,name,tyVars,term) -> termToStmt term) spc.properties) in
    let cSpec = addFuncDefn cSpec "main" [] Int stmt in
    let _ = writeLine (PrettyPrint.toString (format (80, ppCSpec cSpec))) in
    cSpec

  op termToStmt : ATerm Position -> Stmt
  def termToStmt trm =
    case trm of
      | Apply (Fun (Equals,srt,_), Record ([("1",lhs), ("2",rhs)],_), _) ->
          Exp (Apply (Binary Set, [termToCExp lhs, termToCExp rhs]))
      | _ -> fail ("termToStmt: term '"
                  ^ (printTerm trm)
                  ^ "' is not an equality")

  op codSort : ASort Position -> ASort Position
  def codSort srt =
    case srt of
      | Arrow (domSrt,codSrt,_) -> codSrt
      | _ -> fail ("codSort: '" ^ (printSort srt) ^ "' is not a function type")
  
  op generateCFunctions : CSpec -> Spec -> CSpec
  def generateCFunctions cSpec spc =
    let
      def toCFunc cSpec name trm srt =
        case trm of
          | Lambda ([match],_) ->
              (case match of
                 | (VarPat ((id,varSrt),_),_,trm) ->
                      addFuncDefn cSpec name [(id,sortToCType varSrt)] (sortToCType (codSort srt)) (Return (termToCExp trm))
                 | (RecordPat (fields,_),_,trm) ->
                     let def fieldToVarDecl (_,pat) = % was (id,pat) but this id seems to be unused...
                       case pat of
                         | VarPat ((id,varSrt),_) -> (id, sortToCType varSrt)
                         | _ -> fail "generateCFunctions: record field not a var pat"
                     in
                       addFuncDefn cSpec name (map fieldToVarDecl fields) (sortToCType (codSort srt)) (Return (termToCExp trm))
                 | _ -> fail ("generateCFunctions: operator "
                              ^ name
                              ^ " is not a function: '"
                              ^ (printTerm trm)
                              ^ "'"))
          | _ -> fail ("generateCFunctions: operator "
                      ^ name
                      ^ " is not a lambda : '"
                      ^ (printTerm trm)
                      ^ "'")
      def doOp (qual, id, (aliases, fixity, (tyVars,srt), defs), cSpec) =
        case defs of
          | []         -> cSpec
          | (_,trm)::_ -> toCFunc cSpec (showQualifiedId (Qualified (qual,id))) trm srt
    in
      foldriAQualifierMap doOp cSpec spc.ops

  op derefSort : Spec -> ASort Position -> ASort Position
  def derefSort spc srt =
    case srt of
      | Base (qid,srts,_) ->
          (case findTheSort (spc,qid) of
            | None -> srt %
            % | None -> fail ("derefSort: failed to find sort: " ^ (showQualifiedId qid))
            | Some (aliases,tyVars,[]) -> srt
            | Some (aliases,tyVars,(_,srt)::_) -> derefSort spc srt)
      | _ -> srt

  op generateCVars : CSpec -> Spec -> CSpec
  def generateCVars cSpec spc =
    let def doOp (qual, id, (aliases, fixity, (tyVars,srt), defs), cSpec) =
      case defs of
        | [] -> addVarDecl cSpec (showQualifiedId (Qualified (qual,id))) (sortToCType srt)
%             (case (srt : ASort Position) of
%               | Base (qid,srts,_) ->
%                  (case (derefSort spc srt) of
%                    | Base (qid,srts,_) ->
%                        addVarDecl cSpec (showQualifiedId (Qualified (qual,id))) (baseSortToCType qid)
%                    | Product (fields,_) ->
%                        addVarDecl cSpec (showQualifiedId (Qualified (qual,id))) (baseSortToCType qid)
%                    | _ -> fail ("generateCVars: operator "
%                               ^ (showQualifiedId (Qualified (qual,id)))
%                               ^ " resolves to unsupported sort: "
%                               ^ (printSort srt)))
%               | Arrow (domSort,codSrt,_) -> cSpec % not a variable (leave it alone)
%                        addVarDecl cSpec (showQualifiedId (Qualified (qual,id))) (sortToCType srt)
% 
%               | _ -> fail ("generateCVars: operator "
%                           ^ (showQualifiedId (Qualified (qual,id)))
%                           ^ " has an unnamed sort: "
%                           ^ (printSort srt)))
        | _ -> cSpec
    in
      foldriAQualifierMap doOp cSpec spc.ops

  op generateCTypes : CSpec -> Spec -> CSpec
  def generateCTypes cSpec spc =
    let
      def makeCType cSpec name srt =
        case srt of
          | Subsort (srt,term,_) -> makeCType cSpec name srt
          | Product (("1",_)::_,_) -> fail "generateCTypes: found tuples without projections"
          | Product (fields,_) -> 
              addStruct cSpec name (map (fn (fieldName,srt) -> (fieldName, sortToCType srt)) fields)
          | CoProduct (fields,_) -> fail "generateCTypes: found coproduct"
          | Quotient (srt,term,_) -> fail "generateCTypes: found quotient"
          | Base (qid,[],_) -> addTypeDefn cSpec name (baseSortToCType qid)
          | Base (qid,srts,_) -> fail "generateCTypes: found instantiated base type"
          | TyVar _ -> fail "generateCTypes: found type variable"
          | MetaTyVar _ -> fail "generateCTypes: found meta-type variable"
          | _ -> fail ("generateCTypes: unsupported sort: " ^ (printSort srt))
      def doSort (qual, id, (aliases, tyVars, defs), cSpec) =
        case defs of
          | []          -> cSpec
          | (_, srt)::_ -> makeCType cSpec (showQualifiedId (Qualified (qual,id))) srt
    in
      addTypeDefn (foldriAQualifierMap doSort cSpec spc.sorts) "bool" Int

  op removePrime : QualifiedId -> QualifiedId
  def removePrime (qid as Qualified (qual,id)) =
    case (rev (explode id)) of
      | #'::rest -> Qualified (qual, implode (rev rest))
      | _ -> qid % fail ("removePrime: left side identifier not primed: "
                 % ^ (showQualifiedId qid))

  op showQualifiedId : QualifiedId -> String
  def showQualifiedId (Qualified (qual,id)) =
    if qual = UnQualified then
      id
    else
      qual ^ "_" ^ id
\end{spec}

It is reasonable that the next function should disappear. One could argue,
that we should never map the MetaSlang types to C types but rather define
the base types in C. For instance \verb+typedef int Integer+.

\begin{spec}
  op baseSortToCType : QualifiedId -> Type
  def baseSortToCType (Qualified (qual,id)) =
    if qual = UnQualified then
      Base id
    else
      case (qual,id) of
        | ("Boolean","Boolean") -> Base "bool"
        | ("Integer","Integer") -> Int
        | ("Nat","Nat") -> UnsignedInt
        | ("String","String") -> Ptr Char
        | ("Char","Char") -> Char
        | ("Double","Double") -> Double
        | _ -> Base (showQualifiedId (Qualified (qual,id)))

  op sortToCType : ASort Position -> Type
  def sortToCType srt =
    case srt of
      | Subsort (srt,term,_) -> sortToCType srt
      | Base (Qualified ("Array","Array"),[srt],_) -> Array (sortToCType srt)
      | Base (qid,[],_) -> baseSortToCType qid
      | Base (qid,srts,_) -> fail "sortToCType: found instantiated base type"
      | Arrow (domSort,codSort,_) -> 
          let domTypes =
            case domSort of
              | Product (fields as (("1",_)::_),_) -> 
                   map (fn (fieldName,srt) -> sortToCType srt) fields
              | _ -> [sortToCType domSort]
          in
            Fn (domTypes, sortToCType codSort)
      | _ -> 
         let _ = writeLine ("sortToCType: unsupported type: " ^ (printSort srt)) in
         Void
   
  op addVarDecl : CSpec -> String -> Type -> CSpec
  def addVarDecl cSpec name type = {
      includes    = cSpec.includes,
      defines     = cSpec.defines,
      constDefns  = cSpec.constDefns,
      vars        = Cons ((name,type), cSpec.vars),
      extVars     = cSpec.extVars,
      fns         = cSpec.fns,
      axioms      = cSpec.axioms,
      typeDefns   = cSpec.typeDefns,
      structDefns = cSpec.structDefns,
      unionDefns  = cSpec.unionDefns,
      varDefns    = cSpec.varDefns,
      fnDefns     = cSpec.fnDefns
    }

  op addFuncDefn : CSpec -> String -> VarDecls -> Type -> Stmt -> CSpec
  def addFuncDefn cSpec name params type stmt = {
      includes    = cSpec.includes,
      defines     = cSpec.defines,
      constDefns  = cSpec.constDefns,
      vars        = cSpec.vars,
      extVars     = cSpec.extVars,
      fns         = cSpec.fns,
      axioms      = cSpec.axioms,
      typeDefns   = cSpec.typeDefns,
      structDefns = cSpec.structDefns,
      unionDefns  = cSpec.unionDefns,
      varDefns    = cSpec.varDefns,
      fnDefns     = Cons ((name,params,type,stmt),cSpec.fnDefns)
    }

  op addStruct : CSpec -> String -> VarDecls -> CSpec
  def addStruct cSpec name fields = {
      includes    = cSpec.includes,
      defines     = cSpec.defines,
      constDefns  = cSpec.constDefns,
      vars        = cSpec.vars,
      extVars     = cSpec.extVars,
      fns         = cSpec.fns,
      axioms      = cSpec.axioms,
      typeDefns   = Cons ((name,Ptr (Struct name)), cSpec.typeDefns),
      structDefns = Cons ((name,fields), cSpec.structDefns),
      unionDefns  = cSpec.unionDefns,
      varDefns    = cSpec.varDefns,
      fnDefns     = cSpec.fnDefns
    }

  op addTypeDefn : CSpec -> String -> Type -> CSpec
  def addTypeDefn cSpec name type = {
      includes    = cSpec.includes,
      defines     = cSpec.defines,
      constDefns  = cSpec.constDefns,
      vars        = cSpec.vars,
      extVars     = cSpec.extVars,
      fns         = cSpec.fns,
      axioms      = cSpec.axioms,
      typeDefns   = Cons ((name,type), cSpec.typeDefns),
      structDefns = cSpec.structDefns,
      unionDefns  = cSpec.unionDefns,
      varDefns    = cSpec.varDefns,
      fnDefns     = cSpec.fnDefns
    }
\end{spec}

\subsubsection*{Code Generation}

The following operator "termToCExp" translates a MetaSlang term to a C
expression. The "Spec" parameter is not used for now, it may be used
later to unfold sort definitions.

\begin{spec}
  op termToCExp: ATerm Position -> CExp
  def termToCExp term =
    let
      def recordFieldsToCExps (fields : List(Id * ATerm Position)) : CExps =
        case fields of 
          | [] -> []
          | (id,term)::fields -> Cons (termToCExp term, recordFieldsToCExps fields)
      def applyArgsToCExps (args : ATerm Position) =
        case args of
          | Record (fields,_) -> recordFieldsToCExps fields
          | term -> [termToCExp term]
    in
    case term of
      | Fun (fun,srt,_) -> funToCExp fun srt
      | Var ((id,srt),_) -> Var (id,sortToCType srt)
      | IfThenElse (test,term1,term2,_) -> IfExp (termToCExp test, termToCExp term1, termToCExp term2)
      | Apply (Fun (Project id, srt,pos),term,_) ->
          let cStruct = termToCExp term in
          StructRef (Apply (Unary Contents, [cStruct]),id)
      | Apply (Apply (Fun (Op (Qualified ("Array","index"),fxty),srt,pos), arrayTerm,_), indexTerm,_) ->
          let cArray = termToCExp arrayTerm in
          let cIndex = termToCExp indexTerm in
          ArrayRef (cArray,cIndex)
      | Apply (Apply (Fun (Op (Qualified ("Struct","project"),fxty),srt,pos), projTerm,_), structTerm,_) ->
          let cProjFunc = termToCExp projTerm in
          let cStruct = termToCExp structTerm in
            Apply (Apply (Unary Contents,[cProjFunc]), [cStruct])
      | Apply (Fun (fun,srt,_),args,_) ->
          let cFun = funToCExp fun srt in
          let cArgs = applyArgsToCExps args in
          (case cFun of
            | Binary _ ->
               if ~(length cArgs = 2) then 
                 fail ("trying to apply a binary operator to " ^ (natToString (length cArgs)) ^ " arguments.") 
               else
                 Apply (cFun,cArgs)
            | Unary _ ->
               if ~(length cArgs = 1) then 
                 fail ("trying to apply a unary operator to " ^ (natToString (length cArgs)) ^ " arguments.") 
               else
                 Apply (cFun,cArgs)
            | _ -> Apply (cFun,cArgs))
       | _ -> fail ("termToCExp: term is neither a constant nor an application: " ^ (System.toString term))
\end{spec}

In contrast, "funToCExp" converts a one- or more-ary function
identifier to the corresponding C function identifier. Again, only
operators defined for the primitive types are allowed that have their
pendant on the C side.

\begin{spec}
  op funToCExp: AFun Position -> ASort Position -> CExp
  def funToCExp fun srt = 
    case fun of
      | Equals -> Binary Eq
      | Nat val -> Const (Int (true,val))
      | Char val -> Const (Char val)
      | Bool val -> Const (Int (true, if val then 1 else 0))
      | String val -> Const (String val)
      | Op (Qualified("Nat","+"),_) -> Binary Add
      | Op (Qualified("Nat","*"),_) -> Binary Mul
      | Op (Qualified("Nat","-"),_) -> Binary Sub
      | Op (Qualified("Nat","<"),_) -> Binary Lt
      | Op (Qualified("Nat","<="),_) -> Binary Le
      | Op (Qualified("Nat",">"),_) -> Binary Gt
      | Op (Qualified("Nat",">="),_) -> Binary Ge
      | Op (Qualified("Nat","div"),_) -> Binary Div
      | Op (Qualified("Nat","mod"),_) -> Binary Mod

      | Op (Qualified("Integer","+"),_) -> Binary Add
      | Op (Qualified("Integer","*"),_) -> Binary Mul
      | Op (Qualified("Integer","-"),_) -> Binary Sub
      | Op (Qualified("Integer","div"),_) -> Binary Div
      | Op (Qualified("Integer","mod"),_) -> Binary Mod
      | Op (Qualified("Integer","~"),_) -> Unary Negate
      | Op (Qualified("Integer","<"),_) -> Binary Lt
      | Op (Qualified("Integer","<="),_) -> Binary Le
      | Op (Qualified("Integer",">"),_) -> Binary Gt
      | Op (Qualified("Integer",">="),_) -> Binary Ge

      | Op (Qualified("Double","+"),_) -> Binary Add
      | Op (Qualified("Double","*"),_) -> Binary Mul
      | Op (Qualified("Double","-"),_) -> Binary Sub
      | Op (Qualified("Double","//"),_) -> Binary Div
      | Op (Qualified("Double","~"),_) -> Unary Negate
      | Op (Qualified("Double","<"),_) -> Binary Lt
      | Op (Qualified("Double","<="),_) -> Binary Le
      | Op (Qualified("Double",">"),_) -> Binary Gt
      | Op (Qualified("Double",">="),_) -> Binary Ge

      | Op (Qualified("Boolean","~"),_) -> Unary LogNot
      | Op (Qualified("Boolean","&"),_) -> Binary LogAnd
      | Op (Qualified("Boolean","or"),_) -> Binary LogOr
 
      % | Op (qid,_) -> Fn (showQualifiedId (removePrime qid), [], sortToCType srt)
      | Op (qid,_) -> Var (showQualifiedId (removePrime qid),sortToCType srt)

      | Embed (id,_) -> 
          let _ = writeLine ("funToCExp: Ignoring constructor " ^ id) in
          Nop
}
\end{spec}
