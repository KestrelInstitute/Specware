\begin{spec}
let BSpecs = USI(/Languages/BSpecs/Predicative/Coalgebra) in % ("","") in
let Structure = USI(/Languages/PSL/Transformations/Structure) in
let System = USI(/System) in
spec
  import ../../Coalgebra
  import /Languages/C/AbstractSyntax/Printer
  import MergeSort
  import Structure
\end{spec}

The following record type is used as container for additional code generation information that has to be provided to the "generateCode" operator.

\begin{tabular}{@{}ll}
\verb+funName+ & is the name of the C function to be generated;\\
\verb+funParOps+ & are the names of the parameters to the C function;\\
\verb+resultOpName+ & is the name of the operator that should be returned from the function.\\
\end{tabular}

\begin{spec}
  sort CodeGenerationUserInfo = {
     funName        : String,
     funParNames    : List String,
     resultOpName   : Option String,
     procNames      : List String,
     globalVarNames : List String
   }
\end{spec}

The "CodeGenerationInfo" type is used to store internal information used in code generation.

\begin{tabular}{@{}ll}
\verb+finalModes+ & is the list of modes without any outgoing transition;\\
\verb+jumpTargetModes+ & is the list of modes that are jumped at from other modes.
\end{tabular}


\begin{spec}
   sort CodeGenerationInfo = {
     funName         : String,
     funParams       : VarDecls,
     returnStmt      : CStmt,
     procNames       : List String,
     globalVarNames  : List String
   }
\end{spec}

The sort "UpdateTerm" is used to represent left and right-hand-side of
a term representing a state update.

\begin{spec}
  sort Guard = PTerm
  sort UpdateTerm = PTerm * PTerm
\end{spec}

The operator "generateCode" is the main entry point for the code generation. It takes a program as input and generates a CSpec, i.e. an abstract representation of a C program.

\begin{spec}
  op bSpecToC : BSpec -> CodeGenerationUserInfo -> CSpec
  def bSpecToC bSpec cguinfo =
    let _ = writeLine("generating Code...") in
    let startElem = bSpec.initial2 in
\end{spec}

The spec \verb+spc+ is used for code generation and is the one mapped to the start node. It is assumed, that this spec is mapped to all modes and also used to create the spans of the transitions.

\begin{spec}
    let spc = modeSpec bSpec startElem in
    let mergedspc = mergeOps (getAllModeSpecs bSpec) in
    let varDecls = generateVarDecls cguinfo.globalVarNames mergedspc in
    let (returnType,returnStmt) = getReturnInfo(varDecls,cguinfo.resultOpName) in
    let (funParams,varDecls) = divideDecls(varDecls,cguinfo.funParNames) in
\end{spec}

In the following step, for each mode of the original program shape we will generate code and store it in a map assigning mode names to code in terms of C Statements.

    let modes       = progr.system.shape.vertices in

Ensure, that the startelement is the first element in the mode list:
    let modes:(List TaggedElem)  = fold_v (fn(mlist) -> fn(m) -> 
                                          if m = startElem then mlist
                                          else List.cons(m,mlist)) [] modes
    in
    let modes = List.cons(startElem,modes) in

\begin{spec}
    let cginfo = {
                  funName = cguinfo.funName,
                  funParams = funParams,
                  returnStmt = returnStmt,
                  procNames = cguinfo.procNames,
                  globalVarNames = cguinfo.globalVarNames
                 }
    in
\end{spec}


\begin{spec}
    let abstCode = structBSpec bSpec in
    let abstCode = simplifyAbstCode abstCode in
    let abstCode = simplifyAbstCode abstCode in
    let fnbody = Block ([],abstCodeToCStmts cginfo spc abstCode) in
    let fndefn = (cginfo.funName,cginfo.funParams,returnType,fnbody) in
    let fndecl = fnDefnToFnDecl(fndefn) in
    let (fns,fnDefns) =
        case fndefn of
          | (_,_,_,Block(_,[])) -> ([],[])
          | _ -> ([fndecl],[fndefn])
    in
    let result = { 
                  includes    = [],
                  defines     = [],
                  constDefns  = [],
                  vars        = [],
                  extVars     = [],
                  fns         = fns,
                  axioms      = [],
                  typeDefns   = [],
                  structDefns = [],
                  unionDefns  = [],
                  varDefns    = [],
                  fnDefns     = fnDefns
                  }
    in
    result

%   sort AbstCode = List AbstStmt
%   sort AbstStmt =
%       | If AbstCode * AbstCode
%       | Assign PTerm
%       | Guard PTerm
%       | Call PTerm
% 
  op simplifyAbstCode : AbstCode -> AbstCode
  def simplifyAbstCode code =
    case code of
      | (If ((Guard t1)::[],(Guard t2)::[]))::rest -> simplifyAbstCode rest
      | (If (code1,code2))::rest -> Cons(If(simplifyAbstCode code1, simplifyAbstCode code2),simplifyAbstCode rest)
      | (Assign (Fun (Bool true,_)))::rest -> simplifyAbstCode rest
      | (Assign term)::rest -> Cons (Assign term, simplifyAbstCode rest)
      | (Guard term)::rest -> Cons (Guard term,simplifyAbstCode rest)
      | (Call term)::rest -> Cons (Call term,simplifyAbstCode rest)
      | [] -> []

  op abstCodeToCStmts : CodeGenerationInfo -> Spec -> AbstCode -> CStmts
  def abstCodeToCStmts codeGenInfo spc abstCode =
    map (abstStmtToCStmt codeGenInfo spc) abstCode

  op abstStmtToCStmt : CodeGenerationInfo -> Spec -> AbstStmt -> CStmt
  def abstStmtToCStmt codeGenInfo spc abstStmt =
    case abstStmt of
\end{spec}

We work with a very limited class of diagrams. Branches are two way at
most. When we see a two way branch, it is expected to be an if - then -
else. That is, the first transition on each side is a guard and one is
the negation of the other. There are better ways to do this .. but this
is suffices for now.

\begin{spec}
      | Guard term ->
         (case term of
            | Fun(Bool true,_) -> Nop
            | _ -> fail "abstStmtToCStmt: non-trvial non-branching guard")
      | Call term ->
         (case term of
            | Apply(Fun(procOp as Op(Imported("Static",procId),_), procSrt as Base(Imported("Static","Proc"),_)),
                    Record [("1",args),("2",lhs),_]) ->
                 (case lhs of
                      (Record []) ->
                       let procCall = Apply(Fun(procOp,procSrt),args) in
                       (Exp (termToCExp(codeGenInfo,spc,procCall)))
                    | _ ->
                       let lhs = removeDashesFromOpNames lhs in
                       let rhs = Apply(Fun(procOp,procSrt),args) in
                       let updExp = updateTermToCExp (codeGenInfo,spc,(lhs,rhs)) in
                       (Exp updExp))
            | _ -> fail "abstStmtToCStmt: ill-formed procedure call")
      | Assign term ->
         (case term of
              Apply(Fun(Equals,Arrow(Product([_,_]),_)),Record [(_,lhs),(_,rhs)]) ->
              let lhs = removeDashesFromOpNames lhs in
              let updExp = updateTermToCExp (codeGenInfo,spc,(lhs,rhs)) in
              (Exp updExp)
            | Fun(Bool true,_) -> Nop
            | _ -> fail "abstStmtToCStmt: ill-formed assignment")
      | If (left,right) ->
         (case (left,right) of
            | ((Guard leftGuard)::[], (Guard rightGuard)::[]) -> Nop
            | ((Guard leftGuard)::leftBlock, (Guard rightGuard)::[]) ->
                 (case (leftGuard,rightGuard) of
                    | (Apply(Fun(Op(Imported("Boolean","~"),_),_),newLeft),_) ->
                        if newLeft = rightGuard then
                          let cGuard = termToCExp (codeGenInfo,spc,leftGuard) in
                          let leftCode = abstCodeToCStmts codeGenInfo spc leftBlock in
                          (IfThen (cGuard,Block ([],leftCode)))
                        else
                          fail "abstStmtToCStmt: left guard not syntactic negation of right"
                    | (_,Apply(Fun(Op(Imported("Boolean","~"),_),_),newRight)) ->
                        if leftGuard = newRight then
                          let cGuard = termToCExp (codeGenInfo,spc,leftGuard) in
                          let leftCode = abstCodeToCStmts codeGenInfo spc leftBlock in
                          (IfThen (cGuard,Block ([],leftCode)))
                        else
                          fail "abstBlockToCStmts: right guard not syntactic negation of left"
                    | _ -> fail "abstBlockToCStmts: neither guard in branch is negated")
            | ((Guard leftGuard)::[], (Guard rightGuard)::rightBlock) ->
                 (case (leftGuard,rightGuard) of
                    | (Apply(Fun(Op(Imported("Boolean","~"),_),_),newLeft),_) ->
                        if newLeft = rightGuard then
                          let cGuard = termToCExp (codeGenInfo,spc,rightGuard) in
                          let rightCode = abstCodeToCStmts codeGenInfo spc rightBlock in
                          (IfThen (cGuard,Block ([],rightCode)))
                        else
                          fail "abstStmtToCStmt: left guard not syntactic negation of right"
                    | (_,Apply(Fun(Op(Imported("Boolean","~"),_),_),newRight)) ->
                        if leftGuard = newRight then
                          let cGuard = termToCExp (codeGenInfo,spc,rightGuard) in
                          let rightCode = abstCodeToCStmts codeGenInfo spc rightBlock in
                          (IfThen (cGuard,Block ([],rightCode)))
                        else
                          fail "abstBlockToCStmts: right guard not syntactic negation of left"
                    | _ -> fail "abstBlockToCStmts: neither guard in branch is negated")
            | ((Guard leftGuard)::leftBlock, (Guard rightGuard)::rightBlock) ->
                 (case (leftGuard,rightGuard) of
                    | (Apply(Fun(Op(Imported("Boolean","~"),_),_),newLeft),_) ->
                        if newLeft = rightGuard then
                          let cGuard = termToCExp (codeGenInfo,spc,rightGuard) in
                          let leftCode = abstCodeToCStmts codeGenInfo spc leftBlock in
                          let rightCode = abstCodeToCStmts codeGenInfo spc rightBlock in
                          (If (cGuard,Block ([],rightCode),Block ([],leftCode)))
                        else
                          fail "abstStmtToCStmt: left guard not syntactic negation of right"
                    | (_,Apply(Fun(Op(Imported("Boolean","~"),_),_),newRight)) ->
                        if leftGuard = newRight then
                          let cGuard = termToCExp (codeGenInfo,spc,leftGuard) in
                          let leftCode = abstCodeToCStmts codeGenInfo spc leftBlock in
                          let rightCode = abstCodeToCStmts codeGenInfo spc rightBlock in
                          (If (cGuard,Block ([],leftCode),Block ([],rightCode)))
                        else
                          fail "abstBlockToCStmts: right guard not syntactic negation of left"
                    | _ -> fail "abstBlockToCStmts: neither guard in branch is negated")
            | _ -> fail "abstStmtToCStmt: ill-formed if block")
      | _ -> fail "abstStmtToCStmt: unrecognized abstract statement"
\end{spec}

\subsubsection*{Variable Declarations}

The operator \verb+generateVarDefns+ takes a spec and generates the corresponding variable declarations for the operations. Current restrictions:
\begin{itemize}
\item operator may only have primitive sorts "Nat", "Integer", "Boolean", "Char", "String";
\item operators with arrow sorts are not allowed;
\item sort definitions are ignored.
\end{itemize}

\begin{spec}
  op generateVarDecls: List(String) -> Spec -> VarDecls
  def generateVarDecls globalVarNames spc =
    let ops = StringMap_foldli
               (fn(opname,opinfo,smap) -> if List.member(opname,globalVarNames) then smap
                                          else StringMap_insert(smap,opname,opinfo))
               StringMap_empty spc.ops
    in
    let vardecls = 
       StringMap_mapi
              (generateVarDeclFromSpec spc)
              ops
    in
      (StringMap_listItems vardecls)

\end{spec}

The following operator is used for generating global variables.

\begin{spec}
  op generateGlobalVarDecls: Spec -> CSpec
  def generateGlobalVarDecls(spc) =
    let vars = generateVarDecls [] spc in
    { 
     includes    = [],
     defines     = [],
     constDefns  = [],
     vars        = vars,
     extVars     = [],
     fns         = [],
     axioms      = [],
     typeDefns   = [],
     structDefns = [],
     unionDefns  = [],
     varDefns    = [],
     fnDefns     = []
    }
\end{spec}

\begin{spec}
  op generateVarDeclFromSpec: Spec -> String * OpInfo_ms -> VarDecl
  def generateVarDeclFromSpec spc (varname,opinfo) =
    let (fixity,sortscheme,optterm) = opinfo in
    generateVarDecl spc varname sortscheme
\end{spec}

\begin{spec}
  op generateVarDecl: Spec -> String -> (TyVars_ms * Sort_ms) -> VarDecl
  def generateVarDecl spc varname (tyvars,srt) =
    let ctype = varSortToType srt in
    (varname,ctype)
\end{spec}

The operator "varSortToType" converts a MetaSlang sort to a C type for
a variable. As mentioned above, for now only primitve types are
regarded.

\begin{spec}
  op varSortToType0: Sort_ms -> Option Type
  def varSortToType0 srt =
    case srt
      of  Base (Imported("Nat","Nat"),[]) -> Some Int
       |  Base (Imported("Integer","Integer"),[]) -> Some Int
       |  Base (Imported("Boolean","Boolean"),[]) -> Some Int
       |  Base (Imported("Char","Char"),[]) -> Some Char
       |  Base (Imported("String","String"),[]) -> Some (Ptr(Char))
       |  Base (Local(id),_) -> Some (Base(id))
       |  Base (Imported(_,id),_) -> Some (Base(id))
       |  Base (Imported("Static","Double"),[]) -> Some Double
       |  Product [] -> Some Void
       |  _ -> None
       %|  _ -> (writeLine ("only primitive sorts may be used:"^toString(srt));fail "")

  op varSortToType: Sort_ms -> Type
  def varSortToType srt =
    case srt of
      | Arrow(srt1,srt2) ->
        (case varSortToType0 srt1 of
           | Some _ -> (case varSortToType0 srt2 of
                          | Some s -> s
                          | None -> fail("illegal sort: "^toString(srt2))
                       )
           | None -> fail("if using an arrow sort, the domain must be a primitive type")
          )
      | _ -> (case varSortToType0 srt of
                | Some t -> t
                | None -> fail("only primitive types may be used for variables")
             )
\end{spec}

The operator "divideDecls" is used to divide the list of variable
declarations into function parameters and local variables of the
generated function. The list of strings contain the names of the
parameter variables.

\begin{spec}
  op divideDecls: VarDecls * List String -> (VarDecls * VarDecls)
  def divideDecls(vardecls,funParNames) =
    case vardecls of
      | [] ->
          let _ = if funParNames = [] then ()
                  else writeLine ("*** parameter(s) "%^strlistToString(funParNames)
                                 ^"not found in spec.")
          in
          ([],[])
      | vardecl::vardecls ->
          let (id,vartype) = vardecl in
          if vartype = Void then divideDecls(vardecls,funParNames) else
          if List.member(id,funParNames) then
            %- add the decl as parameter decls
            let funParNames = List.filter (fn(x) -> Boolean.~(id = x)) funParNames in
            let (params1,decls1) = divideDecls(vardecls,funParNames) in
            (List.cons(vardecl,params1),decls1)
          else
            %- add the decl as local var decl
            let (params1,decls1) = divideDecls(vardecls,funParNames) in
            (params1,List.cons(vardecl,decls1))
\end{spec}

\begin{spec}
  op getReturnInfo: VarDecls * Option String -> Type * Stmt
  def getReturnInfo(vardecls,resOpName) =
    case resOpName of
      | None -> (Void,VoidReturn)
      | Some resOpName -> 
      case vardecls of
        | [] -> let _ = writeLine("*** result operator \""^resOpName
                                  ^"\" cannot be found in spec.")
                in
                (Void,VoidReturn)
        | vardecl::vardecls ->
                let (id,vartype) = vardecl in
                if id = resOpName then
                  (vartype,if vartype = Void then VoidReturn else Return(Var(id,vartype)))
                else
                  getReturnInfo(vardecls,Some resOpName)
\end{spec}


\subsubsection*{Terms}

We restrict terms that can be used as transition terms to be in some normal form, that means:
\begin{itemize}
\item the term is a conjunction list of the form $t_1 \wedge t_2 \ldots \wedge t_n$;
\item if a dashed variable $x'$ occurs in a term, the term must have the form $x' = t$ and $t$ must not contain any dashed variables.
\end{itemize}

The operator "getConjList" takes a term of the form "$a_1 \wedge a_2 \wedge
... \wedge a_n$" and returns the list of terms "$[a_1,a_2,...,a_n]$".

\begin{spec}
  op getConjList: PTerm -> List PTerm
  def getConjList(t) =
    case t
      of Apply(Fun(Op(Imported("Boolean","&"),_),_),Record [(_,t1),(_,term)])
             -> List.concat(getConjList t1,getConjList(term))
       | _   -> [t]

\end{spec}

The operator "isAssignmentTerm" checks whether the given term has the
format $lhs = rhs$ and returns the term pairs, if this is true.

\begin{spec}
  op isAssignmentTerm: PTerm -> Option(PTerm * PTerm)
  def isAssignmentTerm t =
    case t of
       |  Apply(Fun(Equals,Arrow(Product([_,_]),_)),Record [(_,lhs),(_,rhs)])
              -> %-let _ = writeLine("updateTerm found") in
                 Some (lhs,rhs)
       |  _   -> isProcCall(t) %None
\end{spec}

\begin{spec}
  op isProcCall: PTerm -> Option(PTerm * PTerm)
  def isProcCall t =
    case t of
      | Apply(Fun(procop as Op(Imported("Static",procid),_),
             procsrt as Base(Imported("Static","Proc"),_)),
               Record [("1",args),("2",lhs),_])
          -> let lhs =
               (case lhs of
                   (Record []) -> Fun(Op(Local("void_p"),Nonfix),intSort_ms)
                 | _ -> lhs) in
             Some (lhs,Apply(Fun(procop,procsrt),args))
      | _ -> None
\end{spec}

The predicate "isSuccModeOp" determines whether a given operator belongs to the successor state. Is our case, this means whether it is a local operator the name of which ends with a single quote.

\begin{spec}
  op isSuccModeOp: QualifiedId_ms -> Boolean
  def isSuccModeOp(qid) =
    case qid
      of  Local(id) -> let lastChar = List.nth(String.explode(id),String.length(id)-1) in
                       if lastChar = #' then true else false
        | _ -> false
\end{spec}

The operator "succModeOp2CurrentModeOp" converts an operator of the
successor mode to the corresponding one in the current mode. In our
case this simply means, that the dashes are removed from the
operator's name.

\begin{spec}
  op succModeOp2CurrentModeOp: QualifiedId_ms -> QualifiedId_ms
  def succModeOp2CurrentModeOp(qid) =
    case qid of
      | Local(id) -> let expl = String.explode(id) in
                     let expl = List.foldr 
                                 (fn(c,s) -> if (c = #') then s else List.cons(c,s))
                                 [] expl
                     in
                     Local(String.implode(expl))
      | qid -> qid
\end{spec}

The operator "containsSuccModeOps" determines whether a given term
contains operators of the successor mode.

\begin{spec}
  op containsSuccModeOps: PTerm -> Boolean
  def containsSuccModeOps(t) =
    let usedops = getUsedOperatorsTerm(t) in
    List.exists (fn(opr) -> isSuccModeOp(opr)) usedops
\end{spec}

An operator is updateable, iff it is an operator of the successor
mode. We separated these two operators to abstract from the fact that
an updateable operator must syntactically belong to the successor
mode.

\begin{spec}
  op isUpdateableOp: QualifiedId_ms -> Boolean
  def isUpdateableOp = isSuccModeOp
\end{spec}

Given a term $lhsTerm$ representing the left-hand-side of an assignment term, the following operator determines, whether $lhsTerm$ refers to an operator that may be updated.

\begin{spec}
  op isUpdateableTerm: PTerm -> Boolean
  def isUpdateableTerm(lhsTerm) =
    case lhsTerm
      of Fun(Op(qid,_),_) -> isUpdateableOp qid
       | Apply(Fun(Op(qid,_),_),args) -> isUpdateableOp qid

\end{spec}

\begin{spec}
  op flattenLhsTerm: PTerm -> PTerm
  def flattenLhsTerm(t) =
    case t of
      | Fun(Op(qid,_),_) -> t
      | Apply(Fun(Op(qid,tv),Arrow(srt1,srt2)),args) -> 
          let argstr = makeProcName "" args in
          let qid = (case qid of
                       | Local(id) -> Local(id^"@"^argstr)
                       | Imported(s,id) -> Imported(s,id^"@"^argstr)
                    )
          in
          Fun(Op(qid,tv),srt2)
\end{spec}

"getUpdatedOperator" yields the updated operator from an updateable
term, which is, for now, just the operator itself. Later, when we
allow more complicated lhs's, this would be the functor of an
application term.

\begin{spec}
  op getUpdatedOperator: PTerm -> QualifiedId_ms
  def getUpdatedOperator(lhs) =
    case lhs of
      | Fun(Op(qid,_),_) -> qid
      | Apply(Fun(Op(qid,_),_),args) -> qid

\end{spec}

The fact that a term t is an "update term" means that it has the form $lhs = rhs$, that $lhs$ is an updateable term, and that $rhs$ does not contain any updateable operators.

\begin{spec}
  op isUpdateTerm: PTerm -> Option(UpdateTerm)
  def isUpdateTerm t =
    case isAssignmentTerm t of
      |  Some(lhs,rhs) ->
               if isUpdateableTerm lhs then 
                 if ~(containsSuccModeOps rhs)
                   then
                     Some (flattenLhsTerm lhs,rhs) 
                 else None
               else None
      | _ -> None
\end{spec}

A guard term is a term that isn't an update term and that does not
contain any operators of the successor state.

\begin{spec} 
  op isGuardTerm: PTerm -> Boolean
  def isGuardTerm t =
    case isUpdateTerm t of
      | Some(_,_) -> false
      | _         -> ~ (containsSuccModeOps t)
\end{spec}

\subsubsection*{Code Generation}

The following operator "termToCExp" translates a MetaSlang term to a C
expression. The "Spec" parameter is not used for now, it may be used
later to unfold sort definitions.

\begin{spec}
  op termToCExp: CodeGenerationInfo * Spec * PTerm -> CExp
  def termToCExp(cginfo,spc,term) =
    let def recordFieldsToCExps(fields:List(Id_ms*PTerm)): CExps =
          case fields
        of  [] -> []
          | (id,term)::fields -> List.cons(termToCExp(cginfo,spc,term),recordFieldsToCExps(fields))
    in
    let def applyArgsToCExps(args:PTerm) =
          case args
        of  Record fields -> recordFieldsToCExps fields
          | term -> [termToCExp(cginfo,spc,term)]
    in
    case term of
        Fun(fun,srt) -> fun0ToCExp(cginfo,spc,fun,srt)
      | Apply (Fun (Op(Imported("Static","float64Value"),_),srt),term) -> 
          termToCExp (cginfo,spc,term)
      | Apply (Fun (Op(Imported("Static","int32Value"),_),srt),term) -> 
          termToCExp (cginfo,spc,term)
      | Apply (Fun (Op(Imported("Static","booleanValue"),_),srt),term) -> 
          termToCExp (cginfo,spc,term)
      | Apply (Fun (Op(Imported("Static","int32ToFloat64"),_),srt),term) -> 
          termToCExp (cginfo,spc,term)
      | Apply (Fun (Op(Imported("Static","stringToDouble"),_),srt),term) -> 
          termToCExp (cginfo,spc,term)
      | Apply (Fun (Op(Imported("Static","broadcast"),_),srt),
          Record (("1",Fun (String ev,_))::_)) -> 
            Apply (Fn("broadcast_" ^ ev,[],Void), [])
      | Apply (Fun (Op(Local("active"),_),srt),Fun (String var,_)) -> 
          Var ("active_" ^ var,Void)
      | Apply (Fun (Embed("Var",_),srt),Fun (String var,_)) -> 
          Var (var,Void)
      | Apply (Fun (Op(Local(name),_),srt),Fun (String var,_)) -> 
          Var (var,Void)
      % | Apply (Fun (Embed("Var",_),srt),Fun (String var,_)) -> 
      %     Var ("store" ^ "_" ^ var,Void)
      | Apply (Fun (Embed("Int32",_),srt),term) -> 
          termToCExp (cginfo,spc,term)
      | Apply (Fun (Embed("Float64",_),srt),term) -> 
          termToCExp (cginfo,spc,term)
      | Apply (Fun (Embed("Boolean",_),srt),term) -> 
          termToCExp (cginfo,spc,term)
      | Apply(Fun(fun,srt),args) ->
          let cFun = funToCExp(spc,fun,srt) in
          let cArgs = applyArgsToCExps(args) in
          let l = List.length(cArgs) in
          let check = 
            case cFun of
                Binary(_) ->
                   if l = 2 then true
                   else
                       let _ = writeLine("trying to apply a binary operator with "^natToString(l)^" arguments.") in
                        false
             |  Unary(_) ->
                   if l = 1 then true
                   else
                     let _ = writeLine("trying to apply a unary operator with "^natToString(l)^" arguments.") in
                         false
             | _ -> true
               in
               Apply(cFun,cArgs)

  op optTermToCExp: CodeGenerationInfo * Spec * Option PTerm -> Option CExp
  def optTermToCExp(cginfo,spc,optt) =
    case optt of
      | None -> None
      | Some t -> Some(termToCExp(cginfo,spc,t))

\end{spec}

"fun0ToCExp" transforms a variable or constant to a CExp. For now, we
restrict the code generation to primitive constants and locally
defined variables with a primitive type.

\begin{spec}
  op fun0ToCExp: CodeGenerationInfo * Spec * Fun_ms * Sort_ms -> CExp
  def fun0ToCExp(cginfo,spc,fun,srt) =
    let procNames = cginfo.procNames in
    case fun
      of  Op(Local(id),_) -> 
             let _ = writeLine("local id "^id) in
             if List.member(id,procNames) then Fn(id,[],Void)
             else Var(id,varSortToType srt)
        | Int(val) -> Const(if val<0 then Int(false,Integer.~(val)) else Int(true,val))
        | Char(val) -> Const(Char(val))
        | Bool(val) -> Const(Int(true,if val then 1 else 0))
        | String(val) -> Const(String(val))
\end{spec}

In contrast, "funToCExp" converts a one- or more-ary function
identifier to the corresponding C function identifier. Again, only
operators defined for the primitive types are allowed that have their
pendant on the C side.

\begin{spec}
  op funToCExp: Spec * Fun_ms * Sort_ms -> CExp
  def funToCExp(spc,fun,srt) = 
    case fun of
        Equals -> Binary(Eq)
      | Op (Imported("Nat","+"),_) -> Binary Add
      | Op (Imported("Nat","*"),_) -> Binary Mul
      | Op (Imported("Nat","-"),_) -> Binary Sub
      | Op (Imported("Nat","<"),_) -> Binary Lt
      | Op (Imported("Nat","<="),_) -> Binary Le
      | Op (Imported("Nat",">"),_) -> Binary Gt
      | Op (Imported("Nat",">="),_) -> Binary Ge
      | Op (Imported("Nat","div"),_) -> Binary Div
      | Op (Imported("Nat","mod"),_) -> Binary Mod
      | Op (Imported("Integer","+"),_) -> Binary Add
      | Op (Imported("Integer","*"),_) -> Binary Mul
      | Op (Imported("Integer","-"),_) -> Binary Sub
      | Op (Imported("Integer","div"),_) -> Binary Div
      | Op (Imported("Integer","mod"),_) -> Binary Mod
      | Op (Imported("Integer","~"),_) -> Unary Negate
      | Op (Imported("Integer","<"),_) -> Binary Lt
      | Op (Imported("Integer","<="),_) -> Binary Le
      | Op (Imported("Integer",">"),_) -> Binary Gt
      | Op (Imported("Integer",">="),_) -> Binary Ge
      | Op (Imported("Boolean","~"),_) -> Unary LogNot
      | Op (Imported("Boolean","&"),_) -> Binary LogAnd
      | Op (Imported("Boolean","or"),_) -> Binary LogOr
      | Op (Imported("Static","doubleAdd"),_) -> Binary Add
      | Op (Imported("Static","doubleMult"),_) -> Binary Mul
      | Op (Imported("Static","doubleSubt"),_) -> Binary Sub
      | Op (Imported("Static","doubleDiv"),_) -> Binary Div
      % | Op(Imported("Static","mod"),_) -> Binary Mod
      % | Op(Imported("Static","~"),_) -> Unary Negate
      | Op(Imported("Static","doubleLT"),_) -> Binary Lt
      | Op(Imported("Static","doubleLTEQ"),_) -> Binary Le
      | Op(Imported("Static","doubleGT"),_) -> Binary Gt
      | Op(Imported("Static","doubleGTEQ"),_) -> Binary Ge
      | Op(Imported("Static","doubleEQ"),_) -> Binary Eq
 
      | Op(Local(id),_) ->
            %let _ = writeLine("Don't know how to translate local operator \""^id^"\".") in
            %Const(Int(true,0))
            funIdToCExp(Local(id),srt)
 
      | Op(Imported(sid,id),_) ->
            %let _ = writeLine("Don't know how to translate operator \""^sid^"."^id^"\".") in
            %Const(Int(true,0))
            funIdToCExp(Imported(sid,id),srt)
      | Embed (id,_) -> 
          let _ = writeLine ("funToCExp: Ignoring constructor " ^ id) in
          Nop
\end{spec}

\begin{spec}
  op funIdToCExp: QualifiedId_ms * Sort_ms -> CExp
  def funIdToCExp(qid,srt) =
    let id = case qid of
               | Local(id) -> id
               | Imported(_,id) -> id
    in
    Fn(id,[],Void)

\end{spec}

"updateTermToCExp" translates an update term consisting of lhs and rhs to a set expression in C. It is assumed, that (lhs,rhs) has already been checked to be a valid update (see "isUpdateableTerm").

\begin{spec}
  op updateTermToCExp: CodeGenerationInfo * Spec * UpdateTerm -> CExp
  def updateTermToCExp(cginfo,spc,(lhs,rhs)) =
    let cLhs = termToCExp(cginfo,spc,lhs) in
    let cRhs = termToCExp(cginfo,spc,rhs) in
    let res = Apply(Binary(Set),[cLhs,cRhs]) in
    %let _ = writeLine(cexpToString(res)) in
    res
\end{spec}

The following operator generates a C variable definition/declaration
from an auxiliary update of the form $x = x_0$.

\begin{spec}
  op generateVarDeclFromAuxUpdate : Spec * UpdateTerm -> VarDecl
  def generateVarDeclFromAuxUpdate(spc,(lhs,rhs)) =
    let existingOp = getUpdatedOperator(lhs) in
    let auxOp = getUpdatedOperator(rhs) in % this can be done, because we have constructed the rhs from an lhs
    let Local(auxid) = auxOp in
    case lookupOp(spc,existingOp) of
      | Some (id,(fx,sortscheme,_)) -> generateVarDecl spc auxid sortscheme
      | None -> (writeLine "internal error"; fail "")
\end{spec}

\begin{spec}
  op constructCStmtForTransition: CodeGenerationInfo -> Option(CExp) * VarDecls * CExps * TaggedElem -> CStmt
  def constructCStmtForTransition cginfo (optCguard,localVars,updates,succState) =
    let mlabel = getModeLabel(succState) in 
        let lastStmt = if isFinalMode cginfo succState
               then cginfo.returnStmt
               else Goto mlabel
        in
        let block = Block(localVars,
                  List.concat(
                      (List.map (fn(upd) -> Exp(upd)) updates),
                      [lastStmt]
                      )
                  )
        in
        let res = 
          case optCguard of
        | Some grd -> IfThen(grd,block)
        | None       -> block
        in
        %let _ = writeLine(cstmtToString(res)) in
        res
    \end{spec}

    \subsubsection*{Auxiliary Operators}

        \begin{verbatim}
          op taggedElemToString: TaggedElem -> String
          def taggedElemToString(t) = toString(format(80,ppTaggedElem(t)))

          op cexpToString: CExp -> String
          def cexpToString(e) = toString(format(80,ppExp(e)))

          op cstmtToString: CStmt -> String
          def cstmtToString(s) = toString(format(80,ppStmt(s)))

          op cstmtsToString: CStmts -> String
          def cstmtsToString(stmts) =
            List.foldl (fn(stmt,s) -> s ^ "\n" ^ cstmtToString(stmt)) "" stmts

          op cvarDefnToString: VarDefn -> String
          def cvarDefnToString(d) = toString(format(80,ppVarDefn(d)))

          op strlistToString : List String -> String
          def strlistToString = List.foldl (fn(s,strlist) -> strlist^s^" ") ""

        \end{verbatim}

        \begin{spec}
          op getAxioms: Spec -> List PTerm
          def getAxioms(spc) =
            let axioms = List.foldl (fn((Axiom,_,_,term),tl) -> List.concat(tl,[term])
                                    |  (_,tl)                -> tl)
                         [] spc.properties
            in
            axioms
        \end{spec}

        The following operator computes the final modes for a given
        program. It does it by checking whether the co-algebra is empty, in
        which case the mode is final.

        \begin{spec}
          op getFinalModes: BSpec -> List TaggedElem
          def getFinalModes(progr) =
            let modes = progr.system.shape.vertices in
            fold_v(fn(tlist) ->
                   fn(m) ->
                      let succ = succCoalgebra progr m in
                      if succ = empty_p
                      then List.cons(m,tlist)
                      else tlist
                      ) [] modes
        \end{spec}

        \begin{spec}
        %  op getJumpTargets: BSpec -> List TaggedElem
        %  def getJumpTargets(progr) =
        %    let modes = progr.system.shape.vertices in
        %    fold_v(fn(tlist) -> 
        %           fn(m) ->
        %           let succ = succCoalgebra progr m in
        %           let targetModes = map_p (fn(_,trgm) -> trgm) succ in
        %           fold_p
        %             (fn(tlist0) -> fn(trgm0) -> 
        %              if List.member(trgm0,tlist)
        %              then tlist
        %              else List.cons(trgm0,tlist)
        %             )
        %             tlist targetModes) [] modes

          op getJumpTargets: BSpec -> List TaggedElem
          def getJumpTargets(bspc) =
            let trgmap = bspc.system.shape.target in
            let trgmodes = List.map (fn(_,t) -> t) (mapToList trgmap) in
            trgmodes
        \end{spec}

        \begin{spec}
          op isFinalMode: CodeGenerationInfo -> TaggedElem -> Boolean
          op isJumpTarget: CodeGenerationInfo -> TaggedElem -> Boolean
        \end{spec}
          def isJumpTarget cginfo mod =
            List.member(mod,cginfo.jumpTargetModes)
          def isFinalMode cginfo mod =
            List.member(mod,cginfo.finalModes)




        natSort is the sort for natural numbers. The string "Nat" appears
        twice. The first is the name of the (imported) spec in which the sort
        is defined.  compSort is the sort for comparison operators: =, <= and >
        on the natural numbers and arithSort is for arithmetic operations.

        \begin{spec}
          % def natSort = Base (Imported ("Nat","Nat"), []) : Sort_ms
          % def boolSort = Base (Imported ("Boolean","Boolean"), []) : Sort_ms

          def compSort =
            Arrow (mkProduct_ms [natSort_ms, natSort_ms], boolSort_ms) : Sort_ms
          def arithSort =
            Arrow (mkProduct_ms [natSort_ms, natSort_ms], natSort_ms) : Sort_ms
        \end{spec}

        Next is the sort for conjunction.

        \begin{spec}
          def conjSort =
            Arrow (mkProduct_ms [boolSort_ms,boolSort_ms], boolSort_ms) : Sort_ms
        \end{spec}

        The next few help to construct terms.  localOp is a local operator, impOp
        is an imported operator, natConst is a natural numbers constant. For
        some reason that is not clear to me, equality has its own constructor
        in the abstract syntax.

        \begin{spec}
          def localOp opr srt = Fun (Op (Local opr, Nonfix), srt) : PTerm
          def impOp opr srt = Fun (Op (Imported opr, Nonfix), srt) : PTerm
          def natConst n = Fun (Int n, natSort_ms) : PTerm
          def equals = (Fun (Equals, compSort)) : PTerm
        \end{spec}

        Given a list of (assumed) boolean terms, this returns the term representing
        their conjunction

        \begin{spec}
          op conjList : List PTerm -> PTerm
          def conjList l = case l of
              [] -> Fun (Bool true, boolSort_ms)
            | h::[] -> h
            | h::t -> Apply (impOp ("Boolean","&") conjSort, mkTuple_ms [h, conjList t])
        \end{spec}

        \begin{spec}
          op removeDashesFromOpNames: PTerm -> PTerm
          def removeDashesFromOpNames(t) =
            mapPTerm ((fn
                      | Fun(Op(qid,fx),srt) -> Fun(Op(succModeOp2CurrentModeOp(qid),fx),srt)
                      | t -> t)
                     ,(fn(srt) -> srt),(fn(pat) -> pat)) t
        \end{spec}

        "substOp" substitutes one operator by another in a given term.

        \begin{spec}
          op substOp: QualifiedId_ms * QualifiedId_ms -> PTerm -> PTerm
          def substOp(oldqid,newqid) t =
            mapPTerm ((fn
                      | Fun(Op(qid,fx),srt) -> if qid = oldqid then Fun(Op(newqid,fx),srt)
                                               else Fun(Op(qid,fx),srt)
                      | t -> t)
                     ,(fn(srt) -> srt),(fn(pat) -> pat)) t
        \end{spec}

        \begin{spec}
          op substOpInLhs : QualifiedId_ms * QualifiedId_ms -> PTerm -> PTerm
          def substOpInLhs(oldqid,newqid) lhs =
            case lhs of
              | Fun(Op(_,_),_) -> substOp(oldqid,newqid) lhs
              %- | Apply(t as Fun(Op(qid,_),_),args) -> Apply(substOp(oldqid,newqid) t,args)
        \end{spec}


        "lookupOp" returns the opinfo entry in the spec declaring the given operator.

        \begin{spec}
          op lookupOp: Spec * QualifiedId_ms -> Option (String * OpInfo_ms)
          def lookupOp(spc,qid) =
            let id = case qid of
                        | Local(id) -> id
                        | Imported(_,id) -> id
            in
            %find (fn(id1,opinfo) -> id1 = id) spc.ops
            case StringMap_find (spc.ops,id) of
              | Some opinfo -> Some (id,opinfo)
              | None -> None
        \end{spec}

        \begin{spec}
          op suffixOp : QualifiedId_ms * String -> QualifiedId_ms
          def suffixOp(qid,suffix) =
            case qid of
              | Local(id) -> Local(id^suffix)
              | Imported(sid,id) -> Imported(sid,id^suffix)

        \end{spec}

        \begin{spec}
          op elemToString: Elem -> String
          op getModeLabel: TaggedElem -> String
          def getModeLabel = fn
            | Just(X) -> "Mode"^cString(elemToString(X))
            | Tag(_,t) -> getModeLabel(t)
        \end{spec}

        \begin{spec}
          op getUsedOperatorsTerm: PTerm -> List QualifiedId_ms
          def getUsedOperatorsTerm(t) =
            case t
              of  Fun(Op(qid,_),_) -> [qid]
                | Apply(t1,t2) -> getUsedOperatorsTermList [t1,t2]
                | Record fields -> getUsedOperatorsTermList (List.map (fn(_,t) -> t) fields)
                | Bind(_,_,t) -> getUsedOperatorsTerm t
                | Let (ptl,t) -> getUsedOperatorsTermList(List.cons(t,(List.map (fn(_,t) -> t) ptl)))
                | LetRec(ptl,t) -> getUsedOperatorsTermList(List.cons(t,(List.map (fn(_,t) -> t) ptl)))
                | Lambda match -> List.foldl 
                                    (fn((p,t1,t2),ql) -> 
                                     ql
                                     List.++ getUsedOperatorsPattern(p)
                                     List.++ getUsedOperatorsTerm(t1)
                                     List.++ getUsedOperatorsTerm(t2)
                                     )
                                    [] match
                | IfThenElse(t1,t2,t3) -> getUsedOperatorsTermList [t1,t2,t3]
                | Seq tl -> getUsedOperatorsTermList tl
                | _ -> []

          op getUsedOperatorsPattern: Pattern_ms -> List QualifiedId_ms
          def getUsedOperatorsPattern(p) =
            case p
              of  AliasPat(p1,p2) -> List.concat(getUsedOperatorsPattern(p1),getUsedOperatorsPattern(p2))
                | EmbedPat(_,Some p,_) -> getUsedOperatorsPattern(p)
                | RecordPat plist -> List.foldl (fn((id,p),ql) ->
                                                 ql
                                                 List.++ getUsedOperatorsPattern(p)
                                                 ) [] plist
                | RelaxPat(p,t) -> List.concat(getUsedOperatorsPattern(p),getUsedOperatorsTerm(t))
                | QuotientPat(p,t) -> List.concat(getUsedOperatorsPattern(p),getUsedOperatorsTerm(t))
                | _ -> []

          op getUsedOperatorsTermList: List PTerm -> List QualifiedId_ms
          def getUsedOperatorsTermList(tl) =
            case tl
              of  [] -> []
                | t::tl -> List.concat(getUsedOperatorsTerm(t),getUsedOperatorsTermList(tl))


        \end{spec}

        The following operators are used to collect all opinfos from the modes of a bSpec.

        \begin{spec}

          op getAllModeSpecs: BSpec -> List Spec
          def getAllModeSpecs(bspc) =
            let modes = toList_v bspc.system.shape.vertices in
            List.map (fn(m) -> modeSpec bspc m) modes

          op mergeOps: List Spec -> Spec
          def mergeOps(spclist) =
            case spclist of
              | [spc] -> spc
              | spc1::spc2::spclist -> 
                   let ops = StringMap_foldli
                              (fn(opname,opinfo1,strmap) ->
                                 case StringMap_find(strmap,opname) of
                                   | Some _ -> strmap
                                   | None -> StringMap_insert(strmap,opname,opinfo1)
                                  )
                              spc1.ops spc2.ops
                   in
                     {
                      sorts = spc1.sorts,
                      ops = ops,
                      imports = spc1.imports,
                      name = spc1.name,
                      properties = spc1.properties
                     }

        \end{spec}

        {\em copied from Languages/PSL/Transformations/X:}

        The following makes a name for a new procedure by concatenating a
        string derived from a term. The term is one of the arguments to the
        procedure. This pretty prints the term and then discards all the
        characters that might cause the C parser to complain. This method
        is not entirely sound. To make it sound, it may be necessary to
        introduce a counter to ensure a fresh name or it may be necessary
        to check the list of procedures and if the name is taken, then
        suffix the name with a counter at that point.

        \begin{spec}
          op makeProcName : String -> PTerm -> String
          def makeProcName oldName term =
            let def validChar c = (isAlphaNum c) or (c = #_) in
            let str = ppFormat (ppPTerm term) in 
            let newStr = implode (filter validChar (explode str)) in
            oldName ^ "_" ^ newStr
        \end{spec}


        The following code collects any additional variables in the C code
        that has been introduced in "flattenLhsTerm" above.

        \begin{spec}
          op collUndecStmt: VarDecls * Stmt -> VarDecls
          def collUndecStmt(decls,stmt) =
            case stmt of
              | Exp e -> collUndecExp(decls,e)
              | Block(bdecls,stmts) -> let decls = List.concat(decls,bdecls) in
                                       List.foldl 
                                       (fn(stmt,res) -> List.concat(res,collUndecStmt(decls,stmt)))
                                       [] stmts
              | If(e,s1,s2) -> List.concat(collUndecExp(decls,e),
                                           List.concat(collUndecStmt(decls,s1),collUndecStmt(decls,s2)))
              | Return(e) -> collUndecExp(decls,e)
              | While(e,s) -> List.concat(collUndecExp(decls,e),collUndecStmt(decls,s))
              | IfThen(e,s) -> List.concat(collUndecExp(decls,e),collUndecStmt(decls,s))
              | Switch(e,stmts) -> List.foldl 
                                   (fn(stmt,res) -> List.concat(res,collUndecStmt(decls,stmt)))
                                   (collUndecExp(decls,e)) stmts
              | _ -> []

          op collUndecExp: VarDecls * Exp -> VarDecls
          def collUndecExp(decls,exp) =
            let def isDeclared(vd as (id,_)):Boolean =
                  case List.find (fn(id0,_) -> id0 = id) decls of
                    | Some d -> true
                    | None -> false
            in
            case exp of
              | Var(var) -> if isDeclared(var) then [] else [var]
              | Apply(e,exps) -> List.foldl 
                                 (fn(e0,res) -> List.concat(res,collUndecExp(decls,e0)))
                                 (collUndecExp(decls,e)) exps
              | Cast(_,e) -> collUndecExp(decls,e)
              | StructRef(e,_) -> collUndecExp(decls,e)
              | UnionRef(e,_) -> collUndecExp(decls,e)
              | ArrayRef(e,_) -> collUndecExp(decls,e)
              | IfExp(e0,e1,e2) -> List.concat(collUndecExp(decls,e0),
                                               List.concat(collUndecExp(decls,e1),
                                                           collUndecExp(decls,e2)))
              | Comma(e1,e2) -> List.concat(collUndecExp(decls,e1),collUndecExp(decls,e2))
              | SizeOfExp(e) -> collUndecExp(decls,e)
              | _ -> []

          op collectUndeclared: List(String) * VarDecls * Stmt -> VarDecls
          def collectUndeclared(idlist,decls,stmt) =
            collUndecStmt(List.concat(makeDummyVarDecls(idlist),decls),stmt)

          op makeDummyVarDecls: List(String) -> VarDecls
          def makeDummyVarDecls(idlist) =
            List.map (fn(id) -> (id,Void)) idlist


        \end{spec}

        The following operator splits the undeclared variables into those
        being global and those being local. Here come the hack: because the
        generated names have been created in a way that a "@" sign is inserted
        right after the original name, the fact whether a variable is global
        or not is determined by looking at its prefix, i.e. the string before
        the "@": If it refers to a global variable, then also the generated
        variable will be global, otherwise it will be local.

        \begin{spec}
          op splitUndeclaredVars: List(String) * VarDecls -> (VarDecls * VarDecls)
          def splitUndeclaredVars(globalVarNames,undeclVars) =
            let def getPrefixA(idA) =
                  case idA of
                    | [] -> []
                    | #@::_ -> []
                    | c::cl -> List.cons(c,getPrefixA(cl))
            in
            let def getPrefix(id) =
                  let ida = String.explode(id) in
                  String.implode(getPrefixA(ida))
            in
            case undeclVars of
              | [] -> ([],[])
              | (id,t)::undeclVars -> let idp = getPrefix(id) in
                                      let (gv,lv) = splitUndeclaredVars(globalVarNames,undeclVars) in
                                      if List.member(idp,globalVarNames) then
                                        (List.cons((id,t),gv),lv)
                                      else
                                        (gv,List.cons((id,t),lv))

        \end{spec}

        \begin{spec}
          op removeFancyChars: CSpec -> CSpec
          def removeFancyChars {includes,defines,constDefns,vars,extVars,fns,axioms,
                                typeDefns,structDefns,unionDefns,varDefns,fnDefns} =
            {
             includes=includes,
             defines=defines,
             constDefns=constDefns,
             vars=removeFancyCharsVarDecls(vars),
             extVars=removeFancyCharsVarDecls(extVars),
             fns=fns,
             axioms=axioms,
             typeDefns=typeDefns,
             structDefns=structDefns,
             unionDefns=unionDefns,
             varDefns=varDefns,
             fnDefns=removeFancyCharsFnDefns(fnDefns)
            }

          op removeFancyCharsVarDecl: VarDecl -> VarDecl
          def removeFancyCharsVarDecl(id,t) =
            let def validChar c = (isAlphaNum c) or (c = #_) in
            (String.implode(List.foldr 
                            (fn(c,s) -> if validChar(c) then List.cons(c,s) else s)
                            [] (String.explode(id))),
             t)

          op removeFancyCharsVarDecls: VarDecls -> VarDecls
          def removeFancyCharsVarDecls(decls) =
            List.map removeFancyCharsVarDecl decls

          op removeFancyCharsFnDefns: FnDefns -> FnDefns
          def removeFancyCharsFnDefns(fndefns) =
            List.map (fn(fname,decls,ftype,stmt) -> (fname,removeFancyCharsVarDecls(decls),ftype,
                                                     removeFancyCharsStmt(stmt))) fndefns

          op removeFancyCharsStmt: Stmt -> Stmt
          def removeFancyCharsStmt(stmt) =
            case stmt of
              | Exp(e) -> Exp(removeFancyCharsExp(e))
              | Block(decls,stmts) -> let decls = removeFancyCharsVarDecls(decls) in
                                      let stmts = List.map removeFancyCharsStmt stmts in
                                      Block(decls,stmts)
              | If(e,s1,s2) -> If(removeFancyCharsExp(e),removeFancyCharsStmt(s1),
                                      removeFancyCharsStmt(s2))
              | Return(e) -> Return(removeFancyCharsExp(e))
              | While(e,s) -> While(removeFancyCharsExp(e),removeFancyCharsStmt(s))
              | IfThen(e,s) -> IfThen(removeFancyCharsExp(e),removeFancyCharsStmt(s))
              | Switch(e,stmts) -> let stmts = List.map removeFancyCharsStmt stmts in
                                   Switch(removeFancyCharsExp(e),stmts)
              | stmt -> stmt

          op removeFancyCharsExp: Exp -> Exp
          def removeFancyCharsExp(exp) =
            case exp of
              | Var(vd) -> Var(removeFancyCharsVarDecl(vd))
              | Apply(e,exps) -> Apply(removeFancyCharsExp(e),
                                       List.map removeFancyCharsExp exps)
              | Cast(t,e) -> Cast(t,removeFancyCharsExp(e))
              | StructRef(e,str) -> StructRef(removeFancyCharsExp(e),str)
              | UnionRef(e,str) -> UnionRef(removeFancyCharsExp(e),str)
              | ArrayRef(e,str) -> ArrayRef(removeFancyCharsExp(e),str)
              | SizeOfExp(e) -> SizeOfExp(removeFancyCharsExp(e))
              | IfExp(e1,e2,e3) -> IfExp(removeFancyCharsExp(e1),
                                         removeFancyCharsExp(e2),
                                         removeFancyCharsExp(e3))
              | Comma(e1,e2) -> Comma(removeFancyCharsExp(e1),
                                      removeFancyCharsExp(e2))
              | exp -> exp
            
        \end{spec}

\begin{spec}
}
\end{spec}

