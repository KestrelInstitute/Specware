(*
   Java spec defines an abstract syntax for Java programs using MetaSlang.
*)


spec

sort JavaFile = (*filename*) String * CompUnit

sort CompUnit = Option Name * List Name * List ClsOrInterfDecl
%% Name is for package
%% List Name for imports

sort ClsOrInterfDecl = 
  | ClsDecl     ClsDecl
  | InterfDecl  InterfDecl 

sort ClsDecl = List Mod * ClsHeader * ClsBody

sort InterfDecl = List Mod * InterfHeader * InterfBody

sort Mod = 
  | Public | Protected | Private 
  | Static 
  | Abstract | Final | Native | Synchronized | Transient | Volatile
  | Strictfp 

sort ClsHeader = Ident * SuperCls * SuperInterf

sort InterfHeader = Ident * SuperInterf

sort SuperCls = Option Name

sort SuperInterf = List Name

sort ClsBody = 
  { handwritten : List String,
    staticInits : List Block,
    flds        : List FldDecl,
    constrs     : List ConstrDecl, 
    meths       : List MethDecl,
    clss        : List ClsDecl,
    interfs     : List InterfDecl }  

sort InterfBody = 
  { flds : List FldDecl,
    %% only constants
    meths  : List MethHeader,
    %% only abstract methods
    clss      : List ClsDecl,
    interfs   : List InterfDecl }

sort FldDecl = List Mod * Type * VarDecl * List VarDecl

sort ConstrDecl = 
     List Mod * Ident * FormPars * Throws * Block

sort MethDecl = MethHeader * Option Block

sort VarDecl = VarDeclId * Option VarInit

sort VarDeclId = Ident * Integer
%% Integer is for # of dimensions, 0 indicating it is not an array

sort VarInit = 
  | Expr     Expr
  | ArrInit  ArrInit

sort ArrInit = List (Option VarInit)
%% NONE indicates occurrence of a comma

sort MethHeader = List Mod * RetType * Ident * FormPars * Throws

sort FormPar = Boolean * Type * VarDeclId
%% Boolean value "true" indicates that "final" is present
sort FormPars = List FormPar

sort Throws = List Name

sort Block = List BlockStmt

sort BlockStmt = 
  | LocVarDecl  Boolean * Type * VarDecl * List VarDecl
    %% Boolean indicates if "final" is present
  | ClsDecl     List Mod * ClsHeader * ClsBody
  | Stmt        Stmt

sort Stmt = 
  | Block         Block
  | Labeled       Ident * Stmt
  | If            Expr * Stmt * Option Stmt
  | For           Option ForInit * Option Expr * 
                  Option ForUpdate * Stmt
  | While         Expr * Stmt
  | Do            Stmt * Expr
  | Try           Block * List (FormPar * Block) * Option Block
    %% FormPar * Block is for catch-clause, Option Block for finally-clause.
    %% At least one catch or the finally is present.
  | Switch        Expr * SwitchBlock
  | Synchronized  Expr * Block
  | Return        Option Expr
  | Throw         Expr
  | Break         Option Ident
  | Continue      Option Ident
  | Expr          Expr
  | Empty

sort ForInit =
  | LocVarDecl  Boolean * Type * VarDecl * List VarDecl           
  | StmtExprs    Expr * List Expr 

sort ForUpdate = Expr * List Expr 

sort SwitchBlock = List (List SwitchLab * List BlockStmt)

sort SwitchLab = 
  | JCase     Expr
  | Default

sort Expr = 
  | CondExp CondExp
  | Ass     LHS * AssOp * Expr

sort LHS =
  | Name          Name
    %% field access
  | FldAcc        FldAcc
    %% 2 array access
  | ArrAcc        ArrAcc

sort AssOp = 
  | Assgn 
  | Mul | Div | Rem | Plus | Minus 
  | LShift | RShift | LShiftSpec
  | BitAnd | BitExclOr | BitInclOr
%% = , * = , / = , % = , + = , - = , <<= , >>= , >>>= , & = , ^ = , | =

def assOpToString (o : AssOp) : String = 
    case o of
           Assgn      ->  "="
         | Mul        -> "*="
         | Div        -> "/="
         | Rem        -> "%="
         | Plus       -> "+="
         | Minus      -> "-="
         | LShift     -> "<<="
         | RShift     -> ">>="
         | LShiftSpec -> ">>>="
         | BitAnd     -> "&="
         | BitExclOr  -> "^="
         | BitInclOr  -> "|="


sort CondExp = BinExp * Option (Expr * CondExp)

sort BinExp =  
  | Bin    BinOp * BinExp * BinExp
  | InstOf BinExp * Type
  | Un     UnExp
  
sort BinOp = 
  | CdOr | CdAnd | InclOr | ExclOr | And 
  | Eq | NotEq | Gt | Lt | Ge | Le
  | LShft | RShft | RShftSp
  | Plus | Minus | Mul | Div | Rem

def binOpToString (o : BinOp) : String =
    case o of 
           CdAnd  -> "&&"
         | CdOr   -> "||"
         | InclOr -> "|"
         | ExclOr -> "^"
         | And    -> "&"
         | Eq     -> "=="
         | NotEq  -> "!= "
         | Gt     -> ">"
         | Lt     -> "<"
         | Ge     -> ">="
         | Le     -> "<="
         | LShft  -> "<<"
         | RShft  -> ">>"
         | RShftSp -> ">>>"
         | Plus   -> "+"
         | Minus  -> "-"
         | Mul    -> "*"
         | Div    -> "/"
         | Rem    -> "%"

sort UnExp = 
  | Un      UnOp * UnExp
  | Cast    Type * UnExp
  | PostUn  UnExp * PostUnOp
  | Prim    Prim
%  | Name    Name

sort UnOp = 
  | Plus | Minus
  | PreInc | PreDec
  | BitNot | LogNot

def unOpToString (o : UnOp) : String =
    case o of 
           Plus    -> "+"
         | Minus   -> "-"
         | PreInc  -> "++"
         | PreDec  -> "--"
         | BitNot  -> "~"
         | LogNot  -> "!"

sort PostUnOp = 
  | PostInc | PostDec

def postUnOpToString (o : PostUnOp) : String =
    case o of 
           PostInc -> "++"
         | PostDec -> "--"

sort Prim =
  | Name             Name
    %% 6 literals follow
  | IntL             Integer
  | Float            Integer * Integer
                          %% the second int should be a nat
  | Bool             Boolean
  | Char             Char
  | String           String
  | Null 
    %% Class instance
  | ClsInst          Option Type
    %% this or (Class)Name.this
  | This             Option Name
    %%
  | Paren            Expr
    %% new class inst creation
  | NewClsInst       NewClsInst
    %% new class inst creation
  | NewArr           NewArr
    %% field access
  | FldAcc           FldAcc
    %% Method invocation
  | MethInv          MethInv
    %% 2 array accesses
  | ArrAcc           ArrAcc

def mkNamePr (nm : Name) : Prim = Name nm
def mkIntLPr (i : Integer) : Prim = IntL i
def mkFloatPr (i : Integer, j : Integer)  : Prim = Float (i,j)
def mkBoolPr (b : Boolean) : Prim = Bool b
def mkCharPr (c : Char) : Prim = Char c
def mkStringPr (s : String) : Prim = String s
def mkNullPr () : Prim = Null
def mkClsInstPr (oty :  Option Type) : Prim = ClsInst oty
def mkThisPr (onm : Option Name) : Prim = This onm
def mkParenPr (e : Expr) : Prim = Paren e
def mkNewClsInstPr (nci : NewClsInst) : Prim = NewClsInst nci
def mkNewArrPr (na : NewArr) : Prim = NewArr na
def mkFldAccPr (fac : FldAcc) : Prim = FldAcc fac
def mkMethInvPr (mi : MethInv) : Prim = MethInv mi
def mkArrAccPr (aac : ArrAcc) : Prim = ArrAcc aac


sort NewClsInst =
  | ForCls        Name * List Expr * Option ClsBody
  | ForInnCls     Prim * Ident * List Expr * Option ClsBody

def mkForClsNCI (nm : Name, args : List Expr, cbd : Option ClsBody)
                                                : NewClsInst =
    ForCls (nm, args, cbd)
def mkForInnClsNCI (pm : Prim, id : Ident, args : List Expr,
                            cbd : Option ClsBody): NewClsInst =
    ForInnCls (pm, id, args, cbd) 
 
sort NewArr =
    %% List Expr is for the lenths of the first n dimensions. 
    %% Integer is for the extra # of "[]"
  | Arr           Name * List Expr * Integer
  | ArrWInit      Name * Integer * ArrInit

sort FldAcc =
  | ViaPrim       Prim * Ident
  | ViaSuper      Ident
  | ViaCls        Name * Ident

def mkViaPrimFA (pm : Prim, id : Ident) : FldAcc =
    ViaPrim (pm,id)
def mkViaSuperFA (id : Ident) : FldAcc =
    ViaSuper id
def mkViaClsFA (nm : Name, id : Ident) : FldAcc =
    ViaCls (nm,id)

sort MethInv =
  | ViaName       Name * List Expr
  | ViaPrim      Prim * Ident * List Expr
  | ViaSuper     Ident  * List Expr
  | ViaClsSuper  Name * Ident * List Expr

def mkViaNameMI (nm : Name, args : List Expr) : MethInv =
    ViaName (nm,args)
def mkViaPrimMI (pm : Prim, id : Ident, args : List Expr) 
                                                : MethInv =
    ViaPrim (pm,id,args)
def mkViaSuperMI (id : Ident, args : List Expr) : MethInv =
    ViaSuper (id,args)
def mkViaClsSuperMI (nm : Name, id : Ident, args : List Expr)
                                                : MethInv =
    ViaClsSuper (nm,id,args)

sort ArrAcc = 
  | ViaName        Name * Expr
  | ViaNoNewArray  Prim * Expr


sort Type = BasicOrName * Integer
%% Integer is for dimension, 0 means that it is not an array.

sort BasicOrName = | Basic Basic | Name Name 

sort Basic = 
  | JBool | Byte | Short | Char | JInt | Long | JFloat | Double | Void

sort RetType = Option Type


sort Name = List Ident * Ident
%% Package, method, type, expression names are all qualified identifiers.

sort Ident = String

% --------------------------------------------------------------------------------

op mapJName: (Ident -> Ident) -> CompUnit -> CompUnit
def mapJName ii (optpkg,ifnames,cis) =
  (case optpkg of
     | Some pkg -> Some (mapNameName ii pkg)
     | None -> None,
   map (mapNameName ii)  ifnames,
   map (fn | ClsDecl cld -> ClsDecl(mapNameClsDecl ii cld)
	   | InterfDecl ifd -> InterfDecl(mapNameInterfDecl ii ifd)
       ) cis)

op mapNameName: (Ident -> Ident) -> Name -> Name
def mapNameName ii (clsids,id) =
  (map ii clsids,ii id)

op mapNameClsDecl: (Ident -> Ident) -> ClsDecl -> ClsDecl
def mapNameClsDecl ii (mods,hdr as (id,supercls,superifs),bdy) =
  let hdr = (ii id,mapOption (mapNameName ii) supercls,map (mapNameName ii) superifs) in
  let bdy = mapNameClsBody ii bdy in
  (mods,hdr,bdy)

op mapNameClsBody: (Ident -> Ident) -> ClsBody -> ClsBody
def mapNameClsBody ii bdy =
  {
   handwritten = bdy.handwritten,
   staticInits = map (mapNameBlock ii) bdy.staticInits,
   flds = map (mapNameFldDecl ii) bdy.flds,
   constrs = map (mapNameConstrDecl ii) bdy.constrs,
   meths = map (mapNameMethDecl ii) bdy.meths,
   clss = map (mapNameClsDecl ii) bdy.clss,
   interfs = map (mapNameInterfDecl ii) bdy.interfs
  }

op mapNameInterfDecl: (Ident -> Ident) -> InterfDecl -> InterfDecl
def mapNameInterfDecl ii (mods,hdr as (id,superifs),bdy) =
  let hdr = (ii id,map (mapNameName ii) superifs) in
  let bdy = {
	     flds = map (mapNameFldDecl ii) bdy.flds,
	     meths = map (mapNameMethHeader ii) bdy.meths,
	     clss = map (mapNameClsDecl ii) bdy.clss,
	     interfs = map (mapNameInterfDecl ii) bdy.interfs
	    }
  in
  (mods,hdr,bdy)


op mapNameFldDecl: (Ident -> Ident) -> FldDecl -> FldDecl
def mapNameFldDecl ii (mods,ftype,vdecl,vdecls) =
  let ftype = mapNameType ii ftype in
  let vdecl = mapNameVarDecl ii vdecl in
  let vdecls = map (mapNameVarDecl ii) vdecls in
  (mods,ftype,vdecl,vdecls)

op mapNameConstrDecl: (Ident -> Ident) -> ConstrDecl -> ConstrDecl
def mapNameConstrDecl ii (mods,id,fpars,throws,block) =
  let id = ii id in
  let fpars = map (mapNameFormPar ii) fpars in
  let throws = map (mapNameName ii) throws in
  let block = mapNameBlock ii block in
  (mods,id,fpars,throws,block)

op mapNameMethDecl: (Ident -> Ident) -> MethDecl -> MethDecl
def mapNameMethDecl ii (hdr,optblock) =
  (mapNameMethHeader ii hdr, mapOption (mapNameBlock ii) optblock)

op mapNameMethHeader: (Ident -> Ident) -> MethHeader -> MethHeader
def mapNameMethHeader ii (mods,rettype,id,fpars,throws) =
  let rettype = mapOption (mapNameType ii) rettype in
  let id = ii id in
  let fpars = map (mapNameFormPar ii) fpars in
  let throws = map (mapNameName ii) throws in
  (mods,rettype,id,fpars,throws)

op mapNameVarDecl: (Ident -> Ident) -> VarDecl -> VarDecl
def mapNameVarDecl ii (vdeclid,varinit) =
  let vdeclid = mapNameVarDeclId ii vdeclid in
  let varinit = mapOption (mapNameVarInit ii) varinit in
  (vdeclid,varinit)

op mapNameVarDeclId: (Ident -> Ident) -> VarDeclId -> VarDeclId
def mapNameVarDeclId ii (id,index) =
  (ii id,index)

op mapNameVarInit: (Ident -> Ident) -> VarInit -> VarInit
def mapNameVarInit ii varinit =
  case varinit of
    | Expr e -> Expr(mapNameExpr ii e)
    | ArrInit arrinit -> ArrInit(map (mapOption (mapNameVarInit ii)) arrinit)

op mapNameFormPar: (Ident -> Ident) -> FormPar -> FormPar
def mapNameFormPar ii (isfinal,ptype,vdeclid) =
  let vdeclid = mapNameVarDeclId ii vdeclid in
  let ptype = mapNameType ii ptype in
  (isfinal,ptype,vdeclid)

op mapNameExpr: (Ident -> Ident) -> Expr -> Expr
def mapNameExpr ii expr =
  case expr of
    | CondExp ce -> CondExp(mapNameCondExp ii ce)
    | Ass(lhs,assop,e) -> Ass(mapNameLHS ii lhs,assop,mapNameExpr ii e)

op mapNameCondExp: (Ident -> Ident) -> CondExp -> CondExp
def mapNameCondExp ii (binexp,opte) =
  (mapNameBinExp ii binexp,mapOption (fn(e,ce) -> (mapNameExpr ii e,mapNameCondExp ii ce)) opte)

op mapNameLHS: (Ident -> Ident) -> LHS -> LHS
def mapNameLHS ii lhs =
  case lhs of
    | Name n -> Name(mapNameName ii n)
    | FldAcc facc -> FldAcc(mapNameFldAcc ii facc)
    | ArrAcc arracc -> ArrAcc(mapNameArrAcc ii arracc)

op mapNameFldAcc: (Ident -> Ident) -> FldAcc -> FldAcc
def mapNameFldAcc ii facc =
  case facc of
    | ViaPrim (p,id) -> ViaPrim(mapNamePrim ii p,ii id)
    | ViaSuper id -> ViaSuper (ii id)
    | ViaCls(n,id) -> ViaCls(mapNameName ii n,ii id)

op mapNameArrAcc: (Ident -> Ident) -> ArrAcc -> ArrAcc
def mapNameArrAcc ii arracc =
  case arracc of
    | ViaName(n,e) -> ViaName(mapNameName ii n,mapNameExpr ii e)
    | ViaNoNewArray(p,e) -> ViaNoNewArray(mapNamePrim ii p,mapNameExpr ii e)

op mapNameType: (Ident -> Ident) -> Type -> Type
def mapNameType ii (bname,ind) =
  (mapNameBasicOrName ii bname,ind)

op mapNameBasicOrName: (Ident -> Ident) -> BasicOrName -> BasicOrName
def mapNameBasicOrName ii bname =
  case bname of
    | Basic _ -> bname
    | Name n -> Name(mapNameName ii n)

op mapNameBlock: (Ident -> Ident) -> Block -> Block
def mapNameBlock ii block =
  map (fn LocVarDecl (isfinal,t,vdecl,vdecls) ->
          LocVarDecl(isfinal,mapNameType ii t,mapNameVarDecl ii vdecl,map (mapNameVarDecl ii) vdecls)
	| ClsDecl cld -> ClsDecl(mapNameClsDecl ii cld)
	| Stmt stmt -> Stmt(mapNameStmt ii stmt)
	 ) block

op mapNameStmt: (Ident -> Ident) -> Stmt -> Stmt
def mapNameStmt ii stmt =
  case stmt of
    | Block block -> Block(mapNameBlock ii block)
    | Labeled(id,stmt) -> Labeled(ii id,mapNameStmt ii stmt)
    | If(e,stmt,optstmt) -> If(mapNameExpr ii e,mapNameStmt ii stmt, mapOption (mapNameStmt ii) optstmt)
    | For(optfinit,optexpr,optfupd,stmt) ->
      For(mapOption (mapNameForInit ii) optfinit,
	  mapOption (mapNameExpr ii) optexpr,
	  mapOption (mapNameForUpdate ii) optfupd,
	  mapNameStmt ii stmt)
    | While(e,stmt) -> While(mapNameExpr ii e,mapNameStmt ii stmt)
    | Do(stmt,e) -> Do(mapNameStmt ii stmt,mapNameExpr ii e)
    | Try(block,fparsblocks,optblock) ->
      Try(mapNameBlock ii block,map (fn(fpar,block) -> (mapNameFormPar ii fpar,mapNameBlock ii block)) fparsblocks,
	  mapOption (mapNameBlock ii) optblock)
    | Switch(e,swblock) -> Switch(mapNameExpr ii e,mapNameSwitchBlock ii swblock)
    | Synchronized(e,block) -> Synchronized(mapNameExpr ii e,mapNameBlock ii block)
    | Return(opte) -> Return(mapOption (mapNameExpr ii) opte)
    | Throw(e) -> Throw(mapNameExpr ii e)
    | Break(optid) -> Break(mapOption ii optid)
    | Continue(optid) -> Continue(mapOption ii optid)
    | Expr e -> Expr(mapNameExpr ii e)
    | Empty -> Empty


op mapNameForInit: (Ident -> Ident) -> ForInit -> ForInit
def mapNameForInit ii finit =
  case finit of
    | LocVarDecl(isfinal,t,vdecl,vdecls) ->
      LocVarDecl(isfinal,mapNameType ii t,mapNameVarDecl ii vdecl,map (mapNameVarDecl ii) vdecls)
    | StmtExprs(e,el) -> StmtExprs(mapNameExpr ii e,map (mapNameExpr ii) el)

op mapNameForUpdate: (Ident -> Ident) -> ForUpdate -> ForUpdate
def mapNameForUpdate ii (e,el) =
  (mapNameExpr ii e,map (mapNameExpr ii) el)

op mapNameSwitchBlock: (Ident -> Ident) -> SwitchBlock -> SwitchBlock
def mapNameSwitchBlock ii swblock =
  map (fn(labels,block) ->
       let labels = map (fn(lbl) ->
			 case lbl of
			   | JCase e -> JCase(mapNameExpr ii e)
			   | Default -> Default) labels
       in
       (labels,mapNameBlock ii block)) swblock


op mapNameBinExp: (Ident -> Ident) -> BinExp -> BinExp
def mapNameBinExp ii binexp =
  case binexp of
    | Bin(binop,binexp1,binexp2) -> Bin(binop,mapNameBinExp ii binexp1,mapNameBinExp ii binexp2)
    | InstOf(binexp,etype) -> InstOf(mapNameBinExp ii binexp,mapNameType ii etype)
    | Un(unexp) -> Un(mapNameUnExp ii unexp)

op mapNameUnExp: (Ident -> Ident) -> UnExp -> UnExp
def mapNameUnExp ii unexp =
  case unexp of
    | Un(unop,unexp) -> Un(unop,mapNameUnExp ii unexp)
    | Cast(etype,unexp) -> Cast(mapNameType ii etype,mapNameUnExp ii unexp)
    | PostUn(unexp,pop) -> PostUn(mapNameUnExp ii unexp,pop)
    | Prim p -> Prim(mapNamePrim ii p)

op mapNamePrim: (Ident -> Ident) -> Prim -> Prim
def mapNamePrim ii p =
  case p of
    | Name n -> Name(mapNameName ii n)
    | ClsInst opttype -> ClsInst(mapOption (mapNameType ii) opttype)
    | This optname -> This(mapOption (mapNameName ii) optname)
    | Paren e -> Paren(mapNameExpr ii e)
    | NewClsInst newclsinst -> NewClsInst(mapNameNewClsInst ii newclsinst)
    | NewArr narr -> NewArr(mapNameNewArr ii narr)
    | FldAcc facc -> FldAcc(mapNameFldAcc ii facc)
    | MethInv minv -> MethInv(mapNameMethInv ii minv)
    | ArrAcc arracc -> ArrAcc(mapNameArrAcc ii arracc)
    | _ -> p
    
op mapNameNewClsInst: (Ident -> Ident) -> NewClsInst -> NewClsInst
def mapNameNewClsInst ii newclsinst =
  case newclsinst of
    | ForCls(n,el,optbody) -> ForCls(mapNameName ii n,map (mapNameExpr ii) el,mapOption (mapNameClsBody ii) optbody)
    | ForInnCls(p,id,el,optbody) -> ForInnCls(mapNamePrim ii p,ii id,map (mapNameExpr ii) el,
					      mapOption (mapNameClsBody ii) optbody)

op mapNameNewArr: (Ident -> Ident) -> NewArr -> NewArr
def mapNameNewArr ii newarr =
  case newarr of
    | Arr(n,el,nmb) -> Arr(mapNameName ii n,map (mapNameExpr ii) el,nmb)
    | ArrWInit(n,nmb,arrinit) -> ArrWInit(mapNameName ii n,nmb,map (mapOption (mapNameVarInit ii)) arrinit)

op mapNameMethInv: (Ident -> Ident) -> MethInv -> MethInv
def mapNameMethInv ii minv =
  case minv of
    | ViaName(n,el) -> ViaName(mapNameName ii n,map (mapNameExpr ii) el)
    | ViaPrim(p,id,el) -> ViaPrim(mapNamePrim ii p,ii id,map (mapNameExpr ii) el)
    | ViaSuper(id,el) -> ViaSuper(ii id,map (mapNameExpr ii) el)
    | ViaClsSuper(n,id,el) -> ViaClsSuper(mapNameName ii n,ii id,map (mapNameExpr ii) el)


op javaKeyword?: Ident -> Boolean
def javaKeyword?(id) =
  id="abstract" or
  id="double" or
  id="int" or
  id="strictfp" or
  id="boolean" or
  id="else" or
  id="interface" or
  id="super" or
  id="break" or
  id="extends" or
  id="long" or
  id="switch" or
  id="byte" or
  id="final" or
  id="native" or
  id="synchronized" or
  id="case" or
  id="finally" or
  id="new" or
  id="this" or
  id="catch" or
  id="float" or
  id="package" or
  id="throw" or
  id="char" or
  id="for" or
  id="private" or
  id="throws" or
  id="class" or
  id="protected" or
  id="transient" or
  id="const" or
  id="if" or
  id="goto" or
  id="public" or
  id="try" or
  id="continue" or
  id="implements" or
  id="return" or
  id="void" or
  id="default" or
  id="import" or
  id="short" or
  id="volatile" or
  id="do" or
  id="instanceof" or
  id="static" or
  id="while"

endspec

