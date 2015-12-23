(* Copyright 2015 Kestrel Institute. See file LICENSE for license details *)

(*
   Java spec defines an abstract syntax for Java programs using MetaSlang.
*)

Java qualifying
spec

type JavaFile = (*filename*) String * CompUnit

type CompUnit = Option JavaName * List JavaName * List ClsOrInterfDecl
%% JavaName is for package
%% List JavaName for imports

type ClsOrInterfDecl = 
  | ClsDecl     ClsDecl
  | InterfDecl  InterfDecl 

type ClsDecl = List Mod * ClsHeader * ClsBody

type InterfDecl = List Mod * InterfHeader * InterfBody

type Mod = 
  | Public | Protected | Private 
  | Static 
  | Abstract | Final | Native | Synchronized | Transient | Volatile
  | Strictfp 

type ClsHeader = Ident * SuperCls * SuperInterf

type InterfHeader = Ident * SuperInterf

type SuperCls = Option JavaName

type SuperInterf = List JavaName

type ClsBody = 
  { handwritten : List String,
    staticInits : List JavaBlock,
    flds        : List FldDecl,
    constrs     : List ConstrDecl, 
    meths       : List MethDecl,
    clss        : List ClsDecl,
    interfs     : List InterfDecl }  

type InterfBody = 
  { flds : List FldDecl,
    %% only constants
    meths  : List MethHeader,
    %% only abstract methods
    clss      : List ClsDecl,
    interfs   : List InterfDecl }

type FldDecl = List Mod * JavaType * VarDecl * List VarDecl

type ConstrDecl = 
     List Mod * Ident * FormPars * Throws * JavaBlock

type MethDecl = MethHeader * Option JavaBlock

type VarDecl = VarDeclId * Option VarInit

type VarDeclId = Ident * Int
%% Int is for # of dimensions, 0 indicating it is not an array

type VarInit = 
  | Expr     JavaExpr
  | ArrInit  ArrInit

type ArrInit = List (Option VarInit)
%% NONE indicates occurrence of a comma

type MethHeader = List Mod * JavaRetType * Ident * FormPars * Throws

type FormPar = Bool * JavaType * VarDeclId
%% Boolean value "true" indicates that "final" is present
type FormPars = List FormPar

type Throws = List JavaName

type JavaBlock = List JavaBlockStmt

type JavaBlockStmt = 
  | LocVarDecl  Bool * JavaType * VarDecl * List VarDecl
    %% Boolean indicates if "final" is present
  | ClsDecl     List Mod * ClsHeader * ClsBody
  | Stmt        JavaStmt

type JavaStmt = 
  | Block         JavaBlock
  | Labeled       Ident * JavaStmt
  | If            JavaExpr * JavaStmt * Option JavaStmt
  | For           Option ForInit * Option JavaExpr * 
                  Option ForUpdate * JavaStmt
  | While         JavaExpr * JavaStmt
  | Do            JavaStmt * JavaExpr
  | Try           JavaBlock * List (FormPar * JavaBlock) * Option JavaBlock
    %% FormPar * JavaBlock is for catch-clause, Option JavaBlock for finally-clause.
    %% At least one catch or the finally is present.
  | Switch        JavaExpr * SwitchBlock
  | Synchronized  JavaExpr * JavaBlock
  | Return        Option JavaExpr
  | Throw         JavaExpr
  | Break         Option Ident
  | Continue      Option Ident
  | Expr          JavaExpr
  | Empty

type ForInit =
  | LocVarDecl  Bool * JavaType * VarDecl * List VarDecl           
  | StmtExprs    JavaExpr * List JavaExpr 

type ForUpdate = JavaExpr * List JavaExpr 

type SwitchBlock = List (List SwitchLab * List JavaBlockStmt)

type SwitchLab = 
  | JCase     JavaExpr
  | Default

type JavaExpr = 
  | CondExp CondExp
  | Ass     JavaLHS * AssOp * JavaExpr

type JavaLHS =
  | Name          JavaName
    %% field access
  | FldAcc        FldAcc
    %% 2 array access
  | ArrAcc        ArrAcc

type AssOp = 
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


type CondExp = BinExp * Option (JavaExpr * CondExp)

type BinExp =  
  | Bin    BinOp * BinExp * BinExp
  | InstOf BinExp * JavaType
  | Un     UnExp
  
type BinOp = 
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

type UnExp = 
  | Un      UnOp * UnExp
  | Cast    JavaType * UnExp
  | PostUn  UnExp * PostUnOp
  | Prim    Prim
%  | Name    JavaName

type UnOp = 
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

type PostUnOp = 
  | PostInc | PostDec

def postUnOpToString (o : PostUnOp) : String =
    case o of 
           PostInc -> "++"
         | PostDec -> "--"

type Prim =
  | Name             JavaName
    %% 6 literals follow
  | IntL             Int
  | Float            Int * Int
                          %% the second int should be a nat
  | Bool             Bool
  | Char             Char
  | String           String
  | Null 
    %% Class instance
  | ClsInst          Option JavaType
    %% this or (Class)JavaName.this
  | This             Option JavaName
    %%
  | Paren            JavaExpr
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

def mkNamePr (nm : JavaName) : Prim = Name nm
def mkIntLPr (i : Int) : Prim = IntL i
def mkFloatPr (i : Int, j : Int)  : Prim = Float (i,j)
def mkBoolPr (b : Bool) : Prim = Bool b
def mkCharPr (c : Char) : Prim = Char c
def mkStringPr (s : String) : Prim = String s
def mkNullPr () : Prim = Null
def mkClsInstPr (oty :  Option JavaType) : Prim = ClsInst oty
def mkThisPr (onm : Option JavaName) : Prim = This onm
def mkParenPr (e : JavaExpr) : Prim = Paren e
def mkNewClsInstPr (nci : NewClsInst) : Prim = NewClsInst nci
def mkNewArrPr (na : NewArr) : Prim = NewArr na
def mkFldAccPr (fac : FldAcc) : Prim = FldAcc fac
def mkMethInvPr (mi : MethInv) : Prim = MethInv mi
def mkArrAccPr (aac : ArrAcc) : Prim = ArrAcc aac


type NewClsInst =
  | ForCls        JavaName * List JavaExpr * Option ClsBody
  | ForInnCls     Prim * Ident * List JavaExpr * Option ClsBody

def mkForClsNCI (nm : JavaName, args : List JavaExpr, cbd : Option ClsBody)
                                                : NewClsInst =
    ForCls (nm, args, cbd)
def mkForInnClsNCI (pm : Prim, id : Ident, args : List JavaExpr,
                            cbd : Option ClsBody): NewClsInst =
    ForInnCls (pm, id, args, cbd) 
 
type NewArr =
    %% List JavaExpr is for the lenths of the first n dimensions. 
    %% Int is for the extra # of "[]"
  | Arr           JavaName * List JavaExpr * Int
  | ArrWInit      JavaName * Int * ArrInit

type FldAcc =
  | ViaPrim       Prim * Ident
  | ViaSuper      Ident
  | ViaCls        JavaName * Ident

def mkViaPrimFA (pm : Prim, id : Ident) : FldAcc =
    ViaPrim (pm,id)
def mkViaSuperFA (id : Ident) : FldAcc =
    ViaSuper id
def mkViaClsFA (nm : JavaName, id : Ident) : FldAcc =
    ViaCls (nm,id)

type MethInv =
  | ViaName       JavaName * List JavaExpr
  | ViaPrim      Prim * Ident * List JavaExpr
  | ViaSuper     Ident  * List JavaExpr
  | ViaClsSuper  JavaName * Ident * List JavaExpr

def mkViaNameMI (nm : JavaName, args : List JavaExpr) : MethInv =
    ViaName (nm,args)
def mkViaPrimMI (pm : Prim, id : Ident, args : List JavaExpr) 
                                                : MethInv =
    ViaPrim (pm,id,args)
def mkViaSuperMI (id : Ident, args : List JavaExpr) : MethInv =
    ViaSuper (id,args)
def mkViaClsSuperMI (nm : JavaName, id : Ident, args : List JavaExpr)
                                                : MethInv =
    ViaClsSuper (nm,id,args)

type ArrAcc = 
  | ViaName        JavaName * JavaExpr
  | ViaNoNewArray  Prim * JavaExpr


type JavaType = BasicOrName * Int
%% Int is for dimension, 0 means that it is not an array.

type BasicOrName = | Basic Basic | Name JavaName 

type Basic = 
  | JBool | Byte | Short | Char | JInt | Long | JFloat | Double | Void

type JavaRetType = Option JavaType


type JavaName = List Ident * Ident
%% Package, method, type, expression names are all qualified identifiers.

type Ident = String

% --------------------------------------------------------------------------------

op Java.emptyClsBody: ClsBody
def Java.emptyClsBody =
  { handwritten = [],
    staticInits = [],
    flds        = [],
    constrs     = [], 
    meths       = [],
    clss        = [],
    interfs     = [] }



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

op mapNameName: (Ident -> Ident) -> JavaName -> JavaName
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

op mapNameExpr: (Ident -> Ident) -> JavaExpr -> JavaExpr
def mapNameExpr ii expr =
  case expr of
    | CondExp ce -> CondExp(mapNameCondExp ii ce)
    | Ass(lhs,assop,e) -> Ass(mapNameLHS ii lhs,assop,mapNameExpr ii e)

op mapNameCondExp: (Ident -> Ident) -> CondExp -> CondExp
def mapNameCondExp ii (binexp,opte) =
  (mapNameBinExp ii binexp,mapOption (fn(e,ce) -> (mapNameExpr ii e,mapNameCondExp ii ce)) opte)

op mapNameLHS: (Ident -> Ident) -> JavaLHS -> JavaLHS
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

op mapNameType: (Ident -> Ident) -> JavaType -> JavaType
def mapNameType ii (bname,ind) =
  (mapNameBasicOrName ii bname,ind)

op mapNameBasicOrName: (Ident -> Ident) -> BasicOrName -> BasicOrName
def mapNameBasicOrName ii bname =
  case bname of
    | Basic _ -> bname
    | Name n -> Name(mapNameName ii n)

op mapNameBlock: (Ident -> Ident) -> JavaBlock -> JavaBlock
def mapNameBlock ii block =
  map (fn LocVarDecl (isfinal,t,vdecl,vdecls) ->
          LocVarDecl(isfinal,mapNameType ii t,mapNameVarDecl ii vdecl,map (mapNameVarDecl ii) vdecls)
	| ClsDecl cld -> ClsDecl(mapNameClsDecl ii cld)
	| Stmt stmt -> Stmt(mapNameStmt ii stmt)
	 ) block

op mapNameStmt: (Ident -> Ident) -> JavaStmt -> JavaStmt
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


op javaKeyword?: Ident -> Bool
def javaKeyword? id =
  id="abstract" ||
  id="double" ||
  id="int" ||
  id="strictfp" ||
  id="boolean" ||
  id="else" ||
  id="interface" ||
  id="super" ||
  id="break" ||
  id="extends" ||
  id="long" ||
  id="switch" ||
  id="byte" ||
  id="final" ||
  id="native" ||
  id="synchronized" ||
  id="case" ||
  id="finally" ||
  id="new" ||
  id="this" ||
  id="catch" ||
  id="float" ||
  id="package" ||
  id="throw" ||
  id="char" ||
  id="for" ||
  id="private" ||
  id="throws" ||
  id="class" ||
  id="protected" ||
  id="transient" ||
  id="const" ||
  id="if" ||
  id="goto" ||
  id="public" ||
  id="try" ||
  id="continue" ||
  id="implements" ||
  id="return" ||
  id="void" ||
  id="default" ||
  id="import" ||
  id="short" ||
  id="volatile" ||
  id="do" ||
  id="instanceof" ||
  id="static" ||
  id="while"

% --------------------------------------------------------------------------------

% auxiliary type to extract the actual expression from a JavaExpr, i.e. any
% "wrapping" constructor is stripped from the expression.

type ActualExpr = | Expr JavaExpr
                  | CondExp CondExp
                  | BinExp BinExp
                  | UnExp UnExp
                  | Prim Prim

% returns the actual expr, i.e. "wrapper" constructors are removed
% in order to get the real contents of the expression
op Expr.getActualExpr: JavaExpr -> ActualExpr
def Expr.getActualExpr e =
  case e of
    | CondExp ce -> getActualExpr ce
    | _ -> Expr e

op CondExp.getActualExpr: CondExp -> ActualExpr
def CondExp.getActualExpr ce =
  case ce of
    | (be,None) -> getActualExpr be
    | _ -> CondExp ce

op BinExp.getActualExpr: BinExp -> ActualExpr
def BinExp.getActualExpr be =
  case be of
    | Un ue -> getActualExpr ue
    | _ -> BinExp be

op UnExp.getActualExpr: UnExp -> ActualExpr
def UnExp.getActualExpr ue =
  case ue of
    | Prim p -> getActualExpr p
    | _ -> UnExp ue

op Prim.getActualExpr: Prim -> ActualExpr
def Prim.getActualExpr p =
  case p of
    | Paren e -> getActualExpr e
    | _ -> Prim p

% ----------------------------------------

% wrap the ActualExpr so that it becomes a JavaExpr
op ActualExpr.wrap: ActualExpr -> JavaExpr
def ActualExpr.wrap ae =
  case ae of
    | Expr e -> e
    | CondExp ce -> CondExp ce
    | BinExp be -> wrap(CondExp (be,None))
    | UnExp ue -> wrap(BinExp (Un ue))
    | Prim p -> wrap(UnExp (Prim p))

% --------------------------------------------------------------------------------

op getMapExprFun: (JavaExpr * JavaExpr) -> JavaExpr -> JavaExpr
def getMapExprFun(oldExpr,newExpr) e0 =
  let actualOldExpr = getActualExpr oldExpr in
  let actualE0 = getActualExpr e0 in
  if actualE0 = actualOldExpr then newExpr
  else e0

op Expr.mapOneExpr: (JavaExpr * JavaExpr) -> JavaExpr -> JavaExpr
def Expr.mapOneExpr (oldExpr,newExpr) =
  let mex = getMapExprFun(oldExpr,newExpr) in
  mapExpr mex

op Block.mapOneExpr: (JavaExpr * JavaExpr) -> JavaBlock -> JavaBlock
def Block.mapOneExpr(oldExpr,newExpr) =
  let mex = getMapExprFun(oldExpr,newExpr) in
  mapExpr mex


% --------------------------------------------------------------------------------

op Expr.mapExpr: (JavaExpr -> JavaExpr) -> JavaExpr -> JavaExpr
def Expr.mapExpr mex e =
  let e1 =
    case e of
      | CondExp ce -> CondExp(mapExpr mex ce)
      | Ass(lhs,assignop,e) -> Ass(lhs,assignop,mapExpr mex e)
  in
  if e1 = e then mex e else e1

op CondExp.mapExpr: (JavaExpr -> JavaExpr) -> CondExp -> CondExp
def CondExp.mapExpr mex ce =
  case ce of
    | (be,None) -> (mapExpr mex be,None)
    | (be,Some(e,ce)) -> (mapExpr mex be,Some(mapExpr mex e,mapExpr mex ce))


op BinExp.mapExpr: (JavaExpr -> JavaExpr) -> BinExp -> BinExp
def BinExp.mapExpr mex be =
  case be of
    | Bin(bop,be1,be2) -> Bin(bop,mapExpr mex be1,mapExpr mex be2)
    | InstOf(be,ty) -> InstOf(mapExpr mex be,ty)
    | Un ue -> Un(mapExpr mex ue)

op UnExp.mapExpr: (JavaExpr -> JavaExpr) -> UnExp -> UnExp
def UnExp.mapExpr mex ue =
  case ue of
    | Un(uop,ue) -> Un(uop,mapExpr mex ue)
    | Cast(ty,ue) -> Cast(ty,mapExpr mex ue)
    | PostUn(ue,puop) -> PostUn(mapExpr mex ue,puop)
    | Prim p -> Prim(mapExpr mex p)

op Prim.mapExpr: (JavaExpr -> JavaExpr) -> Prim -> Prim
def Prim.mapExpr mex p =
  case p of
    | Paren e -> Paren(mapExpr mex e)
    | NewClsInst nci -> NewClsInst(mapExpr mex nci)
    | NewArr na -> NewArr(mapExpr mex na)
    | FldAcc facc -> FldAcc(mapExpr mex facc)
    | MethInv mi -> MethInv(mapExpr mex mi)
    | ArrAcc aacc -> ArrAcc(mapExpr mex aacc)
    | _ -> p



op NewClsInst.mapExpr: (JavaExpr -> JavaExpr) -> NewClsInst -> NewClsInst
def NewClsInst.mapExpr mex nci =
  case nci of
    | ForCls(n,es,optcb) ->
      let es = map (mapExpr mex) es in
      let optcb = mapOption (mapExpr mex) optcb in
      ForCls(n,es,optcb)
    | ForInnCls(p,id,es,optcb) ->
      let p = mapExpr mex p in
      let es = map (mapExpr mex) es in
      let optcb = mapOption (mapExpr mex) optcb in
      ForInnCls(p,id,es,optcb)

op NewArr.mapExpr: (JavaExpr -> JavaExpr) -> NewArr -> NewArr
def NewArr.mapExpr mex na =
  case na of
    | Arr(name,es,n) -> Arr(name,map (mapExpr mex) es,n)
    | ArrWInit(name,n,ai) -> ArrWInit(name,n,mapExpr mex ai)

op ArrInit.mapExpr: (JavaExpr -> JavaExpr) -> ArrInit -> ArrInit
def ArrInit.mapExpr mex ai =
  map (mapOption (mapExpr mex)) ai

op VarInit.mapExpr: (JavaExpr -> JavaExpr) -> VarInit -> VarInit
def VarInit.mapExpr mex vi =
  case vi of
    | Expr e -> Expr(mapExpr mex e)
    | ArrInit ai -> ArrInit(mapExpr mex ai)

op FldAcc.mapExpr: (JavaExpr -> JavaExpr) -> FldAcc -> FldAcc
def FldAcc.mapExpr mex facc =
  case facc of
    | ViaPrim(p,id) -> ViaPrim(mapExpr mex p,id)
    | _ -> facc

op MethInv.mapExpr: (JavaExpr -> JavaExpr) -> MethInv -> MethInv
def MethInv.mapExpr mex mi =
  case mi of
    | ViaName(name,es) -> ViaName(name,map (mapExpr mex) es)
    | ViaPrim(p,id,es) -> ViaPrim(mapExpr mex p,id,map (mapExpr mex) es)
    | ViaSuper(id,es) -> ViaSuper(id,map (mapExpr mex) es)
    | ViaClsSuper(name,id,es) -> ViaClsSuper(name,id,map (mapExpr mex) es)

op ArrAcc.mapExpr: (JavaExpr -> JavaExpr) -> ArrAcc -> ArrAcc
def ArrAcc.mapExpr mex aacc =
  case aacc of
    | ViaName(name,e) -> ViaName(name,mapExpr mex e)
    | ViaNoNewArray(p,e) -> ViaNoNewArray(mapExpr mex p,mapExpr mex e)

op Block.mapExpr: (JavaExpr -> JavaExpr) -> JavaBlock -> JavaBlock
def Block.mapExpr mex = map (mapExpr mex)

op BlockStmt.mapExpr: (JavaExpr -> JavaExpr) -> JavaBlockStmt -> JavaBlockStmt
def BlockStmt.mapExpr mex bstmt =
  case bstmt of
    | LocVarDecl(isfinal,ty,vdecl,vdecls) -> LocVarDecl(isfinal,ty,mapExpr mex vdecl,map (mapExpr mex) vdecls)
    | ClsDecl(mods,ch,cb) -> ClsDecl(mods,ch,mapExpr mex cb)
    | Stmt s -> Stmt(mapExpr mex s)

op VarDecl.mapExpr: (JavaExpr -> JavaExpr) -> VarDecl -> VarDecl
def VarDecl.mapExpr mex (vdid,optvi) =
  (vdid,mapOption (mapExpr mex) optvi)

op Stmt.mapExpr: (JavaExpr -> JavaExpr) -> JavaStmt -> JavaStmt
def Stmt.mapExpr mex s =
  case s of
    | Block b -> Block(mapExpr mex b)
    | Labeled(id,s) -> Labeled(id,mapExpr mex s)
    | If(e,s,opts) -> If(mapExpr mex e,mapExpr mex s,mapOption (mapExpr mex) opts)
    | For(optfi,opte,optfu,s) -> For(mapOption (mapExpr mex) optfi,
				     mapOption (mapExpr mex) opte,
				     mapOption (mapExpr mex) optfu,
				     mapExpr mex s)
    | While(e,s) -> While(mapExpr mex e,mapExpr mex s)
    | Do(s,e) -> Do(mapExpr mex s,mapExpr mex e)
    | Try(b,fpbs,optb) -> Try(mapExpr mex b,
			      map (fn(fp,b) -> (fp,mapExpr mex b)) fpbs,
			      mapOption (mapExpr mex) optb)
    | Switch(e,sb) -> Switch(mapExpr mex e,
			     map (fn(swlabs,b) -> (map (fn(JCase e) -> JCase(mapExpr mex e)
							 | Default -> Default) swlabs,
						   mapExpr mex b)) sb)
    | Synchronized(e,b) -> Synchronized(mapExpr mex e,mapExpr mex b)
    | Return opte -> Return(mapOption (mapExpr mex) opte)
    | Throw e -> Throw(mapExpr mex e)
    | Expr e -> Expr(mapExpr mex e)
    | _ -> s


op ForInit.mapExpr: (JavaExpr -> JavaExpr) -> ForInit -> ForInit
def ForInit.mapExpr mex fi =
  case fi of
    | LocVarDecl(isfinal,ty,vdecl,vdecls) -> LocVarDecl(isfinal,ty,mapExpr mex vdecl,map (mapExpr mex) vdecls)
    | StmtExprs(e,es) -> StmtExprs(mapExpr mex e,map (mapExpr mex) es)

op ForUpdate.mapExpr: (JavaExpr -> JavaExpr) -> ForUpdate -> ForUpdate
def ForUpdate.mapExpr mex (e,es) =
  (mapExpr mex e,map (mapExpr mex) es)

%%% TODO !!!
op ClsBody.mapExpr: (JavaExpr -> JavaExpr) -> ClsBody -> ClsBody
def ClsBody.mapExpr _(*mex*) cb = cb


endspec

