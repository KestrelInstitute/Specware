(*
   Java spec defines an abstract syntax for Java programs using MetaSlang.
*)


spec


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
  { staticInits : List Block,
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

endspec

