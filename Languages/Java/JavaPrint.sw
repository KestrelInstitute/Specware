
(*
   Pretty printing the Java spec in java-zq.sl.
*)

Java qualifying spec
  import Java
  import /Library/PrettyPrinter/BjornerEspinosa

%%%% Renaming pp.sl interfaces

  def toPretty = string

%%%% Utilitiy functions

  % concatList is in spec StringUtilities
  def concatList (sl : List String) : String = 
      List.foldr String.concat "" sl

  % qualName (["aa","bb","cc"],"dd") = "aa.bb.cc.dd"
  def qualName (ids : List Ident, id : Ident) : String =
      List.foldr 
        (fn (x,y) -> if x = "" then y
                     else if y = "" then x
                     else concatList [x,".",y])
        ""
        (List.concat (ids, [id]))

  % addPrettys ([p1,p2,p3],q) = [p1,q,p2,q,p3]
  def addPrettys (ps : Prettys, p : Pretty) : Prettys = 
        case ps of 
           [] -> ps
         | q::[] -> ps
         | q1::(q2::ps1) -> 
             List.cons 
               (q1, 
                (List.cons 
                   (p, addPrettys (List.cons (q2,ps1), p))))
 
  def addEmpty (ps : Prettys) : Prettys =
        if ps = [] then []
        else List.cons (emptyPretty (), ps)

  def addEmptys (ps : Prettys) : Prettys =
      addPrettys (ps, emptyPretty ())

  def addCommentLine (comment : String, ps : Prettys) : Prettys =
        if comment = "" then ps
        else List.cons (toPretty comment, ps)

  def emptyBrackets (n : Integer) : Pretty =
      if n <= 0 then emptyPretty () 
      else prettysNone [toPretty "[]", emptyBrackets(n - 1)]


%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%

%%%% compilation units

  def ppCompUnit ((pn,ims,cids) : CompUnit) : Pretty =
      let pnps =
          case pn of
            None    -> []
          | Some nm -> addEmpty [ppPackageName nm] 
      in
      let imsps = 
          if ims = [] then []
          else addEmpty [ppImports ims] 
      in
      prettysAll 
        (List.flatten 
           [pnps,
            imsps,
            addEmpty 
              (addEmptys (List.map ppClsOrInterfDecl cids))])

%%%% package name 

  def ppPackageName (nm : Name) : Pretty =
      prettysNone [toPretty "package ", ppName nm, toPretty ";"]

%%%% import declarations

  def ppImports (ims : List Name) : Pretty =
      prettysAll 
        (List.map
           (fn nm ->
               prettysNone
                 [toPretty "import ", ppName nm, toPretty ";"])
           ims)

%%%% single class or interface declaration

  def ppClsOrInterfDecl (cid : ClsOrInterfDecl) : Pretty =
      case cid of 
        ClsDecl cd -> ppClsDecl cd
      | InterfDecl ifd -> ppInterfDecl ifd

%%%% single class declaration

  def ppClsDecl (ms : List Mod, ch : ClsHeader, cb : ClsBody) 
                                                  : Pretty =
      prettysAll
         (List.cons
            (prettysNone [ppMods ms,
                          ppClsHeader ch, 
                          toPretty " ",
                          toPretty "{"],
             if isEmptyClsBody(cb) then [toPretty "}"]
             else [emptyPretty (), 
                   prettysNone [toPretty "  ", ppClsBody cb],
                   emptyPretty (),
                   toPretty "}"]
             ))
 
%%%% single interface declaration

  def ppInterfDecl (ms : List Mod, ih : InterfHeader, 
                    ib : InterfBody) : Pretty =
      prettysAll
         (List.cons
            (prettysNone [ppMods ms,
                          ppInterfHeader ih,
                          toPretty " ",
                          toPretty "{"],
             if isEmptyInterfBody(ib) then [toPretty "}"]
             else [emptyPretty (),
                   prettysNone [toPretty "  ", ppInterfBody ib],
                   emptyPretty (),
                   toPretty "}"]))

%%%% modifiers

  def ppMods (ms : List Mod) : Pretty =
      let ps = 
        List.map 
        (fn n ->  
          toPretty
            (case n of
               Public       -> "public "
             | Protected    -> "protected "
             | Private      -> "private "
             | Static       -> "static "
             | Abstract     -> "abstract "
             | Final        -> "final "
             | Native       -> "native "
             | Synchronized -> "synchronized "
             | Transient    -> "transient "
             | Volatile     -> "volatile "
             | Strictfp     -> "strictfp "
            ))
         ms
       in prettysNone (ps) 

%%%% class header

  def ppClsHeader (id : Ident, sc : SuperCls, sis : SuperInterf) 
                                                      : Pretty =
      prettysNone 
        [toPretty "class ",
         toPretty id,
         toPretty (if sc = None then "" else " extends "),
         ppSuperCls sc,
         toPretty (if sis = [] then "" else " implements "),
         ppSuperInterf sis]

%%%% interface header

  def ppInterfHeader (id : Ident, sis : SuperInterf) : Pretty =
      prettysNone [toPretty "interface ",
                   toPretty id,
                   toPretty (if sis = [] then "" else " extends "),
                   ppSuperInterf sis]

%%%% super class

  def ppSuperCls (sc : SuperCls) : Pretty =
      case sc of
        None    -> emptyPretty ()
      | Some nm -> ppName nm

%%%% all super interfaces

  def ppSuperInterf (sis : SuperInterf) : Pretty =
      if sis = [] then emptyPretty ()
      else prettysNone 
             (addPrettys (List.map ppName sis, toPretty ", "))

%%%% class body

  def ppClsBody (cb : ClsBody) : Pretty = 
      prettysAll
        (addEmptys
           (List.flatten
              [List.map ppStaticInits cb.staticInits,
               List.map ppFldDecl cb.flds,
               List.map ppConstrDecl cb.constrs,
               List.map ppMethDecl cb.meths,
               List.map ppClsDecl cb.clss,
               List.map ppInterfDecl cb.interfs]))

  def isEmptyClsBody (cb : ClsBody) : Boolean =
      List.null cb.staticInits & List.null cb.flds &
      List.null cb.constrs & List.null cb.meths &
      List.null cb.clss & List.null cb.interfs

%%%% interface body

  def ppInterfBody (ib : InterfBody) : Pretty = 
      prettysAll
        (addEmptys
           (List.flatten
              [List.map ppFldDecl ib.flds,
               List.map 
                 (fn mh -> prettysNone 
                             [ppMethHeader mh, toPretty ";"])
                 ib.meths,
               List.map ppClsDecl ib.clss,
               List.map ppInterfDecl ib.interfs]))

  def isEmptyInterfBody (ib : InterfBody) : Boolean =
      List.null ib.flds & List.null ib.meths &
      List.null ib.clss & List.null ib.interfs

%%%% Static initialization

  def ppStaticInits (bk : Block) : Pretty =
      case bk of 
        [] -> 
         toPretty "static { }"
      | _ -> 
         prettysAll 
           [toPretty "static {", ppBlock bk, toPretty "}"]

%%%% field declaration

  def ppFldDecl (ms : List Mod, t : Type, vd : VarDecl, 
                                    vds : List VarDecl) : Pretty =
      prettysNone [ppMods ms,
                   ppType t,
                   toPretty " ",
                   ppVarDecl vd,
                   toPretty ", ", 
                   ppVarDecls vds,
                   toPretty ";"]

%%%% variable declarations

  def ppVarDecls (vdl : List VarDecl) : Pretty = 
      prettysNone 
        (addPrettys (List.map ppVarDecl vdl,
                     toPretty ", "))

%%%% variable declaration

  def ppVarDecl (vdi : VarDeclId, vi : Option VarInit) : Pretty =
      case vi of
        None     -> ppVarDeclId vdi
      | Some vin -> prettysNone [ppVarDeclId vdi, 
                                 toPretty " = ",
                                 ppVarInit vin]
 
%%%% variable identifier (in variable declaration)

  def ppVarDeclId (id : Ident, n : Integer) : Pretty = 
      prettysNone [toPretty id,emptyBrackets n]

%%%% variable initliazer 

  def ppVarInit (vin : VarInit) : Pretty = 
        case vin of
          Expr e     -> ppExpr e
        | ArrInit ai -> prettysNone [toPretty "{",
                                     ppArrInit ai,
                                     toPretty "}"]

%%%% array initializers

  def ppArrInit (ais : List (Option VarInit)) : Pretty = 
      prettysNone (addPrettys (List.map ppOptVarInit ais,
                               toPretty ", "))

%%%% single array initializer

  def ppOptVarInit (oai : Option VarInit) : Pretty = 
      case oai of
        None    -> emptyPretty ()
      | Some vi -> ppVarInit vi

%%%% method declaration

  def ppMethDecl (mh : MethHeader, obk : Option Block) : Pretty =
      case obk of
        None -> 
          prettysNone [ppMethHeader mh, toPretty ";"]
      | Some bk -> 
          (case bk of 
             [] -> 
               prettysNone [ppMethHeader mh, toPretty " { }"]
           | _ -> 
               prettysAll 
                 [prettysNone [ppMethHeader mh, toPretty " {"],
                  ppBlock bk,
                  toPretty "}"])

%%%% method header

  def ppMethHeader (ms : List Mod, rt : Option Type, id : Ident,
                    fps : List FormPar, thrs : Throws) : Pretty =
      prettysNone [ppMods ms,
                   case rt of 
                        None   -> toPretty "void"
                      | Some t -> ppType t,
                   toPretty " ",
                   toPretty id,
                   toPretty " (",
                   ppFormPars fps,
                   toPretty ")",
                   if thrs = [] then emptyPretty ()
                            else prettysNone
                                     [toPretty " throws ",
                                      ppThrows thrs]
                   ]
             
%%%% formal parameters

  def ppFormPars (fps : List FormPar) : Pretty =
      prettysNone 
        (addPrettys (List.map ppFormPar fps, toPretty ", "))


%%%% single formal parameter

  def ppFormPar (b : Boolean, t : Type, vdi : VarDeclId) 
                                                 : Pretty =
      prettysNone
        [toPretty (if b = true then "final " else ""),
         ppType t,
         toPretty " ",
         ppVarDeclId vdi]

%%%% throws-statement

  def ppThrows (ns : List Name) : Pretty =
      prettysNone 
        (addPrettys (List.map ppName ns, toPretty ", "))

%%%% constructor declaration

  def ppConstrDecl (ms : List Mod, id : Ident, fps : List FormPar, 
                thrs : Throws, bk : Block) : Pretty =
      let hd =  
          prettysNone 
            [ppMods ms,
             toPretty id,
             toPretty " (",
             ppFormPars fps,
             toPretty ")",
             if thrs = [] then emptyPretty ()
             else prettysNone [toPretty " throws ", ppThrows thrs]
            ]
      in 
         case bk of 
           [] -> 
             prettysNone [hd, toPretty " { }"]
         | _ -> 
             prettysAll 
               [prettysNone [hd, toPretty " {"],
                ppBlock bk, 
                toPretty "}"]

%%%% block

  def ppBlock (bss : List BlockStmt) : Pretty =
      prettysAll (List.map ppBlockStmt bss)

%  def ppBlock (bss : List BlockStmt) : Pretty =
%      prettysAll 
%        (List.cons 
%           (toPretty "{",
%            List.concat (List.map ppBlockStmt bss,
%                         [toPretty "}"])))

%%%% block statment

  def ppBlockStmt (bs : BlockStmt) : Pretty =
      case bs of
        LocVarDecl lvd
               -> prettysNone [ppLocVarDecl lvd,
                               toPretty ";"]
      | ClsDecl cd 
                -> ppClsDecl cd
      | Stmt st -> ppStmt st

%%%% local vriable declaration

 def ppLocVarDecl (b : Boolean, t : Type, vd : VarDecl,
                                 vds : List VarDecl) : Pretty =
     prettysNone 
       [toPretty (if b then "final " else ""),
        ppType t,
        toPretty " ",
        ppVarDecl vd,
        toPretty (if vds = [] then "" else ", "),
        ppVarDecls vds]

%%%% statement 

  def ppStmt (st : Stmt) : Pretty = 
      case st of 
        Block bk ->
          (case bk of 
             [] -> 
               toPretty "{ }"
           | _ -> 
               prettysNone 
                 [toPretty "{ ", ppBlock bk, toPretty " }"])
      | Labeled (id,st) ->
          prettysNone 
            [toPretty (String.concat (id," : ")), ppStmt st]
      | If (e,st,opst) -> 
          prettysAll 
            (List.cons
               (prettysNone 
                  [toPretty "if (",
                   ppExpr e,
                   toPretty ") ",
                   ppStmt st],
                case opst of 
                  None     -> []
                | Some st1 -> [toPretty "else ", ppStmt st1]))
      | For (opfi,ope,opfu,st) ->
          prettysAll 
            [prettysNone 
               [toPretty "for ( ",
                ppOptForInit opfi,
                toPretty "; ",
                ppOptExpr ope,
                toPretty "; ",
                ppOptForUpdate opfu,
                toPretty " )"],
              ppStmt st]
      | While (e,st) ->
          prettysAll 
            [prettysLinear 
               [toPretty "while ( ",
                ppExpr e,
                toPretty " ) "],
             ppStmt st]
      | Do (st,e) -> 
          prettysLinear 
            [prettysNone 
               [toPretty "do ",
                ppStmt st,
                toPretty " "],
             toPretty "while ( ",
             ppExpr e,
             toPretty " )"]
      | Try (bk,ccs,opf) -> 
          let try = 
              [toPretty "try { ", 
               prettysNone [toPretty "  ", ppBlock bk]]
          in 
          let cat =  
              List.map 
                (fn (fp, bk) -> 
                    prettysAll
                      [prettysNone 
                         [toPretty "} catch ( ", 
                          ppFormPar fp, 
                          toPretty " ) {"],
                       prettysNone
                         [toPretty "  ", ppBlock bk]
                      ])
                 ccs
          in
          let fin =
              case opf of 
                None -> []
              | Some bk -> 
                  (case bk of 
                     [] -> []
                   | _ -> 
                       [toPretty "} finally {",
                        prettysNone [toPretty "  ", ppBlock bk]
                       ])
          in 
          prettysAll
            (List.flatten
               [try,cat,fin, [toPretty "}"]])
      | Switch (e,sbk) ->
          prettysNone
            [toPretty "switch (",
             ppExpr e,
             toPretty " ) ",
             ppSwitchBlock sbk]
      | Synchronized (e,bk) ->
          let hd = 
              prettysNone 
                [toPretty "synchronized ( ", 
                 ppExpr e,
                 toPretty " ) { "]
          in 
          (case bk of
            [] -> 
              prettysNone 
                [hd, toPretty "}"]
          | _ -> 
              prettysAll
                [hd,
                 prettysNone [toPretty "  ", ppBlock bk],
                 toPretty "}"] )
      | Return ope ->
          prettysNone
            [toPretty "return",
             case ope of
               None -> emptyPretty ()
             | Some e -> 
                  prettysNone [toPretty " ", ppExpr e],
             toPretty ";"]
      | Throw e  -> 
          prettysNone
            [toPretty "throw ", ppExpr e, toPretty ";"]
      | Break opid ->
          prettysNone
            [toPretty "break",
             case opid of
               None -> emptyPretty ()
             | Some id -> toPretty (String.concat (" ",id)),
             toPretty ";"]
      | Continue opid ->
          prettysNone
            [toPretty "continue",
             case opid of
               None -> emptyPretty ()
             | Some id -> toPretty (String.concat (" ",id)),
             toPretty ";"]
      | Expr e -> prettysNone [ppExpr e, toPretty ";"] 
      | Empty -> toPretty ";"

%%%% optional for-initializer 

  def ppOptForInit (opfi : Option ForInit) : Pretty = 
      case opfi of
        None      -> emptyPretty ()
      | Some fi -> 
           (case fi of 
              LocVarDecl lvd -> ppLocVarDecl lvd
            | StmtExprs (e,es)  -> 
                prettysLinear 
                  (addPrettys (List.map ppExpr (List.cons (e,es)),
                              toPretty ",")))

%%%% optional for-update 

  def ppOptForUpdate (opfu : Option ForUpdate) : Pretty = 
      case opfu of
        None    -> emptyPretty ()
      | Some (e,es) -> 
              prettysLinear 
                (addPrettys (List.map ppExpr (List.cons (e,es)), 
                             toPretty ","))

%%%% switch block
   
  def ppSwitchBlock (swbk : SwitchBlock) : Pretty =
      prettysAll
         [prettysNone
            [toPretty "{ ",
             prettysNone (List.map ppSwitchLabStmtPa swbk)],
          toPretty "}"]

%%%% switch label-statement pair

  def ppSwitchLabStmtPa (slabs : List SwitchLab, 
                         bksts : List BlockStmt) : Pretty = 
      prettysNone [prettysNone (List.map  ppSwitchLab slabs),
                   toPretty " ",
                   prettysAll (List.map ppBlockStmt bksts)]

%%%% switch label

  def ppSwitchLab (sl : SwitchLab) : Pretty = 
      case sl of
        JCase e  -> prettysNone [toPretty "case ",
                                ppExpr e,
                                toPretty ":"]
     |  Default -> toPretty "default:"
 

%%%% optional expressions 

  def ppOptExpr (ope : Option Expr) : Pretty = 
      case ope of
        None   -> emptyPretty ()
      | Some e -> ppExpr e

%%%% expression 

  def ppExpr (e : Expr) : Pretty = 
      case e of 
        Ass ass     -> ppAss ass
     |  CondExp ce -> ppCondExp ce

%%%% assignment

  def ppAss (l : LHS, o : AssOp, e : Expr) : Pretty =
      prettysNone [ppLHS l, 
                   toPretty " ", 
                   ppAssOp o, 
                   toPretty " ",
                   ppExpr e]

%%%% assignment operator

  def ppAssOp (o : AssOp) : Pretty =
      toPretty (assOpToString o)

%%%% left hand side of assignment

  def ppLHS (l : LHS) : Pretty =
      case l of 
        Name nm   -> ppName nm
      | FldAcc fac -> ppFldAcc fac
      | ArrAcc aac -> ppArrAcc aac

%%%% field access

  def ppFldAcc (fac : FldAcc) : Pretty =
      case fac of
        ViaPrim (pm,id)
            -> prettysNone
                 [ppPrim pm, 
                  toPretty ".",
                  toPretty id]
      | ViaSuper id   
            -> toPretty (String.concat ("super.",id))
      | ViaCls (nm,id)
            -> prettysNone 
                 [ppName nm,
                  toPretty (String.concat (".super.",id))]

%%%% array access

  def ppArrAcc (aa : ArrAcc) : Pretty =
      case aa of 
        ViaName (nm,e)
          -> prettysNone [ppName nm, 
                          toPretty " [ ",
                          ppExpr e,
                          toPretty " ]"]
      | ViaNoNewArray (pm,e) 
          -> prettysNone [ppPrim pm,
                          toPretty " [ ",
                          ppExpr e,
                          toPretty " ]"]

%%%% conditional expression

  def ppCondExp (be : BinExp, rest : Option (Expr * CondExp))
                                                     : Pretty =
      prettysNone
        [ppBinExp be,
         case rest of 
            None        -> emptyPretty ()
          | Some (e,ce) -> 
              prettysNone
                [toPretty " ? ",
                 ppExpr e,
                 toPretty " : ",
                 ppCondExp ce]]

%%%% binary expression 

  def ppBinExp (be : BinExp) : Pretty =
      case be of 
        Bin (o,be1,be2) 
           -> prettysNone
                [toPretty "( ",
                 ppBinExp be1,
                 toPretty " ",
                 ppBinOp o,
                 toPretty " ",
                 ppBinExp be2,
                 toPretty " )"]
      | InstOf (be,t)
           -> prettysNone
                [toPretty "( ",
                 ppBinExp be,
                 toPretty " instanceof ",
                 ppType t,
                 toPretty " )"]
      | Un ue -> ppUnExp ue

%%%% binary operator

  def ppBinOp (o : BinOp) : Pretty =
      toPretty (binOpToString o)

%%%% unary expression

  def ppUnExp (ue : UnExp) : Pretty =
      case ue of
        Un (o,ue)  -> prettysNone [toPretty "( ",
                                     ppUnOp o,
                                     toPretty " ",
                                     ppUnExp ue,
                                     toPretty " )"]
      | Cast (t,ue)   -> prettysNone [toPretty "(",
                                      ppType t,
                                      toPretty ")",
                                      ppUnExp ue]
      | PostUn (ue,o) -> prettysNone [ppUnExp ue, 
                                      ppPostUnOp o]
      | Prim pm       -> ppPrim pm

%%%% unary operator 

  def ppUnOp (o : UnOp) : Pretty =
      toPretty (unOpToString o)

%%%% postfix unary operator 

  def ppPostUnOp (o : PostUnOp) : Pretty =
      toPretty (postUnOpToString o)

%%%% Prim 

  def ppPrim (pm : Prim) : Pretty =
      case pm of 
        Name nm         -> ppName nm
      | IntL i          -> toPretty (Integer.toString i)
      | Float (i1,i2)   -> prettysNone
                             [toPretty (Integer.toString i1),
                              toPretty ".",
                              toPretty (Integer.toString i2)]
      | Bool b          -> toPretty (Boolean.toString b)
      | Char c          -> toPretty (Char.toString c)
      | String s        -> toPretty (concatList ["\"",s,"\""])
      | Null            -> toPretty "null"
      | ClsInst opt     -> prettysNone [case opt of
                                           None -> toPretty "void"
                                         | Some t -> ppType t, 
                                        toPretty ".class"]
      | This opnm       -> (case opnm of 
                              None    -> toPretty "this"
                            | Some nm -> prettysNone
                                          [ppName nm,
                                           toPretty "this"])
      | Paren e         -> prettysNone [%toPretty "( ",
                                        ppExpr e]
                                        %toPretty " )"]
      | NewClsInst nw   -> ppNewClsInst nw
      | NewArr nw       -> ppNewArr nw
      | FldAcc fda      -> ppFldAcc fda
      | MethInv mi      -> ppMethInv mi
      | ArrAcc aac      -> ppArrAcc aac

%%%% new class instance creation

  def ppNewClsInst (nw : NewClsInst) : Pretty = 
      case nw of 
        ForCls (nm,es,opcb) 
          -> prettysNone
               [toPretty "new ",
                ppName nm,
                toPretty "(",
                prettysNone
                    (addPrettys (List.map ppExpr es,
                                 toPretty ",")),
                toPretty ")",
                case opcb of
                     None    -> emptyPretty()
                   | Some cb -> prettysAll
                                  [toPretty "{", 
                                   ppClsBody cb,
                                   toPretty "}"]]
      | ForInnCls (pm,id,es,opcb)
          -> prettysNone
               [toPretty "new ",
                ppPrim pm,
                toPretty ".",
                toPretty id,
                toPretty "(",
                prettysNone
                    (addPrettys (List.map ppExpr es,
                                 toPretty ",")),
                toPretty ")",
                case opcb of
                     None    -> emptyPretty ()]
 
%%%% new array creation

  def ppNewArr (nw : NewArr) : Pretty = 
      case nw of
        Arr (nm,es,n) 
          -> prettysNone
               [toPretty "new ",
                ppName nm,
                prettysNone
                   (List.map 
                    (fn e -> prettysNone [toPretty "[",
                                          ppExpr e,
                                          toPretty "]"])
                     es),
                    emptyBrackets n]
      | ArrWInit (nm,n,ai)
          -> prettysNone
               [toPretty "new ",
                ppName nm,
                emptyBrackets n,
                ppArrInit ai]

%%%% method invocation

  def ppMethInv (mi : MethInv) : Pretty =
      let def ppArgs (es : List Expr) : Pretty =
              prettysNone
                (List.flatten
                   [[toPretty "("],
                    addPrettys (List.map ppExpr es, toPretty ","),
                    [toPretty ")"]])
      in
      case mi of 
        ViaName (nm,es) ->
          prettysNone [ppName nm, ppArgs es]
      | ViaPrim (pm,id,es) ->
          prettysNone 
            [ppPrim pm, toPretty ".", toPretty id, ppArgs es]
      | ViaSuper (id,es) -> 
          prettysNone 
            [toPretty"super.", toPretty id, ppArgs es]
      | ViaClsSuper (nm,id,es) -> 
          prettysNone 
            [ppName nm, toPretty".super.", toPretty id, ppArgs es]
%%%% type

  def ppType (btn : BasicOrName, n : Integer) : Pretty =
      prettysNone [ppBasicOrName btn,
                   emptyBrackets n]

%%%% basic type or name

  def ppBasicOrName (btn : BasicOrName) : Pretty =
      case btn of 
        Basic bt  -> ppBasic bt 
      | Name  nm  -> ppName nm

%%%% baisc type

  def ppBasic (bt : Basic) : Pretty =
     toPretty
       (case bt of 
          JBool   -> "boolean"
        | Byte    -> "byte"
        | Short   -> "short"
        | Char    -> "char"
        | JInt    -> "int"
        | Long    -> "int"
        | JFloat  -> "float"
        | Double  -> "double")

%%%% name

  def ppName (ids : List Ident, id : Ident) : Pretty =
      toPretty (qualName (ids,id))

%%%% Test 

  def clsDecl1 () : CompUnit = 
      (Some (["kestrel"],"zhenyu"), 
       [(["java","lang"],"*"),(["java","swing"],"xyz")],
       [ClsDecl([Public],
                ("MyClass",
                 Some ([],"SuperClass"),
                 [([],"SuperI1"), ([],"SuperI2")]),
                 {staticInits = [],
                  constrs = [],
                  flds =
                     [([Private],(Basic JInt,2),
                      (("xx",0),None),
                      [(("yy",2),Some (ArrInit [None,None]))])],
                  meths =
                     [(([Static,Public], None, "mm",
                         [(true, (Name([],"String"),1),("p",2)),
                          (false,(Basic JBool,0),      ("b",0))],
                         [([],"Exception")]),
                        None)
                     ],
                  clss = [],
                  interfs = []
                })
       ])

  def testcls1 (n : Nat) : () =
      toTerminal (format (n, ppCompUnit (clsDecl1())))

  def itfDecl1 () : CompUnit = 
      (Some (["kestrel"],"zhenyu"), 
       [],
       [InterfDecl([Public],
                   ("MyClass",
                    [([],"SuperI1"),([],"SuperI2")]),
                    {flds = [],
                     meths = [],
                     clss = [],
                     interfs = []
                    }
                   )
       ])

  def testitf1 (n : Nat) : () =
      toTerminal (format (n, ppCompUnit (itfDecl1())))

  %% (javaprint::testcls1 80)
  %% (javaprint::testitf1 80)

end-spec
