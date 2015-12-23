(* Copyright 2015 Kestrel Institute. See file LICENSE for license details *)

CFlatten = CGen qualifying spec

import C


  op [a,b] unzip(l:List (a*b)):(List a * List b) =
    case l of
    | (x,y)::ls -> let (xs',ys') = unzip ls in (x::xs',y::ys')
    | [] -> ([],[])

  op mkSequence(s:List C_Stmt):C_Stmt =
    % FIXME: Should be smarter...
    case s of
      | [] -> C_Block ([],[])
      | [s1] -> s1
      | _ -> C_Block ([],s)

  op mkIfStmt(p:C_Exp,tt:List C_Stmt, ff:List C_Stmt):List C_Stmt =
     case (tt,ff) of
       | ([],[]) -> []
       | (ts,[]) -> [C_IfThen (p,mkSequence ts)]
       | ([],fs) -> [C_IfThen (C_Unary (C_LogNot, p), mkSequence fs)]
       | (ts,fs) -> [C_If (p, mkSequence ts, mkSequence fs)]
        
        
  op flattenExp(e:C_Exp):(List C_Stmt * C_Exp) =
      case e of
          | C_Apply (f,args) ->
            let args' = map flattenExp args in
            let (ss,vs) = unzip args' in
            (flatten ss,C_Apply (f, vs))

          | C_Binary (o,l,r) ->
            let (ls,lv) = flattenExp l in
            let (rs,rv) = flattenExp r in
            (ls ++ rs, C_Binary (o, lv, rv))
          | C_Unary (o,l) ->
            let (ls,lv) = flattenExp l in
            (ls, C_Unary (o, lv))
          | C_Cast (ty,e) ->
            let (ls,v) = flattenExp e
            in (ls, C_Cast (ty,v))
          | C_StructRef (e,f) ->
            let (ls,v) = flattenExp e
            in (ls, C_StructRef (v,f))
          | C_UnionRef (e,f) ->
            let (ls,v) = flattenExp e
            in (ls, C_UnionRef (v,f))
          | C_ArrayRef (l,r) ->
            let (ls,lv) = flattenExp l in
            let (rs,rv) = flattenExp r in
            (ls ++ rs, C_ArrayRef (lv, rv))
          | C_IfExp (p,tt,ff) ->
            let (ps,pv) = flattenExp p in                 
            let (tts,ttv) = flattenExp tt in
            let (ffs,ffv) = flattenExp ff in
            let pre = mkIfStmt(pv,tts,ffs) in 
            (ps ++ pre, C_IfExp (pv,ttv,ffv))
          | C_Comma (l,r) ->
            let (ls,lv) = flattenExp l in
            let (rs,rv) = flattenExp r in
            (ls ++ [C_Exp lv] ++ rs, rv)
          | _ -> ([],e)
            
            
  op flattenStmt (s : C_Stmt) : C_Stmt =
    case s of
      | C_Exp e          ->
        let (ss,v) = flattenExp e in mkSequence (ss ++ [C_Exp v])
      | C_Block b        -> C_Block (flattenBlock b)
      | C_IfThen (e, s1) ->
        let (es,ev) = flattenExp e in
        let ss = flattenStmt s1 in
        mkSequence (es ++ [C_IfThen (ev, ss)])
      | C_If (e, s1, s2) ->
        let (es,ev) = flattenExp e in
        let ss1 = flattenStmt s1 in
        let ss2 = flattenStmt s2 in         
        mkSequence (es ++ [C_If (ev, ss1, ss2)])
      | C_Return e       ->
        let (es,ev) = flattenExp e in
        mkSequence (es ++ [C_Return ev])
      | C_While (e, s)   ->
        let (es,ev) = flattenExp e in
        let ss = flattenStmt s in
        mkSequence (es ++ [C_While (ev,ss)])
      | C_Switch (e,ss) ->
        let (es,ev) = flattenExp e in
        let ss' = map flattenStmt ss in
        mkSequence (es ++ [C_Switch (ev,ss')])
      | _ -> s

  op flattenBlock ((vs,ss) : C_Block) : C_Block =
     let ss' = map flattenStmt ss in
     let def emptyBlock s =
           case s of
             | C_Block ([],ss) -> ss
             | _ -> [s]
     in
     let ss'' = flatten (map emptyBlock ss') in 
     %% FIXME: should be more intelligent, removing internal blocks in
     %% ss' that have empty var decls.
     (vs,ss'')

  op flattenFunDefn((f,vars,ty,body):C_FnDefn):C_FnDefn =
     let body' = flattenStmt body in (f,vars,ty,body')
    

  op flattenSpec(spc:C_Spec):C_Spec =
     let fnDefns' = map flattenFunDefn spc.fnDefns in
     spc << { fnDefns = fnDefns' }


endspec