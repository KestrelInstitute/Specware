% Functions for folding functions over a term, sort and patten.

spec {
 import AnnTerm

 sort Fold (a,b) = a -> b -> a
 sort TSP_Folds (a,b) = Fold (a,ATerm b) * Fold (a,ASort b) * Fold (a,APattern b)

 op foldTerm    : fa(a,b) TSP_Folds (a,b) -> a -> ATerm b -> a
 op foldSort    : fa(a,b) TSP_Folds (a,b) -> a -> ASort b -> a
 op foldPattern : fa(a,b) TSP_Folds (a,b) -> a -> APattern b -> a

 def foldTerm (tsp_folds as (termFold,_,_)) acc term = 
   let foldOfChildren = 
     case term of
       | Fun (top, srt, a) -> foldSort tsp_folds acc srt
       | Var ((id, srt), a) -> foldSort tsp_folds acc srt
       | Let (decls, bdy, a) -> 
           foldl (fn ((pat,trm),acc) -> foldPattern tsp_folds (foldTerm tsp_folds acc trm) pat) acc decls
       | LetRec (decls, bdy, a) -> 
           foldl (fn (((id,srt),trm),acc) -> foldSort tsp_folds (foldTerm tsp_folds acc trm) srt) acc decls
       | Record (row, a) -> foldl (fn ((id,trm),acc) -> foldTerm tsp_folds acc trm) acc row
       | IfThenElse (t1, t2, t3, a) -> 
           foldTerm tsp_folds (foldTerm tsp_folds (foldTerm tsp_folds acc t1) t2) t3
       | Lambda (match, a) -> 
           foldl (fn ((pat,cond,trm),acc)->
             foldPattern tsp_folds (foldTerm tsp_folds (foldTerm tsp_folds acc cond) trm) pat) acc match
       | Bind (bnd, vars, trm, a) -> 
           foldTerm tsp_folds (foldl (fn ((id,srt),acc) -> foldSort tsp_folds acc srt) acc vars) trm
       | Apply (t1, t2,  a) -> foldTerm tsp_folds (foldTerm tsp_folds acc t1) t2
       | Seq (terms, a) -> 
           foldl (fn (trm,acc) -> foldTerm tsp_folds acc trm) acc terms
       | ApplyN (terms, a) -> 
           foldl (fn (trm,acc) -> foldTerm tsp_folds acc trm) acc terms
       | SortedTerm (trm, srt, a) -> 
           foldTerm tsp_folds (foldSort tsp_folds acc srt) trm
   in
     termFold foldOfChildren term

 def foldSort (tsp_folds as (_,sortFold,_)) acc srt = 
   let foldOfChildren =
     case srt of
       | CoProduct (row, a) ->
           foldl (fn | ((id,None),acc) -> acc
                     | ((id,Some srt),acc) -> foldSort tsp_folds acc srt) acc row 
       | Product (row, a) -> 
           foldl (fn ((id,srt),acc) -> foldSort tsp_folds acc srt) acc row 
       | Arrow (s1, s2, a) -> foldSort tsp_folds (foldSort tsp_folds acc s1) s2
       | Quotient (srt, trm, a) -> foldSort tsp_folds (foldTerm tsp_folds acc trm) srt
       | Subsort (srt, trm, a) -> foldSort tsp_folds (foldTerm tsp_folds acc trm) srt
     % | Subset (ssrt, trm, a) -> 
       | Base (qid, srts, a) -> foldl (fn (srt,acc) -> foldSort tsp_folds acc srt) acc srts
       | PBase (qid, srts, a) -> foldl (fn (srt,acc) -> foldSort tsp_folds acc srt) acc srts
       | _ -> acc
   in
     sortFold foldOfChildren srt

 def foldPattern (tsp_folds as (_,_,patternFold)) acc pattern = 
   let foldOfChildren =
     case pattern of
       | AliasPat (p1, p2, a) -> foldPattern tsp_folds (foldPattern tsp_folds acc p1) p2
       | EmbedPat (id, Some pat, srt, a) -> foldSort tsp_folds (foldPattern tsp_folds acc pat) srt
       | EmbedPat (id, None, srt, a) -> foldSort tsp_folds acc srt
       | RelaxPat (pat, trm, a) -> foldPattern tsp_folds (foldTerm tsp_folds acc trm) pat
       | QuotientPat (pat, trm, a) -> foldPattern tsp_folds (foldTerm tsp_folds acc trm) pat
       | VarPat ((v, srt), a) -> foldSort tsp_folds acc srt
       | WildPat (srt, a) -> foldSort tsp_folds acc srt
       | RecordPat (fields, a) -> foldl (fn ((id, pat),acc) -> foldPattern tsp_folds acc pat) acc fields
       | SortedPat (pat, srt, a) -> foldSort tsp_folds (foldPattern tsp_folds acc pat) srt
       | _ -> acc
  in
    patternFold foldOfChildren pattern
}
