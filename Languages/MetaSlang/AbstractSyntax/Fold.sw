% Functions for folding functions over a term, sort and patten.

Utilities qualifying
spec
 import AnnTerm

 type Fold (a,b) = a -> b -> a
 type TSP_Folds (a,b) = Fold (a,ATerm b) * Fold (a,ASort b) * Fold (a,APattern b)

 op foldTerm    : [a,b] TSP_Folds (a,b) -> a -> ATerm b -> a
 op foldSort    : [a,b] TSP_Folds (a,b) -> a -> ASort b -> a
 op foldPattern : [a,b] TSP_Folds (a,b) -> a -> APattern b -> a

 def foldTerm (tsp_folds as (termFold,_,_)) acc term = 
   let foldOfChildren = 
     case term of
       | Fun (top, srt, a) -> foldSort tsp_folds acc srt
       | Var ((id, srt), a) -> foldSort tsp_folds acc srt
       | Let (decls, bdy, a) ->
         let acc = foldl (fn (acc,(pat,trm)) -> foldPattern tsp_folds (foldTerm tsp_folds acc trm) pat)
                     acc decls
         in
         foldTerm tsp_folds acc bdy
       | LetRec (decls, bdy, a) -> 
         let acc = foldl (fn (acc,((id,srt),trm)) -> foldSort tsp_folds (foldTerm tsp_folds acc trm) srt)
                     acc decls
         in
         foldTerm tsp_folds acc bdy
       | Record (row, a) -> foldl (fn (acc,(id,trm)) -> foldTerm tsp_folds acc trm) acc row
       | IfThenElse (t1, t2, t3, a) -> 
         foldTerm tsp_folds (foldTerm tsp_folds (foldTerm tsp_folds acc t1) t2) t3
       | Lambda (match, a) -> 
         foldl (fn (acc,(pat,cond,trm))->
                  foldPattern tsp_folds (foldTerm tsp_folds (foldTerm tsp_folds acc cond) trm)
                    pat)
           acc match
       | Bind (bnd, vars, trm, a) -> 
         foldTerm tsp_folds (foldl (fn (acc,(id,srt)) -> foldSort tsp_folds acc srt) acc vars) trm
       | The ((id,srt), trm, a) -> foldTerm tsp_folds (foldSort tsp_folds acc srt) trm
       | Apply (t1, t2,  a) -> foldTerm tsp_folds (foldTerm tsp_folds acc t1) t2
       | Seq (terms, a) -> 
         foldl (fn (acc,trm) -> foldTerm tsp_folds acc trm) acc terms
       | ApplyN (terms, a) -> 
         foldl (fn (acc,trm) -> foldTerm tsp_folds acc trm) acc terms
       | SortedTerm (trm, srt, a) -> 
         foldTerm tsp_folds (foldSort tsp_folds acc srt) trm
       | Pi(_, trm, _) -> foldTerm tsp_folds acc trm
       | And(trms, _) -> foldl (fn (acc, trm) -> foldTerm tsp_folds acc trm) acc trms
       | _ -> acc
   in
     termFold foldOfChildren term

 def foldSort (tsp_folds as (_,sortFold,_)) acc srt = 
   let foldOfChildren =
     case srt of
       | CoProduct (row, a) ->
         foldl (fn | (acc,(id,None)) -> acc
                   | (acc,(id,Some srt)) -> foldSort tsp_folds acc srt) acc row 
       | Product (row, a) -> 
           foldl (fn (acc,(id,srt)) -> foldSort tsp_folds acc srt) acc row 
       | Arrow (s1, s2, a) -> foldSort tsp_folds (foldSort tsp_folds acc s1) s2
       | Quotient (srt, trm, a) -> foldSort tsp_folds (foldTerm tsp_folds acc trm) srt
       | Subsort (srt, trm, a) -> foldSort tsp_folds (foldTerm tsp_folds acc trm) srt
       | Base (qid, srts, a) -> foldl (fn (acc,srt) -> foldSort tsp_folds acc srt) acc srts
       | Boolean _ -> acc
       | Pi(_, srt, _) -> foldSort tsp_folds acc srt
       | And(srts, _) -> foldl (fn (acc, srt) -> foldSort tsp_folds acc srt) acc srts
       | _ -> acc
   in
     sortFold foldOfChildren srt

 def foldPattern (tsp_folds as (_,_,patternFold)) acc pattern = 
   let foldOfChildren =
     case pattern of
       | AliasPat (p1, p2, a) -> foldPattern tsp_folds (foldPattern tsp_folds acc p1) p2
       | EmbedPat (id, Some pat, srt, a) -> foldSort tsp_folds (foldPattern tsp_folds acc pat) srt
       | EmbedPat (id, None, srt, a) -> foldSort tsp_folds acc srt
       | QuotientPat (pat, _, a) -> foldPattern tsp_folds acc pat
       | RestrictedPat (pat, trm, a) -> foldPattern tsp_folds (foldTerm tsp_folds acc trm) pat
       | VarPat ((v, srt), a) -> foldSort tsp_folds acc srt
       | WildPat (srt, a) -> foldSort tsp_folds acc srt
       | RecordPat (fields, a) -> foldl (fn (acc,(id, pat)) -> foldPattern tsp_folds acc pat) acc fields
       | SortedPat (pat, srt, a) -> foldSort tsp_folds (foldPattern tsp_folds acc pat) srt
       | _ -> acc
  in
    patternFold foldOfChildren pattern
endspec

