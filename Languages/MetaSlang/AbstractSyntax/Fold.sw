(* Copyright 2015 Kestrel Institute. See file LICENSE.text for license details *)

% Functions for folding functions over a term, type and patten.

Utilities qualifying
spec
 import AnnTerm

 type Fold (a,b) = a -> b -> a
 type TSP_Folds (a,b) = Fold (a,ATerm b) * Fold (a,AType b) * Fold (a,APattern b)

 op foldTerm    : [a,b] TSP_Folds (a,b) -> a -> ATerm b -> a
 op foldType    : [a,b] TSP_Folds (a,b) -> a -> AType b -> a
 op foldPattern : [a,b] TSP_Folds (a,b) -> a -> APattern b -> a

 def foldTerm (tsp_folds as (termFold,_,_)) acc term = 
   let foldOfChildren = 
     case term of
       | Fun (top, srt, a) -> foldType tsp_folds acc srt
       | Var ((id, srt), a) -> foldType tsp_folds acc srt
       | Let (decls, bdy, a) ->
         let acc = foldl (fn (acc,(pat,trm)) -> foldPattern tsp_folds (foldTerm tsp_folds acc trm) pat)
                     acc decls
         in
         foldTerm tsp_folds acc bdy
       | LetRec (decls, bdy, a) -> 
         let acc = foldl (fn (acc,((id,srt),trm)) -> foldType tsp_folds (foldTerm tsp_folds acc trm) srt)
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
         foldTerm tsp_folds (foldl (fn (acc,(id,srt)) -> foldType tsp_folds acc srt) acc vars) trm
       | The ((id,srt), trm, a) -> foldTerm tsp_folds (foldType tsp_folds acc srt) trm
       | Apply (t1, t2,  a) -> foldTerm tsp_folds (foldTerm tsp_folds acc t1) t2
       | Seq (terms, a) -> 
         foldl (fn (acc,trm) -> foldTerm tsp_folds acc trm) acc terms
       | ApplyN (terms, a) -> 
         foldl (fn (acc,trm) -> foldTerm tsp_folds acc trm) acc terms
       | TypedTerm (trm, srt, a) -> 
         foldTerm tsp_folds (foldType tsp_folds acc srt) trm
       | Pi(_, trm, _) -> foldTerm tsp_folds acc trm
       | And(trms, _) -> foldl (fn (acc, trm) -> foldTerm tsp_folds acc trm) acc trms
       | _ -> acc
   in
     termFold foldOfChildren term

 def foldType (tsp_folds as (_,typeFold,_)) acc srt = 
   let foldOfChildren =
     case srt of
       | CoProduct (row, a) ->
         foldl (fn | (acc,(id,None)) -> acc
                   | (acc,(id,Some srt)) -> foldType tsp_folds acc srt) acc row 
       | Product (row, a) -> 
           foldl (fn (acc,(id,srt)) -> foldType tsp_folds acc srt) acc row 
       | Arrow (s1, s2, a) -> foldType tsp_folds (foldType tsp_folds acc s1) s2
       | Quotient (srt, trm, a) -> foldType tsp_folds (foldTerm tsp_folds acc trm) srt
       | Subtype (srt, trm, a) -> foldType tsp_folds (foldTerm tsp_folds acc trm) srt
       | Base (qid, srts, a) -> foldl (fn (acc,srt) -> foldType tsp_folds acc srt) acc srts
       | Boolean _ -> acc
       | Pi(_, srt, _) -> foldType tsp_folds acc srt
       | And(srts, _) -> foldl (fn (acc, srt) -> foldType tsp_folds acc srt) acc srts
       | _ -> acc
   in
     typeFold foldOfChildren srt

 def foldPattern (tsp_folds as (_,_,patternFold)) acc pattern = 
   let foldOfChildren =
     case pattern of
       | AliasPat (p1, p2, a) -> foldPattern tsp_folds (foldPattern tsp_folds acc p1) p2
       | EmbedPat (id, Some pat, srt, a) -> foldType tsp_folds (foldPattern tsp_folds acc pat) srt
       | EmbedPat (id, None, srt, a) -> foldType tsp_folds acc srt
       | QuotientPat (pat, _, srts, a) ->
         let acc = foldl (fn (acc, srt) -> foldType tsp_folds acc srt) acc srts in
         foldPattern tsp_folds acc pat
       | RestrictedPat (pat, trm, a) -> foldPattern tsp_folds (foldTerm tsp_folds acc trm) pat
       | VarPat ((v, srt), a) -> foldType tsp_folds acc srt
       | WildPat (srt, a) -> foldType tsp_folds acc srt
       | RecordPat (fields, a) -> foldl (fn (acc,(id, pat)) -> foldPattern tsp_folds acc pat) acc fields
       | TypedPat  (pat, srt, a) -> foldType tsp_folds (foldPattern tsp_folds acc pat) srt
       | _ -> acc
  in
    patternFold foldOfChildren pattern
endspec

