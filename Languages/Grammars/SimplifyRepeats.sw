CFG qualifying spec

import ContextFree
import /Library/Legacy/Utilities/System

op simplify_seq (seq : List RHS) : List RHS =

 %% First simplify elements of sequence.

 let seq = map simplify_rhs seq in

 %% Then simplify patterns in sequence:

 %% [,,, x1, ..., xn, Rep  [x1, ..,. xn], ,,,] 
 %% => 
 %% [...,             Rep1 [x1, ..,. xn], ,,,]

 let
   def remove_prefix prefix lst =
     case (prefix, lst) of
       | ([], _) -> Some lst
       | (x :: prefix, y :: lst) | x = y ->
         remove_prefix prefix lst
       | _ -> None

   def aux (rseq, simplified) =
     case rseq of
       | [] -> simplified
       | x :: tail ->
         case x of
           | Rep y ->
             (case remove_prefix (reverse y) tail of
                | Some tail2 -> 
                  aux (tail2, (Rep1 y) :: simplified)
                | _ ->
                  case y of
                    | sep :: (z as _ :: _) -> 
                      (case remove_prefix (reverse z) tail of
                         | Some tail3 -> 
                           aux (tail3, (Rep1Sep (Seq z, Seq[sep]) :: simplified))
                         | _ -> 
                           aux (tail,  x :: simplified))
                    | _ -> aux (tail,  x :: simplified))
           | _ -> 
             aux (tail,  x :: simplified)
 in
 aux (reverse seq, [])

op simplify_rhs (rhs : RHS) : RHS =
 case rhs of
  | Terminal _               -> rhs
  | NT       _               -> rhs

  | Any      alts            -> Any (map simplify_rhs alts)

  | Seq      seq             -> Seq (simplify_seq seq) 
  | Opt      seq             -> 
    let seq = simplify_seq seq in
    %% An optional repeat is a repeat allowing zero occurences:
    (case seq of
      | [Rep     seq]         -> Rep seq
      | [Rep1    seq]         -> Rep seq
      | [RepSep  (body, sep)] -> RepSep (body, sep)
      | [Rep1Sep (body, sep)] -> RepSep (body, sep)
      | _ -> Opt seq)

  | Rep      seq             -> Rep      (simplify_seq seq)
  | Rep1     seq             -> Rep1     (simplify_seq seq)

  | RepSep   (body, sep)     -> RepSep   (simplify_rhs body, simplify_rhs sep)
  | Rep1Sep  (body, sep)     -> Rep1Sep  (simplify_rhs body, simplify_rhs sep)

  | Diff     (body, exclude) -> Diff     (simplify_rhs body, simplify_rhs exclude)

  | Restrict (body, pred)    -> Restrict (simplify_rhs body, pred)

op simplifyRepeats (grammar : ContextFreeGrammar) : ContextFreeGrammar =
 let directives = 
     map (fn directive ->
            case directive of
              | Rule {lhs, rhs} -> Rule {lhs = lhs, rhs = simplify_rhs rhs}
              | _ -> directive)
         grammar.directives
 in
 grammar << {directives = directives}

end-spec
