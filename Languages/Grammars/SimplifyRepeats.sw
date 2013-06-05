CFG qualifying spec

import ContextFree
import /Library/Legacy/Utilities/System


op simplify_seq (seq : List RHS) : List RHS =

 %%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%
 %% Simplify elements of sequence.
 %%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%

 let seq = map simplify_rhs seq in

 let

   %%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%
   %% If prefix is a prefix of list, return (Some suffix), otherwise None.
   %%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%

   def remove_prefix (prefix, lst) =
     case (prefix, lst) of

       | ([], _) -> 
         Some lst

       | (x :: prefix, y :: lst) | x = y ->
         remove_prefix (prefix, lst)

       | _ -> 
         None

   %%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%
   %% Simplify patterns in sequence:
   %%
   %% [,,, x1, ..., xn, Rep  [x1, ..,. xn], ,,,] 
   %% => 
   %% [...,             Rep1 [x1, ..,. xn], ,,,]
   %%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%

   def aux (rseq, simplified) =
     case rseq of
       | [] -> simplified
       | x :: tail ->
         case x of
           | Rep y ->
             (case remove_prefix (reverse y, tail) of
                | Some tail2 -> 
                  aux (tail2, (Rep1 y) :: simplified)
                | _ ->
                  case y of
                    | sep :: (z as _ :: _) -> 
                      (case remove_prefix (reverse z, tail) of
                         | Some tail3 -> 
                           aux (tail3, (Rep1Sep {body = z, sep = [sep]} :: simplified))
                         | _ -> 
                           aux (tail,  x :: simplified))
                    | _ -> aux (tail,  x :: simplified))
           | _ -> 
             aux (tail,  x :: simplified)
 in
 aux (reverse seq, [])

op simplify_rhs (rhs : RHS) : RHS =
 case rhs of

  | Terminal _ -> rhs
  | NT       _ -> rhs

  | Any                   alts -> 
    Any (map simplify_rhs alts)

  | Seq               seq -> 
    Seq (simplify_seq seq) 

  | Opt seq ->
    let seq = simplify_seq seq in
    (case seq of
      %% An optional repeat is a repeat allowing zero occurences:
      | [Rep     seq]      -> Rep seq
      | [Rep1    seq]      -> Rep seq
      | [RepSep  body_sep] -> RepSep body_sep
      | [Rep1Sep body_sep] -> RepSep body_sep
      | _ -> Opt seq)

  | Rep                seq -> 
    Rep  (simplify_seq seq)

  | Rep1               seq -> 
    Rep1 (simplify_seq seq)

  | RepSep {body, sep} -> 
    RepSep {body = simplify_seq body,
            sep  = simplify_seq sep}

  | Rep1Sep  {body, sep} ->
    Rep1Sep {body = simplify_seq body,
             sep  = simplify_seq sep}

  | Diff     (             body,              exclude) -> 
    Diff     (simplify_rhs body, simplify_rhs exclude)

  | Restrict (             body, pred)    -> 
    Restrict (simplify_rhs body, pred)


op simplifyAnyToRep (rule : Rule) : Rule =
 let

   def mkRep (body_seq : List RHS, sep_seq : List RHS) : RHS =
    case sep_seq of
       | [] -> Rep1 body_seq
       | _  -> Rep1Sep {body = body_seq, sep = sep_seq}

   def maybe_prefix (xs, ys) =
     case (xs, ys) of
       | ([], _) -> Some ys
       | (x :: xs, y :: ys) | x = y -> maybe_prefix (xs, ys)
       | _ -> None

   def aux (x, s) : Rule =
     let x_seq = 
         case x of
           | Seq xs -> xs
           | _ -> [x]
     in
     case s of
       | (NT z) :: y_seq | z = rule.lhs ->  
         
         %% [x1, ... xn]  [NT, s1, ..., sm, x1, ..., xn]  
         %%  => 
         %% Rep1Sep {body = [x1, ..., xn], sep = [s1, ..., sm]}

         (case maybe_prefix (reverse x_seq, reverse y_seq) of
            | Some rev_sep_seq -> rule << {rhs = mkRep (x_seq, reverse rev_sep_seq)}
            | _ -> rule)

       | _ ->
         case reverse s of
           | (NT z) :: rev_y_seq | z = rule.lhs -> 

             %% [x1, ... xn]  [x1, ..., xn, s1, ..., sm, NT]  
             %%  => 
             %% Rep1Sep {body = [x1, ..., xn], sep = [s1, ..., sm]}

             (case maybe_prefix (x_seq, reverse rev_y_seq) of
                | Some sep_seq -> rule << {rhs = mkRep (x_seq, sep_seq)}
                | _ -> rule)

           | _ -> rule
 in             
 case rule.rhs of
   | Any [x, Seq s] -> aux (x, s)
   | Any [Seq s, x] -> aux (x, s)
   | _ -> rule
     
%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%
%% Replace various complicated patterns with simpler repetitions
%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%

op simplifyRepeats (grammar : ContextFreeGrammar) : ContextFreeGrammar =
 let directives = 
     map (fn directive ->
            case directive of
              | Rule rule -> Rule (rule << {rhs = simplify_rhs rule.rhs})
              | _ -> directive)
         grammar.directives
 in
 let directives = 
     map (fn directive ->
            case directive of
              | Rule rule -> Rule (simplifyAnyToRep rule)
              | _ -> directive)
         grammar.directives
 in
 grammar << {directives = directives}

end-spec
