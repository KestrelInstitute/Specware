(* Copyright 2015 Kestrel Institute. See file LICENSE for license details *)

CFG qualifying spec

import ContextFree
import /Library/Legacy/Utilities/System


op simplify_seq (seq : List RHS) : List RHS =

 %%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%
 %% Simplify elements of sequence.
 %%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%

 let seq = map simplify_rep_to_rep1 seq in

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

op simplify_rep_to_rep1 (rhs : RHS) : RHS =
 case rhs of

  | Terminal _ -> rhs
  | NT       _ -> rhs

  | Any                           alts -> 
    Any (map simplify_rep_to_rep1 alts)

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

  | Diff     (                     body,                      exclude) -> 
    Diff     (simplify_rep_to_rep1 body, simplify_rep_to_rep1 exclude)

  | Restrict (                     body, pred) -> 
    Restrict (simplify_rep_to_rep1 body, pred)


op simplify_any_to_rep1 (rule : Rule) : Rule =
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
%% Replace (Opt foo) where foo ::= Rep1 x 
%% with foo, where foo ::- Rep x
%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%

op simplify_optional_rep1s (directives : Directives) : Directives =
 let
   def aux_seq (nts, seq) =
     foldl aux nts seq     

   def aux (rep1_nts, rhs) =
     case rhs of
       | Terminal _      -> rep1_nts

       | NT       nt     -> 
         % nt is appearing in a location that is not optional,
         % so remove it from the list
         filter (fn rep_nt -> rep_nt ~= nt) rep1_nts

       | Any      seq    -> aux_seq (rep1_nts, seq)

       % keep any non-termainal that might appear as Opt [NT nt]
       | Opt      [NT _] -> rep1_nts    
       | Opt      seq    -> aux_seq (rep1_nts, seq)
         
       | Seq      seq    -> aux_seq (rep1_nts, seq)
       | Rep      seq    -> aux_seq (rep1_nts, seq)
       | Rep1     seq    -> aux_seq (rep1_nts, seq)

       | RepSep   {body, sep} -> aux_seq (aux_seq (rep1_nts, body), sep)
       | Rep1Sep  {body, sep} -> aux_seq (aux_seq (rep1_nts, body), sep)

       | Diff     (x, y)      -> aux (aux (rep1_nts, x), y)
       | Restrict (x, _)      -> aux (rep1_nts, x)

   %%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%
   %% Revise rules for the only-optional non-terminals to use Rep or RepSet.
   %%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%

   def change_rep1_to_rep rhs =
     case rhs of
       | Rep1    x -> Rep    x
       | Rep1Sep x -> RepSep x
       | _ -> rhs

   %%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%
   %% Also change references of the form 'Opt [NT nt]' to just 'NT nt'
   %%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%

   def remove_opts (nts, rhs) =
     let
       def aux2 seq =
         map (fn x -> remove_opts (nts, x)) seq         

       def aux rhs =
         case rhs of

           | Terminal _ -> 
             rhs

           | NT _ -> 
             rhs

           | Any       seq -> 
             Any (aux2 seq)

           | Opt [NT nt] -> 
             if nt in? nts then
               NT nt
             else
               rhs

           | Opt       seq -> 
             Opt (aux2 seq)
         
           | Seq       seq -> 
             Seq (aux2 seq)

           | Rep       seq -> 
             Rep (aux2 seq)

           | Rep1       seq  -> 
             Rep1 (aux2 seq)

           | RepSep  {            body,            sep} -> 
             RepSep  {body = aux2 body, sep = aux2 sep}

           | Rep1Sep {            body,            sep} -> 
             Rep1Sep {body = aux2 body, sep = aux2 sep}

           | Diff     (    x,     y) -> 
             Diff     (aux x, aux y)

           | Restrict (    x, pred) -> 
             Restrict (aux x, pred)
     in
     aux rhs
 in

 %%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%
 %% First collect non-terminals that are defined using Rep1 or Rep1Sep
 %%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%

 let rep1_nts =
     foldl (fn (nts, directive) ->
              case directive of
                | Rule rule -> 
                  (case rule.rhs of
                     | Rep1 _    -> rule.lhs :: nts
                     | Rep1Sep _ -> rule.lhs :: nts
                     | _ -> nts)
                | _ -> nts)
           []
           directives
 in

 %%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%
 %% Then remove any of those non-terminals that appear in a context 
 %% that is not of the form    Opt [NT nt]
 %%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%

 let opt_rep1_nts =
     %% Remove every non-terminal that appears in a location
     %% that is not of the form Opt [nt].
     foldl (fn (nts, directive) ->
              case directive of
                | Rule rule -> aux (nts, rule.rhs)
                | _ -> nts)
           rep1_nts
           directives
 in

 %%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%
 %% Finally, revise rules.
 %%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%

 let directives =
     map (fn directive ->
            case directive of
              | Rule rule -> 
                Rule (if rule.lhs in? opt_rep1_nts then
                        rule << {rhs = change_rep1_to_rep rule.rhs} 
                      else
                        rule << {rhs = remove_opts (opt_rep1_nts, rule.rhs)})
              | _ -> 
                directive)
         directives
 in
 directives

%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%
%% Replace various complicated patterns with simpler repetitions
%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%

op simplifyRepeats (grammar : ContextFreeGrammar) : ContextFreeGrammar =

 %%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%
 %% First simplify right hand sides such as  "... x, Rep [NT N, x], ..."
 %%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%

 let directives = 
     map (fn directive ->
            case directive of
              | Rule rule -> Rule (rule << {rhs = simplify_rep_to_rep1 rule.rhs})
              | _ -> directive)
         grammar.directives
 in

 %%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%
 %% Then simplify rules such as  'N ::= Any [x, Seq [NT N, x]]'
 %%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%

 let directives = 
     map (fn directive ->
            case directive of
              | Rule rule -> Rule (simplify_any_to_rep1 rule)
              | _ -> directive)
         grammar.directives
 in

 %%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%
 %% Finally, if a rule looks like             'N := Rep1 {body, sep}'
 %% and all references to N are of the form   'Opt [NT N]'
 %% then change the rule to                   'N := Rep {body, sep}'
 %% and change all references to              'NT N'
 %%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%

 let directives = simplify_optional_rep1s directives in

 grammar << {directives = directives}

end-spec
