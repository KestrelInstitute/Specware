CFG qualifying spec

%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%
%%% These basic grammar files provide a structure for defining grammars from 
%%% which compatible AST's, parsers, an-d printers can be synthesized.
%%%
%%% The general strategy to produce a useful gramamr is:
%%%
%%% (1) Define a complete initial grammar using primitive tokens such as 
%%%     unicode characters.  This should adhere as rigorously an-d literally 
%%%     as possible to published standards.
%%%
%%% (2) Transform that original grammar to simplify repetitions, explicate
%%%     implicit subrules, etc.
%%%
%%% (3) Extract a finte state machine tokenizer from the low-level rules.
%%%
%%% (4) Extract a revised grammar whose tokens are the outout from the tokenizer.
%%%
%%% The latter steps could be repeated at multiple levels, using more complex 
%%% tokens.
%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%

type ContextFreeGrammar (terminal, non_terminal) = 
  {name          : String,      
   documentation : String,      
   directives    : Directives (terminal, non_terminal)}

%% Could simply have a list of rules, but adding this level 
%% of abstraction makes it easier to generate literate 
%% derivative files that contain comments.

type Directives (terminal, non_terminal) = List (Directive (terminal, non_terminal))
type Directive (terminal, non_terminal) = | Rule    (Rule (terminal, non_terminal))
                       | Header  String
                       | Comment String

type Rule (terminal, non_terminal) = {lhs : non_terminal, rhs : RHS (terminal, non_terminal)}

type BodyAndSeparator (terminal, non_terminal) = (RHS (terminal, non_terminal)) * (RHS (terminal, non_terminal))

type RHS (terminal, non_terminal) = 

  | Terminal terminal

  | NT       non_terminal

  | Seq      List (RHS (terminal, non_terminal))        % match each RHS, in order

  | Any      List (RHS (terminal, non_terminal))        % match any RHS 

  | Opt      List (RHS (terminal, non_terminal))        % match the RHS zero or one times

  | Rep      List (RHS (terminal, non_terminal))        % match the RHS zero or more times

  | Rep1     List (RHS (terminal, non_terminal))        % match the RHS one or more times

  | RepSep   BodyAndSeparator (terminal, non_terminal)  % match the first RHS zero or more times, 
                                                        %  with matches to the second RHS interspersed

  | Rep1Sep  BodyAndSeparator (terminal, non_terminal)  % match the first RHS one or more times, 
                                                        %  with matches to the second RHS interspersed
    
  %% Note:
  %%
  %% These two rules may simplify some low-level productions, for example 
  %% those involved in tokenization.
  %%
  %% But they move beyond a simple context free grammar into intersections 
  %% of grammars, so use sparingly.
    
  | Diff     (RHS (terminal, non_terminal)) * (RHS (terminal, non_terminal))          % match the first RHS, but not the second 
                                                                                      %  (e.g. all chars except ...)

  | Restrict (RHS (terminal, non_terminal)) * (RHS (terminal, non_terminal) -> Bool)  % match the RHS, but only if predicate is true
    
end-spec
