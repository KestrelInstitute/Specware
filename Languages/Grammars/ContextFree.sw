(* Copyright 2015 Kestrel Institute. See file LICENSE.text for license details *)

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

% NonTerminal is defined via substitution, since it depends on implementation.

import NonTerminal  

% Terminal is defined by importing files, since it is intrinsic to a grammar.

type Terminal       

type ContextFreeGrammar =
  {name          : String,      
   documentation : String,      
   directives    : Directives}

%% Could simply have a list of rules, but adding this level 
%% of abstraction makes it easier to generate literate 
%% derivative files that contain comments.

type Directives = List Directive
type Directive  = | Rule    Rule 
                  | Header  String
                  | Comment String

type Rule = {lhs : NonTerminal, rhs : RHS}

type BodyAndSeparator = {body : List RHS, sep : List RHS}

type RHS =

  | Terminal Terminal
  | NT       NonTerminal

  | Any      List RHS          % match any RHS 

  | Seq      List RHS          % match each RHS, in order
  | Opt      List RHS          % match the RHS zero or one times
  | Rep      List RHS          % match the RHS zero or more times
  | Rep1     List RHS          % match the RHS one or more times

  | RepSep   BodyAndSeparator  % match the first RHS zero or more times, 
                               %  with matches to the second RHS interspersed

  | Rep1Sep  BodyAndSeparator  % match the first RHS one or more times, 
                               %  with matches to the second RHS interspersed
    
  %% Note:
  %%
  %% These two rules may simplify some low-level productions, for example 
  %% those involved in tokenization.
  %%
  %% But they move beyond a simple context free grammar into intersections 
  %% of grammars, so use sparingly.
    
  | Diff     RHS * RHS            % match the first RHS, but not the second 
                                  %  (e.g. all chars except ...)

  | Restrict RHS * (RHS -> Bool)  % match the RHS, but only if predicate is true
    
end-spec
