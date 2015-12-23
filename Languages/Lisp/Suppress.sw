(* Copyright 2015 Kestrel Institute. See file LICENSE for license details *)

SpecToLisp qualifying
spec
  %% This file is used by Interpreter and SpecToLisp

  import /Languages/MetaSlang/Specs/StandardSpec

  op SuppressGeneratedDefuns : List String 
  %% SpecToLisp.SuppressGeneratedDefuns is initialized by 
  %%  $SPECWARE4/Applications/Specware/Handwritten/Lisp/Specware4.lisp
  %% It is updated by Char.lisp, Integer.lisp, etc.

  op printPackageId : QualifiedId * String -> String
  %% SpecToLisp.printPackageId is defined in SpecToLisp

  %% There are three distinct, but closely related concepts here:
  %%
  %% (1) MSInterpreter.avoidExpanding? is used solely by Interpreter to avoid expanding.
  %% (2) The usual reason for not expanding is a non-constructive definition.
  %% (3) The usual reason something is in SuppressGeneratedDefuns is that it has a non-constructive definition.
  %%
  %% If there are problems using SuppressGeneratedDefuns to determine expansion avoidance,
  %% we may need to introduce a second list of names, specifically for expansion avoidance,

 %%% sjw: The reason for not expanding in the interpreter is that the interpreter has a built-in
 %%% definition, so this belongs in Interpreter.sw and should be more explicit

end-spec
