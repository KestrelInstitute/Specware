spec
  %% This file is used by Interpreter and SpecToLisp

  import ../../Specs/StandardSpec

  op SpecToLisp.SuppressGeneratedDefuns : List String 
  %% SpecToLisp.SuppressGeneratedDefuns is initialized by 
  %%  $SPECWARE4/Applications/Specware/Handwritten/Lisp/Specware4.lisp
  %% It is updated by Char.lisp, Integer.lisp, etc.

  op SpecToLisp.printPackageId : QualifiedId * String -> String
  %% SpecToLisp.printPackageId is defined in SpecToLisp

  %% There are three distinct, but closely related concepts here:
  %%
  %% (1) MSInterpreter.avoidExpanding? is used solely by Interpreter to avoid expanding.
  %% (2) The usual reason for not expanding is a non-constructive definition.
  %% (3) The usual reason something is in SuppressGeneratedDefuns is that it has a non-constructive definition.
  %%
  %% If there are problems using SuppressGeneratedDefuns to determine expansion avoidance,
  %% we may need to introduce a second list of names, specifically for expansion avoidance,

  op MSInterpreter.avoidExpanding? (qid : QualifiedId) : Boolean =
    let Qualified(q,id) = qid in
    let lisp_name = printPackageId (qid, id) in
    member (lisp_name, SpecToLisp.SuppressGeneratedDefuns)

end-spec
