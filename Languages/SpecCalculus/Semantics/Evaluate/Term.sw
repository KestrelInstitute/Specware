(* Copyright 2015 Kestrel Institute. See file LICENSE.text for license details *)

(* Interpreter for Spec Calculus *)

SpecCalc qualifying spec
 % import Signature          
 import UnitId          
 import Spec         
 import Let         
 import Qualify         
 import Diagram      
 import Colimit
 import SpecMorphism 
 import SpecInterp    % tenatitve
 import SpecPrism     % tenatitve
%% import ExtendMorphism 
 import DiagMorphism 
 import Generate      
 import Translate      
 import Obligations
 import Substitute      
 import OpRefine
 import Print      
 import Prove
 import translate ProofCheck by {Set._ +-> PCSet._}
 import Expand			
 import Reduce
 import Transform

 %% Experimental file:
 import Make   % we don't yet have SpecCalc term to dispatch to this,
               % but it can in principle be accessed from toplevel.lisp
	       % via hooks in Specware.sw (Prism actually does this)

(* This is a monadic interpreter for the Spec Calculus. *)

 def evaluateTerm term =
   {(value,_,_) <- evaluateTermInfo term;
    return value}

 def evaluateTermInfo term =
   let pos = positionOf term in
   case (valueOf term) of
    | Print       term     -> evaluatePrint       (term,false)
    | UnitId      unitId   -> evaluateUID         pos unitId
    | Spec        elems    -> evaluateSpec        elems UnQualified pos
    | SpecMorph   fields   -> evaluateSpecMorph   fields    pos
    | SpecInterp  fields   -> evaluateSpecInterp  fields    pos % tenatitve
    | SpecPrism   fields   -> evaluateSpecPrism   fields    pos % tenatitve
%%    | ExtendMorph term     -> evaluateExtendMorph term
    | Diag        elems    -> evaluateDiag        elems     pos
    | Colimit     sub_term -> evaluateColimit     sub_term  pos
    | Subst       args     -> evaluateSubstitute  args      pos
    | OpRefine    args     -> evaluateOpRefine    args      pos
    | Transform   args     -> evaluateTransform   args      pos
    | DiagMorph   fields   -> evaluateDiagMorph   fields

    | Qualify  ((Spec elems, pos1), qualifier) -> evaluateSpec elems qualifier pos1
    | Qualify  (sub_term, qualifier) -> evaluateQualify sub_term qualifier
    | Let      (decls, sub_term)     -> evaluateLet     decls sub_term
    | Where    (decls, sub_term)     -> evaluateLet     decls sub_term

    | Hide     (names, sub_term) -> {
          print "hide request ignored\n";
          evaluateTermInfo sub_term
        }

    | Export (names, sub_term) -> {
          print "export request ignored\n";
          evaluateTermInfo sub_term
        }

    | Translate   (tm, renaming)  -> evaluateTranslate   tm renaming   pos

    | Obligations (sub_term)      -> evaluateObligations sub_term
    | Expand      (sub_term)      -> evaluateExpand      sub_term      pos
    | Prove       args            -> evaluateProve       args          pos
    | ProofCheck  args            -> evaluateProofCheck  args          pos
    | Generate    args            -> evaluateGenerate    args          pos
    | Reduce      (msTerm,scTerm) -> reduce              msTerm scTerm pos
    | Other       args            -> evaluateOther                args pos  % used for extensions to Specware
    | Quote       value_info      -> return value_info
end-spec