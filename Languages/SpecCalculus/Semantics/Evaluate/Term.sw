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
 import ExtendMorphism 
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

 def SpecCalc.evaluateTerm term =
   {(value,_,_) <- SpecCalc.evaluateTermInfo term;
    return value}

 def SpecCalc.evaluateTermInfo term =
   let pos = positionOf term in
   case (valueOf term) of
    | Print       term     -> SpecCalc.evaluatePrint       (term,false)
    | UnitId      unitId   -> SpecCalc.evaluateUID         pos unitId
    | Spec        elems    -> SpecCalc.evaluateSpec        elems UnQualified pos
    | SpecMorph   fields   -> SpecCalc.evaluateSpecMorph   fields    pos
    | SpecInterp  fields   -> SpecCalc.evaluateSpecInterp  fields    pos % tenatitve
    | SpecPrism   fields   -> SpecCalc.evaluateSpecPrism   fields    pos % tenatitve
    | ExtendMorph term     -> SpecCalc.evaluateExtendMorph term
    | Diag        elems    -> SpecCalc.evaluateDiag        elems     pos
    | Colimit     sub_term -> SpecCalc.evaluateColimit     sub_term  pos
    | Subst       args     -> SpecCalc.evaluateSubstitute  args      pos
    | OpRefine    args     -> SpecCalc.evaluateOpRefine    args      pos
    | Transform   args     -> SpecCalc.evaluateTransform   args      pos
    | DiagMorph   fields   -> SpecCalc.evaluateDiagMorph   fields

    | Qualify  ((Spec elems, pos1), qualifier) -> SpecCalc.evaluateSpec elems qualifier pos1
    | Qualify  (sub_term, qualifier) -> SpecCalc.evaluateQualify sub_term qualifier
    | Let      (decls, sub_term)     -> SpecCalc.evaluateLet     decls sub_term
    | Where    (decls, sub_term)     -> SpecCalc.evaluateLet     decls sub_term

    | Hide     (names, sub_term) -> {
          print "hide request ignored\n";
          SpecCalc.evaluateTermInfo sub_term
        }

    | Export (names, sub_term) -> {
          print "export request ignored\n";
          SpecCalc.evaluateTermInfo sub_term
        }

    | Translate   (tm, renaming)  -> SpecCalc.evaluateTranslate   tm renaming   pos

    | Obligations (sub_term)      -> SpecCalc.evaluateObligations sub_term
    | Expand      (sub_term)      -> SpecCalc.evaluateExpand      sub_term      pos
    | Prove       args            -> SpecCalc.evaluateProve       args          pos
    | ProofCheck  args            -> SpecCalc.evaluateProofCheck  args          pos
    | Generate    args            -> SpecCalc.evaluateGenerate    args          pos
    | Reduce      (msTerm,scTerm) -> SpecCalc.reduce              msTerm scTerm pos
    | Other       args            -> SpecCalc.evaluateOther       args pos  % used for extensions to Specware
    | Quote       value_info      -> return value_info
end-spec