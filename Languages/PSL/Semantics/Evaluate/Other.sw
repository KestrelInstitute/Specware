\section{PSL Extension of the Spec Calculus}

\begin{spec}
SpecCalc qualifying spec {
  import ../../AbstractSyntax/Types
  import ../../AbstractSyntax/SimplePrinter
  import Oscar
  import /Languages/SpecCalculus/Semantics/Evaluate/SpecMorphism
  import /Languages/SpecCalculus/Semantics/Evaluate/Substitute
  import Transformations/PartialEval
  import Transformations/Inline
  import ../../CodeGen/ToC

  % op Convert.mapToList : fa (a,b) FinitePolyMap.Map (a,b) -> List (a * b)
  def Convert.mapToList map = map

  % op Convert.toList : EdgSet.Set -> List Edg.Edge
  % def Convert.toList set = set

  def SpecCalc.evaluateOther other pos = 
    case other of
      | OscarDecls oscarSpecElems -> evaluateOscar oscarSpecElems
      | Project (procName,unit,fileName) -> {
          (value,timeStamp,depUnitIds) <- SpecCalc.evaluateTermInfo unit;
          case value of
            | Other oscarSpec -> {
                  newOscarSpec <- inlineProc oscarSpec (makeId procName);
                  junk <-
                    case ProcMap.evalPartial (procedures newOscarSpec, makeId procName) of
                      | None -> raise (SpecError (noPos, "project: procedure " ^ (Id.show (makeId procName)) ^ " is not defined"))
                      | Some proc -> {
                           cSpec <- generateCProcedure emptySpec (emptyCSpec "") (makeId procName) proc;
                           cSpec <- return (addInclude(cSpec,"matlab.h"));
                           %return (toFile (fileName, format (80, ppCSpec cSpec)))
                           return (CG.printToFile(cSpec,Some(fileName)))
                         };
                  return (Other newOscarSpec,timeStamp,depUnitIds)
                }
            | _ -> raise (SpecError (positionOf unit, "Unit for inline is not an Oscar spec"))
          }
      | Inline (procName,unit) -> {
          (value,timeStamp,depUnitIds) <- SpecCalc.evaluateTermInfo unit;
          case value of
            | Other oscarSpec -> {
                  newOscarSpec <- inlineProc oscarSpec (makeId procName);
                  return (Other newOscarSpec,timeStamp,depUnitIds)
                }
            | _ -> raise (SpecError (positionOf unit, "Unit for inline is not an Oscar spec"))
          }
      | Specialize (metaSlangTerm,unit) -> {
          (value,timeStamp,depUnitIds) <- SpecCalc.evaluateTermInfo unit;
          case value of
            | Other oscarSpec -> {
                  (newOscarSpec,newTerm) <- specializeOscar oscarSpec metaSlangTerm;
                  print (ppFormat (ppATerm newTerm));
                  return (Other newOscarSpec,timeStamp,depUnitIds)
                }
            | _ -> raise (SpecError (positionOf unit, "Specialized unit is not an Oscar spec"))
          }

  def SpecCalc.ppOtherValue = Oscar.pp
%   def formatOtherValue pSpec = {
%       pslBaseUnitId <- pathToRelativeUID "/Library/PSL/Base";
%       (Spec pslBase,_,_) <- SpecCalc.evaluateUID (Internal "PSpec base") pslBaseUnitId;
%       fixPSpec <- return {
%            staticSpec = convertPosSpecToSpec pSpec.staticSpec,
%            dynamicSpec = convertPosSpecToSpec pSpec.dynamicSpec,
%            procedures = pSpec.procedures
%          };
%       return (ppPSpecLess fixPSpec pslBase)
%     }

%   def SpecCalc.evaluateOtherPrint oscarSpec pos = {
%        base <- baseOscarSpec;
%        oscarDoc <- OscarEnv.pp oscarSpec (modeSpec base);
%        print (ppFormat oscarDoc)
%        % print (ppFormat (ppLess oscarSpec (modeSpec base)))
%     }

  def SpecCalc.evaluateOtherPrint oscarSpec pos = {
       base <- baseOscarSpec;
       oscarString <- OscarEnv.show oscarSpec (modeSpec base);
       print (oscarString ^ "\n");
       conv <- convertOscarSpec oscarSpec;
       convString <- return (OscarStruct.show conv (modeSpec base));
       print ("converted\n" ^ convString ^ "\n");
       struct <- structOscarSpec conv;
       structString <- return (OscarStruct.show struct (modeSpec base));
       print ("structured\n" ^ structString ^ "\n")
    }

  def SpecCalc.evaluateOtherSpecMorph
         (domValue,domTimeStamp,domDepUnitIds)
         (codValue,codTimeStamp,codDepUnitIds)
         morphRules pos =
    case (domValue,codValue) of
      | (Other oscarSpec, Spec spc) -> {
            morph <- makeSpecMorphism (specOf (modeSpec oscarSpec)) spc morphRules pos;
            return (Morph morph,max (domTimeStamp,codTimeStamp),
              listUnion (domDepUnitIds,codDepUnitIds))
          }
      | (Other oscarSpec1, Other oscarSpec2) -> {
            morph <- makeSpecMorphism (specOf (modeSpec oscarSpec1)) (specOf (modeSpec oscarSpec2)) morphRules pos;
            return (Morph morph,max (domTimeStamp,codTimeStamp),
              listUnion (domDepUnitIds,codDepUnitIds))
          }
      | (_,_) -> raise
          (TypeCheck (pos, "(Other) domain and codomain of spec morphism are not specs"))

%   def SpecCalc.evaluateOtherSubstitute (domValue,domTimeStamp,domDepUnitIds)
%             (morphValue,morphTimeStamp,morphDepUnitIds) morphTerm pos =
%     case (domValue,morphValue) of
%       | (Other pSpec, Morph morph) ->
%            let def appSub x = unEnv (fn x -> applySubstitution morph x morphTerm pos) x in
%            let timeStamp = max (domTimeStamp, morphTimeStamp) in
%            let dep_UnitIds  = listUnion (domDepUnitIds, morphDepUnitIds) in {
%              dyCtxt <- dynamicSpec pSpec;
%              print "\nApplying morphism to dynamic spec\n";
%              newDyCtxt <- attemptSubstitution dyCtxt morph morphTerm pos;
%              pSpec <- setDynamicSpec pSpec newDyCtxt;
%              procs <- return (pSpec.procedures);
%              print "\nApplying morphism to procedures\n";
%              procs <- return (mapMap (fn proc -> {
%                            parameters= proc.parameters,
%                            returnInfo = proc.returnInfo,
%                            staticSpec = proc.staticSpec,
%                            dynamicSpec = appSub proc.dynamicSpec,
%                            bSpec = mapBSpec proc.bSpec (fn spc -> appSub spc) (fn x -> x)
%                            }) procs);
%              pSpec <- setProcedures pSpec procs;
%              return (Other pSpec, timeStamp, dep_UnitIds)
%            }
%       | (_,        _) ->
%            raise (TypeCheck (pos, "(Other) substitution is not a morphism, and is attempted on a non-spec"))

  def SpecCalc.evaluateOtherGenerate (lang,term,optFile) (oscSpec,timeStamp,depUnitIds) pos = {
      pslBaseUnitId <- pathToRelativeUID "/Library/PSL/Base";
      (Spec pslBase,_,_) <- SpecCalc.evaluateUID (Internal "Oscar base") pslBaseUnitId;
      case lang of
        | "c" -> {
             CSpec <- oscarToC oscSpec pslBase; 
             return (Other oscSpec,timeStamp,depUnitIds)
           }
        | lang -> raise (Unsupported (pos, "no generation for language "
                                         ^ lang
                                         ^ " yet"))
    }
}
\end{spec}
