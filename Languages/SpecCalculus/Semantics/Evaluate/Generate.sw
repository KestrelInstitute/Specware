\subsection{Generation from Specs}

\begin{spec}
SpecCalc qualifying spec {
  import Snark
  import Java
  import C
  import /Languages/MetaSlang/CodeGen/C/ToC
  import /Languages/MetaSlang/CodeGen/Lisp/SpecToLisp
  %import /Languages/MetaSlang/CodeGen/Java/ToJava

  def SpecCalc.evaluateGenerate (language, sub_term as (term,position), optFile) pos = {
        (value,timeStamp,depUIDs) <- SpecCalc.evaluateTermInfo sub_term;
        baseUID <- pathToRelativeUID "/Library/Base";
        (Spec baseSpec,_,_) <- SpecCalc.evaluateUID (Internal "base") baseUID;
        cValue <- return (coerceToSpec value);
        case cValue of
          | Spec spc -> 
              (case language of
                 | "lisp" -> evaluateLispCompile
		             ((cValue,timeStamp,depUIDs), sub_term,optFile)
                 | "lisp_local" -> evaluateLispCompileLocal
			          ((cValue,timeStamp,depUIDs), sub_term,optFile)
                 | "snark" -> evaluateSnarkGen
			       ((cValue,timeStamp,depUIDs), sub_term,optFile)
                 | "spec" -> {
                        print (showValue cValue);
                        return (cValue,timeStamp,depUIDs)
                      }
                 | "c_old" -> 
                       let _ = specToC (subtractSpec spc baseSpec) in
                       return (cValue,timeStamp,depUIDs)
		 | "c" -> evaluateCGen((cValue,timeStamp,depUIDs),optFile)
                 | "java" -> evaluateJavaGen ((cValue,timeStamp,depUIDs), sub_term,optFile)
                       %let _ = specToJava (subtractSpec spc baseSpec) in
                       %return (cValue,timeStamp,depUIDs)
                 | lang -> raise (Unsupported ((positionOf sub_term),
                                "no generation for language "
                              ^ lang
                              ^ " yet")))

          | Other value -> evaluateOtherGenerate (language,sub_term,optFile) (value,timeStamp,depUIDs) pos

          | _ -> raise (TypeCheck (pos,
                        "attempting to generate code from an object that is not a specification"))
        }

  %% Need to add error detection code
  def SpecCalc.evaluateLispCompile(valueInfo as (value,_,_), cterm, optFileName) =
    case coerceToSpec value of
      | Spec spc ->
        {cUID <- SpecCalc.getUID cterm;
         lispFileName <- UIDtoLispFile (cUID, optFileName);
         print (";;; Generating lisp file " ^ lispFileName ^ "\n");
         let _ = ensureDirectoriesExist lispFileName in
         let _ = toLispFile (spc, lispFileName,"") in
         return valueInfo}
      | _ -> raise (TypeCheck ((positionOf cterm),
                               "attempting to generate code from an object that is not a specification"))

  %% Need to add error detection code
  def SpecCalc.evaluateLispCompileLocal(valueInfo as (value,_,_), cterm, optFileName) =
    case coerceToSpec value of
      | Spec spc ->
        {cUID <- SpecCalc.getUID cterm;
         lispFileName <- UIDtoLispFile (cUID, optFileName);
         print (";;; Generating lisp file " ^ lispFileName ^ "\n");
         let _ = ensureDirectoriesExist lispFileName in
         let _ = localDefsToLispFile (spc, lispFileName,"") in
         return valueInfo}
      | _ -> raise (TypeCheck ((positionOf cterm),
                               "attempting to generate code from an object that is not a specification"))
      
\end{spec}

Make a lisp file name for a UnitId.

\begin{spec}
  op UIDtoLispFile: UnitId * Option String -> SpecCalc.Env String
  def UIDtoLispFile ((unitId as {path,hashSuffix}), optFileName) =
    case optFileName of
      | Some fileName -> return fileName
      | _ -> {
         prefix <- removeLastElem path;
         mainName <- lastElem path;
         fileName <- return ((uidToFullPath {path=prefix,hashSuffix=None})
                             ^ "/lisp/" ^ mainName ^ ".lisp");
         return fileName}
\end{spec}

Recursively compile imports. If there is a UnitId for the import then
compile it in a separate file if necessary, and return a load form. If
no UnitId then generate the text for it.

Add these in later
%\ begin{spec}
%  op compileImports: List Spec * Text * List Spec -> SpecCalc.Env (Text * List Spec)
%  def compileImports(spcs, resultSoFar, doneSpecs) =
%    case spcs
%      of [] -> return(resultSoFar,doneSpecs)
%       | iSpc::rSpcs ->
%	 {(thisISpcText,newDoneSpecs) <- compileImport(iSpc,doneSpecs);
%	  compileImports(rSpcs, thisISpcText ++ resultSoFar,
%			 newDoneSpecs) }
%\ end{spec}


%\ begin{spec}
%  op compileImport: Spec * List Spec -> SpecCalc.Env (Text * List Spec)
%  def compileImport(spc, doneSpecs) =
%    if member(spc, doneSpecs)
%      then return ([],doneSpecs)
%      else {(preamble,newDoneSpecs)
%	      <- compileImports(importedSpecsList spc.importedSpecs, [],
%				cons(spc,doneSpecs));
%	    print("Compiling "^ spc.name ^ " in line.\n");
%	    return((toLispText spc) ++ preamble,newDoneSpecs)}
%\ end{spec}

\begin{spec}
}
\end{spec}
