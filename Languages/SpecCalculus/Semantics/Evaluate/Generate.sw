(* Copyright 2015 Kestrel Institute. See file LICENSE for license details *)

\subsection{Generation from Specs}

\begin{spec}
SpecCalc qualifying spec
  import Snark
  import Proofs
  import Java
  import C
  %import /Languages/MetaSlang/CodeGen/C/ToC
  import /Languages/MetaSlang/CodeGen/Lisp/SpecToLisp
  import /Languages/MetaSlang/CodeGen/Haskell/SpecToHaskell

  def SpecCalc.evaluateGenerate (language, sub_term as (term,position), optFile) pos = {
        (value,timeStamp,depUIDs) <- SpecCalc.evaluateTermInfo sub_term;
        (optBaseUnitId,baseSpec) <- getBase;
        cValue <- return (coerceToSpec value);
        case cValue of
          | Spec spc -> 
              (case language of
                 | "lisp" -> evaluateLispCompile((cValue,timeStamp,depUIDs), sub_term, optFile, false)
                 | "lisp_local" -> evaluateLispCompileLocal
                                  ((cValue,timeStamp,depUIDs), sub_term,optFile)
                 | "snark" -> evaluateSnarkGen
                               ((cValue,timeStamp,depUIDs), sub_term,optFile)
                 | "spec" -> {
                        print (showValue cValue);
                        return (cValue,timeStamp,depUIDs)
                      }
                 %| "c_old" -> 
                 %      let _ = specToC (subtractSpec spc baseSpec) in
                 %      return (cValue,timeStamp,depUIDs)
		 | "c" -> evaluateCGen((cValue,timeStamp,depUIDs), sub_term, optFile)  % TODO: add name to shell command options
                 | "Java" ->
		       evaluateJavaGen ((cValue,timeStamp,depUIDs), sub_term,optFile)
                 | "java" ->
		       evaluateJavaGen ((cValue,timeStamp,depUIDs), sub_term,optFile)
		 | "proofs" ->
		       evaluateProofGen ((cValue,timeStamp,depUIDs), sub_term,optFile,false)
                 | lang -> raise (Unsupported ((positionOf sub_term),
                                "no generation for language "
                              ^ lang
                              ^ " (yet)")))

          | Other value -> evaluateOtherGenerate (language,sub_term,optFile) (value,timeStamp,depUIDs) pos

          | _ -> raise (TypeCheck (pos,
                        "attempting to generate code from an object that is not a specification"))
        }


  %% Need to add error detection code
  def SpecCalc.evaluateLispCompile(valueInfo as (value,_,_), cterm, optFileName, slicing?) =
    case coerceToSpec value of
      | Spec spc ->
        {cUID <- SpecCalc.getUID cterm;
         print (";;; Generating lisp file ");
         lispFileName <- UIDtoLispFile (cUID, optFileName);
         print (                          lispFileName ^ "\n");
         let _ = ensureDirectoriesExist lispFileName in
         let _ = toLispFile (spc, lispFileName, lispFilePreamble(), true, slicing?) in
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
         let preamble = ";; THIS FILE IS GENERATED FROM SPECWARE SOURCE. DO NOT HAND-EDIT THIS FILE.\n" in
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
         prefix <- removeLast path;
         mainName <- last path;
         fileName <- return ((uidToFullPath {path=prefix,hashSuffix=None})
                             ^ "/lisp/" ^ mainName ^ ".lisp");
         return fileName}
endspec
\end{spec}
