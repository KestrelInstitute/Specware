\subsection{Generation from Specs}

\begin{spec}
SpecCalc qualifying spec {
  import Signature  
  import ../SpecPath
  import /Languages/MetaSlang/CodeGen/Lisp/SpecToLisp

  %% Need to add error detection code
  def SpecCalc.evaluateLispCompile(valueInfo as (Spec spc,_,_), cterm, optFileName) =
    {cURI <- SpecCalc.getURI cterm;
     lispFileName <- URItoLispFile (cURI, optFileName);
     let _ = ensureDirectoriesExist lispFileName in
     let _ = toLispFile (spc, lispFileName,[]) in
     return valueInfo}
\end{spec}

Make a lisp file name for a URI.

\begin{spec}
  op URItoLispFile: URI * Option String -> SpecCalc.Env String
  def URItoLispFile ((uri as {path,hashSuffix}), optFileName) =
    case optFileName of
      | Some fileName -> return fileName
      | _ -> {
         prefix <- removeLastElem path;
         mainName <- lastElem path;
         fileName <- return ((uriToPath {path=prefix,hashSuffix=None})
                             ^ "/lisp/" ^ mainName ^ ".lisp");
         print (";;; Generating lisp file " ^ fileName ^ "\n");
         return fileName}
\end{spec}

Recursively compile imports. If there is a URI for the import then
compile it in a separate file if necessary, and return a load form. If
no URI then generate the text for it.

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
