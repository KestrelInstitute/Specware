\subsection{Generation from Specs}

Synchronized with r1.6 SW4/Languages/SpecCalculus/Semantics/Evaluate/EvalCompile.sl

\begin{spec}
SpecCalc qualifying spec {
  import Signature  
  import ../SpecPath
  import /Languages/MetaSlang/CodeGen/Lisp/SpecToLisp

  %% Hopefully these will be unnecessary in the final system

  % sort Env a = SpecCalc.Env a
  %sort Spec = MetaSlang.Spec

  %% Need to add error detection code
  def SpecCalc.evaluateLispCompile(valueInfo as (Spec spc,_,_), cterm, optFileNm) =
    {%(preamble,_) <- compileImports(importedSpecsList spc.importedSpecs,[],[spc]);
     cURI <- SpecCalc.getURI(cterm);
     lispFileName <- URItoLispFile (cURI, optFileNm);
     let _ = ensureDirectoriesExist lispFileName in
     let _ = toLispFile(spc, lispFileName,[]) in
     {print("Compiled");
      return valueInfo}}
\end{spec}

Make a lisp file name for a URI.

\begin{spec}
  op URItoLispFile: URI * Option String -> SpecCalc.Env String
  def URItoLispFile ((uri as {path,hashSuffix}), optFileNm) =
    case optFileNm
      of Some filNam -> return filNam
       | _ ->
    {prefix <- removeLastElem path;
     mainName <- lastElem path;
     let filNm = (uriToPath {path=prefix,hashSuffix=None})
        ^ "/lisp/" ^ mainName ^ ".lisp"
     in
     {print("Lisp file name " ^ filNm ^ "\n");
      return filNm}}
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
