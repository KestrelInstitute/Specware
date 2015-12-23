(* Copyright 2015 Kestrel Institute. See file LICENSE.text for license details *)

\section{Evaluation of Let and Where}

Synchronized with from r1.9 SW4/Languages/SpecCalculus/Semantics/Evaluate/EvalTerm.sl

When evaluating a let, the let bindings (declarations) are in scope only
within the body of the let. So we retrieve and save the current binding
context, add the local bindings, evaluate the term and then restore
the saved context.

\begin{spec}
SpecCalc qualifying spec {
  import Signature
\end{spec}

\begin{spec}
  def SpecCalc.evaluateLet decls term = {
      context <- getLocalContext;
      evaluateLocalDecls decls;
      valueInfo <- evaluateTermInfo term;
      setLocalContext context;
      return valueInfo
    }
\end{spec}

The next evaluates a list of declarations. It is used in the evaluation
of \verb+let+ and \verb+where+ declarations and at the top level when
evaluating a list of declarations in a file.

The list must be typeed in dependence order. Recursion is not allowed.

\begin{spec}
  op evaluateLocalDecls : SCDecls -> Env ()
  def evaluateLocalDecls decls =
    let def evaluateLocalDecl ((name,term)) = {
        valueInfo <- evaluateTermInfo term;
        bindInLocalContext (UnitId_Relative {path=[name], hashSuffix=None}) valueInfo;
        return ()
      } in
      foldM (fn _ -> fn decl -> evaluateLocalDecl decl)
            () 
            decls
}
\end{spec}
