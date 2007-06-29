
\section{Testing the Rewrite Engine}


\subsection{TestRewriter}
\begin{spec}
spec
  import Rewriter

% should skolemize type variables
   
  op specTermsToRewrite: fa(a) a -> Spec -> List MS.Term
  def specTermsToRewrite (* context *)_  (spc:Spec) =
      List.map (fn (_,_,_,t,_) -> t) (localProperties spc)

  op testSpec: Spec -> ()
  def testSpec(spc) = 
      let context = makeContext spc              in
      let rules = specRules context spc          in
      let terms = specTermsToRewrite context spc in
      List.app 
       (fn term -> 
	   (context.traceDepth := 0;
	    rewriteRecursive(context,[],rules,term); ()))
         terms

      
  %def test() =    testSpec RewritingBenchmarks.SimpleRewriteTest
  %def testMAG() = testSpec RewritingBenchmarks.MAGRules

  def testFile(fileName: String) = 
      let specs = Lisp.uncell
	 	  (Lisp.apply(Lisp.symbol("RE","PARSE-META-SLANG"),
	            [Lisp.string fileName]))
      in
      let spc = hd specs in
      testSpec spc


end-spec
\end{spec}


\section{MAG Transformation}
This Section tests the matcher on the examples from MAG adapted to MetaSlang.

\subsection{TODO}
\begin{itemize}
\item Encode the overall rewrite control loop.
\item Conversion functions from specifications into rewrite rules.
\item Represent MAG example vocabulary within MetaSlang.
\item Test MAG rewrites.
\end{itemize}

