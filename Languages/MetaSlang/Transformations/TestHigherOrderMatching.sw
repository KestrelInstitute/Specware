

\section{Testing Higher Order Matching}

\begin{spec}

spec  

 import RewriteRules

 %def benchmarks = MatchingBenchmarks.benchmarks

 def skolemize (fml:Term) = 
     let (freeVars,n,S,fml) = bound(Exists:Binder,0,fml,[],[]) in
     let fml = substitute(fml,S) 		   in
     case fml
       of Apply(Fun(Equals,_,_),Record([(_,M),(_,N)], _),_) -> (M,N)

 op test: Spec -> ()
 def test(spc) = 
     let properties = spc.properties 	       in
     let context = makeContext spc 	       in
     List.app 
	(fn (pt,desc,tvs,fml) -> 
	  let _ = writeLine ("Matching "^desc)  in
	  let _ = writeLine (printTermWithSorts fml) in
	  let subs = match context (skolemize fml)     in
	  (writeLine "";
	   List.app printSubst subs))
        properties
 
endspec

\end{spec}

