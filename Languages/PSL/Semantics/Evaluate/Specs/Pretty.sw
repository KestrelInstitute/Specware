\section{Abstract Pretty Printer}

We want to postpone committing to one pretty printer or the other. The
Wadler/Lindig pretty printer has the advantage of being much simpler and
better documented.  The Bjorner/Espinosa printer is complex, has a poor
interface (eg. one has to provide indenting information) and there is
no documentation. It has the advantage that the coverage of MetaSlang
is better. Also, it is probably less likely to get a stack overflow.

There might be a problem finding a refinement from the following to
the Bjorner/Espinosa printer as many of its operators require indent
information. 

Also a pretty printer can benefit from state (recording context and
layout information). There might be a win in placing the pretty printer
in the state monad.

\begin{spec}
Pretty qualifying spec
  sort Doc
endspec
\end{spec}
