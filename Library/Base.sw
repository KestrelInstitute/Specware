\section{Base}

The Base spec is implicitly imported by every user-defined spec.

\begin{spec}

spec Base
  % Note:
  % The following definition is in ast-pp.sl :
  % def isBuiltIn s = (s = "String" or s = "Nat" or s = "Boolean" or s = "Char" or s = "Integer")
  % That predicate is used to prevent some imports from printing 

  import Base/Boolean
  import Base/Functions 
  import Base/Integer 
  import Base/Nat
  import Base/Char
  import Base/String
  import Base/List
  import Base/Lift 
  import Base/System
  import Base/Compare
  % import Base/PrettyPrinter % in base??
 end
\end{spec}
