OPr = obligations Primitives  % none


OS = obligations Syntax  % none


OSC = obligations SyntaxWithCoreOps

PSC1 = prove exprFreeVars_Obligation in OSC  % crash
