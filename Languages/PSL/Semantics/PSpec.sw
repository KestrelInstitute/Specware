\section{Procedural Specs}

The static spec records information about ops and sorts that are not
considered part of the machine state and do not change.

The dynamic spec, reflects all the vars in scope
within the procedures and the invariants that hold about those
variables.

Presumably there should be axioms in each. Should the syntax be extended
with invariants (same as axioms except dynamic), or should
we inspect axioms to see whether they contain references to the 
variables .. in which case they are invariants. Are variables and
ops in the same name space?

\begin{spec}
% translate
Context
% by {
%   NatTrans.ppNatTrans +-> BSpec.ppNatTrans,
%   NatTrans.components +-> BSpec.components,
%   NatTrans.build +-> BSpec.ntBuild,
%   Functor.vertexMap +-> BSpec.modeMap,
%   Functor.edgeMap +-> BSpec.transitionMap,
%   Functor.ppFunctor +-> BSpec.ppFunctor
% }
where { 
Context = spec {
  import Procedure
  import /Languages/MetaSlang/Specs/AnnSpec
  import /Languages/MetaSlang/Specs/SimplePrinter
  import PolyMap qualifying /Library/Structures/Data/Maps/Polymorphic

  sort PSpec = {
    staticSpec : Spec,
    dynamicSpec : Spec,
    procedures : PolyMap.Map (QualifiedId,Procedure)
  }

  op ppPSpec : PSpec -> Doc
  def ppPSpec pSpec =
    ppConcat [
      ppString "static=",
      ppNewline,
      ppIndent (ppASpec pSpec.staticSpec),
      ppNewline,
      ppString "dynamic=",
      ppNewline,
      ppIndent (ppASpec pSpec.dynamicSpec),
      ppNewline,
      ppString "procedures=",
      ppNewline,
      ppIndent (ppMap ppQualifiedId ppProcedure pSpec.procedures)
    ]

  % the "Less" means pretty print all the specs but removed
  % the spec given in the second argument. Usually the Base.
  op ppPSpecLess : PSpec -> Spec -> Doc
  def ppPSpecLess pSpec spc =
    ppConcat [
      ppString "static=",
      ppNewline,
      ppIndent (ppASpec (subtractSpec pSpec.staticSpec spc)),
      ppNewline,
      ppString "dynamic=",
      ppNewline,
      ppIndent (ppASpec (subtractSpec pSpec.dynamicSpec pSpec.staticSpec)),
      ppNewline,
      ppString "procedures=",
      ppNewline,
      ppIndent (ppMap ppQualifiedId (fn proc -> ppProcedureLess proc spc) pSpec.procedures)
    ]
}}
\end{spec}
