(* Copyright 2015 Kestrel Institute. See file LICENSE for license details *)

SpecCalc qualifying spec
  %% Value.sw indirectly imports Types.sw
  import /Languages/MetaSlang/Specs/Categories/AsRecord  % Morphism
  import /Provers/Proof                                  % Proof
  import /Library/IO/Primitive/IO                        % Time
  import /Library/Algorithms/Thread                      % Mutex
  import ValueSig                                        % ValueInfo
  import /Languages/SpecCalculus/AbstractSyntax/SCTerm   % SCTerm

  type SpecCalc.ValueInfo     = Value * TimeStamp * UnitId_Dependency
  type SpecCalc.ValueTermInfo = Value * TimeStamp * UnitId_Dependency * SCTerm

  %% --------------------------------------------------------------------------------

%  type UnitId 
%  type RelativeUID

  type Value =
    | Value.Spec        Spec
    | Value.Morph       Morphism
   %| Value.Renaming    Renaming 
    | Value.SpecPrism   SpecPrism       % tentative
    | Value.SpecInterp  SpecInterp      % tentative
    | Value.Diag        SpecDiagram       
    | Value.Colimit     SpecInitialCocone 
    | Value.Proof       SCProof
    | Value.InProcess   Mutex		  % Used for catching circular definitions
    | Value.UnEvaluated SCTerm	  % To allow evaluation by need of multiple terms within a file
   %| Value.DiagMorph
    | Value.Values      List (String * Value)
    | Value.Other       OtherValue      % Used for extensions to Specware

  type OtherValue                % Used for extensions to Specware

  %% tentative for prism...
  type SpecInterp = {dom : Spec,
		     med : Spec,
		     cod : Spec,
		     d2m : Morphism,
		     c2m : Morphism}

  type SpecPrism = {dom   : Spec,  
		    sms   : List Morphism,
		    pmode : PrismMode,
		    tm    : SCTerm}

  type PrismMode = | Uniform     PrismSelection
                   | PerInstance (List SpecInterp)

  %% --------------------------------------------------------------------------------

  type TimeStamp = Time               % In general, can be over 32 bits -- not a fixnum

  op  oldestTimeStamp : TimeStamp     % < than any recent TimeStamp -- perhaps never used
  def oldestTimeStamp = 0               

  op  futureTimeStamp : TimeStamp     % > than any TimeStamp in foreseeable future
  def futureTimeStamp = 9999999999    % NOTE: this is 34 bits, i.e., a bignum

  %% --------------------------------------------------------------------------------

  type UnitId_Dependency = List UnitId

  type ValidatedUIDs     = List UnitId

  %% See validateCache in Evaluate/UnitId.sw -- it chases dependencies recursively,
  %% so we should not need to take unions of dependencies.

  %% --------------------------------------------------------------------------------

endspec
