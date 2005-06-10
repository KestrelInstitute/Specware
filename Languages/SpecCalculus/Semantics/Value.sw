SpecCalc qualifying spec
  %% Value.sw indirectly imports Types.sw
  import /Languages/MetaSlang/Specs/Categories/AsRecord  % Morphism
  import /Provers/Proof                                  % Proof
  import /Library/IO/Primitive/IO                        % Time

  sort ValueInfo = Value * TimeStamp * UnitId_Dependency

  %% --------------------------------------------------------------------------------

  sort Value =
    | Spec        Spec
    | Morph       Morphism
    | Renaming    Renaming 
    | SpecPrism   SpecPrism       % tentative
    | SpecInterp  SpecInterp      % tentative
    | Diag        SpecDiagram       
    | Colimit     SpecInitialCocone 
    | Proof       Proof
    | InProcess			  % Used for catching circular definitions
    | UnEvaluated SCTerm	  % To allow evaluation by need of multiple terms within a file
   %| DiagMorph
    | Other       OtherValue      % Used for extensions to Specware

  sort OtherValue                % Used for extensions to Specware

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

  sort TimeStamp = Time               % In general, can be over 32 bits -- not a fixnum

  op  oldestTimeStamp : TimeStamp     % < than any recent TimeStamp -- perhaps never used
  def oldestTimeStamp = 0               

  op  futureTimeStamp : TimeStamp     % > than any TimeStamp in foreseeable future
  def futureTimeStamp = 9999999999    % NOTE: this is 34 bits, i.e., a bignum

  %% --------------------------------------------------------------------------------

  sort UnitId_Dependency = List UnitId

  sort ValidatedUIDs     = List UnitId

  %% See validateCache in Evaluate/UnitId.sw -- it chases dependencies recursively,
  %% so we should not need to take unions of dependencies.

  %% --------------------------------------------------------------------------------

endspec
