
spec
  import ../Signature 

  %%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%
  %% We worry the following situation:
  %%
  %%   an unqualified Y that refers to B.Y in the domain spec  
  %%
  %%   and translation rules:
  %%     B.Y +-> B.Y 
  %%     A.X +-> Y 
  %% 
  %%   creating a spec in which the unqualified Y refers to the 
  %%   translation of A.X, as opposed to the transation of B.Y
  %%
  %%
  %% Moreover, we wish to avoid gratuitously qualifying every reference, 
  %%  to keep print forms for specs as similar as possible to their 
  %%  original input text.  Seeing Integer.+, String.^ etc. everywhere 
  %%  would be confusing and annoying.
  %%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%

  sort TranslationMap  = AQualifierMap (QualifiedId * Aliases) 
  sort TranslationMaps = TranslationMap * TranslationMap

  op  removeQualifyCaptures : [a] ASpec a -> TranslationMaps -> a -> Env TranslationMaps
  def removeQualifyCaptures spc translation_maps pos = 
    %% TODO: implement this!
    return translation_maps

endspec