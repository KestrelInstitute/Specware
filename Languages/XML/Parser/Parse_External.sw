XML qualifying spec

  %%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%
  %%%          External                                                                            %%%
  %%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%
  %% 
  %%  Well-formedness constraint: External Subset
  %%
  %%   The external subset, if any, must match the production for extSubset.
  %% 
  %% -------------------------------------------------------------------------------------------------
  %% 
  %%  [30]  extSubset           ::=  TextDecl? extSubsetDecl
  %% 
  %% *[31]  extSubsetDecl       ::=  ( markupdecl | conditionalSect | DeclSep)* 
  %%   ==>
  %% [K12]  extSubsetDecl       ::=  ( markupdecl | includeSect | ignoreSect | DeclSep)* 
  %% 
  %%  [61]  conditionalSect     ::=  includeSect | ignoreSect
  %% 
  %%  [62]  includeSect         ::=  '<![' S? 'INCLUDE' S? '[' extSubsetDecl ']]>' 
  %% 
  %%                                                             [VC: Proper Conditional Section/PE Nesting]
  %% 
  %%  [63]  ignoreSect          ::=  '<![' S? 'IGNORE' S? '[' ignoreSectContents* ']]>' 
  %% 
  %%                                                             [VC: Proper Conditional Section/PE Nesting]
  %% 
  %%  [64]  ignoreSectContents  ::=  Ignore ('<![' ignoreSectContents ']]>' Ignore)*
  %% 
  %%  [65]  Ignore              ::=  Char* - (Char* ('<![' | ']]>') Char*)
  %% 
  %% *[77]  TextDecl            ::=  '<?xml' VersionInfo? EncodingDecl S? '?>'
  %%   ==>
  %% [K13]  TextDecl            ::=  ElementTag
  %%
  %%                                                             [KC: Proper Text Decl]
  %%  
  %% -------------------------------------------------------------------------------------------------
  %%  
  %%  This is the rule for an external general parsed entity:
  %%  
  %%  [78]  extParsedEnt        ::=  TextDecl? content
  %%
  %%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%

endspec
