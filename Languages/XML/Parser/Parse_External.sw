XML qualifying spec

  %%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%
  %%%          External                                                                            %%%
  %%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%
  %% 
  %% [30]  extSubset           ::=  TextDecl? extSubsetDecl
  %% 
  %% [31]  extSubsetDecl       ::=  ( markupdecl | conditionalSect | DeclSep)* 
  %% 
  %% [61]  conditionalSect     ::=  includeSect | ignoreSect
  %% 
  %% [62]  includeSect         ::=  '<![' S? 'INCLUDE' S? '[' extSubsetDecl ']]>' 
  %% 
  %%                                                             [VC: Proper Conditional Section/PE Nesting]
  %% 
  %% [63]  ignoreSect          ::=  '<![' S? 'IGNORE' S? '[' ignoreSectContents* ']]>' 
  %% 
  %%                                                             [VC: Proper Conditional Section/PE Nesting]
  %% 
  %% [64]  ignoreSectContents  ::=  Ignore ('<![' ignoreSectContents ']]>' Ignore)*
  %% 
  %% [65]  Ignore              ::=  Char* - (Char* ('<![' | ']]>') Char*)
  %% 
  %% [77]  TextDecl            ::=  '<?xml' VersionInfo? EncodingDecl S? '?>'
  %%
  %% [78]  extParsedEnt        ::=  TextDecl? content
  %%
  %% ====================================================================================================

endspec
