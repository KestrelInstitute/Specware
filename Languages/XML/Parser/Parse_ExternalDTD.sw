XML qualifying spec

  import XML_Parser_Base

  %%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%
  %%%          ExternalDTD (External subset of Doc Type Decl)                                      %%%
  %%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%
  %% 
  %%  [WFC: External Subset]                        *[28] 
  %%
  %%  *The external subset, if any, must match the production for extSubset.
  %%
  %%  ==>
  %%
  %%  [KWFC: External Subset]                       [K11] *[28] 
  %%
  %%   The external subset, if any, must match the production for ExternalDTD.
  %% 
  %% -------------------------------------------------------------------------------------------------
  %%  
  %%  For clarity, we rename "extSubset" to "ExternalDTD" :
  %%  
  %%  *[30]  extSubset           ::=  TextDecl? extSubsetDecl
  %%  *[31]  extSubsetDecl       ::=  ( markupdecl | conditionalSect | DeclSep)* 
  %%  *[61]  conditionalSect     ::=  includeSect | ignoreSect
  %%
  %%    ==>
  %%
  %%  [K15]  ExternalDTD         ::=  TextDecl? ExternalDecls
  %%                                                             [VC: Unique Element Type Declaration]
  %%                                                             [VC: One ID per Element Type]    
  %%                                                             [VC: One Notation Per Element Type] 
  %%                                                             [VC: No Notation on Empty Element]
  %%
  %%  [K16]  ExternalDecls       ::=  ExternalDecl*
  %%
  %%  [K17]  ExternalDecl        ::=  Decl
  %%
  %%  [Definition: Conditional sections are portions of the document type declaration external 
  %%   subset which are included in, or excluded from, the logical structure of the DTD based on 
  %%   the keyword which governs them.]
  %% 
  %%   [62]  includeSect         ::=  '<![' S? 'INCLUDE' S? '[' extSubsetDecl ']]>' 
  %% 
  %%                                                             [VC: Proper Conditional Section/PE Nesting]
  %% 
  %%   [63]  ignoreSect          ::=  '<![' S? 'IGNORE' S? '[' ignoreSectContents* ']]>' 
  %% 
  %%                                                             [VC: Proper Conditional Section/PE Nesting]
  %% 
  %%   [64]  ignoreSectContents  ::=  Ignore ('<![' ignoreSectContents ']]>' Ignore)*
  %% 
  %%   [65]  Ignore              ::=  Char* - (Char* ('<![' | ']]>') Char*)
  %% 
  %%  
  %%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%

  %% -------------------------------------------------------------------------------------------------
  %%  (renaming of extSubset)
  %%  [K15]  ExternalDTD         ::=  TextDecl? ExternalDecls
  %% -------------------------------------------------------------------------------------------------

  op parse_ExternalDTD : UChars -> Required ExternalDTD
  
  %% -------------------------------------------------------------------------------------------------
  %%  [K16]  ExternalDecls       ::=  ExternalDecl*
  %% -------------------------------------------------------------------------------------------------

  %% -------------------------------------------------------------------------------------------------
  %%  [K17]  ExternalDecl        ::=  Decl
  %% -------------------------------------------------------------------------------------------------

  %% -------------------------------------------------------------------------------------------------
  %%   [62]  includeSect         ::=  '<![' S? 'INCLUDE' S? '[' extSubsetDecl ']]>' 
  %% -------------------------------------------------------------------------------------------------

  %% -------------------------------------------------------------------------------------------------
  %%   [63]  ignoreSect          ::=  '<![' S? 'IGNORE' S? '[' ignoreSectContents* ']]>' 
  %% -------------------------------------------------------------------------------------------------

  %% -------------------------------------------------------------------------------------------------
  %%   [64]  ignoreSectContents  ::=  Ignore ('<![' ignoreSectContents ']]>' Ignore)*
  %% -------------------------------------------------------------------------------------------------

  %% -------------------------------------------------------------------------------------------------
  %%   [65]  Ignore              ::=  Char* - (Char* ('<![' | ']]>') Char*)
  %% -------------------------------------------------------------------------------------------------

endspec
