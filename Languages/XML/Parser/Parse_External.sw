XML qualifying spec

  import Parse_TextDecl

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
  %% *[30]  extSubset           ::=  TextDecl? extSubsetDecl
  %%    =>
  %% [K12]  extSubset           ::=  ( extSubsetDecl )*
  %%                                                             [KC: Well-Formed External Subset]
  %% 
  %% *[31]  extSubsetDecl       ::=  ( markupdecl | conditionalSect | DeclSep)* 
  %%   ==>
  %% [K13]  extSubsetDecl       ::=  TextDecl | elementdecl | AttlistDecl | EntityDecl | NotationDecl | PI | Comment | includeSect | ignoreSect | S
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
  %% [K14]  TextDecl            ::=  ElementTag
  %%
  %%                                                             [KC: Well-Formed Text Decl]
  %%  
  %% -------------------------------------------------------------------------------------------------
  %%  
  %%  This is the rule for an external general parsed entity:
  %%  
  %%  [78]  extParsedEnt        ::=  TextDecl? content
  %%
  %%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%


  op parse_ExtSubset : UChars -> Required ExtSubset 

endspec
