
XML qualifying spec

  import Parse_Names

  %%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%
  %%%          References                                                                          %%%
  %%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%
  %%
  %% [66]  CharRef      ::=  '&#' [0-9]+ ';' | '&#x' [0-9a-fA-F]+ ';' 
  %%
  %%                                                             [WFC: Legal Character]
  %%
  %% [67]  Reference    ::=  EntityRef | CharRef
  %%
  %% [68]  EntityRef    ::=  '&' Name ';' 
  %%
  %%                                                             [WFC: Entity Declared]
  %%                                                             [VC:  Entity Declared]
  %%                                                             [WFC: Parsed Entity] 
  %%                                                             [WFC: No Recursion]
  %%
  %% [69]  PEReference  ::=  '%' Name ';' 
  %%
  %%                                                             [VC:  Entity Declared]
  %%                                                             [WFC: No Recursion]
  %%                                                             [WFC: In DTD]
  %%
  %% ----------------------------------------------------------------------------------------------------

  op parse_Reference : UChars -> Possible Reference


endspec
