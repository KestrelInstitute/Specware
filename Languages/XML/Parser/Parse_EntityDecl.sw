XML qualifying spec

  import Parse_Character_Strings % parse_WhiteSpace

  %%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%
  %%%          Data_Type_Document -- EntityDecl                                                    %%%
  %%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%
  %%  [70]  EntityDecl     ::=  GEDecl | PEDecl
  %%
  %%  [71]  GEDecl         ::=  '<!ENTITY' S       Name S EntityDef S? '>'
  %%
  %%  [72]  PEDecl         ::=  '<!ENTITY' S '%' S Name S PEDef     S? '>'
  %%
  %%  [73]  EntityDef      ::=  EntityValue | (ExternalID NDataDecl?)
  %%
  %%  [74]  PEDef          ::=  EntityValue | ExternalID
  %%
  %% *[75]  ExternalID     ::=  'SYSTEM' S SystemLiteral | 'PUBLIC' S PubidLiteral S SystemLiteral 
  %%   ==>
  %% [K14] ExternalID      ::=  GenericID
  %%
  %%                                                             [KC: At Least SYSTEM]
  %%
  %%  [76]  NDataDecl      ::=  S 'NDATA' S Name 
  %%
  %%                                                             [VC: Notation Declared]
  %%
  %%  [82]  NotationDecl   ::=  '<!NOTATION' S Name S (ExternalID | PublicID) S? '>' 
  %%
  %%                                                             [VC: Unique Notation Name]
  %%
  %% *[83]  PublicID       ::=  'PUBLIC' S PubidLiteral 
  %%   ==>
  %% [K15] PublicID        ::=  GenericID
  %%
  %%                                                             [KC: Just PUBLIC]
  %%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%

  op parse_EntityDecl : UChars -> Required EntityDecl

  op parse_GEDecl : UChars -> Possible GEDecl

  op parse_EntityDef : UChars -> Required EntityDef

  op parse_NDataDecl : UChars -> Possible NDataDecl

  op parse_PEDecl : UChars -> Possible PEDecl

  op parse_PEDef : UChars -> Possible PEDef


endspec
