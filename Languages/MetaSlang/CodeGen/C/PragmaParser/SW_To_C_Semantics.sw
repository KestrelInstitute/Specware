SW_TO_C qualifying spec

 import /Languages/SpecCalculus/AbstractSyntax/Types

 %%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%
 %% Pragma
 %%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%

 type Pragma = Sections

 %%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%
 %% Sections
 %%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%

 type Sections = List Section
 type Section = | Include     Inclusions
                | Verbatim    Verbatim
                | Translation Translations
                | Native      Natives

 op make_Inclusion_Section (inclusions : Inclusions) 
  : Section = 
  Include inclusions

 op make_Verbatim_Section (pre  : String,
                           body : String, 
                           post : String)
  : Section = 
  Verbatim body

 op make_Translation_Section (translations : Translations)
  : Section = 
  Translation translations

 op make_Native_Section (natives : Natives)
  : Section = 
  Native natives

 %%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%
 %% Inclusions
 %%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%

 type Inclusions = List Inclusion
 type Inclusion  = {path     : DirectoryPath,
                    filename : FileName}

 type DirectoryPath = List DirectoryName
 type DirectoryName = FileId
 type FileName      = {name      : FileId,
                       extension : FileId}

 type FileId = String %% might want to subtype to avoid "/" etc.

 op make_Inclusion (path     : DirectoryPath, 
                    filename : FileName)
  : Inclusion =
  {path     = path,
   filename = filename}

 op make_FileName (name      : String, 
                   extension : String) 
  : FileName =
  let _ = if extension in? ["c", "h"] then
             () 
          else
            writeLine("Unusual extension for included C file (expected c or h): " ^ extension)
  in
  {name      = name, 
   extension = extension}

 %%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%
 %% Verbatim 
 %%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%

 type Verbatim = String

 %%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%
 %%% Translations
 %%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%

 type Translations  = List Translation
 type Translation  = | TransType  TypeTranslation
                     | TransField FieldTranslation
                     | TransOp    OpTranslation

 %% ------------------------------------------------------------------------------
 %% Types
 %% ------------------------------------------------------------------------------

 type TypeTranslation = {sw : SW_TypeName,
                         c  : C_TypeName}

 type SW_TypeName = QualifiedId
 type C_TypeName  = String

 op make_Type_Translation (sw_name : SW_TypeName, 
                           c_name  : C_TypeName) 
  : Translation =
  TransType {sw = sw_name,
             c  = c_name}

 op make_C_TypeName (name : String) 
  : C_TypeName = 
  name

 %% ------------------------------------------------------------------------------
 %% Fields
 %% ------------------------------------------------------------------------------

 type FieldTranslation = {sw : SW_FieldRef,
                          c  : C_FieldRef}

 type SW_FieldRef = {type_name  : SW_TypeName,
                     field_name : SW_FieldName}

 type C_FieldRef = {type_name  : C_TypeName,
                    field_name : C_FieldName}

 type SW_FieldName = String
 type C_FieldName  = String

 op make_Field_Translation (sw_ref : SW_FieldRef,
                            c_ref  : C_FieldRef)
  : Translation =
  TransField {sw = sw_ref,
              c  = c_ref}

 op make_SW_FieldRef (type_name  : SW_TypeName, 
                      field_name : SW_FieldName)
  : SW_FieldRef =
  {type_name  = type_name,
   field_name = field_name}

 op make_C_FieldRef (type_name  : C_TypeName, 
                     field_name : C_FieldName) 
  : C_FieldRef =
  {type_name  = type_name,
   field_name = field_name}

 op make_SW_FieldName (name : String) 
  : SW_FieldName = 
  name

 op make_C_FieldName  (name : String) 
  : C_FieldName = 
  name

 %% ------------------------------------------------------------------------------
 %% Ops
 %% ------------------------------------------------------------------------------

 type OpTranslation = {sw : SW_OpName,
                       c  : C_OpName}

 type SW_OpName  = QualifiedId
 type C_OpName   = String

 op make_Op_Translation (sw_name : SW_OpName, 
                         c_name  : C_OpName) 
  : Translation =
  TransOp {sw = sw_name,
           c  = c_name}

 op make_C_OpName (name : String) 
  : C_OpName = 
  name

 %%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%
 %%% Natives
 %%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%

 type Natives = List Native  
 type Native  = | NativeType C_TypeName
                | NativeOp   C_OpName

 op make_Type_Native (name : C_TypeName) 
  : Native =
  NativeType name

 op make_Op_Native (name : C_OpName) 
  : Native =
  NativeOp name

end-spec

