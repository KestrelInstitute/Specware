LM qualifying spec

import /Languages/SpecCalculus/AbstractSyntax/Types

%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%
%% This spec describes a rather generic structure for mapping symbols from one
%% language into terms for another.  It coordinates with the parsing rules in 
%% lm-rules.lisp
%%
%% Terms created here could fail to be meaningful (e.g. '(0.A) (A.X.4 :: <=)'
%% so any code using them must verify appropriately in context.
%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%

op lowercase (s : String) : String = map toLowerCase s % why not in string library?

%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%
%% LanguageMorphism
%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%

type Parsed a = | Parsed a
                | Error  String

op parseLanguageMorphism (s : String) : Parsed LanguageMorphism % defined in lm-parser-interface.lisp

type LanguageMorphisms = List LanguageMorphism
type LanguageMorphism  = {source   : Language,
                          target   : Language,
                          sections : Sections}

op make_LanguageMorphism (source   : Language, 
                          target   : Language, 
                          sections : Sections)
 : LanguageMorphism =
 {source   = source,
  target   = target,
  sections = sections}

%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%
%% Language
%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%

type Language = 
  | MetaSlang 
  | Lisp
  | C
  | Java
  | Haskell
  | Isabelle
  | ACL2
  | XML
  | Unknown String
            
op make_Language (s : String) : Language =
 case lowercase s of
   | "metaslang" -> MetaSlang 
   | "lisp"      -> Lisp
   | "c"         -> C
   | "java"      -> Java
   | "haskell"   -> Haskell
   | "isabelle"  -> Isabelle
   | "acl2"      -> ACL2
   | "xml"       -> XML
   |  _ ->
      let _ = writeLine ("Unknown language in translation pragma: " ^ s) in
      Unknown s

%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%
%% Sections
%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%

%% Output for sections (other than Native) preserves the order in which those
%% sections are declared.
%%
%% E.g., we could emit verbatim text followed by imports followed by generated 
%% code then emit more verbatim text after that.
%%
%% TODO:  If multiple LanguageMorphism's are imported, how do we order them?

type Sections = List Section
type Section = | Verbatim  String
               | Imports   Imports
               | Morphism  Translations
               | Natives   Natives
               | Generated

%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%
%% Verbatim
%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%

op make_Verbatim_Section  (pre : String, body : String, post : String) 
 : Section = 
 Verbatim  body

%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%
%% Imports
%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%

op make_Imports_Section (imports : Imports)
 : Section = 
 Imports imports

type Imports = List Import
type Import  = {path     : DirectoryPath,
                filename : FileName}

op make_Import (path : DirectoryPath, filename : FileName) 
 : Import =
 {path     = path,
  filename = filename}

type DirectoryPath = List DirectoryName
type DirectoryName = FileId
type FileName      = {name      : FileId,
                      extension : FileId}

op make_FileName (name : String, extension : String) 
 : FileName =
 {name      = name, 
  extension = extension}

type FileId = String              %% in practice, no dots or slashes

%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%
%%% Morphism
%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%

op make_Morphism_Section (translations : Translations)
 : Section = 
 Morphism translations

type Translations = List Translation
type Translation  = | Type  TypeTranslation
                    | Field FieldTranslation
                    | Op    OpTranslation

%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%
%% Names
%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%

type Symbol  = String               %% in practice, no dots

type Name    = List Symbol

%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%
%% Terms (for both ops and types)
%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%

type Terms = List Term
type Term  = | Name  Name
             | List  Terms
             | Apply {x   : Term, y   : Term}
             | Typed {typ : Term, trm : Term}

op make_Name_Term  (name  : Name)             : Term = Name name
op make_List_Term  (terms : Terms)            : Term = List terms
op make_Apply_Term (x     : Term, y   : Term) : Term = Apply {x = x,     y = y}
op make_Typed_Term (typ   : Term, trm : Term) : Term = Typed {typ = typ, trm = trm}

%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%
%% TypeTranslation
%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%

type TypeTranslation = {source : Name, target : Term}

op make_Type_Translation (source : Name, target : Term)
 : Translation =
 Type {source = source, target = target}

%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%
%% FieldTranslation
%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%

type FieldId  = Symbol
type FieldRef = {type_name : Name, field_id : FieldId}

type FieldTranslation = {source : FieldRef, target : FieldRef}

op make_Field_Translation (source : FieldRef,
                           target : FieldRef)
 : Translation =
 Field {source = source,
        target = target}

op make_FieldRef (type_name : Name, 
                  field_id  : FieldId)
 : FieldRef =
 {type_name = type_name,
  field_id  = field_id}

%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%
%% OpTranslation
%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%

type OpTranslation = {source     : Name, 
                      target     : Term,
                      recurry    : Option ReCurry,
                      reversed?  : Bool,
                      fixity     : Option LM_Fixity,
                      precedence : Option Nat}

type LM_Fixity = | Left | Right | Infix

op make_LM_Fixity (s : String) : LM_Fixity =
   case lowercase s of
     | "right" -> Right 
     | "left"  -> Left 
     | "infix" -> Infix

op make_Op_Translation (source     : Name, 
                        target     : Term,
                        recurry    : Option ReCurry,
                        fixity     : Option LM_Fixity,
                        precedence : Option Nat,
                        reversed?  : Bool)
 : Translation =
 Op {source     = source,
     target     = target,
     recurry    = recurry,
     fixity     = fixity,
     precedence = precedence,
     reversed?  = reversed?}

op make_true () : Bool = true

%%% --------

type ReCurry = | Curry | UnCurry

op make_ReCurry (s : String) 
 : ReCurry =
 case lowercase s of
   | "curry"   -> Curry
   | "uncurry" -> UnCurry


%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%
%%% Natives
%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%

op make_Natives_Section (natives : Natives)
 : Section = 
 Natives natives

type Natives = List Native  
type Native  = | Type Name
               | Op   Name

op make_Type_Native (name : Name) : Native = Type name
op make_Op_Native   (name : Name) : Native = Op   name

%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%
%%% Generated
%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%

op make_Generated_Section ()                                           : Section = Generated

end-spec

