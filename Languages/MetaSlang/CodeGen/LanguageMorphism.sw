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

type NativeLocations = List NativeLocation
type NativeLocation  = {name : Name, location : Option Location}

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

op extractVerbatims (lms : LanguageMorphisms) : List String =
 foldl (fn (all_strs, lm) ->
          foldl (fn (all_strs, section) ->
                   case section of
                     | Verbatim str -> all_strs ++ [str]
                     | _ -> all_strs)
                all_strs
                lm.sections)
       []
       lms

%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%
%% Imports
%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%

op make_Imports_Section (imports : Imports)
 : Section = 
 Imports imports

op extractImports (lms : LanguageMorphisms) : Imports =
 foldl (fn (all_imports, lm) ->
          foldl (fn (all_imports, section) ->
                   case section of
                     | Imports imports -> all_imports ++ imports
                     | _ -> all_imports)
                all_imports
                lm.sections)
       []
       lms

type Imports   = List Import
type Import    = Pathname

op printImport (lm_import : Import) : String =
 printPathname lm_import

type Pathname  = {directory : Option Directory,
                  name      : FileName,
                  extension : FileExtension}

type Directory = {root_slash? : Bool,
                  path        : DirectoryPath}

type DirectoryPath = List DirectoryId
type DirectoryId   = String              %% in practice, no dots or slashes
type FileName      = String              %% in practice, no dots or slashes
type FileExtension = String              %% in practice, no dots or slashes

op make_Directory (root_slash? : Bool, 
                   path        : DirectoryPath)
 : Directory =
 {root_slash? = root_slash?,
  path        = path}
                   
op printDirectory (dir : Directory) : String =
 foldl (fn (s, file_id) -> s ^ file_id ^ "/")
       (if dir.root_slash? then "/" else "")
       dir.path

op make_Pathname (directory : Option Directory, 
                  name      : FileName,
                  extension : FileExtension)
 : Pathname =
 {directory = directory,
  name      = name,
  extension = extension}

op printPathname (pathname : Pathname) : String =
 let dir_str  = case pathname.directory of
                  | Some dir -> printDirectory dir
                  | _ -> ""
 in
 let name_str = pathname.name      in
 let ext_str  = pathname.extension in
 dir_str ^ name_str ^ "." ^ ext_str

%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%
%%% Morphism
%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%

op make_Morphism_Section (translations : Translations)
 : Section = 
 Morphism translations

op extractTranslations (lms : LanguageMorphisms) 
 : Translations =
 foldl (fn (all_translations, lm) ->
          foldl (fn (all_translations, section) ->
                   case section of
                     | Morphism translations -> 
                       all_translations ++ translations
                     | _ -> 
                       all_translations)
                all_translations
                lm.sections)
       []
       lms

op markNativeTranslations (translations : Translations)
                          (natives      : Natives)
 : Translations =
 let native_type_names = foldl (fn (native_names, native : Native) ->
                                  case native of
                                    | Type x -> native_names ++ [x.name]
                                    | _ -> native_names)
                                []
                                natives
 in
 let native_op_names   = foldl (fn (native_names, native : Native) ->
                                  case native of
                                    | Op x -> native_names ++ [x.name]
                                    | _ -> native_names)
                                []
                                natives
 in
 map (fn translation ->
        case translation of
          | Type trans | trans.native? = false ->
            (case trans.target of
               | Name name -> 
                 % the target definition is among the types declared to be native
                 Type (trans << {native? = name in? native_type_names})
               | _ -> translation)
          | Op trans | trans.native? = false ->
            (case trans.target of
               | Name name -> 
                 % the target definition is among the ops declared to be native
                 Op (trans << {native? = name in? native_op_names})
               | _ -> translation)
          | _ ->
            translation)
     translations

type Translations = List Translation
type Translation  = | Type  TypeTranslation
                    | Field FieldTranslation
                    | Op    OpTranslation

op printTranslation (lm_translation : Translation) : String =
  case lm_translation of
    | Type  trans -> printTypeTranslation  trans
    | Field trans -> printFieldTranslation trans
    | Op    trans -> printOpTranslation    trans

%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%
%% Names
%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%

type Symbol = String               %% in practice, no dots

type Names  = List Name
type Name   = List Symbol

op printName (name : Name) : String =
 let hd :: tail = name in
 foldl (fn (str, sym) -> str ^ "," ^ sym)
       hd
       tail

%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%
%% Terms (for both ops and types)
%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%

type Terms = List Term
type Term  = | Name   Name
             | Number Nat
             | Apply  ApplyTerm
             | List   SeqTerm
             | Vector SeqTerm
             | Typed  TypedTerm 

type ApplyTerm = {x     : Term,  y         : Term}
type SeqTerm   = {terms : Terms, separator : String}
type TypedTerm = {typ   : Term,  trm       : Term,  prefix? : Bool}

op make_Name_Term           (name  : Name)             : Term = Name   name

op make_Number_Term         (n     : Nat)              : Term = Number n

op make_Apply_Term          (x     : Term, y   : Term) : Term = Apply  {x     = x,     y         = y}
op make_List_Term_Spaces    (terms : Terms)            : Term = List   {terms = terms, separator = " "}
op make_List_Term_Commas    (terms : Terms)            : Term = List   {terms = terms, separator = ","}

op make_Vector_Term         (terms : Terms)            : Term = Vector {terms = terms, separator = ","}

op make_Prefix_Typed_Term   (typ   : Term, trm : Term) : Term = Typed  {typ   = typ,   trm       = trm, prefix? = true}
op make_Postfix_Typed_Term  (typ   : Term, trm : Term) : Term = Typed  {typ   = typ,   trm       = trm, prefix? = false}


op printTerm (term : Term) : String =
 case term of 
   | Name   name  -> printName       name
   | Number n     -> show n
   | Apply  aterm -> printApplyTerm  aterm
   | List   sterm -> printListTerm   sterm
   | Vector sterm -> printVectorTerm sterm
   | Typed  tterm -> printTypedTerm  tterm

op printApplyTerm (aterm : ApplyTerm) : String =
  "(" ^ printTerm aterm.x ^ " " ^ printTerm aterm.y ^ ")"

op printListTerm (seq : SeqTerm) : String =
 case seq.terms of
   | [] -> "()"
   | hd :: tail ->
     "(" ^
     foldl (fn (str, tm) -> str ^ seq.separator ^ printTerm tm) 
           (printTerm hd)
           tail
     ^ ")"

op printVectorTerm (seq : SeqTerm) : String =
 case seq.terms of
   | [] -> "[]"
   | hd :: tail ->
     "[" ^
     foldl (fn (str, tm) -> str ^ seq.separator ^ printTerm tm) 
           (printTerm hd)
           tail
     ^ "]"

op printTypedTerm (tterm : TypedTerm) : String =
 if tterm.prefix? then
   "((" ^ printTerm tterm.typ ^ ") " ^ printTerm tterm.trm ^ ")"
 else
   printTerm tterm.trm ^ " :: " ^ printTerm tterm.typ

%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%
%% Location
%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%

type Location = | Pathname Pathname
                | Primitive

op make_Pathname_Location (pathname : Pathname)
 : Location =
 Pathname pathname  

op make_Primitive_Location ()
 : Location =
 Primitive

op printLocation (location : Location) : String =
 case location of
   | Pathname pathname -> "in " ^ printPathname pathname
   | Primitive         -> "primitive"

op printOptionalLocation (x : Option Location) : String =
 case x of
   | Some location -> " \t " ^ printLocation location
   | _ -> ""

%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%
%% TypeTranslation
%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%

type TypeTranslations = List TypeTranslation
type TypeTranslation  = {source   : Name, 
                         target   : Term,
                         location : Option Location,
                         native?  : Bool,
                         struct?  : Bool}  % if true, claims to be C structure

%% TODO: more general scheme for properties, instead of ad-hoc struct? field for C

op make_Type_Translation (source   : Name, 
                          target   : Term,
                          location : Option Location,
                          struct?  : Bool)
 : Translation =
 let native? = 
     case location of
       | Some _ -> true  % if it has a target location, it must be native
       | _ -> 
         % At this point, we don't know for sure if native or not.
         % See markNativeTranslations, which uses information from native 
         % section to possibly revise this to true.
         false
 in
 Type {source   = source, 
       target   = target, 
       location = location,
       native?  = native?,
       struct?  = struct?}

op printTypeTranslation (trans : TypeTranslation) : String =
 "Translate type:  "     ^ 
 printName trans.source  ^ 
 " \t=> "                ^ 
 (if trans.struct? then "struct " else "") ^
 printTerm trans.target  ^
 printOptionalLocation trans.location

%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%
%% FieldTranslation
%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%

type FieldId  = Symbol
type FieldRef = {type_name : Name, field_id : FieldId}

type FieldTranslations = List FieldTranslation
type FieldTranslation  = {source   : FieldRef, 
                          target   : FieldRef,
                          location : Option Location}

op make_Field_Translation (source   : FieldRef,
                           target   : FieldRef,
                           location : Option Location)
 : Translation =
 Field {source   = source,
        target   = target,
        location = location}

op make_FieldRef (type_name : Name, 
                  field_id  : FieldId)
 : FieldRef =
 {type_name = type_name,
  field_id  = field_id}

op printFieldRef (ref : FieldRef) : String =
 (printName ref.type_name) ^ "." ^ ref.field_id

op printFieldTranslation (trans : FieldTranslation) : String =
 "Translate field: "         ^ 
 printFieldRef trans.source  ^
 " \t=> "                    ^ 
 printFieldRef trans.target

%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%
%% OpTranslation
%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%

type OpTranslations = List OpTranslation
type OpTranslation  = {source     : Name, 
                       target     : Term,
                       recurry    : Option ReCurry,
                       reversed?  : Bool,
                       fixity     : Option LM_Fixity,
                       precedence : Option Nat,
                       location   : Option Location,
                       native?    : Bool}

type LM_Fixity = | Left | Right | Infix | Prefix | Postfix

op make_LM_Fixity (s : String) : LM_Fixity =
   case lowercase s of
     | "right"   -> Right 
     | "left"    -> Left 
     | "infix"   -> Infix
     | "prefix"  -> Prefix
     | "postfix" -> Postfix

op make_Op_Translation (source     : Name, 
                        target     : Term,
                        recurry    : Option ReCurry,
                        fixity     : Option LM_Fixity,
                        precedence : Option Nat,
                        reversed?  : Bool,
                        location   : Option Location)
 : Translation =
 let native? = 
     case location of
       | Some _ -> true  % if it has a target location, it must be native
       | _ -> 
         % At this point, we don't know for sure if native or not.
         % See markNativeTranslations, which uses information from native 
         % section to possibly revise this to true.
         false
 in
 Op {source     = source,
     target     = target,
     recurry    = recurry,
     fixity     = fixity,
     precedence = precedence,
     reversed?  = reversed?,
     location   = location,
     native?    = native?}

%%% --------

type ReCurry = | Curry | UnCurry

op make_ReCurry (s : String) 
 : ReCurry =
 case lowercase s of
   | "curry"   -> Curry
   | "uncurry" -> UnCurry

op printOpTranslation (trans : OpTranslation) : String =
 "Translate op:    "    ^ 
 printName trans.source ^ 
 " \t=> "               ^ 
 printTerm trans.target 
 ^
 (case trans.recurry of
    | Some recurry -> " recurry"
    | _ -> "")
 ^
 (case trans.fixity of
    | Some Left  -> " left"
    | Some Right -> " right"
    | Some Infix -> " infix"
    | _ -> "")
 ^
 (case trans.precedence of
    | Some n -> Nat.show n
    | _ -> "")
 ^
 (if trans.reversed? then " reversed" else "")
 ^
 printOptionalLocation trans.location

%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%
%%% Natives
%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%

op make_Natives_Section (natives : Natives)
 : Section = 
 Natives natives

op extractNatives (lms : LanguageMorphisms) : Natives =
 foldl (fn (all_natives, lm) ->
          foldl (fn (all_natives, section) ->
                   case section of
                     | Natives natives -> all_natives ++ natives
                     | _ -> all_natives)
                all_natives
                lm.sections)
       []
       lms

type Natives = List Native  
type Native  = | Type NativeLocation
               | Op   NativeLocation

op make_Type_Native (name     : Name,
                     location : Option Location)
 : Native = 
 Type {name = name, location = location}

op make_Op_Native   (name     : Name, 
                     location : Option Location) 
 : Native = 
 Op {name = name, location = location}

op printNative (lm_native : Native) : String =
 case lm_native of
   | Type {name, location} -> 
     "Native type " ^ printName name ^ printOptionalLocation location

   | Op   {name, location} -> 
     "Native op " ^ printName name ^ printOptionalLocation location

%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%
%%% Generated
%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%

op make_Generated_Section () : Section = Generated

%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%
%%% Post-Processing for easier use 
%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%

type LMData = {lms                : LanguageMorphisms,
               op_translations    : OpTranslations,
               type_translations  : TypeTranslations,
               field_translations : FieldTranslations,
               native_ops         : NativeLocations,   % both explicit and implicit
               native_types       : NativeLocations}   % both explicit and implicit

op nativeOp? (name : Name, lm_data : LMData) : Bool =
 let just_id = [last name] in
 exists? (fn native -> 
            native.name = name || 
            native.name = just_id) 
         lm_data.native_ops

op nativeType? (name : Name, lm_data : LMData) : Bool =
 let just_id = [last name] in
 exists? (fn native -> 
            native.name = name || 
            native.name = just_id) 
         lm_data.native_types
            
op collectNativeOps (natives      : Natives, 
                     translations : OpTranslations) 
 : NativeLocations =
 %% explicitly native ops --
 %%   those in "native" section
 let native_ops = foldl (fn (nlocs, native : Native) ->
                           case native of
                             | Op nloc -> nlocs ++ [nloc]
                             | _ -> nlocs)
                        []
                        natives
 in
 %% plus all implicitly native ops -- 
 %%  those translated to a target op defined at some target location
 %%  (excluding ad hoc macros, for example)
 let native_ops = foldl (fn (nlocs : NativeLocations, trans : OpTranslation) ->
                           let name = trans.source in
                           if exists? (fn nloc -> name = nloc.name) nlocs then
                             nlocs
                           else
                             case trans.location of
                               | Some loc -> nlocs ++ [{name = name, location = Some loc}]
                               | _ -> nlocs)
                        native_ops
                        translations
 in
 native_ops

op collectNativeTypes (natives      : Natives, 
                       translations : TypeTranslations) 
 : NativeLocations =
 %% explicitly native types -- 
 %%   those in "native" section
 let native_types = foldl (fn (nlocs, native : Native) ->
                             case native of
                               | Type nloc -> nlocs ++ [nloc]
                               | _ -> nlocs)
                          []
                          natives
 in
 %% plus all implicitly native types -- 
 %%  those translated to a target type defined at some target location
 %%  (excluding ad hoc macros, for example)
 let native_types = foldl (fn (nlocs : NativeLocations, trans : TypeTranslation) ->
                             let name = trans.source in
                             if exists? (fn nloc -> name = nloc.name) nlocs then
                               nlocs
                             else
                               case trans.location of
                                 | Some loc -> nlocs ++ [{name = name, location = Some loc}]
                                 | _ -> nlocs)
                          native_types
                          translations
 in
 native_types

op make_LMData (lms : LanguageMorphisms) : LMData =
 let translations       = extractTranslations lms in
 let natives            = extractNatives      lms in
 let op_translations    = foldl (fn (otranslations, trans) ->
                                   case trans of
                                     | Op otrans -> otranslations ++ [otrans]
                                     | _ -> otranslations)
                                []
                                translations
 in
 let type_translations  = foldl (fn (ttranslations, trans) ->
                                   case trans of
                                     | Type ttrans -> ttranslations ++ [ttrans]
                                     | _ -> ttranslations)
                                []
                                translations
 in
 let field_translations = foldl (fn (ftranslations, trans) ->
                                   case trans of
                                     | Field ftrans -> ftranslations ++ [ftrans]
                                     | _ -> ftranslations)
                                []
                                translations
 in
 let native_ops         = collectNativeOps   (natives, op_translations)   in
 let native_types       = collectNativeTypes (natives, type_translations) in

 {lms                = lms,
  op_translations    = op_translations,
  type_translations  = type_translations,
  field_translations = field_translations,
  native_ops         = native_ops,
  native_types       = native_types}

end-spec

