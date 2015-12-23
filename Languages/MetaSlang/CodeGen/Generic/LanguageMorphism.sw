(* Copyright 2015 Kestrel Institute. See file LICENSE for license details *)

LM qualifying spec

import /Languages/SpecCalculus/AbstractSyntax/Types
import /Languages/MetaSlang/Transformations/Pragma

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
                          spc      : Option Spec,
                          sections : Sections}

%% called from handwritten lisp code for parseLanguageMorphism (in lm-rules.lisp) :
op make_LanguageMorphism (source   : Language, 
                          target   : Language, 
                          sections : Sections)
 : LanguageMorphism =
 {source   = source,
  target   = target,
  spc      = None,
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
               | CVerbatim String         % verbatim to be printed at start of .c 
               | Imports   Imports
               | CImports  Imports        % imports  to be printed at start of .c 
               | Morphism  Translations
               | Natives   Natives
               | Generated

%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%
%% Verbatim
%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%

op make_Verbatim_Section  (pre : String, body : String, post : String) 
 : Section = 
 case pre of
   | "-cverbatim" -> CVerbatim body
   | "-hverbatim" -> Verbatim  body
   | _            -> Verbatim  body

type Verbatims = {pre  : List String,
                  post : List String}

op extractVerbatims (lms : LanguageMorphisms) : Verbatims =
 foldl (fn (verbatims, lm) ->
          let (verbatims, _) =
              foldl (fn ((verbatims, saw_generated?), section) ->
                       case section of
                         | Verbatim str -> let revised_verbatims = 
                                               if saw_generated? then
                                                 if str in? verbatims.post then
                                                   verbatims
                                                 else
                                                   verbatims << {post = verbatims.post ++ [str]}
                                               else
                                                 if str in? verbatims.pre then
                                                   verbatims
                                                 else
                                                   verbatims << {pre  = verbatims.pre  ++ [str]}
                                           in
                                           (revised_verbatims, saw_generated?)
                         | Generated    -> (verbatims, true)
                         | _            -> (verbatims, saw_generated?))
                    (verbatims, false)
                    lm.sections
          in
          verbatims)
       {pre  = [],
        post = []}
       lms


%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%
%% Imports
%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%

op make_Imports_Section (imports : Imports)
 : Section = 
 Imports imports

op make_CImports_Section (imports : Imports)
 : Section = 
 CImports imports

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

op extractHImports (lms : LanguageMorphisms) : Imports =
 %% -import => HImports
 extractImports lms

op extractCImports (lms : LanguageMorphisms) : Imports =
 %% -cimport => CImports
 foldl (fn (all_imports, lm) ->
          foldl (fn (all_imports, section) ->
                   case section of
                     | CImports imports -> all_imports ++ imports
                     | _ -> all_imports)
                all_imports
                lm.sections)
       []
       lms

op extractHVerbatims (lms : LanguageMorphisms) : Verbatims =
 %% -verbatim => HVerbatims
 extractVerbatims lms

op extractCVerbatims (lms : LanguageMorphisms) : Verbatims =
 %% TODO: allow for post c_verbatims?
 let c_verbatims =
     foldl (fn (c_verbatims, lm) ->
              foldl (fn (c_verbatims, section) ->
                       case section of
                         | CVerbatim verbatim -> c_verbatims ++ [verbatim]
                         | _ -> c_verbatims)
                    c_verbatims
                    lm.sections)
          []
          lms
 in
 {pre = c_verbatims, post = []}

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

op markNativeTranslations (translations : Translations,
                           natives      : Natives)
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
type Translation  = | Type   TypeTranslation
                    | Field  FieldTranslation
                    | Op     OpTranslation

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
                | Verbatim
                | HVerbatim
                | CVerbatim

op make_Pathname_Location (pathname : Pathname)
 : Location =
 Pathname pathname  

op make_Primitive_Location ()
 : Location =
 Primitive

op make_Verbatim_Location (kw)
 : Location =
 case kw of
   | "hverbatim" -> HVerbatim
   | "cverbatim" -> CVerbatim
   | _ -> Verbatim

op printLocation (location : Location) : String =
 case location of
   | Pathname pathname -> "in " ^ printPathname pathname
   | Primitive         -> "primitive"
   | Verbatim          -> "verbatim"
   | HVerbatim         -> "hverbatim"
   | CVerbatim         -> "cverbatim"

op printOptionalLocation (x : Option Location) : String =
 case x of
   | Some location -> " \t " ^ printLocation location
   | _ -> ""

%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%
%% TypeTranslation
%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%

type NameSpace = | Type | Structure | Enumeration | Union

type TypeTranslations = List TypeTranslation
type TypeTranslation  = {source    : Name, 
                         target    : Term,
                         location  : Option Location,
                         native?   : Bool,
                         namespace : NameSpace}

%% TODO: more general scheme for properties, instead of ad-hoc struct? field for C

op make_Type_Translation (source    : Name, 
                          target    : Term,
                          location  : Option Location,
                          namespace : Option String)
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
 let namespace =
     case namespace of
       | Some "struct" -> Structure
       | Some "enum"   -> Enumeration
       | Some "union"  -> Union
       | _ -> Type
 in
 Type {source    = source, 
       target    = target, 
       location  = location,
       native?   = native?,
       namespace = namespace}

op printTypeTranslation (trans : TypeTranslation) : String =
 "Translate type:  "     ^ 
 printName trans.source  ^ 
 " \t=> "                ^ 
 (case trans.namespace of | Structure -> "struct " | Enumeration -> "enum" | _ -> "") ^
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
                       native?    : Bool,
                       macro?     : Bool}

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
                        location   : Option Location,
                        kind       : String)
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
     native?    = native?,
     macro?     = (kind = "macro")}

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

type NativeTypeLocations = List NativeTypeLocation
type NativeTypeLocation  = {name      : Name,
                            location  : Option Location,
                            namespace : NameSpace}

type NativeOpLocations = List NativeOpLocation
type NativeOpLocation  = {name     : Name,
                          location : Option Location,
                          macro?   : Bool}

type Natives = List Native  
type Native  = | Type   NativeTypeLocation
               | Op     NativeOpLocation

op make_Type_Native (name     : Name,
                     location : Option Location)
 : Native = 
 Type {name      = name, 
       location  = location, 
       namespace = Type}

op make_Enum_Native (name     : Name,
                     location : Option Location)
 : Native = 
 Type {name      = name, 
       location  = location, 
       namespace = Enumeration}

op make_Struct_Native (name     : Name,
                       location : Option Location)
 : Native = 
 Type {name      = name, 
       location  = location, 
       namespace = Structure}

op make_Union_Native (name     : Name,
                      location : Option Location)
 : Native = 
 Type {name      = name, 
       location  = location, 
       namespace = Union}

op make_Op_Native (name     : Name, 
                   location : Option Location) 
 : Native = 
 Op {name     = name, 
     location = location, 
     macro?   = false}

op make_Macro_Native (name     : Name, 
                      location : Option Location) 
 : Native = 
 Op {name     = name, 
     location = location, 
     macro?  = true}

op printNative (lm_native : Native) : String =
 "Native " ^
 (case lm_native of
    | Type {name, location, namespace} -> 
      (case namespace of
         | Structure   -> "struct "
         | Enumeration -> "enum "
         | Type        -> "type ")
      ^ printName name ^ printOptionalLocation location

    | Op {name, location, macro?} -> 
      (if macro? then "macro " else "op") ^ printName name ^ printOptionalLocation location)

%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%
%%% Generated
%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%

op make_Generated_Section () : Section = Generated

%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%
%%% Post-Processing for easier use 
%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%

type LMData = {lms                   : LanguageMorphisms,
               op_translations       : OpTranslations,
               type_translations     : TypeTranslations,
               field_translations    : FieldTranslations,
               native_op_locations   : NativeOpLocations,   % explict via native and implicit via translate
               native_type_locations : NativeTypeLocations, % explict via native and implicit via translate
               native_ops            : OpNames,
               native_types          : TypeNames,
               op_macros             : OpNames,
               type_macros           : TypeNames,
               structure_types       : TypeNames,
               enumeration_types     : TypeNames,
               union_types           : TypeNames}

op nativeOp? (name : Name, lm_data : LMData) : Bool =
 let just_id = [last name] in
 exists? (fn native -> 
            native.name = name || 
            native.name = just_id) 
         lm_data.native_op_locations

op nativeType? (name : Name, lm_data : LMData) : Bool =
 let just_id = [last name] in
 exists? (fn native -> 
            native.name = name || 
            native.name = just_id) 
         lm_data.native_type_locations
            
op collectNativeOpLocations (natives      : Natives, 
                             translations : OpTranslations) 
 : NativeOpLocations =
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
 let native_ops = foldl (fn (nlocs, trans) ->
                           let name = trans.source in
                           if exists? (fn nloc -> name = nloc.name) nlocs then
                             nlocs
                           else
                             case trans.location of
                               | Some loc -> nlocs ++ [{name     = name, 
                                                        location = Some loc, 
                                                        macro?   = trans.macro?}]
                               | _ -> nlocs)
                        native_ops
                        translations
 in
 native_ops

op collectNativeTypeLocations (natives      : Natives, 
                               translations : TypeTranslations) 
 : NativeTypeLocations =
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
 let native_types = foldl (fn (nlocs, trans) ->
                             let name = trans.source in
                             if exists? (fn nloc -> name = nloc.name) nlocs then
                               nlocs
                             else
                               case trans.location of
                                 | Some loc -> nlocs ++ [{name      = name,
                                                          location  = Some loc, 
                                                          namespace = trans.namespace}]
                                 | _ -> nlocs)
                          native_types
                          translations
 in
 native_types

op make_LMData (lms : LanguageMorphisms) : LMData =
 let
   def nameToQid name =
     case name of
       | [id]   -> mkUnQualifiedId id
       | [q,id] -> mkQualifiedId (q, id)
       | _ -> fail ("illegal name in pragma: " ^ anyToString name)

   def QidForNativeType n_type =
     nameToQid n_type.name

   def QidForNativeOp n_op =
     nameToQid n_op.name
 in
 let translations       = extractTranslations lms in
 let natives            = extractNatives      lms in
 let translations       = markNativeTranslations (translations, natives) in % set native? flag

 %% partition translations:

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

 let native_op_locations   = collectNativeOpLocations   (natives, op_translations)   in
 let native_type_locations = collectNativeTypeLocations (natives, type_translations) in
 let native_ops            = map QidForNativeOp         native_op_locations          in
 let native_types          = map QidForNativeType       native_type_locations        in

 let op_macros       = foldl (fn (macro_names, otrans) ->
                                case otrans.target of
                                  % Target Term can be Name, Number, Apply, List, Vector, or Typed
                                  | Name _ -> macro_names
                                  | _ -> (nameToQid otrans.source) |> macro_names)
                             []
                             op_translations
 in
 let type_macros     = foldl (fn (macro_names, ttrans) ->
                                % Target Term can be Name, Number, Apply, List, Vector, or Typed
                                case ttrans.target of
                                  | Name _ -> macro_names
                                  | _ -> (nameToQid ttrans.source) |> macro_names)
                             []
                             type_translations
 in
 let native_structure_types = foldl (fn (struct_names, ntloc) ->
                                       case ntloc.namespace of
                                         | Structure ->
                                           let qid = case ntloc.name of
                                                       | [id]   -> mkUnQualifiedId id
                                                       | [q,id] -> mkQualifiedId (q, id)
                                           in
                                           struct_names ++ [qid]
                                         | _ ->
                                           struct_names)
                                   []
                                   native_type_locations
 in
 let structure_types = foldl (fn (struct_names, ttrans) ->
                                case ttrans.namespace of
                                  | Structure ->
                                    let qid = case ttrans.source of
                                                | [id]   -> mkUnQualifiedId id
                                                | [q,id] -> mkQualifiedId (q, id)
                                    in
                                    struct_names ++ [qid]
                                  | _ ->
                                    struct_names)
                              native_structure_types
                              type_translations
 in
 let native_enumeration_types = foldl (fn (struct_names, ntloc) ->
                                       case ntloc.namespace of
                                         | Enumeration ->
                                           let qid = case ntloc.name of
                                                       | [id]   -> mkUnQualifiedId id
                                                       | [q,id] -> mkQualifiedId (q, id)
                                           in
                                           struct_names ++ [qid]
                                         | _ ->
                                           struct_names)
                                   []
                                   native_type_locations
 in
 let enumeration_types = foldl (fn (struct_names, ttrans) ->
                                case ttrans.namespace of
                                  | Enumeration ->
                                    let qid = case ttrans.source of
                                                | [id]   -> mkUnQualifiedId id
                                                | [q,id] -> mkQualifiedId (q, id)
                                    in
                                    struct_names ++ [qid]
                                  | _ ->
                                    struct_names)
                              native_enumeration_types
                              type_translations
 in
 let native_union_types = foldl (fn (struct_names, ntloc) ->
                                       case ntloc.namespace of
                                         | Union ->
                                           let qid = case ntloc.name of
                                                       | [id]   -> mkUnQualifiedId id
                                                       | [q,id] -> mkQualifiedId (q, id)
                                           in
                                           struct_names ++ [qid]
                                         | _ ->
                                           struct_names)
                                   []
                                   native_type_locations
 in
 let union_types = foldl (fn (struct_names, ttrans) ->
                                case ttrans.namespace of
                                  | Union ->
                                    let qid = case ttrans.source of
                                                | [id]   -> mkUnQualifiedId id
                                                | [q,id] -> mkQualifiedId (q, id)
                                    in
                                    struct_names ++ [qid]
                                  | _ ->
                                    struct_names)
                              native_union_types
                              type_translations
 in

 {lms                   = lms,
  op_translations       = op_translations,
  type_translations     = type_translations,
  field_translations    = field_translations,
  native_op_locations   = native_op_locations,
  native_type_locations = native_type_locations,
  native_ops            = native_ops,
  native_types          = native_types,
  op_macros             = op_macros,
  type_macros           = type_macros,
  structure_types       = structure_types,
  enumeration_types     = enumeration_types,
  union_types           = union_types}


%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%

op parseTranslationPragmas (language : String) (s : Spec) : LanguageMorphisms =
 %% language will be "C", "Lisp", etc.
 foldlSpecElements (fn (lms, elt) ->
                      case elt of
                        | Pragma (p as ("#translate", body, "#end", _)) | isPragmaKind (body, language) ->
                          (case parseLanguageMorphism body of
                             | Parsed lm -> 
                               let lm = lm << {spc = Some s} in
                               lms ++ [lm]
                             | Error msg ->
                               let _ = writeLine("Error parsing " ^ language ^ " translation pragma: " ^ msg) in
                               lms
                             | result ->
                               let _ = writeLine "=======================================" in
                               let _ = writeLine "Unecognized result from parsing pragma:" in
                               let _ = writeLine body                                      in
                               let _ = writeLine " => "                                    in
                               let _ = writeLine (anyToString result)                      in
                               let _ = writeLine "=======================================" in
                               lms)
                        | _ ->
                          lms)
                   []
                   s.elements

end-spec

