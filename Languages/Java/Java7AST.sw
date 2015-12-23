(* Copyright 2015 Kestrel Institute. See file LICENSE for license details *)

(*
 *  This specification defines an abstract syntax for Java programs, based on
 *  "The Java Language Specification, Java SE 7 Edition", by James Gosling,
 *  Bill Joy, Guy Steele, Gilad Bracha, Alex Buckley, Feb 28, 2013,
 *  as found at http://docs.oracle.com/javase/specs/jls/se7/html/index.html
 *
 *  Throughout, we refer to this document as [JavaSpec], and sections 
 *  within it simply as [4.2], [10.3], etc.
 *
 *  IMPORTANT:  The goal of this specification is to facilitate parsing and 
 *  printing of Java programs, and to present a clean target for compilation
 *  from specware specifications into Java code.  
 *
 *  In particular, given a program expressed using this spec, it should be 
 *  absolulely trivial to print legal Java code that a compliant Java compiler 
 *  will accept and process.  In that regard, this spec hews as closely as 
 *  possible to the published standard, even when (or especially when) choices 
 *  made there seem arbitrary or less than ideal and could be "fixed".
 *
 *  This spec differs in many details from one designed to facilitate
 *  compilation, static analysis, symbolic execution, etc.  For example,
 *  attention is paid to preserving notions such as parsing precedence, 
 *  which would be irrelevant to execution semantics.  No attempt is made
 *  to optimize anything for execution or even for symbolically analyzing 
 *  the programs that are represented.
 *
 *  It's also worth noting that a small number of deficiencies and 
 *  inconsistencies still exist in the published standard, but in those 
 *  cases the obvious intent can be deduced with a bit of patience.
 *  These observations are noted in comments.
 *
 *  The presentation follows that of [JavaSpec], section by section,
 *  although productions of the form 'type FooList = List Foo' are typically
 *  moved to be adjacent to the declaration for 'type Foo'.
 *
 *  NOTE: We do not (yet) attempt to handle comments.  Parsing into this 
 *  structure will simply skip them, and there is no way to include comments 
 *  in a structure to be printed.
 *
 *  NOTE: We do not (yet) attempt to handle underscores in numerals.  
 *  Parsing into this structure will simply skip them, and there is no 
 *  way to include underscores in a number to be printed.
 *
 *  NOTE: Where the spec has a production with an optional Foo, and Foo is 
 *  in turn defined as a non-empty sequence, we may use a non-optional Foo 
 *  defined as a potentially empty sequence.  This should not cause any 
 *  problems, and often makes the spec a bit easier to read.
 *)

Java qualifying spec

%%% ========================================================================
%%%  Ad hoc interface to 
%%% ========================================================================

type ClassName  = Identifier   %% NOTE: ClassName is used but undefined in the spec

%%% ========================================================================
%%%  Unicode
%%% ========================================================================

%%% TODO:  Change to import a Unicode spec
%%% Reference: http://www.unicode.org/

type UnicodeString  %% TODO: Define this. 
type UnicodeChar    %% TODO: Define this. 
op Unicode.explode (s : UnicodeString) : List UnicodeChar

type UnicodeInputCharacter

%% TODO: UTF16 is merely an external printed format, but maybe it makes 
%%       sense to internalize it here, thus minimizing internal/external 
%%       differences.  Or the parser and printer could convert back and 
%%       forth between UTF16 and a simpler internal form here.

%%% ========================================================================
%%%  3.4 Line Terminators
%%% ========================================================================

type InputCharacter = UnicodeInputCharacter %% TODO: not CR or LF

%%% ========================================================================
%%%  3.8 Identifiers
%%% ========================================================================

op JavaLetter?        (c : UnicodeChar)   : Bool % TODO
op JavaLetterOrDigit? (c : UnicodeChar)   : Bool % TODO
op booleanLiteral?    (s : UnicodeString) : Bool % TODO
op nullLiteral?       (s : UnicodeString) : Bool % TODO

op JavaIdentifierChars? (s : UnicodeString) : Bool = 
 case explode s of
   | [] -> false
   | char :: tail -> (JavaLetter? char) && (forall? JavaLetterOrDigit? tail) 

op JavaIdentifier?    (s : UnicodeString) : Bool = 
  (JavaIdentifierChars? s) &&
  ~ (keyword?           s) &&
  ~ (booleanLiteral?    s) &&
  ~ (nullLiteral?       s)


type Identifier        = UnicodeString | JavaIdentifier?
type IdentifierChars   = UnicodeString | JavaIdentifierChars?
type JavaLetter        = UnicodeChar   | JavaLetter?
type JavaLetterOrDigit = UnicodeChar   | JavaLetterOrDigit?

%%% ========================================================================
%%%  3.9 Keywords
%%% ========================================================================

op keyword? (s : UnicodeString) : Bool % TODO
%% [3.9] lists 50 of these

%%% ========================================================================
%%%  3.10 -- Literals
%%% ========================================================================

type Literal = | Integer IntegerLiteral
               | Float   FloatingPointLiteral
               | Boolean BooleanLiteral
               | Char    CharacterLiteral
               | String  StringLiteral
               | Null

%%% ========================================================================
%%%  3.10.1 -- Integer Literals
%%% ========================================================================

type IntegerLiteral = | Decimal DecimalIntegerLiteral
                      | Hex     HexIntegerLiteral
                      | Octal   OctalIntegerLiteral
                      | Binary  BinaryIntegerLiteral

%% TODO: We currently let the parser & printer deal with precise formatting
%%       of literals, but that prevents us from specifying underscores in 
%%       numerals. 

type DecimalIntegerLiteral = {n : Nat, suffix : Option IntegerSuffix}
type HexIntegerLiteral     = {n : Nat, suffix : Option IntegerSuffix}
type OctalIntegerLiteral   = {n : Nat, suffix : Option IntegerSuffix}
type BinaryIntegerLiteral  = {n : Nat, suffix : Option IntegerSuffix}

type IntegerSuffix = | Lowercase_L | Capital_L  

%%% ========================================================================
%%%  3.10.2 -- Floating-Point Literals
%%% ========================================================================

type FloatingPointLiteral = | Decimal DecimalFloatingPointLiteral
                            | Hex     HexFloatingPointLiteral

type DecimalFloatingPointLiteral %% TODO
type HexFloatingPointLiteral     %% TODO

%%% ========================================================================
%%%  3.10.3 -- Boolean Literals
%%% ========================================================================

type BooleanLiteral = Bool  % printed as "true" or "false"

%%% ========================================================================
%%%  3.10.4 -- Character Literals
%%% ========================================================================

type CharacterLiteral = | Single  SingleCharacter
                        | Escaped EscapeSequence

type SingleCharacter = InputCharacter %% TODO: but not ' or \

%%% ========================================================================
%%%  3.10.5 -- String Literals
%%% ========================================================================

%% TODO: The following is a clumsy way to represent strings, but do we care?
%%       We could avoid escape sequences, letting parser/printer deal with it.

type StringLiteral   = List StringCharacter
type StringCharacter = | Normal InputCharacter % TODO: but not doublequote or \
                       | Escape EscapeSequence

%%% ========================================================================
%%%  3.10.6 -- Escape Sequences for Character & String Literals
%%% ========================================================================

type EscapeSequence = | Backspace   
                      | Tab         
                      | Linefeed    
                      | Formfeed    
                      | DoubleQuote 
                      | SingleQuote 
                      | Backslash
                      | Octal       OctalByte  %% 0 <= n <= 0xFF

type OctalByte = {n : Nat | n <= 0xFF}

%%% ========================================================================
%%%  4.1 -- The Kinds of Types & Values
%%% ========================================================================

type Type = | Primitive PrimitiveType
            | Reference ReferenceType

%%% ========================================================================
%%%  4.2 -- Primitive Types & Values
%%% ========================================================================

%%% For simplicity and clarity, we expand the options here to a flat coproduct

type PrimitiveType = | Byte
                     | Short
                     | Int
                     | Long
                     | Char
                     | Float
                     | Double
                     | Boolean

%%% To keep everyone honest, we also define the subytypes used in [Java],
%%% thus letting the typechecker constrain legal uses of a primitive value.

op integral? (t : PrimitiveType) : Bool = t in? [Byte, Short, Int, Long, Char]
op floating? (t : PrimitiveType) : Bool = t in? [Float, Double]
op numeric?  (t : PrimitiveType) : Bool = integral? t || floating? t

type NumericType       = PrimitiveType | numeric?
type IntegegralType    = NumericType   | integral?
type FloatingPointType = NumericType   | floating?

%%% ========================================================================
%%%  4.3 -- Reference Types / Values
%%% ========================================================================

op class? (t : ReferenceType) : Bool = 
 case t of 
   | Class     _ -> true
   | _ -> false

op interface? (t : ReferenceType) : Bool = 
 case t of 
   | Class     _ -> true
   | _ -> false

op typeVariable? (t : ReferenceType) : Bool = 
 case t of 
   | TypeVariable   _ -> true
   | _ -> false

op array? (t : ReferenceType) : Bool = 
 case t of 
   | Array  _ -> true
   | _ -> false

op classOrInterface? (t : ReferenceType) : Bool = 
  class? t || interface? t

op reference? (t : TypeArgument) : Bool = % TypeArgument is defined in [4.5.1]
 case t of
   | Unresolved   _ -> true
   | Class        _ -> true
   | Interface    _ -> true
   | TypeVariable _ -> true
   | Array        _ -> true
   | _ -> false

type ReferenceType        = TypeArgument         | reference?
type ClassOrInterfaceType = ReferenceType        | classOrInterface?
type ClassType            = ClassOrInterfaceType | class?
type InterfaceType        = ClassOrInterfaceType | interface?
type TypeVariable         = ReferenceType        | typeVariable?
type ArrayType            = ReferenceType        | array?

%%% type ReferenceType = | Unresolved   UnresolvedTypeFields
%%%                      | Class        ClassTypeFields
%%%                      | Interface    InterfaceTypeFields
%%%                      | TypeVariable TypeVariableFields
%%%                      | Array        ArrayTypeFields

type UnresolvedTypeFields = {name : TypeNameNoPackage,
                             args : Option TypeArguments}

type ClassTypeFields      = {name : TypeDeclSpecifier,
                             args : Option TypeArguments}

type InterfaceTypeFields  = {name : TypeDeclSpecifier,
                             args : Option TypeArguments}

%%% Note: [4.3] and [6.5.1] both define TypeName (sigh)
%%% We assume that TypeDeclSpecifier uses just the local definition here,
%%% which is more restrictive than the version in [6.5.1]

type TypeDeclSpecifier    = | Direct     TypeNameNoPackage
                            | WithParent TypeDeclWithParent

type TypeDeclWithParent   = {parent : ClassOrInterfaceType,
                             name   : Identifier}

type TypeVariableFields   = Identifier

type ArrayTypeFields      = {base : Type}


op noPackage? (tn : TypeName) : Bool % TODO 

type TypeNameNoPackage = TypeName | noPackage?

%%% ========================================================================
%%%  4.4 -- Type Variables
%%% ========================================================================

type TypeParameter  = {name  : TypeVariable,
                       bound : TypeBound}

type TypeBound = | TypeVariable     TypeVariable
                 | ClassOrInterface BoundedClassOrInterfaceType

type BoundedClassOrInterfaceType = {jtype  : ClassOrInterfaceType,
                                    bounds : Option AdditionalBoundList}

type AdditionalBoundList = List AdditionalBound
type AdditionalBound = InterfaceType

%%% ========================================================================
%%%  4.5.1 -- Type Arguments & WildCards
%%% ========================================================================

type TypeArguments = List TypeArgument
type TypeArgument  = | Unresolved   UnresolvedTypeFields  % [4.1]
                     | Class        ClassTypeFields       % [4.1]
                     | Interface    InterfaceTypeFields   % [4.1]
                     | TypeVariable TypeVariableFields    % [4.1]
                     | Array        ArrayTypeFields       % [4.1]
                     | WildCard     Option WildCardBounds

op wildcard? (t : TypeArgument) : Bool = 
 case t of
   | WildCard _ -> true
   | _ -> false

type WildCard = TypeArgument | wildcard?

type WildCardBounds = | Extends ReferenceType
                      | Super   ReferenceType

%%% ========================================================================
%%%  6.5 -- Determining the Meaning of a Name
%%% ========================================================================

%%% Note: Many of these types are resolved by context, so we use the
%%%       'kind' field of AmbiguousName to record whatever has been 
%%%       learned by processing.  When creating internal structures,
%%%       setting that flag restricts usage to specific contexts.
%%%       The downside is that this could make it very hard to statically 
%%%       verify type-checking conditions. 

op expressionName?    (name : AmbiguousName) : Bool = (name.kind = Expression)
op packageOrTypeName? (name : AmbiguousName) : Bool = (name.kind = Package ||
                                                       name.kind = Type)

op packageName?       (name : PackageOrTypeName) : Bool = (name.kind = Package)
op typeName?          (name : PackageOrTypeName) : Bool = (name.kind = Type)

type TypeName          = PackageOrTypeName | typeName?
type PackageName       = PackageOrTypeName | packageName?
type PackageOrTypeName = AmbiguousName     | packageOrTypeName?
type ExpressionName    = AmbiguousName     | expressionName?   % e.g. fields of vars

%%% Method names are always clear from context.
type MethodName        = {prefix : Option AmbiguousName, 
                          name   : Identifier}

type AmbiguousName     = {prefix : Option AmbiguousName,
                          name   : Identifier,
                          kind   : Disambiguation}

type Disambiguation = | Package | Type | Expression | Method 

%%% ========================================================================
%%%  7.3 -- Compilation Units
%%% ========================================================================

type CompilationUnit = {package : Option PackageDeclaration,
                        imports : Option ImportDeclarations,
                        types   : Option TypeDeclarations}

%%% ========================================================================
%%%  7.4 -- Package Declarations
%%% ========================================================================

type PackageDeclaration = {annotations : Option Annotations,
                           name        : PackageName}

%%% ========================================================================
%%%  7.5 -- Import Declarations
%%% ========================================================================

type ImportDeclarations = List ImportDeclaration 
type ImportDeclaration  = | SingleType     SingleTypeImportDeclaration
                          | TypeOnDemand   TypeImportOnDemandDeclaration
                          | SingleStatic   SingleStaticImportDeclaration
                          | StaticOnDemand StaticImportOnDemandDeclaration

type SingleTypeImportDeclaration     = {type_name : TypeName}
type TypeImportOnDemandDeclaration   = {type_name : PackageOrTypeName}
type SingleStaticImportDeclaration   = {type_name : TypeName, id : Identifier}
type StaticImportOnDemandDeclaration = {type_name : TypeName}

%%% ========================================================================
%%%  7.6 -- Top Level Type Declarations
%%% ========================================================================

type TypeDeclarations = List TypeDeclaration
type TypeDeclaration  = % ClassDeclaration:
                        | Class      NormalClassDeclaration      % [8.1]
                        | Enum       EnumDeclaration             % [8.9]
                        % InterfaceDeclaration:
                        | Interface  NormalInterfaceDeclaration  % [9.1]
                        | Annotation AnnotationTypeDeclaration   % [9.6]
                        %
                        | Vacuous

%%% ------------------------------------------------------------------------
%%% Note:
%%%
%%% [JavaSpec] includes ClassDeclaration and InterfaceDeclaration as 
%%%  subtypes of many different types (e..g. BlockStatement), which makes 
%%%  it messy to model them with specware subtypes.
%%%
%%% We finesse that by interpolating a pair of coproduct  options into the 
%%%  definition of any type that [JavaSpec] indicates is a super type of 
%%%  ClassDeclaration:
%%%
%%%    % ClassDeclaration:
%%%    | Class      NormalClassDeclaration     % [8.1]
%%%    | Enum       EnumDeclaration            % [8.9]
%%%
%%%  and for InterfaceDeclaration:
%%% 
%%%    % InterfaceDeclaration:
%%%    | Interface  NormalInterfaceDeclaration % [9.1]
%%%    | Annotation AnnotationTypeDeclaration  % [9.6]
%%% 
%%% ------------------------------------------------------------------------

%%% ========================================================================
%%%  8.1 -- Class Declaration
%%% ========================================================================

%%% See note in 7.6
type ClassDeclaration = | Class NormalClassDeclaration  
                        | Enum  EnumDeclaration         % [8.9]

type NormalClassDeclaration = {modifiers       : Option ClassModifiers,
                               name            : Identifier,
                               type_parameters : Option TypeParameters,
                               super           : Option Super,
                               interfaces      : Option Interfaces,
                               body            : ClassBody}

%%% ========================================================================
%%%  8.1.1 -- Class Modifiers
%%% ========================================================================

type ClassModifiers = List ClassModifier
type ClassModifier  = | Annotation Annotation
                      | Public
                      | Protected
                      | Private
                      | Abstract
                      | Static
                      | Final
                      | Strictfp

%%% ========================================================================
%%%  8.1.2 -- Generic Classes & Type Parameters
%%% ========================================================================

type TypeParameters = List TypeParameter

%%% ========================================================================
%%%  8.1.4 -- Superclasses & Subclasses
%%% ========================================================================

type Super = ClassType 

%%% ========================================================================
%%%  8.1.5 -- Superinterfaces
%%% ========================================================================

type Interfaces = InterfaceTypeList  

type InterfaceTypeList  = List InterfaceType

%%% ========================================================================
%%%  8.1.6 -- Class Body and Member Declarations
%%% ========================================================================

type ClassBody = ClassBodyDeclarations
type ClassBodyDeclarations = List ClassBodyDeclaration

type ClassBodyDeclaration  = | Field               FieldDeclaration
                             | Method              MethodDeclaration
                             % ClassDeclaration:
                             | Class               NormalClassDeclaration     % [8.1]
                             | Enum                EnumDeclaration            % [8.9]
                             % InterfaceDeclaration:
                             | Interface           NormalInterfaceDeclaration % [9.1]
                             | Annotation          AnnotationTypeDeclaration  % [9.6]
                             %
                             | InstanceInitializer InstanceInitializer
                             | StaticInitializer   StaticInitializer
                             | Constructor         ConstructorDeclaration
                             | Vacuous

op classDeclaration? (d : ClassBodyDeclaration) : Bool = 
  case d of
    | Class      _ -> true
    | Enum       _ -> true
    | _ -> false

op interfaceDeclaration? (d : ClassBodyDeclaration) : Bool = 
  case d of
    | Interface  _ -> true
    | Annotation _ -> true
    | _ -> false

op classMemberDeclaration? (d : ClassBodyDeclaration) : Bool = 
  case d of
    | Field      _ -> true
    | Method     _ -> true
    % classDeclaration?
    | Class      _ -> true
    | Enum       _ -> true
    % interfaceDeclaration?
    | Interface  _ -> true
    %
    | Annotation _ -> true
    | _ -> false

op instanceInitializer? (d : ClassBodyDeclaration) : Bool = 
  case d of 
    | InstanceInitializer_ -> true 
    | _ -> false

op staticInitializer? (d : ClassBodyDeclaration) : Bool = 
  case d of 
    | StaticInitializer _ -> true
    | _ -> false

op constructorDeclaration? (d : ClassBodyDeclaration) : Bool = 
  case d of 
    | Constructor _ -> true
    | _ -> false

%% The following two types would need to be subtypes of several disjoint types.
%% To avoid any confusion, we avoid defining them and instead expand their
%%  meaning at all references: see note in 7.6
%%
%% type ClassDeclaration     = ClassBodyDeclaration | classDeclaration?
%% type InterfaceDeclaration = ClassBodyDeclaration | interfaceDeclaration?

%% type ClassMemberDeclaration = ClassBodyDeclaration | classMemberDeclaration?
%% type InstanceInitializer    = ClassBodyDeclaration | instanceInitializer?
%% type StaticInitializer      = ClassBodyDeclaration | staticInitializer?
%% type ConstructorDeclaration = ClassBodyDeclaration | constructorDeclaration?

%%% ========================================================================
%%%  8.3 -- Field Declarations
%%% ========================================================================

type FieldDeclaration = {modifiers : Option FieldModifiers,
                         jtype     : Type,
                         variables : VariableDeclarators}

type VariableDeclarators = List VariableDeclarator
type VariableDeclarator  = {variable    : VariableDeclaratorId,
                            dimensions  : Dims,  
                            initializer : VariableInitializer}

type VariableDeclaratorId = {id   : Identifier,
                             dims : Dims}  % depth of nesting


type Dims = Nat  % depth of nesting, arrays of arrays: ((X []) []) [] 

type VariableInitializer = | Expr      Expression
                           | ArrayInit ArrayInitializer

%%% ========================================================================
%%%  8.3.1 -- Field Modifiers
%%% ========================================================================

type FieldModifiers = List FieldModifier
type FieldModifier = | Annotation Annotation
                     | Public
                     | Protected
                     | Private
                     | Static
                     | Final
                     | Transient
                     | Volatile

%%% ========================================================================
%%%  8.4 -- Method Declarations
%%% ========================================================================

type MethodDeclaration = {header : MethodHeader,
                          body   : MethodBody}

type MethodHeader = {modifiers  : Option MethodModifiers,
                     parameters : Option TypeParameters,
                     result     : Result,
                     body       : MethodDeclarator,
                     throws     : Option Throws}

type MethodDeclarator = {name       : Identifier,
                         parameters : Option FormalParameterList,
                         dimensions : Dims} % deprecated
                         
%%% ========================================================================
%%%  8.4.1 -- Formal Parameters
%%% ========================================================================

%%% [8.4.1] distinguishes the last parameter, but only to allow it to have
%%% elipses

type FormalParameterList = List FormalParameter 

type FormalParameter = {modifiers : Option VariableModifiers,
                        jtype     : Type,
                        elipses?  : Bool,  % meaningful only for last parameter
                        variable  : VariableDeclaratorId}

type VariableModifiers = List VariableModifier
type VariableModifier  = | Annotation Annotation
                         | Final

%%% ========================================================================
%%%  8.4.3 -- Method Modifiers
%%% ========================================================================

type MethodModifiers = List MethodModifier
type MethodModifier  = | Annotation  Annotation
                       | Public
                       | Protected
                       | Private
                       | Abstract
                       | Static
                       | Final
                       | Synchronized
                       | Native
                       | Strictfp

%%% ========================================================================
%%%  8.4.5 -- Method Return Type
%%% ========================================================================

type Result = | Type Type
              | Void


%%% ========================================================================
%%%  8.4.6 -- Method Throws
%%% ========================================================================

type Throws = ExceptionTypeList
type ExceptionTypeList = List ExceptionType
type ExceptionType = | TypeName     TypeName
                     | TypeVariable TypeVariable

%%% ========================================================================
%%%  8.4.7 -- Method Throws
%%% ========================================================================

type MethodBody = | Block Block
                  | Vacuous

%%% ========================================================================
%%%  8.6 -- Instance Initializers
%%% ========================================================================

type InstanceInitializer = Block

%%% ========================================================================
%%%  8.7 -- Static Initializers
%%% ========================================================================

type StaticInitializer = Block

%%% ========================================================================
%%%  8.8 -- Constructor Declarations
%%% ========================================================================

type ConstructorDeclaration = {modifers   : Option ConstructorModifiers,
                               declarator : ConstructorDeclarator,
                               throws     : Option Throws,
                               body       : ConstructorBody}

type ConstructorDeclarator = {type_parameters   : Option TypeParameters,
                              name              : SimpleTypeName,
                              formal_parameters : Option FormalParameterList}

%%% SimpleTypeName is used but not defined in the main [JavaSpec] discussion.
%%% However, the BNF parser they provide in chapter 18 seems to resolve it.

type SimpleTypeName = Identifier  % See BNF rules for ConstructorDeclarator 

%%% ========================================================================
%%%  8.8.3 -- Constructor Modifiers
%%% ========================================================================

type ConstructorModifiers = List ConstructorModifier
type ConstructorModifier  = | Annotation Annotation
                            | Public
                            | Protected
                            | Private

%%% ========================================================================
%%%  8.8.7 -- Constructor Body
%%% ========================================================================

type ConstructorBody = {invocation : Option ExplicitConstructorInvocation,
                        statements : Option BlockStatements}

type ExplicitConstructorInvocation = | This  ExplicitConstructorInvocation_This
                                     | Super ExplicitConstructorInvocation_Super

type ExplicitConstructorInvocation_This  = {nw_targs : NonWildTypeArguments,
                                            args     : Option ArgumentList}

type ExplicitConstructorInvocation_Super = {context  : Primary, 
                                            nw_targs : Option NonWildTypeArguments,
                                            args     : Option ArgumentList}

type NonWildTypeArguments = ReferenceTypeList
type ReferenceTypeList    = List ReferenceType

%%% ========================================================================
%%%  8.9 -- Enums
%%% ========================================================================

%%% See note in 7.6 about ClassDeclaration

type EnumDeclaration = {modifiers : Option ClassModifiers,
                        name      : Identifier,
                        interface : Option Interfaces,
                        body      : EnumBody}

type EnumBody = {constants              : Option EnumConstants,
                 comma_after_constants? : Bool,  
                 decls                  : Option EnumBodyDeclarations}

%%% ========================================================================
%%%  8.9.1 -- Enum Constants
%%% ========================================================================

type EnumConstants = List EnumConstant
type EnumConstant  = {annotations : Option Annotations,
                      name        : Identifier,
                      arguments   : Option Arguments,
                      body        : Option ClassBody}

type EnumBodyDeclarations = Option ClassBodyDeclarations

%%% ========================================================================
%%%  9.1 -- Interface Declarations
%%% ========================================================================

%%% See note in 7.6

type InterfaceDeclaration = | Interface  NormalInterfaceDeclaration       
                            | Annotation AnnotationTypeDeclaration   % [9.6]

type NormalInterfaceDeclaration = {modifiers       : Option InterfaceModifiers,
                                   name            : Identifier,
                                   type_paramaters : Option TypeParameters,
                                   extends         : Option ExtendsInterfaces,
                                   body            : InterfaceBody}

%%% ========================================================================
%%%  9.1 -- Interface Modifiers
%%% ========================================================================

type InterfaceModifiers = List InterfaceModifier
type InterfaceModifier  = | Annotation Annotation
                          | Public
                          | Protected
                          | Private
                          | Abstract
                          | Static
                          | Strictfp

%%% ========================================================================
%%%  9.1.3 -- Superinterfaces & Subinterfaces
%%% ========================================================================

type ExtendsInterfaces = InterfaceTypeList

%%% ========================================================================
%%%  9.1.4 -- Interface Body & Member Declarations
%%% ========================================================================

type InterfaceBody = Option InterfaceMemberDeclarations

type InterfaceMemberDeclarations = List InterfaceMemberDeclaration
type InterfaceMemberDeclaration  = | Constant       ConstantDeclaration        % [9.3]
                                   | AbstractMethod AbstractMethodDeclaration  % [9.4]
                                   % [7.6] ClassDeclaration
                                   | Class          NormalClassDeclaration     % [8.1]
                                   | Enum           EnumDeclaration            % [8.9]
                                   % [7.6] InterfaceDeclaration:
                                   | Interface      NormalInterfaceDeclaration % [9.1]
                                   | Annotation     AnnotationTypeDeclaration  % [9.6]
                                   %
                                   | Vacuous

%%% ========================================================================
%%%  9.3 -- Field (Constant) Declarations
%%% ========================================================================

type ConstantDeclaration = {modifiers : Option ConstantModifiers,
                            jtype     : Type,
                            decls     : VariableDeclarators}

type ConstantModifiers = List ConstantModifier
type ConstantModifier  = | Annotation Annotation
                         | Public
                         | Static
                         | Final

%%% ========================================================================
%%%  9.4 -- Abstract Method Declarations
%%% ========================================================================

type AbstractMethodDeclaration = {modifiers       : Option AbstractMethodModifiers,
                                  type_parameters : Option TypeParameters,
                                  result          : Result,
                                  body            : MethodDeclarator,
                                  throws          : Option Throws}

type AbstractMethodModifiers = List AbstractMethodModifier
type AbstractMethodModifier  = | Annotation Annotation
                               | Public
                               | Abstract

%%% ========================================================================
%%%  9.6 -- Annotation Types
%%% ========================================================================

type AnnotationTypeDeclaration = {modifiers : Option InterfaceModifiers,
                                  name      : Identifier,
                                  body      : AnnotationTypeBody}

type AnnotationTypeBody = Option AnnotationTypeElementDeclarations
type AnnotationTypeElementDeclarations = List AnnotationTypeElementDeclaration

%%% ========================================================================
%%%  9.6.1 -- Annotation Type Elements
%%% ========================================================================

%%% Note:  [9.6.1] lists the subtypes of AnnotationTypeElementDeclaration
%%% redundantly, e.g. including both ClassDeclaration and EnumDeclaration,
%%% even though ClassDeclaration includes EnumDeclaration
%%% Ditto for InterfaceDeclaration 

type AnnotationTypeElementDeclaration = | Method          AnnotationTypeElementDeclaration_Method
                                        % ConstantDeclaration
                                        | Constant        ConstantDeclaration        % [9.3]
                                        % ClassDeclaration:
                                        | Class           NormalClassDeclaration     % [8.1]
                                        | Enum            EnumDeclaration            % [8.9]
                                        % InterfaceDeclaration:
                                        | Interface       NormalInterfaceDeclaration % [9.1]
                                        | Annotation      AnnotationTypeDeclaration  % [9.6]
                                        %
                                        | Vacuous

type AnnotationTypeElementDeclaration_Method = {modifiers : Option AbstractMethodModifiers,
                                                jtype     : Type,
                                                name      : Identifier,
                                                dims      : Option Dims,
                                                default   : Option DefaultValue}

type DefaultValue = ElementValue

%%% ========================================================================
%%%  9.7 -- Annotations
%%% ========================================================================

type Annotations = List Annotation
type Annotation = | Normal NormalAnnotation
                  | Marker MarkerAnnotation
                  | Single SingleElementAnnotation

%%% ========================================================================
%%%  9.7.1 -- Normal Annotations
%%% ========================================================================

type NormalAnnotation = {name           : TypeName,
                         element_values : Option ElementValuePairs}

type ElementValuePairs = List ElementValuePair
type ElementValuePair  = {name  : Identifier,
                          value : ElementValue}

type ElementValues = List ElementValue
type ElementValue  = | Expr             ConditionalExpression
                     | Annotation       Annotation
                     | ArrayInitializer ElementValueArrayInitializer

type ElementValueArrayInitializer = {values          : Option ElementValues,
                                     trailing_comma? : Bool}

%%% ========================================================================
%%%  9.7.2 -- Marker Annotations
%%% ========================================================================

type MarkerAnnotation = Identifier

%%% ========================================================================
%%%  9.7.3 -- Single-Element Annotations
%%% ========================================================================

type SingleElementAnnotation = {name  : Identifier,
                                value : ElementValue}

%%% ========================================================================
%%%  10.6 -- Array Initializers
%%% ========================================================================

type ArrayInitializer = {initialiers     : Option VariableInitializers,
                         trailing_comma? : Bool}

type VariableInitializers = List VariableInitializer

%%% ========================================================================
%%%  14.2 --  Blocks
%%% ========================================================================

type Block = Option BlockStatements

type BlockStatements = List BlockStatement

type BlockStatement = | VarDecl   LocalVariableDeclarationStatement
                      % [7.6] ClassDeclaration:
                      | Class     NormalClassDeclaration    % [8.1]
                      | Enum      EnumDeclaration           % [8.9]
                      %
                      | Statement Statement

%%% ========================================================================
%%%  14.4 -- Local Variable Declaration Statements
%%% ========================================================================

type LocalVariableDeclarationStatement = {decl : LocalVariableDeclaration}

type LocalVariableDeclaration = {modifiers : Option VariableModifiers,
                                 jtype     : Type,
                                 decls     : VariableDeclarators}

%%% ========================================================================
%%%  14.5 -- Statements
%%% ========================================================================

%%% UberStatement is the union of Statement and StatementNoShortIf
type UberStatement = % StatementWithoutTrailingSubstatement:
                    | Block               Block
                    | Empty          
                    | Expression          ExpressionStatement
                    | Assert              AssertStatement
                    | Switch              SwitchStatement
                    | Do                  DoStatement
                    | Break               BreakStatement
                    | Continue            ContinueStatement
                    | Return              ReturnStatement
                    | Synchronized        SynchronizedStatement
                    | Throw               ThrowStatement
                    | Try                 TryStatement
  
                    % Statement extends StatementWithoutTrailingSubstatement
                    | Labeled             LabeledStatement
                    | IfThen              IfThenStatement
                    | IfThenElse          IfThenElseStatement
                    | While               WhileStatement
                    | For                 ForStatement
  
                    % StatementNoShortIf extends StatementWithoutTrailingSubstatement
                    | LabeledNoShortIf    LabeledStatementNoShortIf
                    | IfThenElseNoShortIf IfThenElseStatementNoShortIf
                    | WhileNoShortIf      WhileStatementNoShortIf
                    | ForNoShortIf        ForStatementNoShortIf

op statementWithoutTrailingSubstatement? (s : Statement) : Bool =
  case s of
    | Block         _ -> true
    | Empty           -> true 
    | Expression    _ -> true
    | Assert        _ -> true
    | Switch        _ -> true
    | Do            _ -> true
    | Break         _ -> true
    | Continue      _ -> true
    | Return        _ -> true
    | Synchronized  _ -> true
    | Throw         _ -> true
    | Try           _ -> true
    | _ -> false

op statement? (s : UberStatement) : Bool =
 (statementWithoutTrailingSubstatement? s) ||
 (case s of
   | Labeled    _ -> true
   | IfThenElse _ -> true
   | While      _ -> true
   | For        _ -> true
   | _ -> false)
   
op statementNoShortIf? (s : UberStatement) : Bool =
 (statementWithoutTrailingSubstatement? s) ||
 (case s of
   | LabeledNoShortIf    _ -> true
   | IfThenElseNoShortIf _ -> true
   | WhileNoShortIf      _ -> true
   | ForNoShortIf        _ -> true
   | _ -> false)

type Statement          = UberStatement | statement?
type StatementNoShortIf = UberStatement | statementNoShortIf?

%%% ========================================================================
%%%  14.6 -- Empty Statement
%%% ========================================================================

%%% ========================================================================
%%%  14.7 -- Labeled Statements
%%% ========================================================================

type LabeledStatement = {label     : Identifier,
                         statement : Statement}

type LabeledStatementNoShortIf = {label     : Identifier,
                                  statement : StatementNoShortIf}

%%% ========================================================================
%%%  14.8 -- Expression Statements
%%% ========================================================================

type ExpressionStatement = StatementExpression

type StatementExpression = | Assignment AssignmentArgs
                           | PreIncr    PrefixArg
                           | PreDecr    PrefixArg
                           | PostIncr   PostfixArg
                           | PostDecr   PostfixArg
                           | Invocation MethodInvocation
                           | New        ClassInstanceCreationExpression

type PrefixArg = UnaryExpression


%%% ========================================================================
%%%  14.9 -- If Statement
%%% ========================================================================

type IfThenStatement = {pred      : Expression,
                        then_stmt : Statement}

type IfThenElseStatement = {pred      : Expression,
                            then_stmt : StatementNoShortIf,
                            else_stmt : Statement}

type IfThenElseStatementNoShortIf = {pred      : Expression,
                                     then_stmt : StatementNoShortIf,
                                     else_stmt : StatementNoShortIf}

%%% ========================================================================
%%%  14.10 -- The assert Statement
%%% ========================================================================

type AssertStatement = {expr1 : Expression,  % must return boolean or Boolean
                        expr2 : Expression}  

%%% ========================================================================
%%%  14.11 -- The switch Statement
%%% ========================================================================

type SwitchStatement = {expr  : Expression,
                        block : SwitchBlock}

type SwitchBlock = {groups: List SwitchBlockStatementGroup,
                    labels: SwitchLabels}

type SwitchBlockStatementGroup = {labels     : SwitchLabels,
                                  statements : BlockStatements}

type SwitchLabels = List SwitchLabel
type SwitchLabel  = | Constant ConstantExpression
                    | Enum     EnumConstantName
                    | Default

type EnumConstantName = Identifier

%%% ========================================================================
%%%  14.12 -- The while Statement
%%% ========================================================================

type WhileStatement = {test : Expression,
                       body : Statement}

type WhileStatementNoShortIf = {test : Expression,
                                body : StatementNoShortIf}

%%% ========================================================================
%%%  14.13 -- The do Statement
%%% ========================================================================

type DoStatement = {body : Statement,
                    test : Expression}

%%% ========================================================================
%%%  14.14 -- The for Statement
%%% ========================================================================

type ForStatement = | Basic    BasicForStatement
                    | Enhanced EnhancedForStatement

%%% ========================================================================
%%%  14.14.1 -- The basic for Statement
%%% ========================================================================

type BasicForStatement = {init   : Option ForInit,
                          pred   : Option Expression,
                          update : Option ForUpdate,
                          body   : Statement}

type ForStatementNoShortIf = {init   : Option ForInit,
                              pred   : Option Expression,
                              update : Option ForUpdate,
                              body   : StatementNoShortIf}

type ForInit = | Statements StatementExpressionList
               | VarDecls   LocalVariableDeclaration

type ForUpdate = StatementExpressionList

type StatementExpressionList = List StatementExpression

%%% ========================================================================
%%%  14.14.2 -- The enhanced for Statement
%%% ========================================================================

type EnhancedForStatement = {formal_parameter : FormalParameter,
                             pred             : Expression,
                             body             : Statement}

%%% ========================================================================
%%%  14.15 -- The break Statement
%%% ========================================================================

type BreakStatement = {label : Option Identifier}

%%% ========================================================================
%%%  14.16 -- The continue Statement
%%% ========================================================================

type ContinueStatement = {label : Option Identifier}

%%% ========================================================================
%%%  14.17 -- The return Statement
%%% ========================================================================

type ReturnStatement = {value : Option Expression}

%%% ========================================================================
%%%  14.18 -- The throw Statement
%%% ========================================================================

type ThrowStatement = {value : Expression}

%%% ========================================================================
%%%  14.19 -- The synchronized Statement
%%% ========================================================================

type SynchronizedStatement = {sync : Expression,
                              body : Block}

%%% ========================================================================
%%% 14.20 -- The try Statement
%%% ========================================================================

type TryStatement = {resources : Option ResourceSpecification,
                     body      : Block,
                     catches   : Option Catches,  % both cannot be None
                     finally   : Option Finally}

type Catches = List CatchClause 
type CatchClause = {parameter : CatchFormalParameter,
                    body      : Block}

type CatchFormalParameter = {modifiers  : VariableModifiers,
                             catch_type : CatchType,
                             var        : VariableDeclaratorId}

type CatchType = List ClassType  % disjunction

type Finally = Block

%%% ========================================================================
%%% 14.20.3 -- try-with-resources
%%% ========================================================================

type TryWithResourcesStatement = {s : TryStatement | s.resources ~= None}

type ResourceSpecification = List Resource

type Resource = {modifiers : Option VariableModifiers,
                 jtype     : Type,
                 var       : VariableDeclaratorId,
                 value     : Expression}

%%% ========================================================================
%%%  15.8 -- Primary Expressions
%%% ========================================================================

%%% For simplicity and clarity, we expand the options here to a flat coproduct

%%% VariableInitializer is actually defined in [8.3], but only to slightly 
%%% generalize Expression, found here

type Expression = %% [15.8]  PrimaryNoNewArray is first batch:
                  | Literal                Literal                   % [3.10]
                  | Class                  Type                      % [15.8]
                  | Void                                             % [15.8]
                  | This                                             % [15.8]
                  | QualifiedThis          ClassName                 % [15.8]
                  | Parenthesized          Expression                % [15.27]
                  | ClassInstanceCreation  ClassInstanceCreationExpression % [15.9]
                  | FieldAccess            FieldAccess               % [15.11]
                  | MethodInvocation       MethodInvocation          % [15.12]
                  | ArrayAccess            ArrayAccess               % [15.14]
                  % [15.8] Primary adds this:
                  | ArrayCreation          ArrayCreationExpression   % [15.10]
                  % [15.14] PostfixExpression adds next three:
                  | Name                   ExpressionName
                  | PostIncrement          PostfixArg
                  | PostDecrement          PostfixArg
                  % [15.15] UnaryExpressionNotPlusMinus adds next three:
                  | Tilde                  UnaryArg                  % [15.15]
                  | Bang                   UnaryArg                  % [15.15]
                  | Cast                   CastArgs                  % [15.16]
                  % [15.15] UnaryExpression adds next four
                  | PreIncrement           UnaryArg                  % [15.15]
                  | PreDecrement           UnaryArg                  % [15.15]
                  | UnaryPlus              UnaryArg                  % [15.15]
                  | UnaryMinus             UnaryArg                  % [15.15]
                  % [15.17] MultiplicativeExpression adds next three
                  | Multiply               MultiplicativeArgs        % [15.17]
                  | Divide                 MultiplicativeArgs        % [15.17]
                  | Remainder              MultiplicativeArgs        % [15.17]
                  % [15.18] AdditiveExpression adds next two
                  | Add                    AdditiveArgs              % [15.18]
                  | Subtract               AdditiveArgs              % [15.18]
                  % [15.19] ShiftExpression adds next three:
                  | LeftShift              ShiftArgs                 % [15.19]
                  | RightShiftSign         ShiftArgs                 % [15.19] 
                  | RightShiftZero         ShiftArgs                 % [15.19]
                  % [15.20] RelationalExpresion adds next five:
                  | LT                     RelationalArgs            % [15.20]
                  | GT                     RelationalArgs            % [15.20]
                  | LE                     RelationalArgs            % [15.20]
                  | GE                     RelationalArgs            % [15.20]
                  | InstanceOf             InstanceOfArgs            % [15.20]
                  % [15.21] EqualityExpresion adds next two
                  | EQ                     EqualityArgs              % [15.21]
                  | NE                     EqualityArgs              % [15.21]
                  % [15.22] AndExpression adds next one
                  | BitwiseAnd             BitwiseAndArgs            % [15.22]
                  % [15.22] XOrExpression adds next one
                  | BitwiseXor             BitwiseXorArgs            % [15.22]
                  % [15.22] OrExpression adds next one
                  | BitwiseOr              BitwiseOrArgs             % [15.22]
                  % [15.23] ConitionalAnd adds next one
                  | ConditionalAnd         ConditionalAndArgs        % [15.23]
                  % [15.24] ConitionalOr adds next one
                  | ConditionalOr          ConditionalOrArgs         % [15.24]
                  % [15.25] Conitional adds next one
                  | Conditional            ConditionalArgs           % [15.25]
                  % [15.26] Assignment adds next one
                  | Assignment             AssignmentArgs            % [15.26]

%% --------------------

op primaryNoNewArrayExpr? (x : Primary) : Bool =
  case x of
    | Literal                _ -> true
    | Class                  _ -> true
    | Void                     -> true
    | This                     -> true
    | QualifiedThis          _ -> true
    | Parenthesized          _ -> true
    | ClassInstanceCreation  _ -> true
    | FieldAccess            _ -> true
    | MethodInvocation       _ -> true
    | ArrayAccess            _ -> true
    | _ -> false
      
type PrimaryNoNewArray = Primary | primaryNoNewArrayExpr?

%% --------------------

op primaryExpr? (x : Expression) : Bool =
  case x of
    | ArrayCreation _ -> false
    | _ -> primaryNoNewArrayExpr? x

type Primary = PostfixExpression | primaryExpr?

%%% ========================================================================
%%%  15.9 -- Class Instance Creation Expressions
%%% ========================================================================

type ClassInstanceCreationExpression = | NoExpr ClassInstanceCreation_noExpr
                                       | Expr   ClassInstanceCreation_Expr

type ClassInstanceCreation_noExpr = {targs  : Option TypeArguments,
                                     tdecl  : TypeDeclSpecifier,
                                     targs2 : Option TypeArgumentsOrDiamond,
                                     args   : Option ArgumentList,
                                     body   : Option ClassBody}

type ClassInstanceCreation_Expr = {expr   : Primary,
                                   targs  : Option TypeArguments,
                                   name   : Identifier,
                                   targs2 : Option TypeArgumentsOrDiamond,
                                   args   : Option ArgumentList,
                                   body   : Option ClassBody}

type TypeArgumentsOrDiamond = | Args TypeArguments
                              | Diamond

type Arguments = ArgumentList 
type ArgumentList = List Expression

%%% ========================================================================
%%%  15.10 -- Array Creation Expressions
%%% ========================================================================

%%% Note: Most of the other types here with names ending in "Expression" 
%%%        belong to a nested subset/superset hierarchy.  
%%%       ArrayCreationExpression is different, and merely refers to one
%%%        particular kind of expression.

type ArrayCreationExpression = | Primitive            ArrayCreationPrimitive
                               | ClassOrInterface     ArrayCreationClassOrInterface
                               | PrimitiveInit        ArrayInitPrimitive
                               | ClassOrInterfaceInit ArrayInitClassOrInterface

type ArrayCreationPrimitive        = {jtype : PrimitiveType,
                                      args  : DimExprs,
                                      dims  : Option Dims}

type ArrayCreationClassOrInterface = {jtype : ClassOrInterfaceType,
                                      args  : DimExprs,
                                      dims  : Option Dims}

type ArrayInitPrimitive            = {jtype : PrimitiveType,
                                      dims : Dims,
                                      init : ArrayInitializer}

type ArrayInitClassOrInterface     = {jtype : ClassOrInterfaceType,
                                      dims : Dims,
                                      init : ArrayInitializer}

type DimExprs = List DimExpr
type DimExpr = Expression

%%% ========================================================================
%%%  15.11 -- Field Access Expressions
%%% ========================================================================

type FieldAccess = | Expr       FieldAccessViaExpr
                   | Super      Identifier
                   | ClassSuper FieldAccessViaClassSuper

type FieldAccessViaExpr = {expr : Primary,
                           id   : Identifier}

type FieldAccessViaClassSuper = {classname : ClassName,
                                 id        : Identifier}

%%% ========================================================================
%%%  15.12 -- Method Invocation Expressions
%%% ========================================================================

type MethodInvocation = | Method  MethodInvocationViaMethodName
                        | Primary MethodInvocationViaExpr
                        | Super   MethodInvocationViaSuper
                        | Class   MethodInvocationViaClassName
                        | Type    MethodInvocationViaTypeName

type MethodInvocationViaMethodName = {name : MethodName,
                                      args : Option ArgumentList}

type MethodInvocationViaExpr = {primary : Expression,
                                targs   : Option NonWildTypeArguments,
                                name    : Identifier,
                                args    : Option ArgumentList}

type MethodInvocationViaSuper = {targs : Option NonWildTypeArguments,
                                 name  : Identifier,
                                 args  : Option ArgumentList}

type MethodInvocationViaClassName = {class : ClassName,
                                     targs : Option NonWildTypeArguments,
                                     name  : Identifier,
                                     args  : Option ArgumentList}

type MethodInvocationViaTypeName = {typename : TypeName,
                                    targs    : NonWildTypeArguments,
                                    name     : Identifier,
                                    args     : Option ArgumentList}

%%% ========================================================================
%%%  15.13 -- Array Access Expressions
%%% ========================================================================

type ArrayAccess = | ViaName    ArrayAccessViaName     
                   | ViaPrimary ArrayAccessViaExpr

type ArrayAccessViaName = {name  : ExpressionName,
                           index : Expression}

type ArrayAccessViaExpr = {expr  : PrimaryNoNewArray,
                           index : Expression}
                                        
%%% ========================================================================
%%%  15.14 -- Postfix Expressions
%%% ========================================================================

op postfixExpr? (x : UnaryExpressionNotPlusMinus) : Bool =
  case x of
    | Name          _ -> true
    | PostIncrement _ -> true
    | PostDecrement _ -> true
    | _ -> primaryExpr? x

type PostfixExpression = UnaryExpressionNotPlusMinus | postfixExpr?

type PostfixArg = PostfixExpression  % 1-element record?

%%% ========================================================================
%%%  15.14.2  -- Postfix Incremement Operator ++
%%% ========================================================================

%%% ========================================================================
%%%  15.14.2  -- Postfix Decremement Operator --
%%% ========================================================================

%%% ========================================================================
%%%  15.15  -- Unary Operators
%%% ========================================================================

op unaryNotPlusMinusExpr? (x : UnaryExpression) : Bool =
 case x of
   | Tilde   _ -> true
   | Bang    _ -> true
   | Cast    _ -> true
   | _ -> postfixExpr? x

type UnaryExpressionNotPlusMinus = UnaryExpression | unaryNotPlusMinusExpr?

%% --------------------

op unaryExpr? (x : MultiplicativeExpression) : Bool = 
 case x of
   | PreIncrement _ -> true
   | PreDecrement _ -> true
   | UnaryPlus    _ -> true
   | UnaryMinus   _ -> true
   | _ -> unaryNotPlusMinusExpr? x

type UnaryExpression = MultiplicativeExpression | unaryExpr?

type UnaryArg  = UnaryExpression  % 1-element record?

%%% ========================================================================
%%%  15.16 -- Cast Expressions
%%% ========================================================================

type CastArgs = | Primitive CastArgs_Primitive
                | Reference CastArgs_Reference

type CastArgs_Primitive = {ptype : PrimitiveType,
                           expr  : UnaryExpression}

type CastArgs_Reference = {rtype : ReferenceType,
                           expr  : UnaryExpressionNotPlusMinus}

%%% ========================================================================
%%%  15.17 -- Multiplicative Operators
%%% ========================================================================

op multiplicativeExpr? (x : AdditiveExpression) : Bool =
  case x of
    | Multiply   _ -> true
    | Divide     _ -> true
    | Remainder  _ -> true
    | _ -> unaryExpr? x

type MultiplicativeExpression = AdditiveExpression | multiplicativeExpr?

type MultiplicativeArgs = {x : MultiplicativeExpression, y : UnaryExpression}

%%% ========================================================================
%%%  15.18 -- Additive Operators
%%% ========================================================================

op additiveExpr? (x : ShiftExpression) : Bool =
  case x of
    | Add      _ -> true
    | Subtract _ -> true
    | _ -> multiplicativeExpr? x

type AdditiveExpression = ShiftExpression | additiveExpr?

type AdditiveArgs = {x : AdditiveExpression, y : MultiplicativeExpression}

%%% ========================================================================
%%%  15.19 -- Shift Operators
%%% ========================================================================

op shiftExpr? (x : RelationalExpression) : Bool =
  case x of
    | LeftShift       _ -> true
    | RightShiftSign  _ -> true
    | RightShiftZero  _ -> true
    | _ -> additiveExpr? x

type ShiftExpression = RelationalExpression | shiftExpr?

type ShiftArgs = {x : ShiftExpression, y : AdditiveExpression}

%%% ========================================================================
%%%  15.20 -- Relational Operators
%%% ========================================================================

type InstanceOfArgs = {expr    : Expression, 
                       reftype : ReferenceType}

op relationalExpr? (x : EqualityExpression) : Bool =
  case x of
    | LT         _ -> true
    | GT         _ -> true
    | LE         _ -> true
    | GE         _ -> true
    | InstanceOf _ -> true
    | _ -> shiftExpr? x

type RelationalExpression = EqualityExpression | relationalExpr?

type RelationalArgs = {x : RelationalExpression,
                       y : ShiftExpression}

%%% ========================================================================
%%%  15.21 -- Equality Operators
%%% ========================================================================

op equalityExpr? (x : AndExpression) : Bool =
  case x of
    | EQ _ -> true
    | NE _ -> true
    | _ -> relationalExpr? x

type EqualityExpression = AndExpression | equalityExpr?

type EqualityArgs = {x : EqualityExpression, 
                     y : RelationalExpression}

%%% ========================================================================
%%%  15.22 -- Bitwise and Logical Operators
%%% ========================================================================

op andExpr? (x : ExclusiveOrExpression) : Bool =
  case x of
    | BitwiseAnd _ -> true
    | _ -> equalityExpr? x

type AndExpression = ExclusiveOrExpression | andExpr?

type BitwiseAndArgs = {x : AndExpression, y : EqualityExpression}


op exclusiveOrExpr? (x : InclusiveOrExpression) : Bool =
  case x of
    | BitwiseXor _ -> true
    | _ -> andExpr? x

type ExclusiveOrExpression = InclusiveOrExpression | exclusiveOrExpr?

type BitwiseXorArgs = {x : ExclusiveOrExpression, y : AndExpression}


op inclusiveOrExpr? (x : ConditionalAndExpression) : Bool =
  case x of
    | BitwiseOr _ -> true
    | _ -> exclusiveOrExpr? x

type InclusiveOrExpression = ConditionalAndExpression | inclusiveOrExpr?

type BitwiseOrArgs = {x : InclusiveOrExpression, y : ExclusiveOrExpression}

%%% ========================================================================
%%%  15.23 -- Conditional-And Operator
%%% ========================================================================

op conditionalAndExpr? (x : ConditionalOrExpression) : Bool =
  case x of
    | ConditionalAnd _ -> true
    | _ -> inclusiveOrExpr? x

type ConditionalAndExpression = ConditionalOrExpression | conditionalAndExpr?

type ConditionalAndArgs = {x : ConditionalAndExpression, 
                           y : InclusiveOrExpression}

%%% ========================================================================
%%%  15.24 -- Conditional-Or Operator
%%% ========================================================================

op conditionalOrExpr? (x : ConditionalExpression) : Bool =
  case x of
    | ConditionalOr _ -> true
    | _ -> conditionalAndExpr? x

type ConditionalOrExpression = ConditionalExpression | conditionalOrExpr?

type ConditionalOrArgs = {x : ConditionalOrExpression, 
                          y : ConditionalAndExpression}


%%% ========================================================================
%%%  15.25 -- Conditional Operator
%%% ========================================================================

op conditionalExpr? (x : AssignmentExpression) : Bool =
  case x of
    | Conditional _ -> true
    | _ -> conditionalOrExpr? x

type ConditionalExpression = AssignmentExpression | conditionalExpr?

type ConditionalArgs = {test : ConditionalOrExpression,
                        yes  : Expression,
                        no   : ConditionalExpression}

%%% ========================================================================
%%%  15.26 -- Assignment Operators
%%% ========================================================================

op assignmentExpr? (x : AssignmentExpression) : Bool =
  case x of
    | Assignment _ -> true
    | _ -> conditionalExpr? x

type AssignmentExpression = Expression | assignmentExpr?

type AssignmentArgs = {lhs      : LeftHandSide,
                       operator : AssignmentOperator,
                       expr     : AssignmentExpression}

type LeftHandSide = | Name  ExpressionName
                    | Field FieldAccess
                    | Array ArrayAccess

%% Listing the options explicitly avoids any possible confusion

type AssignmentOperator = | Assign                %  "="  
                          | AssignMultiply        %  "*="
                          | AssignDivide          %  "/=" 
                          | AssignRemainder       %  "%=" 
                          | AssignPlus            %  "+=" 
                          | AssignMinus           %  "-=" 
                          | AssignLeftShift       %  "<<=" 
                          | AssignRightShiftSign  %  ">>="   sign extension
                          | AssignRightShiftZero  %  ">>>="  zero extension
                          | AssignBitwiseAnd      %  "&=" 
                          | AssignBitwiseeXOr     %  "^=" 
                          | AssignBitwiseOR       %  "|="

%%% ========================================================================
%%%  15.27 -- Expression
%%% ========================================================================

%%% ========================================================================
%%%  15.28 -- Constant Expression
%%% ========================================================================

type ConstantExpression = Expression

%%% ========================================================================
%%%  10.6 -- Array Initializers
%%% ========================================================================

end-spec
