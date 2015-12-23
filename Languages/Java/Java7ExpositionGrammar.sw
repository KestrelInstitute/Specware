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

Java7Exp qualifying spec

import Java7Grammars

%%% ========================================================================
%%% 4.1. The Kinds of Types and Values
%%% ========================================================================

op Type : NonTerminal = nonTerminal "Type"

op Directives_4_1_Kinds_Of_Types : Directives =
 [Header "4.1. The Kinds of Types and Values",

  Rule {lhs = Type,
        rhs = Any [NT PrimitiveType,
                   NT ReferenceType]}

  ]

%%% ========================================================================
%%% 4.2. Primitive Types and Values
%%% ========================================================================

op PrimitiveType     : NonTerminal = nonTerminal "PrimitiveType"
op NumericType       : NonTerminal = nonTerminal "NumericType"
op IntegralType      : NonTerminal = nonTerminal "IntegralType"
op FloatingPointType : NonTerminal = nonTerminal "FloatingPointType"

op Directives_4_2_Primitive_Types : Directives =
 [Header "4.2. Primitive Types and Values",

  Rule {lhs = PrimitiveType,
        rhs = Any [NT NumericType,
                   NT KW_boolean]},

  Rule {lhs = NumericType,
        rhs = Any [NT IntegralType,
                   NT FloatingPointType]},

  Rule {lhs = IntegralType,
        rhs = Any [NT KW_byte, NT KW_short, NT KW_int, NT KW_long, NT KW_char]},

  Rule {lhs = FloatingPointType,
        rhs = Any [NT KW_float, NT KW_double]}

  ]

%%% ========================================================================
%%% 4.3. Reference Types and Values
%%% ========================================================================

op ReferenceType        : NonTerminal = nonTerminal "ReferenceType"
op ClassOrInterfaceType : NonTerminal = nonTerminal "ClassOrInterfaceType"
op ClassType            : NonTerminal = nonTerminal "ClassType"
op InterfaceType        : NonTerminal = nonTerminal "InterfaceType"
op TypeDeclSpecifier    : NonTerminal = nonTerminal "TypeDeclSpecifier"
%% TypeName in [4.3] conflicts with a different TypeName in [6.5]
op TypeNameNoPackage    : NonTerminal = nonTerminal "TypeNameNoPackage"  
op TypeVariable         : NonTerminal = nonTerminal "TypeVariable"
op ArrayType            : NonTerminal = nonTerminal "ArrayType"

op Directives_4_3_Reference_Types : Directives =
 [Header "4.3. Reference Types and Values",

  Rule {lhs = ReferenceType,
        rhs = Any [NT ClassOrInterfaceType,
                   NT TypeVariable,
                   NT ArrayType]},

  Rule {lhs = ClassOrInterfaceType,
        rhs = Any [NT ClassType,
                   NT InterfaceType]},

  Rule {lhs = ClassType,
        rhs = Seq [NT TypeDeclSpecifier, Opt [NT TypeArguments]]},

  Rule {lhs = InterfaceType,
        rhs = Seq [NT TypeDeclSpecifier, Opt [NT TypeArguments]]},

  Rule {lhs = TypeDeclSpecifier,
        rhs = Any [NT TypeNameNoPackage,
                   Seq [NT ClassOrInterfaceType, dot, NT Identifier]]},

  %%  Section 6.5 gives an alternative definition for TypeName, using PackageOrTypeName
  %%  Rule {lhs = TypeName,
  %%        rhs = Any [NT Identifier,
  %%                   Seq [NT TypeName, dot, NT Identifier]]},

  Rule {lhs = TypeNameNoPackage,
        rhs = Any [NT Identifier,
                   Seq [NT TypeNameNoPackage, dot, NT Identifier]]},

  Rule {lhs = TypeVariable,
        rhs = NT Identifier},

  Rule {lhs = ArrayType,
        rhs = Seq [NT Type, left_square, right_square]}

  ]

%%% ========================================================================
%%% 4.4. Type Variables
%%% ========================================================================

op TypeParameter       : NonTerminal = nonTerminal "TypeParameter"
op TypeBound           : NonTerminal = nonTerminal "TypeBound"
op AdditionalBoundList : NonTerminal = nonTerminal "AdditionalBoundList"
op AdditionalBound     : NonTerminal = nonTerminal "AdditionalBound"

op Directives_4_4_Type_Variables : Directives =
 [Header "4.3. Reference Types and Values",

  Rule {lhs = TypeParameter,
        rhs = Seq [NT TypeVariable, Opt [NT TypeBound]]},

  Rule {lhs = TypeBound,
        rhs = Any [Seq [NT KW_extends, NT TypeVariable],
                   Seq [NT KW_extends, NT ClassOrInterfaceType, Opt [NT AdditionalBoundList]]]},

  Rule {lhs = AdditionalBoundList,
        rhs = Any [Seq [NT AdditionalBound, NT AdditionalBoundList],
                   NT AdditionalBound]},

  Rule {lhs = AdditionalBound,
        rhs = Seq [ampersand, NT InterfaceType]}
  ]

%%% ========================================================================
%%% 4.5.1. Type Arguments and WildCards
%%% ========================================================================

op TypeArguments    : NonTerminal = nonTerminal "TypeArguments"
op TypeArgumentList : NonTerminal = nonTerminal "TypeArgumentList"
op TypeArgument     : NonTerminal = nonTerminal "TypeArgument"
op Wildcard         : NonTerminal = nonTerminal "Wildcard"
op WildcardBounds   : NonTerminal = nonTerminal "WildcardBounds"

op Directives_4_5_1_Type_Arguments : Directives =
 [Header "4.5.1. Type Arguments and WildCards",

  Rule {lhs = TypeArguments,
        rhs = Seq [left_angle, NT TypeArgumentList, right_angle]},

  Rule {lhs = TypeArgumentList,
        rhs = Any [NT TypeArgument,
                   Seq [NT TypeArgumentList, comma, NT TypeArgument]]},

  Rule {lhs = TypeArgument,
        rhs = Any [NT ReferenceType,
                   NT Wildcard]},

  Rule {lhs = Wildcard,
        rhs = Seq [question_mark, Opt [NT WildcardBounds]]},

  Rule {lhs = WildcardBounds,
        rhs = Any [Seq [NT KW_extends, NT ReferenceType],
                   Seq [NT KW_super,   NT ReferenceType]]}
  ]

%%% ========================================================================
%%%  6.5. -- Determining the Meaning of a Name
%%% ========================================================================

%%% Note: Many of these types are resolved by context, so we use the
%%%       'kind' field of AmbiguousName to record whatever has been
%%%       learned by processing.  When creating internal structures,
%%%       setting that flag restricts usage to specific contexts.
%%%       The downside is that this could make it very hard to statically
%%%       verify type-checking conditions.

op PackageName       : NonTerminal = nonTerminal "PackageName"
% definintion in [6.5] overrides conflicting definition in [4.3]
op TypeName          : NonTerminal = nonTerminal "TypeName"   
op ExpressionName    : NonTerminal = nonTerminal "ExpressionName"
op MethodName        : NonTerminal = nonTerminal "MethodName"
op PackageOrTypeName : NonTerminal = nonTerminal "PackageOrTypeName"
op AmbiguousName     : NonTerminal = nonTerminal "AmbiguousName"

op Directives_6_5_Names : Directives =
 [Header "6.5. -- Determining the Meaning of a Name",

  Rule {lhs = PackageName,
        rhs = Any [NT Identifier,
                   Seq [NT PackageName, dot, NT Identifier]]},

  %% overrides conflicting definition in 4.3, which used TypeName in definition
  Rule {lhs = TypeName,
        rhs = Any [NT Identifier,
                   Seq [NT PackageOrTypeName, dot, NT Identifier]]},

  Rule {lhs = ExpressionName,
        rhs = Any [NT Identifier,
                   Seq [NT AmbiguousName, dot, NT Identifier]]},

  Rule {lhs = MethodName,
        rhs = Any [NT Identifier,
                   Seq [NT AmbiguousName, dot, NT Identifier]]},

  Rule {lhs = PackageOrTypeName,
        rhs = Any [NT Identifier,
                   Seq [NT PackageOrTypeName, dot, NT Identifier]]},

  Rule {lhs = AmbiguousName,
        rhs = Any [NT Identifier,
                   Seq [NT AmbiguousName, dot, NT Identifier]]}
  ]

%%% ========================================================================
%%%  7.3. Compilation Units
%%% ========================================================================

op CompilationUnit    : NonTerminal = nonTerminal "CompilationUnit"
op ImportDeclarations : NonTerminal = nonTerminal "ImportDeclarations"
op TypeDeclarations   : NonTerminal = nonTerminal "TypeDeclarations"

op Directives_7_3_Compilation_Units : Directives =
 [Header "7.3. Compilation Units",

  Rule {lhs = CompilationUnit,
        rhs = Seq [Opt [NT PackageDeclaration], Opt [NT ImportDeclarations], Opt [NT TypeDeclarations]]},

  Rule {lhs = ImportDeclarations,
        rhs = Any [NT ImportDeclaration,
                   Seq [NT ImportDeclarations, NT ImportDeclaration]]},

  Rule {lhs = TypeDeclarations,
        rhs = Any [NT TypeDeclaration,
                   Seq [NT TypeDeclarations, NT TypeDeclaration]]}
  ]

%%% ========================================================================
%%%  7.4. Package Declarations
%%% ========================================================================

op PackageDeclaration : NonTerminal = nonTerminal "PackageDeclaration"

op Directives_7_4_Package_Declarations : Directives =
 [Header "7.4. Package Declarations",

  Rule {lhs = PackageDeclaration,
        rhs = Seq [Opt [NT Annotations], NT KW_package, NT PackageName, semicolon]}
  ]

%%% ========================================================================
%%%  7.5. Import Declarations
%%% ========================================================================

op ImportDeclaration : NonTerminal = nonTerminal "ImportDeclaration"

op Directives_7_5_Import_Declarations : Directives =
 [Header "7.5. Import Declarations",

  Rule {lhs = ImportDeclaration,
        rhs = Any [NT SingleTypeImportDeclaration,
                   NT TypeImportOnDemandDeclaration,
                   NT SingleStaticImportDeclaration,
                   NT StaticImportOnDemandDeclaration]}
  ]

%%% ========================================================================
%%%  7.5.1. Single-Type-Import Declarations
%%% ========================================================================

op SingleTypeImportDeclaration : NonTerminal = nonTerminal "SingleTypeImportDeclaration"

op Directives_7_5_1_Single_Type_Import : Directives =
 [Header "7.5.1. Single-Type-Import Declarations",

  Rule {lhs = SingleTypeImportDeclaration,
        rhs = Seq [NT KW_import, NT TypeName, semicolon]}
  ]

%%% ========================================================================
%%%  7.5.2. Type-Import-on-Demand Declarations
%%% ========================================================================

op TypeImportOnDemandDeclaration : NonTerminal = nonTerminal "TypeImportOnDemandDeclaration"

op Directives_7_5_2_Type_Import_On_Demand : Directives =
 [Header "7.5.2. Type-Import-on-Demand Declarations",

  Rule {lhs = TypeImportOnDemandDeclaration,
        rhs = Seq [NT KW_import, NT PackageOrTypeName, dot, star, semicolon]}
  ]

%%% ========================================================================
%%%  7.5.3. Single-Static-Import Declarations
%%% ========================================================================

op SingleStaticImportDeclaration : NonTerminal = nonTerminal "SingleStaticImportDeclaration"

op Directives_7_5_3_Single_Static_Import : Directives =
 [Header "7.5.3. Single-Static-Import Declarations",

  Rule {lhs = SingleStaticImportDeclaration,
        rhs = Seq [NT KW_import, NT KW_static, NT TypeName, dot, NT Identifier, semicolon]}
  ]

%%% ========================================================================
%%%  7.5.4. Static-Import-on-Demand Declarations
%%% ========================================================================

op StaticImportOnDemandDeclaration : NonTerminal = nonTerminal "StaticImportOnDemandDeclaration"

op Directives_7_5_4_Static_Import_On_Demand : Directives =
 [Header "7.5.4. Static-Import-on-Demand Declarations",

  Rule {lhs = StaticImportOnDemandDeclaration,
        rhs = Seq [NT KW_import, NT KW_static, NT TypeName, dot, star, semicolon]}
  ]

%%% ========================================================================
%%%  7.6. -- Top Level Type Declarations
%%% ========================================================================

op TypeDeclaration : NonTerminal = nonTerminal "TypeDeclaration"

op Directives_7_6_Type_Declarations : Directives =
 [Header "7.6. -- Top Level Type Declarations",

  Rule {lhs = TypeDeclaration,
        rhs = Any [NT ClassDeclaration,
                   NT InterfaceDeclaration,
                   semicolon]}
  ]

%%% ========================================================================
%%%  8.1. Class Declarations
%%% ========================================================================

op ClassDeclaration       : NonTerminal = nonTerminal "ClassDeclaration"
op NormalClassDeclaration : NonTerminal = nonTerminal "NormalClassDeclaration"

op Directives_8_1_Class_Declarations : Directives =
 [Header "8.1. Class Declarations",

  Rule {lhs = ClassDeclaration,
        rhs = Any [NT NormalClassDeclaration,
                   NT EnumDeclaration]},

  Rule {lhs = NormalClassDeclaration,
        rhs = Seq [Opt [NT ClassModifiers], NT KW_class, NT Identifier, Opt [NT TypeParameters],
                   Opt [NT Super], Opt [NT Interfaces], NT ClassBody]}

  ]

%%% ========================================================================
%%%  8.1.1. Class Modifiers
%%% ========================================================================

op ClassModifiers : NonTerminal = nonTerminal "ClassModifiers"
op ClassModifier  : NonTerminal = nonTerminal "ClassModifier"

op Directives_8_1_1_Class_Modifiers : Directives =
 [Header "8.1.1. Class Modifiers",

  Rule {lhs = ClassModifiers,
        rhs = Any [NT ClassModifier,
                   Seq [NT ClassModifiers, NT ClassModifier]]},

  Rule {lhs = ClassModifier,
        rhs = Any [NT Annotation,
                   NT KW_public,
                   NT KW_protected,
                   NT KW_private,
                   NT KW_abstract,
                   NT KW_static,
                   NT KW_final,
                   NT KW_strictfp]}
  ]

%%% ========================================================================
%%%  8.1.2. Generic Classes and Type Parameters
%%% ========================================================================

op TypeParameters    : NonTerminal = nonTerminal "TypeParameters"
op TypeParameterList : NonTerminal = nonTerminal "TypeParameterList"

op Directives_8_1_2_Type_Parameters : Directives =
 [Header "8.1.2. Generic Classes and Type Parameters",

  Rule {lhs = TypeParameters,
        rhs = Seq [left_angle, NT TypeParameterList, right_angle]},

  Rule {lhs = TypeParameterList,
        rhs = Any [Seq [NT TypeParameterList, comma, NT TypeParameter],
                   NT TypeParameter]}
  ]

%%% ========================================================================
%%%  8.1.4. Superclasses and Subclasses
%%% ========================================================================

op Super : NonTerminal = nonTerminal "Super"

op Directives_8_1_4_Superclasses : Directives =
 [Header "8.1.4. Superclasses and Subclasses",

  Rule {lhs = Super,
        rhs = Seq [NT KW_extends, NT ClassType]}
  ]

%%% ========================================================================
%%%  8.1.5. Superinterfaces
%%% ========================================================================

op Interfaces        : NonTerminal = nonTerminal "Interfaces"
op InterfaceTypeList : NonTerminal = nonTerminal "InterfaceTypeList"

op Directives_8_1_5_Superinterfaces : Directives =
 [Header "8.1.5. Superinterfaces",

  Rule {lhs = Interfaces,
        rhs = Seq [NT KW_implements, NT InterfaceTypeList]},

  Rule {lhs = InterfaceTypeList,
        rhs = Any [NT InterfaceType,
                   Seq [NT InterfaceTypeList, comma, NT InterfaceType]]}

  ]

%%% ========================================================================
%%%  8.1.6. Class Body and Member Declarations
%%% ========================================================================

op ClassBody              : NonTerminal = nonTerminal "ClassBody"
op ClassBodyDeclarations  : NonTerminal = nonTerminal "ClassBodyDeclarations"
op ClassBodyDeclaration   : NonTerminal = nonTerminal "ClassBodyDeclaration"
op ClassMemberDeclaration : NonTerminal = nonTerminal "ClassMemberDeclaration"

op Directives_8_1_6_Class_Body : Directives =
 [Header "8.1.6. Class Body and Member Declarations",

  Rule {lhs = ClassBody,
        rhs = Seq [left_curly, Opt [NT ClassBodyDeclarations], right_curly]},

  Rule {lhs = ClassBodyDeclarations,
        rhs = Any [NT ClassBodyDeclaration,
                   Seq [NT ClassBodyDeclarations, NT ClassBodyDeclaration]]},

  Rule {lhs = ClassBodyDeclaration,
        rhs = Any [NT ClassMemberDeclaration,
                   NT InstanceInitializer,
                   NT StaticInitializer,
                   NT ConstructorDeclaration]},

  Rule {lhs = ClassMemberDeclaration,
        rhs = Any [NT FieldDeclaration,
                   NT MethodDeclaration,
                   NT ClassDeclaration,
                   NT InterfaceDeclaration,
                   semicolon]}
  ]

%%% ========================================================================
%%%  8.3. Field Declarations
%%% ========================================================================

op FieldDeclaration     : NonTerminal = nonTerminal "FieldDeclaration"
op VariableDeclarators  : NonTerminal = nonTerminal "VariableDeclarators"
op VariableDeclarator   : NonTerminal = nonTerminal "VariableDeclarator"
op VariableDeclaratorId : NonTerminal = nonTerminal "VariableDeclaratorId"
op VariableInitializer  : NonTerminal = nonTerminal "VariableInitializer"

op Directives_8_3_Field_Declarations : Directives =
 [Header "8.3. Field Declarations",

  Rule {lhs = FieldDeclaration,
        rhs = Seq [Opt [NT FieldModifiers], NT Type, NT VariableDeclarators, semicolon]},

  Rule {lhs = VariableDeclarators,
        rhs = Any [NT VariableDeclarator,
                   Seq [NT VariableDeclarators, comma, NT VariableDeclarator]]},

  Rule {lhs = VariableDeclarator,
        rhs = Any [NT VariableDeclaratorId,
                   Seq [NT VariableDeclaratorId, equal_sign, NT VariableInitializer]]},

  Rule {lhs = VariableDeclaratorId,
        rhs = Any [NT Identifier,
                   Seq [NT VariableDeclaratorId, left_square, right_square]]},

  Rule {lhs = VariableInitializer,
        rhs = Any [NT Expression,
                   NT ArrayInitializer]}
  ]

%%% ========================================================================
%%%  8.3.1. Field Modifiers
%%% ========================================================================

op FieldModifiers : NonTerminal = nonTerminal "FieldModifiers"
op FieldModifier  : NonTerminal = nonTerminal "FieldModifier"

op Directives_8_3_1_Field_Modifiers : Directives =
 [Header "8.3.1. Field Modifiers",

  Rule {lhs = FieldModifiers,
        rhs = Any [NT FieldModifier,
                   Seq [NT FieldModifiers, NT FieldModifier]]},

  Rule {lhs = FieldModifier,
        rhs = Any [NT Annotation,
                   NT KW_public,
                   NT KW_protected,
                   NT KW_private,
                   NT KW_static,
                   NT KW_final,
                   NT KW_transient,
                   NT KW_volatile]}
  ]

%%% ========================================================================
%%%  8.4. Method Declarations
%%% ========================================================================

op MethodDeclaration : NonTerminal = nonTerminal "MethodDeclaration"
op MethodHeader      : NonTerminal = nonTerminal "MethodHeader"
op MethodDeclarator  : NonTerminal = nonTerminal "MethodDeclarator"

op Directives_8_4_Method_Declarations : Directives =
 [Header "8.4. Method Declarations",

  Rule {lhs = MethodDeclaration,
        rhs = Seq [NT MethodHeader, NT MethodBody]},

  Rule {lhs = MethodHeader,
        rhs = Seq [Opt [NT MethodModifiers], Opt [NT TypeParameters], NT Result,
                   NT MethodDeclarator, Opt [NT Throws]]},

  Rule {lhs = MethodDeclarator,
        rhs = Seq [NT Identifier, left_paren, Opt [NT FormalParameterList], right_paren]}
  ]

%%% ========================================================================
%%%  8.4.1. Formal Parameters
%%% ========================================================================

op FormalParameterList : NonTerminal = nonTerminal "FormalParameterList"
op FormalParameters    : NonTerminal = nonTerminal "FormalParameters"
op FormalParameter     : NonTerminal = nonTerminal "FormalParameter"
op VariableModifiers   : NonTerminal = nonTerminal "VariableModifiers"
op VariableModifier    : NonTerminal = nonTerminal "VariableModifier"
op LastFormalParameter : NonTerminal = nonTerminal "LastFormalParameter"

op Directives_8_4_1_Formal_Parameters : Directives =
 [Header "8.4.1. Formal Parameters",

  Rule {lhs = FormalParameterList,
        rhs = Any [NT LastFormalParameter,
                   Seq [NT FormalParameters, comma, NT LastFormalParameter]]},

  Rule {lhs = FormalParameters,
        rhs = Any [NT FormalParameter,
                   Seq [NT FormalParameters, comma, NT FormalParameter]]},

  Rule {lhs = FormalParameter,
        rhs = Seq [Opt [NT VariableModifiers], NT Type, NT VariableDeclaratorId]},

  Rule {lhs = VariableModifiers,
        rhs = Any [NT VariableModifier,
                   Seq [NT VariableModifiers, NT VariableModifier]]},

  Rule {lhs = VariableModifier,
        rhs = Any [NT Annotation,
                   NT KW_final]},

  Rule {lhs = LastFormalParameter,
        rhs = Any [Seq [Opt [NT VariableModifiers], NT Type, NT Ellipses, NT VariableDeclaratorId],
                   NT FormalParameter]}

  ]

%%% ========================================================================
%%%  8.4.3. Method Modifiers
%%% ========================================================================

op MethodModifiers : NonTerminal = nonTerminal "MethodModifiers"
op MethodModifier  : NonTerminal = nonTerminal "MethodModifier"

op Directives_8_4_3_Method_Modifiers : Directives =
 [Header "8.4.3. Method Modifiers",

  Rule {lhs = MethodModifiers,
        rhs = Any [NT MethodModifier,
                   Seq [NT MethodModifiers, NT MethodModifier]]},

  Rule {lhs = MethodModifier,
        rhs = Any [NT Annotation,
                   NT KW_public,
                   NT KW_protected,
                   NT KW_private,
                   NT KW_abstract,
                   NT KW_static,
                   NT KW_final,
                   NT KW_synchronized,
                   NT KW_native,
                   NT KW_strictfp]}
  ]

%%% ========================================================================
%%%  8.4.5. Method Return Type
%%% ========================================================================

op Result : NonTerminal = nonTerminal "Result"

op Directives_8_4_5_Method_Result : Directives =
 [Header "8.4.5. Method Return Type",

  Rule {lhs = Result,
        rhs = Any [NT Type,
                   NT KW_void]}
  ]

%%% ========================================================================
%%%  8.4.6. Method Throws
%%% ========================================================================

op Throws            : NonTerminal = nonTerminal "Throws"
op ExceptionTypeList : NonTerminal = nonTerminal "ExceptionTypeList"
op ExceptionType     : NonTerminal = nonTerminal "ExceptionType"

op Directives_8_4_6_Method_Throws : Directives =
 [Header "8.4.6. Method Throws",

  Rule {lhs = Throws,
        rhs = Seq [NT KW_throws, NT ExceptionTypeList]},

  Rule {lhs = ExceptionTypeList,
        rhs = Any [NT ExceptionType,
                   Seq [NT ExceptionTypeList, comma, NT ExceptionType]]},

  Rule {lhs = ExceptionType,
        rhs = Any [NT TypeName,
                   NT TypeVariable]}

  ]

%%% ========================================================================
%%%  8.4.7. Method Body
%%% ========================================================================

op MethodBody : NonTerminal = nonTerminal "MethodBody"

op Directives_8_4_7_Method_Body : Directives =
 [Header "8.4.7. Method Body",

  Rule {lhs = MethodBody,
        rhs = Any [NT Block,
                   semicolon]}
  ]

%%% ========================================================================
%%%  8.6. Instance Initializers
%%% ========================================================================

op InstanceInitializer : NonTerminal = nonTerminal "InstanceInitializer"

op Directives_8_6_Instance_Initializers : Directives =
 [Header "8.6. Instance Initializers",

  Rule {lhs = InstanceInitializer,
        rhs = NT Block}
  ]

%%% ========================================================================
%%%  8.7. Static Initializers
%%% ========================================================================

op StaticInitializer : NonTerminal = nonTerminal "StaticInitializer"

op Directives_8_7_Static_Initializers : Directives =
 [Header "8.7. Static Initializers",

  Rule {lhs = StaticInitializer,
        rhs = Seq [NT KW_static, NT Block]}
  ]

%%% ========================================================================
%%%  8.8. Constructor Declarations
%%% ========================================================================

op ConstructorDeclaration : NonTerminal = nonTerminal "ConstructorDeclaration"
op ConstructorDeclarator  : NonTerminal = nonTerminal "ConstructorDeclarator"

op Directives_8_8_Constructor_Declarations : Directives =
 [Header "8.8. Constructor Declarations",

  Rule {lhs = ConstructorDeclaration,
        rhs = Seq [Opt [NT ConstructorModifiers], NT ConstructorDeclarator,
                   Opt [NT Throws], NT ConstructorBody]},

  Rule {lhs = ConstructorDeclarator,
        rhs = Seq [Opt [NT TypeParameters], NT SimpleTypeName,
                   left_paren, Opt [NT FormalParameterList], right_paren]}
  ]

%%% ========================================================================
%%%  8.8.3. Constructor Modifiers
%%% ========================================================================

op ConstructorModifiers : NonTerminal = nonTerminal "ConstructorModifiers"
op ConstructorModifier  : NonTerminal = nonTerminal "ConstructorModifier"

op Directives_8_8_3_Constructor_Modifiers : Directives =
 [Header "8.8.3. Constructor Modifiers",

  Rule {lhs = ConstructorModifiers,
        rhs = Any [NT ConstructorModifier,
                   Seq [NT ConstructorModifiers, NT ConstructorModifier]]},

  Rule {lhs = ConstructorModifier,
        rhs = Any [NT Annotation,
                   NT KW_public,
                   NT KW_protected,
                   NT KW_private]}

  ]

%%% ========================================================================
%%%  8.8.7. Constructor Body
%%% ========================================================================

op ConstructorBody : NonTerminal = nonTerminal "ConstructorBody"

op Directives_8_8_7_Constructor_Body : Directives =
 [Header "8.8.7. Constructor Body",

  Rule {lhs = ConstructorBody,
        rhs = Seq [left_curly, Opt [NT ExplicitConstructorInvocation],
                   Opt [NT BlockStatements], right_curly]}
  ]

%%% ========================================================================
%%%  8.8.7.1. Explicit Constructor Invocations
%%% ========================================================================

op ExplicitConstructorInvocation : NonTerminal = nonTerminal "ExplicitConstructorInvocation"
op NonWildTypeArguments          : NonTerminal = nonTerminal "NonWildTypeArguments"
op ReferenceTypeList             : NonTerminal = nonTerminal "ReferenceTypeList"

op Directives_8_8_7_1_Explicit_Constructor_Invocations : Directives =
 [Header "8.8.7.1. Explicit Constructor Invocations",

  Rule {lhs = ExplicitConstructorInvocation,
        rhs = Any [Seq [                 Opt [NT NonWildTypeArguments], NT KW_this,
                        left_paren, Opt [NT ArgumentList], right_paren, semicolon],

                   Seq [                 Opt [NT NonWildTypeArguments], NT KW_super,
                        left_paren, Opt [NT ArgumentList], right_paren, semicolon],

                   Seq [NT Primary, dot, Opt [NT NonWildTypeArguments], NT KW_super,
                        left_paren, Opt [NT ArgumentList], right_paren, semicolon]]},

  Rule {lhs = NonWildTypeArguments,
        rhs = Seq [left_angle, NT ReferenceTypeList, right_angle]},

  Rule {lhs = ReferenceTypeList,
        rhs = Any [NT ReferenceType,
                   Seq [NT ReferenceTypeList, comma, NT ReferenceType]]}

  ]

%%% ========================================================================
%%%  8.9. Enums
%%% ========================================================================

op EnumDeclaration : NonTerminal = nonTerminal "EnumDeclaration"
op EnumBody        : NonTerminal = nonTerminal "EnumBody"

op Directives_8_9_Enums : Directives =
 [Header "8.9. Enums",

  Rule {lhs = EnumDeclaration,
        rhs = Seq [Opt [NT ClassModifiers], NT KW_enum, NT Identifier,
                   Opt [NT Interfaces], NT EnumBody]},

  Rule {lhs = EnumBody,
        rhs = Seq [left_curly, Opt [NT EnumConstants], Opt [comma],
                   Opt [NT EnumBodyDeclarations], right_curly]}

  ]

%%% ========================================================================
%%%  8.9.1. Enum Constants
%%% ========================================================================

op EnumConstants        : NonTerminal = nonTerminal "EnumConstants"
op EnumConstant         : NonTerminal = nonTerminal "EnumConstant"
op Arguments            : NonTerminal = nonTerminal "Arguments"
op EnumBodyDeclarations : NonTerminal = nonTerminal "EnumBodyDeclarations"

op Directives_8_9_1_Enum_Constants : Directives =
 [Header "8.9.1. Enum Constants",

  Rule {lhs = EnumConstants,
        rhs = Any [NT EnumConstant,
                   Seq [NT EnumConstants, comma, NT EnumConstant]]},

  Rule {lhs = EnumConstant,
        rhs = Seq [Opt [NT Annotations], NT Identifier, Opt [NT Arguments], Opt [NT ClassBody]]},

  Rule {lhs = Arguments,
        rhs = Seq [left_paren, Opt [NT ArgumentList], right_paren]},

  Rule {lhs = EnumBodyDeclarations,
        rhs = Seq [semicolon, Opt [NT ClassBodyDeclarations]]}

  ]

%%% ========================================================================
%%% 9.1. Interface Declarations
%%% ========================================================================

op InterfaceDeclaration       : NonTerminal = nonTerminal "InterfaceDeclaration"
op NormalInterfaceDeclaration : NonTerminal = nonTerminal "NormalInterfaceDeclaration"

op Directives_9_1_Interface_Declarations : Directives =
 [Header "9.1. Interface Declarations",

  Rule {lhs = InterfaceDeclaration,
        rhs = Any [NT NormalInterfaceDeclaration,
                   NT AnnotationTypeDeclaration]},

  Rule {lhs = NormalInterfaceDeclaration,
        rhs = Any [Seq [Opt [NT InterfaceModifiers], NT KW_interface, NT Identifier],
                   Seq [Opt [NT TypeParameters], Opt [NT ExtendsInterfaces], NT InterfaceBody]]}

  ]

%%% ========================================================================
%%% 9.1.1. Interface Modifiers
%%% ========================================================================

op InterfaceModifiers : NonTerminal = nonTerminal "InterfaceModifiers"
op InterfaceModifier  : NonTerminal = nonTerminal "InterfaceModifier"

op Directives_9_1_1_Interface_Modifiers : Directives =
 [Header "9.1.1. Interface Modifiers",

  Rule {lhs = InterfaceModifiers,
        rhs = Any [NT InterfaceModifier,
                   Seq [NT InterfaceModifiers, NT InterfaceModifier]]},

  Rule {lhs = InterfaceModifier,
        rhs = Any [NT Annotation,
                   NT KW_public,
                   NT KW_protected,
                   NT KW_private,
                   NT KW_abstract,
                   NT KW_static,
                   NT KW_strictfp]}
  ]

%%% ========================================================================
%%% 9.1.3. Superinterfaces and Subinterfaces
%%% ========================================================================

op ExtendsInterfaces : NonTerminal = nonTerminal "ExtendsInterfaces"

op Directives_9_1_3_Interface_Extends : Directives =
 [Header "9.1.3. Superinterfaces and Subinterfaces",

  Rule {lhs = ExtendsInterfaces,
        rhs = Seq [NT KW_extends, NT InterfaceTypeList]}
  ]

%%% ========================================================================
%%% 9.1.4. Interface Body and Member Declarations
%%% ========================================================================

op InterfaceBody               : NonTerminal = nonTerminal "InterfaceBody"
op InterfaceMemberDeclarations : NonTerminal = nonTerminal "InterfaceMemberDeclarations"
op InterfaceMemberDeclaration  : NonTerminal = nonTerminal "InterfaceMemberDeclaration"

op Directives_9_1_4_Interface_Body : Directives =
 [Header "9.1.4. Interface Body and Member Declarations",

  Rule {lhs = InterfaceBody,
        rhs = Seq [left_curly, Opt [NT InterfaceMemberDeclarations], right_curly]},

  Rule {lhs = InterfaceMemberDeclarations,
        rhs = Any [NT InterfaceMemberDeclaration,
                   Seq [NT InterfaceMemberDeclarations, NT InterfaceMemberDeclaration]]},

  Rule {lhs = InterfaceMemberDeclaration,
        rhs = Any [NT ConstantDeclaration,
                   NT AbstractMethodDeclaration,
                   NT ClassDeclaration,
                   NT InterfaceDeclaration]}
  ]

%%% ========================================================================
%%% 9.3. Field (Constant) Declarations
%%% ========================================================================

op ConstantDeclaration : NonTerminal = nonTerminal "ConstantDeclaration"
op ConstantModifiers   : NonTerminal = nonTerminal "ConstantModifiers"
op ConstantModifier    : NonTerminal = nonTerminal "ConstantModifier"

op Directives_9_3_Constant_Field_Declarations : Directives =
 [Header "9.3. Field (Constant) Declarations",

  Rule {lhs = ConstantDeclaration,
        rhs = Seq [Opt [NT ConstantModifiers], NT Type, NT VariableDeclarators, semicolon]},

  Rule {lhs = ConstantModifiers,
        rhs = Any [NT ConstantModifier,
                   Seq [NT ConstantModifier, NT ConstantModifiers]]},

  Rule {lhs = ConstantModifier,
        rhs = Any [NT Annotation,
                   NT KW_public,
                   NT KW_static,
                   NT KW_final]}

  ]

%%% ========================================================================
%%% 9.4. Abstract Mehtod Declarations
%%% ========================================================================

op AbstractMethodDeclaration : NonTerminal = nonTerminal "AbstractMethodDeclaration"
op AbstractMethodModifiers   : NonTerminal = nonTerminal "AbstractMethodModifiers"
op AbstractMethodModifier    : NonTerminal = nonTerminal "AbstractMethodModifier"

op Directives_9_4_Abstract_Method_Declarations : Directives =
 [Header "9.4. Abstract Mehtod Declarations",

  Rule {lhs = AbstractMethodDeclaration,
        rhs = Seq [Opt [NT AbstractMethodModifiers], Opt [NT TypeParameters], NT Result,
                   NT MethodDeclarator, Opt [NT Throws], semicolon]},

  Rule {lhs = AbstractMethodModifiers,
        rhs = Any [NT AbstractMethodModifier,
                   Seq [NT AbstractMethodModifiers, NT AbstractMethodModifier]]},

  Rule {lhs = AbstractMethodModifier,
        rhs = Any [NT Annotation,
                   NT KW_public,
                   NT KW_abstract]}

  ]

%%% ========================================================================
%%% 9.6. Annotation Types
%%% ========================================================================

op AnnotationTypeDeclaration         : NonTerminal = nonTerminal "AnnotationTypeDeclaration"
op AnnotationTypeBody                : NonTerminal = nonTerminal "AnnotationTypeBody"
op AnnotationTypeElementDeclarations : NonTerminal = nonTerminal "AnnotationTypeElementDeclarations"

op Directives_9_6_Annotation_Types : Directives =
 [Header "9.6. Annotation Types",

  Rule {lhs = AnnotationTypeDeclaration,
        rhs = Seq [Opt [NT InterfaceModifiers], at_sign, NT KW_interface, NT Identifier, NT AnnotationTypeBody]},

  Rule {lhs = AnnotationTypeBody,
        rhs = Seq [left_curly, NT AnnotationTypeElementDeclarations, right_curly]},

  Rule {lhs = AnnotationTypeElementDeclarations,
        rhs = Any [NT AnnotationTypeElementDeclaration,
                   Seq [NT AnnotationTypeElementDeclarations, NT AnnotationTypeElementDeclaration]]}

  ]

%%% ========================================================================
%%% 9.6.1. Annotation Type Elements
%%% ========================================================================

op AnnotationTypeElementDeclaration : NonTerminal = nonTerminal "AnnotationTypeElementDeclaration"
op DefaultValue                     : NonTerminal = nonTerminal "DefaultValue"

op Directives_9_6_1_Annotation_Type_Elements : Directives =
 [Header "9.6.1. Annotation Type Elements",

  Rule {lhs = AnnotationTypeElementDeclaration,
        rhs = Any [Seq [Opt [NT AbstractMethodModifiers], NT Type, NT Identifier, left_paren, right_paren,
                        Opt [NT Dims], Opt [NT DefaultValue], semicolon],
                   NT ConstantDeclaration,
                   NT ClassDeclaration,
                   NT InterfaceDeclaration,
                   NT EnumDeclaration,
                   NT AnnotationTypeDeclaration,
                   semicolon]},

  Rule {lhs = DefaultValue,
        rhs = Seq [NT KW_default, NT ElementValue]}

  ]

%%% ========================================================================
%%% 9.7. Annotations
%%% ========================================================================

op Annotations : NonTerminal = nonTerminal "Annotations"
op Annotation  : NonTerminal = nonTerminal "Annotation"

op Directives_9_7_Annotations : Directives =
 [Header "9.7. Annotations",

  Rule {lhs = Annotations,
        rhs = Any [NT Annotation,
                   Seq [NT Annotations, NT Annotation]]},

  Rule {lhs = Annotation,
        rhs = Any [NT NormalAnnotation,
                   NT MarkerAnnotation,
                   NT SingleElementAnnotation]}

  ]

%%% ========================================================================
%%% 9.7.1. Normal Annotations
%%% ========================================================================

op NormalAnnotation             : NonTerminal = nonTerminal "NormalAnnotation"
op ElementValuePairs            : NonTerminal = nonTerminal "ElementValuePairs"
op ElementValuePair             : NonTerminal = nonTerminal "ElementValuePair"
op ElementValue                 : NonTerminal = nonTerminal "ElementValue"
op ElementValueArrayInitializer : NonTerminal = nonTerminal "ElementValueArrayInitializer"
op ElementValues                : NonTerminal = nonTerminal "ElementValues"

op Directives_9_7_1_Normal_Annotations : Directives =
 [Header "9.7.1. Normal Annotations",

  Rule {lhs = NormalAnnotation,
        rhs = Seq [at_sign, NT TypeName, left_paren, Opt [NT ElementValuePairs], right_paren]},

  Rule {lhs = ElementValuePairs,
        rhs = Any [NT ElementValuePair,
                   Seq [NT ElementValuePairs, comma, NT ElementValuePair]]},

  Rule {lhs = ElementValuePair,
        rhs = Seq [NT Identifier, equal_sign, NT ElementValue]},

  Rule {lhs = ElementValue,
        rhs = Any [NT ConditionalExpression,
                   NT Annotation,
                   NT ElementValueArrayInitializer]},

  Rule {lhs = ElementValueArrayInitializer,
        rhs = Seq [left_curly, Opt [NT ElementValues], Opt [comma], right_curly]},

  Rule {lhs = ElementValues,
        rhs = Any [NT ElementValue,
                   Seq [NT ElementValues, comma, NT ElementValue]]}

  ]

%%% ========================================================================
%%% 9.7.2. Marker Annotations
%%% ========================================================================

op MarkerAnnotation : NonTerminal = nonTerminal "MarkerAnnotation"

op Directives_9_7_2_Marker_Annotations : Directives =
 [Header "9.7.2. Marker Annotations",

  Rule {lhs = MarkerAnnotation,
        rhs = Seq [at_sign, NT Identifier]}
  ]

%%% ========================================================================
%%% 9.7.3. Single-Element Annotations
%%% ========================================================================

op SingleElementAnnotation : NonTerminal = nonTerminal "SingleElementAnnotation"

op Directives_9_7_3_Single_Element_Annotations : Directives =
 [Header "9.7.3. Single-Element Annotations",

  Rule {lhs = SingleElementAnnotation,
        rhs = Seq [at_sign, NT Identifier, left_paren, NT ElementValue, right_paren]}
  ]

%%% ========================================================================
%%% 10.6. Array Initializers
%%% ========================================================================

op ArrayInitializer     : NonTerminal = nonTerminal "ArrayInitializer"
op VariableInitializers : NonTerminal = nonTerminal "VariableInitializers"

op Directives_10_6_Array_Initializers : Directives =
 [Header "10.6. Array Initializers",

  Rule {lhs = ArrayInitializer,
        rhs = Seq [left_curly, Opt [NT VariableInitializers], Opt [comma], right_curly]},

  Rule {lhs = VariableInitializers,
        rhs = Any [NT VariableInitializer,
                   Seq [NT VariableInitializers, comma, NT VariableInitializer]]}

  ]

%%% ========================================================================
%%% 14.2. Blocks
%%% ========================================================================

op Block           : NonTerminal = nonTerminal "Block"
op BlockStatements : NonTerminal = nonTerminal "BlockStatements"
op BlockStatement  : NonTerminal = nonTerminal "BlockStatement"

op Directives_14_2_Blocks : Directives =
 [Header "14.2. Blocks",

  Rule {lhs = Block,
        rhs = Seq [left_curly, Opt [NT BlockStatements], right_curly]},

  Rule {lhs = BlockStatements,
        rhs = Any [NT BlockStatement,
                   Seq [NT BlockStatements, NT BlockStatement]]},

  Rule {lhs = BlockStatement,
        rhs = Any [NT LocalVariableDeclarationStatement,
                   NT ClassDeclaration,
                   NT Statement]}

  ]

%%% ========================================================================
%%% 14.4. Local Variable Declaration Statements
%%% ========================================================================

op LocalVariableDeclarationStatement : NonTerminal = nonTerminal "LocalVariableDeclarationStatement"
op LocalVariableDeclaration          : NonTerminal = nonTerminal "LocalVariableDeclaration"

op Directives_14_4_Local_Variable_Declaration_Statements : Directives =
 [Header "14.4. Local Variable Declaration Statements",

  Rule {lhs = LocalVariableDeclarationStatement,
        rhs = Seq [NT LocalVariableDeclaration, semicolon]},

  Rule {lhs = LocalVariableDeclaration,
        rhs = Seq [Opt [NT VariableModifiers], NT Type, NT VariableDeclarators]}

  ]

%%% ========================================================================
%%% 14.5. Statements
%%% ========================================================================

op Statement                            : NonTerminal = nonTerminal "Statement"
op StatementWithoutTrailingSubstatement : NonTerminal = nonTerminal "StatementWithoutTrailingSubstatement"
op StatementNoShortIf                   : NonTerminal = nonTerminal "StatementNoShortIf"

op Directives_14_5_Statements : Directives =
 [Header "14.5. Statements",

  Rule {lhs = Statement,
        rhs = Any [NT StatementWithoutTrailingSubstatement,
                   NT LabeledStatement,
                   NT IfThenStatement,
                   NT IfThenElseStatement,
                   NT WhileStatement,
                   NT ForStatement]},

  Rule {lhs = StatementWithoutTrailingSubstatement,
        rhs = Any [NT Block,
                   NT EmptyStatement,
                   NT ExpressionStatement,
                   NT AssertStatement,
                   NT SwitchStatement,
                   NT DoStatement,
                   NT BreakStatement,
                   NT ContinueStatement,
                   NT ReturnStatement,
                   NT SynchronizedStatement,
                   NT ThrowStatement,
                   NT TryStatement]},

  Rule {lhs = StatementNoShortIf,
        rhs = Any [NT StatementWithoutTrailingSubstatement,
                   NT LabeledStatementNoShortIf,
                   NT IfThenElseStatementNoShortIf,
                   NT WhileStatementNoShortIf,
                   NT ForStatementNoShortIf]}

  ]

%%% ========================================================================
%%% 14.6. The Empty Statement
%%% ========================================================================

op EmptyStatement : NonTerminal = nonTerminal "EmptyStatement"

op Directives_14_6_Empty_Statement : Directives =
 [Header "14.6. The Empty Statement",

  Rule {lhs = EmptyStatement,
        rhs = semicolon}
  ]

%%% ========================================================================
%%% 14.7. Labeled Statements
%%% ========================================================================

op LabeledStatement          : NonTerminal = nonTerminal "LabeledStatement"
op LabeledStatementNoShortIf : NonTerminal = nonTerminal "LabeledStatementNoShortIf"

op Directives_14_7_Labeled_Statements : Directives =
 [Header "14.7. Labeled Statements",

  Rule {lhs = LabeledStatement,
        rhs = Seq [NT Identifier, colon, NT Statement]},

  Rule {lhs = LabeledStatementNoShortIf,
        rhs = Seq [NT Identifier, colon, NT StatementNoShortIf]}
  ]

%%% ========================================================================
%%% 14.8. Expression Statements
%%% ========================================================================

op ExpressionStatement : NonTerminal = nonTerminal "ExpressionStatement"
op StatementExpression : NonTerminal = nonTerminal "StatementExpression"

op Directives_14_8_Expression_Statements : Directives =
 [Header "14.8. Expression Statements",

  Rule {lhs = ExpressionStatement,
        rhs = NT StatementExpression},

  Rule {lhs = StatementExpression,
        rhs = Any [NT Assignment,
                   NT PreIncrementExpression,
                   NT PreDecrementExpression,
                   NT PostIncrementExpression,
                   NT PostDecrementExpression,
                   NT MethodInvocation,
                   NT ClassInstanceCreationExpression]}
  ]

%%% ========================================================================
%%% 14.9. The if Statement
%%% ========================================================================

op IfThenStatement              : NonTerminal = nonTerminal "IfThenStatement"
op IfThenElseStatement          : NonTerminal = nonTerminal "IfThenElseStatement"
op IfThenElseStatementNoShortIf : NonTerminal = nonTerminal "IfThenElseStatementNoShortIf"

op Directives_14_9_If_Statement : Directives =
 [Header "14.9. The if Statement",

  Rule {lhs = IfThenStatement,
        rhs = Seq [NT KW_if, left_paren, NT Expression, right_paren, NT Statement]},

  Rule {lhs = IfThenElseStatement,
        rhs = Seq [NT KW_if, left_paren, NT Expression, right_paren,
                   NT StatementNoShortIf, NT KW_else, NT Statement]},

  Rule {lhs = IfThenElseStatementNoShortIf,
        rhs = Seq [NT KW_if, left_paren, NT Expression, right_paren,
                   NT StatementNoShortIf, NT KW_else, NT StatementNoShortIf]}
  ]


%%% ========================================================================
%%% 14.10. The assert Statement
%%% ========================================================================

op AssertStatement : NonTerminal = nonTerminal "AssertStatement"
op Expression1     : NonTerminal = nonTerminal "Expression1"    % TODO: just Expression ? 
op Expression2     : NonTerminal = nonTerminal "Expression2"    % TODO: just Expression ? 

op Directives_14_10_Assert_Statement : Directives =
 [Header "14.10. The assert Statement",

  Rule {lhs = AssertStatement,
        rhs = Any [Seq [NT KW_assert, NT Expression1, semicolon], % must return boolean or Boolean
                   Seq [NT KW_assert, NT Expression1, colon, NT Expression2, semicolon]]}
  ]

%%% ========================================================================
%%% 14.11. The switch Statement
%%% ========================================================================

op SwitchStatement            : NonTerminal = nonTerminal "SwitchStatement"
op SwitchBlock                : NonTerminal = nonTerminal "SwitchBlock"
op SwitchBlockStatementGroups : NonTerminal = nonTerminal "SwitchBlockStatementGroups"
op SwitchBlockStatementGroup  : NonTerminal = nonTerminal "SwitchBlockStatementGroup"
op SwitchLabels               : NonTerminal = nonTerminal "SwitchLabels"
op SwitchLabel                : NonTerminal = nonTerminal "SwitchLabel"
op EnumConstantName           : NonTerminal = nonTerminal "EnumConstantName"

op Directives_14_11_Switch_Statement : Directives =
 [Header "14.11. The switch Statement",

  Rule {lhs = SwitchStatement,
        rhs = Seq [NT KW_switch, left_paren, NT Expression, right_paren, NT SwitchBlock]},

  Rule {lhs = SwitchBlock,
        rhs = Seq [left_curly, Opt [NT SwitchBlockStatementGroups], Opt [NT SwitchLabel], right_curly]},

  Rule {lhs = SwitchBlockStatementGroups,
        rhs = Any [NT SwitchBlockStatementGroup,
                   Seq [NT SwitchBlockStatementGroups, NT SwitchBlockStatementGroup]]},

  Rule {lhs = SwitchBlockStatementGroup,
        rhs = Seq [NT SwitchLabels, NT BlockStatements]},

  Rule {lhs = SwitchLabels,
        rhs = Any [NT SwitchLabel,
                   Seq [NT SwitchLabels, NT SwitchLabel]]},

  Rule {lhs = SwitchLabel,
        rhs = Any [Seq [NT KW_case,    NT ConstantExpression, colon],
                   Seq [NT KW_case,    NT EnumConstantName,   colon],
                   Seq [NT KW_default,                        colon]]},

  Rule {lhs = EnumConstantName,
        rhs = NT Identifier}
  ]


%%% ========================================================================
%%% 14.12. The while Statement
%%% ========================================================================

op WhileStatement          : NonTerminal = nonTerminal "WhileStatement"
op WhileStatementNoShortIf : NonTerminal = nonTerminal "WhileStatementNoShortIf"

op Directives_14_12_While_Statement : Directives =
 [Header "14.12. The while Statement",

  Rule {lhs = WhileStatement,
        rhs = Seq [NT KW_while, left_paren, NT Expression, right_paren, NT Statement]},

  Rule {lhs = WhileStatementNoShortIf,
        rhs = Seq [NT KW_while, left_paren, NT Expression, right_paren, NT StatementNoShortIf]}
  ]

%%% ========================================================================
%%% 14.13. The do Statement
%%% ========================================================================

op DoStatement : NonTerminal = nonTerminal "DoStatement"

op Directives_14_13_Do_Statement : Directives =
 [Header "14.13. The do Statement",

  Rule {lhs = DoStatement,
        rhs = Seq [NT KW_do, NT Statement, NT KW_while, left_paren, NT Expression, right_paren, NT Statement]}

  ]

%%% ========================================================================
%%% 14.14. The for Statement
%%% ========================================================================

op ForStatement : NonTerminal = nonTerminal "ForStatement"

op Directives_14_14_For_Statement : Directives =
 [Header "14.14. The for Statement",

  Rule {lhs = ForStatement,
        rhs = Any [NT BasicForStatement,
                   NT EnhancedForStatement]}
  ]

%%% ========================================================================
%%% 14.14.1. The basic for Statement
%%% ========================================================================

op BasicForStatement       : NonTerminal = nonTerminal "BasicForStatement"
op ForStatementNoShortIf   : NonTerminal = nonTerminal "ForStatementNoShortIf"
op ForInit                 : NonTerminal = nonTerminal "ForInit"
op ForUpdate               : NonTerminal = nonTerminal "ForUpdate"
op StatementExpressionList : NonTerminal = nonTerminal "StatementExpressionList"

op Directives_14_14_1_Basic_For_Statement : Directives =
 [Header "14.14.1. The basic for Statement",

  Rule {lhs = BasicForStatement,
        rhs = Seq [NT KW_for, left_paren, Opt [NT ForInit], semicolon, Opt [NT Expression],
                   semicolon, Opt [NT ForUpdate], right_paren, NT Statement]},

  Rule {lhs = ForStatementNoShortIf,
        rhs = Seq [NT KW_for, Opt [NT ForInit], semicolon, Opt [NT Expression],  semicolon,
                   Opt [NT ForUpdate], right_paren, NT StatementNoShortIf]},

  Rule {lhs = ForInit,
        rhs = Any [NT StatementExpressionList,
                   NT LocalVariableDeclaration]},

  Rule {lhs = ForUpdate,
        rhs = NT StatementExpressionList},

  Rule {lhs = StatementExpressionList,
        rhs = Any [NT StatementExpression,
                   Seq [NT StatementExpressionList, comma, NT StatementExpression]]}

  ]

%%% ========================================================================
%%% 14.14.2. The enhanced for statement
%%% ========================================================================

op EnhancedForStatement : NonTerminal = nonTerminal "EnhancedForStatement"

op Directives_14_14_2_Enhanced_For_Statement : Directives =
 [Header "14.14.2. The enhanced for statement",

  Rule {lhs = EnhancedForStatement,
        rhs = Seq [NT KW_for, left_paren, NT FormalParameter, colon, NT Expression, right_paren, NT Statement]}
  ]

%%% ========================================================================
%%% 14.15. The break Statement
%%% ========================================================================

op BreakStatement : NonTerminal = nonTerminal "BreakStatement"

op Directives_14_15_Break_Statement : Directives =
 [Header "14.15. The break Statement",

  Rule {lhs = BreakStatement,
        rhs = Seq [NT KW_break, Opt [NT Identifier], semicolon]}
  ]

%%% ========================================================================
%%% 14.16. The continue Statement
%%% ========================================================================

op ContinueStatement : NonTerminal = nonTerminal "ContinueStatement"

op Directives_14_16_Continue_Statement : Directives =
 [Header "14.16. The continue Statement",

  Rule {lhs = ContinueStatement,
        rhs = Seq [NT KW_continue, Opt [NT Identifier], semicolon]}
  ]

%%% ========================================================================
%%% 14.17. The return Statement
%%% ========================================================================

op ReturnStatement : NonTerminal = nonTerminal "ReturnStatement"

op Directives_14_17_Return_Statement : Directives =
 [Header "14.17. The return Statement",

  Rule {lhs = ReturnStatement,
        rhs = Seq [NT KW_return, Opt [NT Expression], semicolon]}
  ]

%%% ========================================================================
%%% 14.18. The throw Statement
%%% ========================================================================

op ThrowStatement : NonTerminal = nonTerminal "ThrowStatement"

op Directives_14_18_Throw_Statement : Directives =
 [Header "14.18. The throw Statement",

  Rule {lhs = ThrowStatement,
        rhs = Seq [NT KW_throw, Opt [NT Expression], semicolon]}
  ]

%%% ========================================================================
%%% 14.19. The synchronized Statement
%%% ========================================================================

op SynchronizedStatement : NonTerminal = nonTerminal "SynchronizedStatement"

op Directives_14_19_Synchronized_Statement : Directives =
 [Header "14.19. The synchronized Statement",

  Rule {lhs = SynchronizedStatement,
        rhs = Seq [NT KW_synchronized, left_paren, NT Expression, right_paren, NT Block]}
  ]

%%% ========================================================================
%%% 14.20. The try statement
%%% ========================================================================

op TryStatement         : NonTerminal = nonTerminal "TryStatement"
op Catches              : NonTerminal = nonTerminal "Catches"
op CatchClause          : NonTerminal = nonTerminal "CatchClause"
op CatchFormalParameter : NonTerminal = nonTerminal "CatchFormalParameter"
op CatchType            : NonTerminal = nonTerminal "CatchType"
op Finally              : NonTerminal = nonTerminal "Finally"

op Directives_14_20_Try_Statement : Directives =
 [Header "14.20. The try statement",

  Rule {lhs = TryStatement,
        rhs = Any [Seq [NT KW_try, NT Block, NT Catches],
                   Seq [NT KW_try, NT Block, Opt [NT Catches], NT Finally],
                   NT TryWithResourcesStatement]},

  Rule {lhs = Catches,
        rhs = Any [NT CatchClause,
                   Seq [NT Catches, NT CatchClause]]},

  Rule {lhs = CatchClause,
        rhs = Seq [NT KW_catch, left_paren, NT CatchFormalParameter, right_paren, NT Block]},

  Rule {lhs = CatchFormalParameter,
        rhs = Seq [Opt [NT VariableModifiers], NT CatchType, NT VariableDeclaratorId]},

  Rule {lhs = CatchType,
        rhs = Any [NT ClassType,
                   Seq [NT ClassType, bar, NT ClassType]]},

  Rule {lhs = Finally,
        rhs = Seq [NT KW_finally, NT Block]}
  ]

%%% ========================================================================
%%% 14.20.3. try-with-resources
%%% ========================================================================

op TryWithResourcesStatement : NonTerminal = nonTerminal "TryWithResourcesStatement"
op ResourceSpecification     : NonTerminal = nonTerminal "ResourceSpecification"
op Resources                 : NonTerminal = nonTerminal "Resources"
op Resource                  : NonTerminal = nonTerminal "Resource"

op Directives_14_20_3_Try_With_Resources : Directives =
 [Header "14.20.3. try-with-resources",

  Rule {lhs = TryWithResourcesStatement,
        rhs = Seq [NT KW_try, NT ResourceSpecification, NT Block, Opt [NT Catches], Opt [NT Finally]]},

  Rule {lhs = ResourceSpecification,
        rhs = Seq [left_paren, NT Resources, Opt [comma], right_paren]},

  Rule {lhs = Resources,
        rhs = Any [NT Resource,
                   Seq [NT Resource, semicolon, NT Resources]]},

  Rule {lhs = Resource,
        rhs = Seq [Opt [NT VariableModifiers], NT Type, NT VariableDeclaratorId, equal_sign, NT Expression]}
  ]

%%% ========================================================================
%%% 15.8. Primary Expressions
%%% ========================================================================

op Primary           : NonTerminal = nonTerminal "Primary"
op PrimaryNoNewArray : NonTerminal = nonTerminal "PrimaryNoNewArray"

op Directives_15_8_Primary_Expressions : Directives =
 [Header "15.8. Primary Expressions",

  Rule {lhs = Primary,
        rhs = Any [NT PrimaryNoNewArray,
                   NT ArrayCreationExpression]},

  Rule {lhs = PrimaryNoNewArray,
        rhs = Any [NT Literal,
                   Seq [NT Type, dot, NT KW_class],
                   Seq [NT KW_void, dot, NT KW_class],
                   NT KW_this,
                   Seq [NT ClassName, dot, NT KW_this],
                   Seq [left_paren, NT Expression, right_paren],
                   NT ClassInstanceCreationExpression,
                   NT FieldAccess,
                   NT MethodInvocation,
                   NT ArrayAccess]}
  ]

%%% ========================================================================
%%% 15.9. Class Instance Creation Expressions
%%% ========================================================================

op ClassInstanceCreationExpression : NonTerminal = nonTerminal "ClassInstanceCreationExpression"
op TypeArgumentsOrDiamond          : NonTerminal = nonTerminal "TypeArgumentsOrDiamond"
op ArgumentList                    : NonTerminal = nonTerminal "ArgumentList"

op Directives_15_9_Class_Instance_Creation : Directives =
 [Header "15.9. Class Instance Creation Expressions",

  Rule {lhs = ClassInstanceCreationExpression,
        rhs = Any [Seq [NT KW_new, Opt [NT TypeArguments], NT TypeDeclSpecifier, Opt [NT TypeArgumentsOrDiamond],
                        left_paren, Opt [NT ArgumentList], right_paren, Opt [NT ClassBody]],
                   Seq [NT Primary, dot, NT KW_new, Opt [NT TypeArguments], NT Identifier, Opt [NT TypeArgumentsOrDiamond],
                        left_paren, Opt [NT ArgumentList], right_paren, Opt [NT ClassBody]]]},

  Rule {lhs = TypeArgumentsOrDiamond,
        rhs = Any [NT TypeArguments,
                   Seq [left_angle, right_angle]]},

  Rule {lhs = ArgumentList,
        rhs = Any [NT Expression,
                   Seq [NT ArgumentList, comma, NT Expression]]}
  ]


%%% ========================================================================
%%% 15.10. Array Creation Expressions
%%% ========================================================================

op ArrayCreationExpression : NonTerminal = nonTerminal "ArrayCreationExpression"
op DimExprs                : NonTerminal = nonTerminal "DimExprs"
op DimExpr                 : NonTerminal = nonTerminal "DimExpr"
op Dims                    : NonTerminal = nonTerminal "Dims"

op Directives_15_10_Array_Creation : Directives =
 [Header "15.10. Array Creation Expressions",

  Rule {lhs = ArrayCreationExpression,
        rhs = Any [Seq [NT KW_new, NT PrimitiveType,        NT DimExprs, Opt [NT Dims]],
                   Seq [NT KW_new, NT ClassOrInterfaceType, NT DimExprs, Opt [NT Dims]],
                   Seq [NT KW_new, NT PrimitiveType,        NT Dims, NT ArrayInitializer],
                   Seq [NT KW_new, NT ClassOrInterfaceType, NT Dims, NT ArrayInitializer]]},

  Rule {lhs = DimExprs,
        rhs = Any [NT DimExpr,
                   Seq [NT DimExprs, NT DimExpr]]},

  Rule {lhs = DimExpr,
        rhs = Seq [left_square, NT Expression, right_square]},

  Rule {lhs = Dims,
        rhs = Any [Seq [left_square, right_square],
                   Seq [NT Dims, left_square, right_square]]}

  ]

%%% ========================================================================
%%% 15.11. Field Access Expressions
%%% ========================================================================

op FieldAccess : NonTerminal = nonTerminal "FieldAccess"

op Directives_15_11_Field_Access : Directives =
 [Header "15.11. Field Access Expressions",

  Rule {lhs = FieldAccess,
        rhs = Any [Seq [NT Primary,                  dot, NT Identifier],
                   Seq [                   NT KW_super, dot, NT Identifier],
                   Seq [NT ClassName, dot, NT KW_super, dot, NT Identifier]]}
  ]

%%% ========================================================================
%%% 15.12. Method Invocation Expressions
%%% ========================================================================

op MethodInvocation : NonTerminal = nonTerminal "MethodInvocation"

op Directives_15_12_Method_Invocation : Directives =
 [Header "15.12. Method Invocation Expressions",

  Rule {lhs = MethodInvocation,
        rhs = Any [Seq [NT MethodName, left_paren, Opt [NT ArgumentList], right_paren],
                   Seq [NT Primary, dot, Opt [NT NonWildTypeArguments], NT Identifier,
                        left_paren, Opt [NT ArgumentList], right_paren],
                   Seq [NT KW_super, dot, Opt [NT NonWildTypeArguments], NT Identifier,
                        left_paren, Opt [NT ArgumentList], right_paren],
                   Seq [NT ClassName, dot, NT KW_super, dot, Opt [NT NonWildTypeArguments], NT Identifier,
                        left_paren, Opt [NT ArgumentList], right_paren],
                   Seq [NT TypeName, dot, Opt [NT NonWildTypeArguments], NT Identifier,
                        left_paren, Opt [NT ArgumentList], right_paren]]}

  ]

%%% ========================================================================
%%% 15.13. Array Access Expressions
%%% ========================================================================

op ArrayAccess : NonTerminal = nonTerminal "ArrayAccess"

op Directives_15_13_Array_Access : Directives =
 [Header "15.13. Array Access Expressions",

  Rule {lhs = ArrayAccess,
        rhs = Any [Seq [NT ExpressionName,    left_square, NT Expression, right_square],
                   Seq [NT PrimaryNoNewArray, left_square, NT Expression, right_square]]}
  ]

%%% ========================================================================
%%% 15.14. Postfix Expressions
%%% ========================================================================

op PostfixExpression : NonTerminal = nonTerminal "PostfixExpression"

op Directives_15_14_Postfix : Directives =
 [Header "15.14. Postfix Expressions",

  Rule {lhs = PostfixExpression,
        rhs = Any [NT Primary,
                   NT ExpressionName,
                   NT PostIncrementExpression,
                   NT PostDecrementExpression]}
  ]

%%% ========================================================================
%%% 15.14.2. Postfix Incremement Operator ++
%%% ========================================================================

op PostIncrementExpression : NonTerminal = nonTerminal "PostIncrementExpression"

op Directives_15_14_2_Postfix_Increment : Directives =
 [Header "15.14.2. Postfix Incremement Operator ++",

  Rule {lhs = PostIncrementExpression,
        rhs = Seq [NT PostfixExpression, op_++]}
  ]

%%% ========================================================================
%%% 15.14.3. Postfix Decremement Operator --
%%% ========================================================================

op PostDecrementExpression : NonTerminal = nonTerminal "PostDecrementExpression"

op Directives_15_14_3_Postfix_Decrement : Directives =
 [Header "15.14.3. Postfix Decremement Operator --",

  Rule {lhs = PostDecrementExpression,
        rhs = Seq [NT PostfixExpression, op_--]}
  ]

%%% ========================================================================
%%% 15.15. Unary Operators
%%% ========================================================================

op UnaryExpression             : NonTerminal = nonTerminal "UnaryExpression"
op PreIncrementExpression      : NonTerminal = nonTerminal "PreIncrementExpression"
op PreDecrementExpression      : NonTerminal = nonTerminal "PreDecrementExpression"
op UnaryExpressionNotPlusMinus : NonTerminal = nonTerminal "UnaryExpressionNotPlusMinus"

op Directives_15_15_Unary : Directives =
 [Header "15.15. Unary Operators",

  Rule {lhs = UnaryExpression,
        rhs = Any [NT PreIncrementExpression,
                   NT PreDecrementExpression,
                   Seq [plus,  NT UnaryExpression],
                   Seq [minus, NT UnaryExpression],
                   NT UnaryExpressionNotPlusMinus]},

  Rule {lhs = PreIncrementExpression,
        rhs = Seq [op_++, NT UnaryExpression]},

  Rule {lhs = PreDecrementExpression,
        rhs = Seq [op_--, NT UnaryExpression]},

  Rule {lhs = UnaryExpressionNotPlusMinus,
        rhs = Any [NT PostfixExpression,
                   Seq [tilde,        NT UnaryExpression],
                   Seq [exclamation,  NT UnaryExpression],
                   NT CastExpression]}
  ]

%%% ========================================================================
%%% 15.16. Cast Expressions
%%% ========================================================================

op CastExpression : NonTerminal = nonTerminal "CastExpression"

op Directives_15_16_Cast : Directives =
 [Header "15.16. Cast Expressions",

  Rule {lhs = CastExpression,
        rhs = Any [Seq [left_paren, NT PrimitiveType, right_paren, NT UnaryExpression],
                   Seq [left_paren, NT ReferenceType, right_paren, NT UnaryExpressionNotPlusMinus]]}
  ]

%%% ========================================================================
%%% 15.17. Multiplicative Operators
%%% ========================================================================

op MultiplicativeExpression : NonTerminal = nonTerminal "MultiplicativeExpression"

op Directives_15_17_Multiplicative : Directives =
 [Header "15.17. Multiplicative Operators",

  Rule {lhs = MultiplicativeExpression,
        rhs = Any [NT UnaryExpression,
                   Seq [NT MultiplicativeExpression, star,    NT UnaryExpression],
                   Seq [NT MultiplicativeExpression, slash,   NT UnaryExpression],
                   Seq [NT MultiplicativeExpression, percent, NT UnaryExpression]]}
  ]

%%% ========================================================================
%%% 15.18. Additive Operators
%%% ========================================================================

op AdditiveExpression : NonTerminal = nonTerminal "AdditiveExpression"

op Directives_15_18_Additive : Directives =
 [Header "15.18. Additive Operators",

  Rule {lhs = AdditiveExpression,
        rhs = Any [NT MultiplicativeExpression,
                   Seq [NT AdditiveExpression, plus,  NT MultiplicativeExpression],
                   Seq [NT AdditiveExpression, minus, NT MultiplicativeExpression]]}
  ]

%%% ========================================================================
%%% 15.19. Shift Operators
%%% ========================================================================

op ShiftExpression : NonTerminal = nonTerminal "ShiftExpression"

op Directives_15_19_Shift : Directives =
 [Header "15.19. Shift Operators",

  Rule {lhs = ShiftExpression,
        rhs = Any [NT AdditiveExpression,
                   Seq [NT ShiftExpression, op_<<,  NT AdditiveExpression],
                   Seq [NT ShiftExpression, op_>>,  NT AdditiveExpression],
                   Seq [NT ShiftExpression, op_>>>, NT AdditiveExpression]]}

  ]

%%% ========================================================================
%%% 15.20. Relational Operators
%%% ========================================================================

op RelationalExpression : NonTerminal = nonTerminal "RelationalExpression"

op Directives_15_20_Relational : Directives =
 [Header "15.20. Relational Operators",

  Rule {lhs = RelationalExpression,
        rhs = Any [NT ShiftExpression,
                   Seq [NT RelationalExpression, left_angle,    NT ShiftExpression],
                   Seq [NT RelationalExpression, right_angle,   NT ShiftExpression],
                   Seq [NT RelationalExpression, op_<=,         NT ShiftExpression],
                   Seq [NT RelationalExpression, op_>=,         NT ShiftExpression],
                   Seq [NT RelationalExpression, NT KW_instanceof, NT ReferenceType]]}
  ]

%%% ========================================================================
%%% 15.21. Equality Operators
%%% ========================================================================

op EqualityExpression : NonTerminal = nonTerminal "EqualityExpression"

op Directives_15_21_Equality : Directives =
 [Header "15.21. Equality Operators",

  Rule {lhs = EqualityExpression,
        rhs = Any [NT RelationalExpression,
                   Seq [NT EqualityExpression, op_==, NT RelationalExpression],
                   Seq [NT EqualityExpression, op_!=, NT RelationalExpression]]}
  ]

%%% ========================================================================
%%% 15.22. Bitwise and Logical Operators
%%% ========================================================================

op AndExpression         : NonTerminal = nonTerminal "AndExpression"
op ExclusiveOrExpression : NonTerminal = nonTerminal "ExclusiveOrExpression"
op InclusiveOrExpression : NonTerminal = nonTerminal "InclusiveOrExpression"

op Directives_15_22_Bitwise : Directives =
 [Header "15.22. Bitwise and Logical Operators",

  Rule {lhs = AndExpression,
        rhs = Any [NT EqualityExpression,
                   Seq [NT AndExpression, ampersand, NT EqualityExpression]]},

  Rule {lhs = ExclusiveOrExpression,
        rhs = Any [NT AndExpression,
                   Seq [NT ExclusiveOrExpression, carrot, NT AndExpression]]},

  Rule {lhs = InclusiveOrExpression,
        rhs = Any [NT ExclusiveOrExpression,
                   Seq [NT InclusiveOrExpression, bar, NT ExclusiveOrExpression]]}

  ]

%%% ========================================================================
%%% 15.23. Conditional-And Operator &&
%%% ========================================================================

op ConditionalAndExpression : NonTerminal = nonTerminal "ConditionalAndExpression"

op Directives_15_23_And : Directives =
 [Header "15.23. Conditional-And Operator &&",

  Rule {lhs = ConditionalAndExpression,
        rhs = Any [NT InclusiveOrExpression,
                   Seq [NT ConditionalAndExpression, op_&&, NT InclusiveOrExpression]]}
  ]

%%% ========================================================================
%%% 15.24. Conditional-Or Operator ||
%%% ========================================================================

op ConditionalOrExpression : NonTerminal = nonTerminal "ConditionalOrExpression"

op Directives_15_24_Or : Directives =
 [Header "15.24. Conditional-Or Operator ||",

  Rule {lhs = ConditionalOrExpression,
        rhs = Any [NT ConditionalAndExpression,
                   Seq [NT ConditionalOrExpression, op_||, NT ConditionalAndExpression]]}
  ]

%%% ========================================================================
%%% 15.25. Conditional Operator ? :
%%% ========================================================================

op ConditionalExpression : NonTerminal = nonTerminal "ConditionalExpression"

op Directives_15_25_Conditional : Directives =
 [Header "15.25. Conditional Operator ? :",

  Rule {lhs = ConditionalExpression,
        rhs = Any [NT ConditionalOrExpression,
                   Seq [NT ConditionalOrExpression, question_mark, NT Expression, colon, NT ConditionalExpression]]}
  ]

%%% ========================================================================
%%% 15.26. Assignment Operators
%%% ========================================================================

op AssignmentExpression : NonTerminal = nonTerminal "AssignmentExpression"
op Assignment           : NonTerminal = nonTerminal "Assignment"
op LeftHandSide         : NonTerminal = nonTerminal "LeftHandSide"
op AssignmentOperator   : NonTerminal = nonTerminal "AssignmentOperator"

op Directives_15_26_Assignment : Directives =
 [Header "15.26. Assignment Operators",

  Rule {lhs = AssignmentExpression,
        rhs = Any [NT ConditionalExpression,
                   NT Assignment]},

  Rule {lhs = Assignment,
        rhs = Seq [NT LeftHandSide, NT AssignmentOperator, NT AssignmentExpression]},

  Rule {lhs = LeftHandSide,
        rhs = Any [NT ExpressionName,
                   NT FieldAccess,
                   NT ArrayAccess]},

  Rule {lhs = AssignmentOperator,
        rhs = Any [equal_sign, op_*=, op_/=, op_+=, op_-=, op_<<=, op_<<=, op_>>>=, op_&=, op_^=, op_|=]}

  ]

%%% ========================================================================
%%% 15.27. Expression
%%% ========================================================================

op Expression : NonTerminal = nonTerminal "Expression"

op Directives_15_27_Expression : Directives =
 [Header "15.27. Expression",

  Rule {lhs = Expression,
        rhs = NT AssignmentExpression}

  ]

%%% ========================================================================
%%% 15.28. Constant Expressions
%%% ========================================================================

op ConstantExpression : NonTerminal = nonTerminal "ConstantExpression"

op Directives_15_28_Constant : Directives =
 [Header "15.28. Constant Expressions",

  Rule {lhs = ConstantExpression,
        rhs = NT Expression}  % TODO: many restrictions

  ]

%%% ========================================================================
%%% Misc
%%% ========================================================================

op ClassName      : NonTerminal = nonTerminal "ClassName"
op SimpleTypeName : NonTerminal = nonTerminal "SimpleTypeName"

op Directives_Misc : Directives =
 [Header  "Misc",

  %% ClassName is used but undefined in the spec
  Rule {lhs = ClassName,
        rhs = NT Identifier},

  %% SimpleTypeName is used but undefined in the spec
  %% We resolve it by looking at the grammar supplied in Chapter 18.
  %% (second production in GenericMethodOrConstructorRest)
  Rule {lhs = SimpleTypeName,
        rhs = NT Identifier}
  ]

%%% ========================================================================
%%% Full Grammar
%%% ========================================================================

op Java7ExpositionGrammar : ContextFreeGrammar =
 let directives = Directives_Java_Tokens
                  ++ Directives_4_1_Kinds_Of_Types
                  ++ Directives_4_2_Primitive_Types
                  ++ Directives_4_3_Reference_Types
                  ++ Directives_4_4_Type_Variables
                  ++ Directives_4_5_1_Type_Arguments
                  ++ Directives_6_5_Names
                  ++ Directives_7_3_Compilation_Units
                  ++ Directives_7_4_Package_Declarations
                  ++ Directives_7_5_Import_Declarations
                  ++ Directives_7_5_1_Single_Type_Import
                  ++ Directives_7_5_2_Type_Import_On_Demand
                  ++ Directives_7_5_3_Single_Static_Import
                  ++ Directives_7_5_4_Static_Import_On_Demand
                  ++ Directives_7_6_Type_Declarations
                  ++ Directives_8_1_Class_Declarations
                  ++ Directives_8_1_1_Class_Modifiers
                  ++ Directives_8_1_2_Type_Parameters
                  ++ Directives_8_1_4_Superclasses
                  ++ Directives_8_1_5_Superinterfaces
                  ++ Directives_8_1_6_Class_Body
                  ++ Directives_8_3_Field_Declarations
                  ++ Directives_8_3_1_Field_Modifiers
                  ++ Directives_8_4_Method_Declarations
                  ++ Directives_8_4_1_Formal_Parameters
                  ++ Directives_8_4_3_Method_Modifiers
                  ++ Directives_8_4_5_Method_Result
                  ++ Directives_8_4_6_Method_Throws
                  ++ Directives_8_4_7_Method_Body
                  ++ Directives_8_6_Instance_Initializers
                  ++ Directives_8_7_Static_Initializers
                  ++ Directives_8_8_Constructor_Declarations
                  ++ Directives_8_8_3_Constructor_Modifiers
                  ++ Directives_8_8_7_Constructor_Body
                  ++ Directives_8_8_7_1_Explicit_Constructor_Invocations
                  ++ Directives_8_9_Enums
                  ++ Directives_8_9_1_Enum_Constants
                  ++ Directives_9_1_Interface_Declarations
                  ++ Directives_9_1_1_Interface_Modifiers
                  ++ Directives_9_1_3_Interface_Extends
                  ++ Directives_9_1_4_Interface_Body
                  ++ Directives_9_3_Constant_Field_Declarations
                  ++ Directives_9_4_Abstract_Method_Declarations
                  ++ Directives_9_6_Annotation_Types
                  ++ Directives_9_6_1_Annotation_Type_Elements
                  ++ Directives_9_7_Annotations
                  ++ Directives_9_7_1_Normal_Annotations
                  ++ Directives_9_7_2_Marker_Annotations
                  ++ Directives_9_7_3_Single_Element_Annotations
                  ++ Directives_10_6_Array_Initializers
                  ++ Directives_14_2_Blocks
                  ++ Directives_14_4_Local_Variable_Declaration_Statements
                  ++ Directives_14_5_Statements
                  ++ Directives_14_6_Empty_Statement
                  ++ Directives_14_7_Labeled_Statements
                  ++ Directives_14_8_Expression_Statements
                  ++ Directives_14_9_If_Statement
                  ++ Directives_14_10_Assert_Statement
                  ++ Directives_14_11_Switch_Statement
                  ++ Directives_14_12_While_Statement
                  ++ Directives_14_13_Do_Statement
                  ++ Directives_14_14_For_Statement
                  ++ Directives_14_14_1_Basic_For_Statement
                  ++ Directives_14_14_2_Enhanced_For_Statement
                  ++ Directives_14_15_Break_Statement
                  ++ Directives_14_16_Continue_Statement
                  ++ Directives_14_17_Return_Statement
                  ++ Directives_14_18_Throw_Statement
                  ++ Directives_14_19_Synchronized_Statement
                  ++ Directives_14_20_Try_Statement
                  ++ Directives_14_20_3_Try_With_Resources
                  ++ Directives_15_8_Primary_Expressions
                  ++ Directives_15_9_Class_Instance_Creation
                  ++ Directives_15_10_Array_Creation
                  ++ Directives_15_11_Field_Access
                  ++ Directives_15_12_Method_Invocation
                  ++ Directives_15_13_Array_Access
                  ++ Directives_15_14_Postfix
                  ++ Directives_15_14_2_Postfix_Increment
                  ++ Directives_15_14_3_Postfix_Decrement
                  ++ Directives_15_15_Unary
                  ++ Directives_15_16_Cast
                  ++ Directives_15_17_Multiplicative
                  ++ Directives_15_18_Additive
                  ++ Directives_15_19_Shift
                  ++ Directives_15_20_Relational
                  ++ Directives_15_21_Equality
                  ++ Directives_15_22_Bitwise
                  ++ Directives_15_23_And
                  ++ Directives_15_24_Or
                  ++ Directives_15_25_Conditional
                  ++ Directives_15_26_Assignment
                  ++ Directives_15_27_Expression
                  ++ Directives_15_28_Constant
                  ++ Directives_Misc
 in
 {name          = "Java7ExpositionGrammar",
  documentation = "todo",
  directives    = directives}

end-spec
