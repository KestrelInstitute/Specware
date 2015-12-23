(* Copyright 2015 Kestrel Institute. See file LICENSE.text for license details *)

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

Java7Ref qualifying spec

import Java7Grammars

%%% ========================================================================
%%% Identifiers
%%% ========================================================================

op QualifiedIdentifier     : NonTerminal = nonTerminal "QualifiedIdentifier"
op QualifiedIdentifierList : NonTerminal = nonTerminal "QualifiedIdentifierList"

op Directives_Identifiers : Directives =
 [Header  "Identifiers",

  Rule {lhs = QualifiedIdentifier,
        rhs = Seq [NT Identifier, Rep [dot, NT Identifier]]},

  Rule {lhs = QualifiedIdentifierList,
        rhs = Seq [NT QualifiedIdentifier, Rep [comma, NT QualifiedIdentifier]]}

  ]

%%% ========================================================================
%%% Compilation Unit
%%% ========================================================================

op CompilationUnit             : NonTerminal = nonTerminal "CompilationUnit"
op ImportDeclaration           : NonTerminal = nonTerminal "ImportDeclaration"
op TypeDeclaration             : NonTerminal = nonTerminal "TypeDeclaration"
op ClassOrInterfaceDeclaration : NonTerminal = nonTerminal "ClassOrInterfaceDeclaration"
op ClassDeclaration            : NonTerminal = nonTerminal "ClassDeclaration"
op InterfaceDeclaration        : NonTerminal = nonTerminal "InterfaceDeclaration"
op NormalClassDeclaration      : NonTerminal = nonTerminal "NormalClassDeclaration"
op EnumDeclaration             : NonTerminal = nonTerminal "EnumDeclaration"
op NormalInterfaceDeclaration  : NonTerminal = nonTerminal "NormalInterfaceDeclaration"
op AnnotationTypeDeclaration   : NonTerminal = nonTerminal "AnnotationTypeDeclaration"

op Directives_CompilationUnit : Directives =
 [Header  "Compilation Unit",

  Rule {lhs = CompilationUnit,
        rhs = Seq [Opt [Opt [NT Annotations],
                        NT KW_package,
                        NT QualifiedIdentifier,
                        semicolon],
                   Rep [NT ImportDeclaration],
                   Rep [NT TypeDeclaration]]},

  Rule {lhs = ImportDeclaration,
        rhs = Seq [NT KW_import,
                   Opt [NT KW_static],
                   NT Identifier,
                   Rep [dot, NT Identifier],
                   Opt [dot, star],
                   semicolon]},

  Rule {lhs = TypeDeclaration,
        rhs = Any [NT ClassOrInterfaceDeclaration,
                   semicolon]},

  Rule {lhs = ClassOrInterfaceDeclaration,
        rhs = Seq [Rep [NT Modifier],
                   Any [NT ClassDeclaration,
                        NT InterfaceDeclaration]]},

  Rule {lhs = ClassDeclaration,
        rhs = Any [NT NormalClassDeclaration,
                   NT EnumDeclaration]},

  Rule {lhs = InterfaceDeclaration,
        rhs = Any [NT NormalInterfaceDeclaration,
                   NT AnnotationTypeDeclaration]},

  Rule {lhs = NormalClassDeclaration,
        rhs = Seq [NT KW_class,
                   NT Identifier,
                   Opt [NT TypeParameters],
                   Opt [NT KW_extends,    NT Type],
                   Opt [NT KW_implements, NT TypeList],
                   NT ClassBody]},

  Rule {lhs = EnumDeclaration,
        rhs = Seq [NT KW_enum,
                   NT Identifier,
                   Opt [NT KW_implements, NT TypeList],
                   NT EnumBody]},

  Rule {lhs = NormalInterfaceDeclaration,
        rhs = Seq [NT KW_interface,
                   NT Identifier,
                   Opt [NT TypeParameters],
                   Opt [NT KW_extends, NT TypeList],
                   NT InterfaceBody]},

  Rule {lhs = AnnotationTypeDeclaration,
        rhs = Seq [at_sign,
                   NT KW_interface,
                   NT Identifier,
                   NT AnnotationTypeBody]}
  ]

%%% ========================================================================
%%% Types
%%% ========================================================================

op Type          : NonTerminal = nonTerminal "Type"
op BasicType     : NonTerminal = nonTerminal "BasicType"
op ReferenceType : NonTerminal = nonTerminal "ReferenceType"
op TypeArguments : NonTerminal = nonTerminal "TypeArguments"
op TypeArgument  : NonTerminal = nonTerminal "TypeArgument"

op Directives_Types : Directives =
 [Header "Types",

  Rule {lhs = Type,
        rhs = Any [Seq [NT BasicType,     Rep [left_square, right_square]],
                   Seq [NT ReferenceType, Rep [left_square, right_square]]]},

  Rule {lhs = BasicType,
        rhs = Any [NT KW_byte,
                   NT KW_short,
                   NT KW_char,
                   NT KW_int,
                   NT KW_long,
                   NT KW_float,
                   NT KW_double,
                   NT KW_boolean]},

  Rule {lhs = ReferenceType,
        rhs = Seq [NT Identifier,
                   Opt [NT TypeArguments],
                   Rep [dot, NT Identifier, Opt [NT TypeArguments]]]},

  Rule {lhs = TypeArguments,
        rhs = Seq [left_angle,
                   NT TypeArgument,
                   Rep [comma, NT TypeArgument],
                   right_angle]},

  Rule {lhs = TypeArgument,
        rhs = Any [NT ReferenceType,
                   Seq [question_mark,
                        Opt [Any [NT KW_extends, NT KW_super],
                             NT ReferenceType]]]}
  ]

%%% ========================================================================
%%% Type Arguments
%%% ========================================================================

op NonWildcardTypeArguments          : NonTerminal = nonTerminal "NonWildcardTypeArguments"
op TypeList                          : NonTerminal = nonTerminal "TypeList"
op TypeArgumentsOrDiamond            : NonTerminal = nonTerminal "TypeArgumentsOrDiamond"
op NonWildcardTypeArgumentsOrDiamond : NonTerminal = nonTerminal "NonWildcardTypeArgumentsOrDiamond"
op TypeParameters                    : NonTerminal = nonTerminal "TypeParameters"
op TypeParameter                     : NonTerminal = nonTerminal "TypeParameter"
op Bound                             : NonTerminal = nonTerminal "Bound"

op Directives_TypeArguments : Directives =
 [Header "Type Arguments",

  Rule {lhs = NonWildcardTypeArguments,
        rhs = Seq [left_angle, NT TypeList, right_angle]},

  Rule {lhs = TypeList,
        rhs = Seq [NT ReferenceType, Rep [comma, NT ReferenceType]]},

  Rule {lhs = TypeArgumentsOrDiamond,
        rhs = Any [Seq [left_angle, right_angle],
                   NT TypeArguments]},

  Rule {lhs = NonWildcardTypeArgumentsOrDiamond,
        rhs = Any [Seq [left_angle, right_angle],
                   NT NonWildcardTypeArguments]},

  Rule {lhs = TypeParameters,
        rhs = Seq [left_angle,
                   NT TypeParameter,
                   Rep [comma, NT TypeParameter],
                   right_angle]},

  Rule {lhs = TypeParameter,
        rhs = Seq [NT Identifier,
                   Opt [NT KW_extends, NT Bound]]},

  Rule {lhs = Bound,
        rhs = Seq [NT ReferenceType,
                   Rep [ampersand, NT ReferenceType]]}
  ]

%%% ========================================================================
%%% Modifiers
%%% ========================================================================

op Modifier                     : NonTerminal = nonTerminal "Modifier"
op Annotations                  : NonTerminal = nonTerminal "Annotations"
op Annotation                   : NonTerminal = nonTerminal "Annotation"
op AnnotationElement            : NonTerminal = nonTerminal "AnnotationElement"
op ElementValuePairs            : NonTerminal = nonTerminal "ElementValuePairs"
op ElementValuePair             : NonTerminal = nonTerminal "ElementValuePair"
op ElementValue                 : NonTerminal = nonTerminal "ElementValue"
op ElementValueArrayInitializer : NonTerminal = nonTerminal "ElementValueArrayInitializer"
op ElementValues                : NonTerminal = nonTerminal "ElementValues"

op Directives_Modifiers : Directives =
 [Header "Modifiers",

  Rule {lhs = Modifier,
        rhs = Any [NT Annotation,
                   NT KW_public,
                   NT KW_protected,
                   NT KW_private,
                   NT KW_static,
                   NT KW_abstract,
                   NT KW_final,
                   NT KW_native,
                   NT KW_synchronized,
                   NT KW_transient,
                   NT KW_volatile,
                   NT KW_strictfp]},

  Rule {lhs = Annotations,
        rhs = Seq [NT Annotation, Rep [NT Annotation]]},

  Rule {lhs = Annotation,
        rhs = Seq [at_sign,
                   NT QualifiedIdentifier,
                   Opt [left_paren, Opt [NT AnnotationElement], right_paren]]},

  Rule {lhs = AnnotationElement,
        rhs = Any [NT ElementValuePairs,
                   NT ElementValue]},

  Rule {lhs = ElementValuePairs,
        rhs = Seq [NT ElementValuePair, Rep [comma, NT ElementValuePair]]},

  Rule {lhs = ElementValuePair,
        rhs = Seq [NT Identifier,
                   equal_sign,
                   NT ElementValue]},

  Rule {lhs = ElementValue,
        rhs = Any [NT Annotation,
                   NT Expression1,
                   NT ElementValueArrayInitializer]},

  Rule {lhs = ElementValueArrayInitializer,
        rhs = Seq [left_curly,
                   Opt [NT ElementValues],
                   Opt [comma],
                   right_curly]},

  Rule {lhs = ElementValues,
        rhs = Seq [NT ElementValue, Rep [comma, NT ElementValue]]}

]

%%% ========================================================================
%%% Classes
%%% ========================================================================

op ClassBody                      : NonTerminal = nonTerminal "ClassBody"
op ClassBodyDeclaration           : NonTerminal = nonTerminal "ClassBodyDeclaration"
op MemberDecl                     : NonTerminal = nonTerminal "MemberDecl"
op MethodOrFieldDecl              : NonTerminal = nonTerminal "MethodOrFieldDecl"
op MethodOrFieldRest              : NonTerminal = nonTerminal "MethodOrFieldRest"
op FieldDeclaratorsRest           : NonTerminal = nonTerminal "FieldDeclaratorsRest"
op MethodDeclaratorRest           : NonTerminal = nonTerminal "MethodDeclaratorRest"
op VoidMethodDeclaratorRest       : NonTerminal = nonTerminal "VoidMethodDeclaratorRest"
op ConstructorDeclaratorRest      : NonTerminal = nonTerminal "ConstructorDeclaratorRest"
op GenericMethodOrConstructorDecl : NonTerminal = nonTerminal "GenericMethodOrConstructorDecl"
op GenericMethodOrConstructorRest : NonTerminal = nonTerminal "GenericMethodOrConstructorRest"

op Directives_Classes : Directives =
 [Header "Classes",

  Rule {lhs = ClassBody,
        rhs = Seq [left_curly, Rep [NT ClassBodyDeclaration], right_curly]},

  Rule {lhs = ClassBodyDeclaration,
        rhs = Any [semicolon,
                   Seq [Rep [NT Modifier], NT MemberDecl],
                   Seq [Opt [NT KW_static],   NT Block]]},

  Rule {lhs = MemberDecl,
        rhs = Any [NT MethodOrFieldDecl,
                   Seq [NT KW_void, NT Identifier, NT VoidMethodDeclaratorRest],
                   Seq [NT Identifier, NT ConstructorDeclaratorRest],
                   NT GenericMethodOrConstructorDecl,
                   NT ClassDeclaration,
                   NT InterfaceDeclaration]},

  Rule {lhs = MethodOrFieldDecl,
        rhs = Seq [NT Type, NT Identifier, NT MethodOrFieldRest]},

  Rule {lhs = MethodOrFieldRest,
        rhs = Any [Seq [NT FieldDeclaratorsRest, semicolon],
                   NT MethodDeclaratorRest]},

  Rule {lhs = FieldDeclaratorsRest,
        rhs = Seq [NT VariableDeclaratorRest, Rep [comma, NT VariableDeclarator]]},

  Rule {lhs = MethodDeclaratorRest,
        rhs = Seq [NT FormalParameters,
                   Rep [left_square, right_square],
                   Opt [NT KW_throws, NT QualifiedIdentifierList],
                   Any [NT Block, semicolon]]},

  Rule {lhs = VoidMethodDeclaratorRest,
        rhs = Seq [NT FormalParameters,
                   Opt [NT KW_throws, NT QualifiedIdentifierList],
                   Any [NT Block, semicolon]]},

  Rule {lhs = ConstructorDeclaratorRest,
        rhs = Seq [NT FormalParameters,
                   Opt [NT KW_throws, NT QualifiedIdentifierList],
                   NT Block]},

  Rule {lhs = GenericMethodOrConstructorDecl,
        rhs = Seq [NT TypeParameters, NT GenericMethodOrConstructorRest]},

  Rule {lhs = GenericMethodOrConstructorRest,
        rhs = Any [Seq [Any [NT Type, NT KW_void], NT Identifier, NT MethodDeclaratorRest],
                   Seq [NT Identifier, NT ConstructorDeclaratorRest]]}
  ]

%%% ========================================================================
%%% Interfaces
%%% ========================================================================

op InterfaceBody                     : NonTerminal = nonTerminal "InterfaceBody"
op InterfaceBodyDeclaration          : NonTerminal = nonTerminal "InterfaceBodyDeclaration"
op InterfaceMemberDecl               : NonTerminal = nonTerminal "InterfaceMemberDecl"
op InterfaceMethodOrFieldDecl        : NonTerminal = nonTerminal "InterfaceMethodOrFieldDecl"
op InterfaceMethodOrFieldRest        : NonTerminal = nonTerminal "InterfaceMethodOrFieldRest"
op ConstantDeclaratorsRest           : NonTerminal = nonTerminal "ConstantDeclaratorsRest"
op ConstantDeclaratorRest            : NonTerminal = nonTerminal "ConstantDeclaratorRest"
op ConstantDeclarator                : NonTerminal = nonTerminal "ConstantDeclarator"
op InterfaceMethodDeclaratorRest     : NonTerminal = nonTerminal "InterfaceMethodDeclaratorRest"
op VoidInterfaceMethodDeclaratorRest : NonTerminal = nonTerminal "VoidInterfaceMethodDeclaratorRest"
op InterfaceGenericMethodDecl        : NonTerminal = nonTerminal "InterfaceGenericMethodDecl"

op Directives_Interfaces : Directives =
 [Header "Interfaces",

  Rule {lhs = InterfaceBody,
        rhs = Seq [left_curly, Rep [NT InterfaceBodyDeclaration], right_curly]},

  Rule {lhs = InterfaceBodyDeclaration,
        rhs = Any [semicolon,
                   Seq [Rep [NT Modifier], NT InterfaceMemberDecl]]},

  Rule {lhs = InterfaceMemberDecl,
        rhs = Any [NT InterfaceMethodOrFieldDecl,
                   Seq [NT KW_void, NT Identifier, NT VoidInterfaceMethodDeclaratorRest],
                   NT InterfaceGenericMethodDecl,
                   NT ClassDeclaration,
                   NT InterfaceDeclaration]},

  Rule {lhs = InterfaceMethodOrFieldDecl,
        rhs = Seq [NT Type, NT Identifier, NT InterfaceMethodOrFieldRest]},

  Rule {lhs = InterfaceMethodOrFieldRest,
        rhs = Any [Seq [NT ConstantDeclaratorsRest, semicolon],
                   NT InterfaceMethodDeclaratorRest]},

  Rule {lhs = ConstantDeclaratorsRest,
        rhs = Seq [NT ConstantDeclaratorRest, Rep [comma, NT ConstantDeclarator]]},

  Rule {lhs = ConstantDeclaratorRest,
        rhs = Seq [Rep [left_square, right_square],
                   equal_sign,
                   NT VariableInitializer]},

  Rule {lhs = ConstantDeclarator,
        rhs = Seq [NT Identifier, NT ConstantDeclaratorRest]},

  Rule {lhs = InterfaceMethodDeclaratorRest,
        rhs = Seq [NT FormalParameters,
                   Rep [left_square, right_square],
                   Opt [NT KW_throws, NT QualifiedIdentifierList],
                   semicolon]},

  Rule {lhs = VoidInterfaceMethodDeclaratorRest,
        rhs = Seq [NT FormalParameters,
                   Opt [NT KW_throws, NT QualifiedIdentifierList],
                   semicolon]},

  Rule {lhs = InterfaceGenericMethodDecl,
        rhs = Seq [NT TypeParameters,
                   Any [NT Type, NT KW_void],
                   NT Identifier,
                   NT InterfaceMethodDeclaratorRest]}
  ]

%%% ========================================================================
%%% Parameters
%%% ========================================================================

op FormalParameters         : NonTerminal = nonTerminal "FormalParameters"
op FormalParameterDecls     : NonTerminal = nonTerminal "FormalParameterDecls"
op VariableModifier         : NonTerminal = nonTerminal "VariableModifier"
op FormalParameterDeclsRest : NonTerminal = nonTerminal "FormalParameterDeclsRest"
op VariableDeclaratorId     : NonTerminal = nonTerminal "VariableDeclaratorId"
op VariableDeclarators      : NonTerminal = nonTerminal "VariableDeclarators"
op VariableDeclarator       : NonTerminal = nonTerminal "VariableDeclarator"
op VariableDeclaratorRest   : NonTerminal = nonTerminal "VariableDeclaratorRest"
op VariableInitializer      : NonTerminal = nonTerminal "VariableInitializer"
op ArrayInitializer         : NonTerminal = nonTerminal "ArrayInitializer"

op Directives_Parameters : Directives =
 [Header "Parameters",

  Rule {lhs = FormalParameters,
        rhs = Seq [left_paren, Opt [NT FormalParameterDecls], right_paren]},

  Rule {lhs = FormalParameterDecls,
        rhs = Seq [Rep [NT VariableModifier],
                   NT Type,
                   NT FormalParameterDeclsRest]},

  Rule {lhs = VariableModifier,
        rhs = Any [NT KW_final,
                   NT Annotation]},

  Rule {lhs = FormalParameterDeclsRest,
        rhs = Any [Seq [NT VariableDeclaratorId, Opt [comma, NT FormalParameterDecls]],
                   Seq [NT Ellipses, NT VariableDeclaratorId]]},

  Rule {lhs = VariableDeclaratorId,
        rhs = Seq [NT Identifier, Rep [left_square, right_square]]},

  Rule {lhs = VariableDeclarators,
        rhs = Seq [NT VariableDeclarator, Rep [comma, NT VariableDeclarator]]},

  Rule {lhs = VariableDeclarator,
        rhs = Seq [NT Identifier, NT VariableDeclaratorRest]},

  Rule {lhs = VariableDeclaratorRest,
        rhs = Seq [Rep [left_square, right_square],
                   Opt [equal_sign, NT VariableInitializer]]},

  Rule {lhs = VariableInitializer,
        rhs = Any [NT ArrayInitializer,
                   NT Expression]},

  Rule {lhs = ArrayInitializer,
        rhs = Seq [left_curly,
                   Opt [NT VariableInitializer,
                        Rep [comma, NT VariableInitializer],
                        Opt [comma]],
                   right_curly]}
  ]

%%% ========================================================================
%%% Statements
%%% ========================================================================

op Block                             : NonTerminal = nonTerminal "Block"
op BlockStatements                   : NonTerminal = nonTerminal "BlockStatements"
op BlockStatement                    : NonTerminal = nonTerminal "BlockStatement"
op LocalVariableDeclarationStatement : NonTerminal = nonTerminal "LocalVariableDeclarationStatement"
op Statement                         : NonTerminal = nonTerminal "Statement"
op StatementExpression               : NonTerminal = nonTerminal "StatementExpression"

op Directives_Statements : Directives =
 [Header "Statements",

  Rule {lhs = Block,
        rhs = Seq [left_curly, NT BlockStatements, right_curly]},

  Rule {lhs = BlockStatements,
        rhs = Rep [NT BlockStatement]},

  Rule {lhs = BlockStatement,
        rhs = Any [NT LocalVariableDeclarationStatement,
                   NT ClassOrInterfaceDeclaration,
                   Seq [Opt [NT Identifier, colon],
                        NT Statement]]},

  Rule {lhs = LocalVariableDeclarationStatement,
        rhs = Seq [Rep [NT VariableModifier],
                   NT Type,
                   NT VariableDeclarators,
                   semicolon]},

  Rule {lhs = Statement,
        rhs = Any [NT Block,
                   semicolon,
                   Seq [NT Identifier, colon, NT Statement],
                   Seq [NT StatementExpression, semicolon],
                   Seq [NT KW_if, NT ParExpression, NT Statement, Opt [NT KW_else, NT Statement]],
                   Seq [NT KW_assert, NT Expression, Opt [colon, NT Expression], semicolon],
                   Seq [NT KW_switch, NT ParExpression, left_curly, NT SwitchBlockStatementGroups, right_curly],
                   Seq [NT KW_while,  NT ParExpression, NT Statement],
                   Seq [NT KW_do, NT Statement, NT KW_while, NT ParExpression, semicolon],
                   Seq [NT KW_for, left_paren, NT ForControl, right_paren, NT Statement],
                   Seq [NT KW_break,    Opt [NT Identifier], semicolon],
                   Seq [NT KW_continue, Opt [NT Identifier], semicolon],
                   Seq [NT KW_return,   Opt [NT Expression], semicolon],
                   Seq [NT KW_throw,    NT Expression,       semicolon],
                   Seq [NT KW_synchronized, NT ParExpression, NT Block],
                   Seq [NT KW_try, NT Block, Any [NT Catches, Seq [Opt [NT Catches], NT Finally]]],
                   Seq [NT KW_try, NT ResourceSpecification, NT Block, Opt [NT Catches], Opt [NT Finally]]]},

  Rule {lhs = StatementExpression,
        rhs = NT Expression}

]

%%% ========================================================================
%%% Catches
%%% ========================================================================

op Catches               : NonTerminal = nonTerminal "Catches"
op CatchClause           : NonTerminal = nonTerminal "CatchClause"
op CatchType             : NonTerminal = nonTerminal "CatchType"
op Finally               : NonTerminal = nonTerminal "Finally"
op ResourceSpecification : NonTerminal = nonTerminal "ResourceSpecification"
op Resources             : NonTerminal = nonTerminal "Resources"
op Resource              : NonTerminal = nonTerminal "Resource"

op Directives_Catches : Directives =
 [Header "Catches",

  Rule {lhs = Catches,
        rhs = Seq [NT CatchClause, Rep [NT CatchClause]]},

  Rule {lhs = CatchClause,
        rhs = Seq [NT KW_catch,
                   left_paren,
                   Rep [NT VariableModifier],
                   NT CatchType,
                   NT Identifier,
                   right_paren,
                   NT Block]},

  Rule {lhs = CatchType,
        rhs = Seq [NT QualifiedIdentifier, Rep [bar, NT QualifiedIdentifier]]},

  Rule {lhs = Finally,
        rhs = Seq [NT KW_finally, NT Block]},

  Rule {lhs = ResourceSpecification,
        rhs = Seq [left_paren,
                   NT Resources,
                   Opt [semicolon],
                   right_paren]},

  Rule {lhs = Resources,
        rhs = Seq [NT Resource, Rep [semicolon, NT Resource]]},

  Rule {lhs = Resource,
        rhs = Seq [Rep [NT VariableModifier],
                   NT ReferenceType,
                   NT VariableDeclaratorId,
                   equal_sign,
                   NT Expression]}
  ]

%%% ========================================================================
%%% Switch
%%% ========================================================================

op SwitchBlockStatementGroups : NonTerminal = nonTerminal "SwitchBlockStatementGroups"
op SwitchBlockStatementGroup  : NonTerminal = nonTerminal "SwitchBlockStatementGroup"
op SwitchLabels               : NonTerminal = nonTerminal "SwitchLabels"
op SwitchLabel                : NonTerminal = nonTerminal "SwitchLabel"
op EnumConstantName           : NonTerminal = nonTerminal "EnumConstantName"

op Directives_Switch : Directives =
 [Header "Switch",

  Rule {lhs = SwitchBlockStatementGroups,
        rhs = Seq [left_curly, NT SwitchBlockStatementGroup, right_curly]},

  Rule {lhs = SwitchBlockStatementGroup,
        rhs = Seq [NT SwitchLabels,
                   NT BlockStatements]},

  Rule {lhs = SwitchLabels,
        rhs = Seq [NT SwitchLabel, Rep [NT SwitchLabel]]},

  Rule {lhs = SwitchLabel,
        rhs = Any [Seq [NT KW_case, NT Expression,       colon],
                   Seq [NT KW_case, NT EnumConstantName, colon],
                   Seq [NT KW_default,                   colon]]},

  Rule {lhs = EnumConstantName,
        rhs = NT Identifier}
  ]

%%% ========================================================================
%%% For
%%% ========================================================================

op ForControl                 : NonTerminal = nonTerminal "ForControl"
op ForVarControl              : NonTerminal = nonTerminal "ForVarControl"
op ForVarControlRest          : NonTerminal = nonTerminal "ForVarControlRest"
op ForVariableDeclaratorsRest : NonTerminal = nonTerminal "ForVariableDeclaratorsRest"
op ForInit                    : NonTerminal = nonTerminal "ForInit"
op ForUpdate                  : NonTerminal = nonTerminal "ForUpdate"

op Directives_For : Directives =
 [Header "For",

  Rule {lhs = ForControl,
        rhs = Any [NT ForVarControl,
                   Seq [NT ForInit,
                        semicolon,
                        Opt [NT Expression],
                        semicolon,
                        Opt [NT ForUpdate]]]},

  Rule {lhs = ForVarControl,
        rhs = Seq [Rep [NT VariableModifier],
                   NT Type,
                   NT VariableDeclaratorId,
                   NT ForVarControlRest]},

  Rule {lhs = ForVarControlRest,
        rhs = Any [Seq [NT ForVariableDeclaratorsRest,
                        semicolon,
                        Opt [NT Expression],
                        semicolon,
                        Opt [NT ForUpdate]],
                   Seq [colon,
                        NT Expression]]},

  Rule {lhs = ForVariableDeclaratorsRest,
        rhs = Seq [Opt [equal_sign, NT VariableInitializer],
                   Rep [comma, NT VariableDeclarator]]},

  Rule {lhs = ForInit,
        rhs = Seq [NT StatementExpression, Rep [comma, NT StatementExpression]]},

  Rule {lhs = ForUpdate,
        rhs = Seq [NT StatementExpression, Rep [comma, NT StatementExpression]]}
  ]

%%% ========================================================================
%%% Expression
%%% ========================================================================

op Expression         : NonTerminal = nonTerminal "Expression"
op AssignmentOperator : NonTerminal = nonTerminal "AssignmentOperator"
op Expression1        : NonTerminal = nonTerminal "Expression1"
op Expression1Rest    : NonTerminal = nonTerminal "Expression1Rest"
op Expression2        : NonTerminal = nonTerminal "Expression2"
op Expression2Rest    : NonTerminal = nonTerminal "Expression2Rest"

op Directives_Expression : Directives =
 [Header "Expression",

  Rule {lhs = Expression,
        rhs = Seq [NT Expression1,
                   Opt [NT AssignmentOperator, NT Expression1]]},

  Rule {lhs = AssignmentOperator,
        rhs = Any [equal_sign,
                   op_+=,
                   op_-=,
                   op_*=,
                   op_/=,
                   op_&=,
                   op_|=,
                   op_^=,
                   op_percent_=,
                   op_<<=,
                   op_>>=,
                   op_>>>=]},

  Rule {lhs = Expression1,
        rhs = Seq [NT Expression2, Opt [NT Expression1Rest]]},

  Rule {lhs = Expression1Rest,
        rhs = Seq [question_mark,
                   NT Expression,
                   colon,
                   NT Expression1]},

  Rule {lhs = Expression2,
        rhs = Seq [NT Expression3, Opt [NT Expression2Rest]]},

  Rule {lhs = Expression2Rest,
        rhs = Any [Seq [left_curly, NT InfixOp, NT Expression3, right_curly],
                   Seq [NT KW_instanceof, NT Type]]}
  ]

%%% ========================================================================
%%% Infix
%%% ========================================================================

op InfixOp     : NonTerminal = nonTerminal "InfixOp"
op Expression3 : NonTerminal = nonTerminal "Expression3"
op PrefixOp    : NonTerminal = nonTerminal "PrefixOp"
op PostfixOp   : NonTerminal = nonTerminal "PostfixOp"

op Directives_Infix : Directives =
 [Header "Infix",

  Rule {lhs = InfixOp,
        rhs = Any [op_||,
                   op_&&,
                   bar,
                   carrot,
                   op_==,
                   op_!=,
                   left_angle,
                   right_angle,
                   op_<=,
                   op_>=,
                   op_<<,
                   op_>>,
                   op_>>>,
                   plus,
                   minus,
                   star,
                   slash,
                   percent]},

  Rule {lhs = Expression3,
        rhs = Any [Seq [NT PrefixOp, NT Expression3],
                   Seq [left_paren, Any [NT Expression, NT Type], right_paren, NT Expression3],
                   Seq [NT Primary, Rep [NT Selector], Rep [NT PostfixOp]]]},

  Rule {lhs = PrefixOp,
        rhs = Any [op_++,
                   op_--,
                   exclamation,
                   tilde,
                   plus,
                   minus]},

  Rule {lhs = PostfixOp,
        rhs = Any [op_++,
                   op_--]}
  ]

%%% ========================================================================
%%% Primary
%%% ========================================================================

op Primary                         : NonTerminal = nonTerminal "Primary"
op ParExpression                   : NonTerminal = nonTerminal "ParExpression"
op Arguments                       : NonTerminal = nonTerminal "Arguments"
op SuperSuffix                     : NonTerminal = nonTerminal "SuperSuffix"
op ExplicitGenericInvocationSuffix : NonTerminal = nonTerminal "ExplicitGenericInvocationSuffix"

op Directives_Primary : Directives =
 [Header "Primary",

  Rule {lhs = Primary,
        rhs = Any [NT Literal,
                   NT ParExpression,
                   Seq [NT KW_this,  Opt [NT Arguments]],
                   Seq [NT KW_super, NT SuperSuffix],
                   Seq [NT KW_new,   NT Creator],
                   Seq [NT NonWildcardTypeArguments,
                        Any [NT ExplicitGenericInvocationSuffix,
                             Seq [NT KW_this, NT Arguments]]],
                   Seq [NT Identifier, Rep [dot, NT Identifier],
                        Opt [NT IdentifierSuffix]],
                   Seq [NT BasicType, Rep [left_square, right_square], dot, NT KW_class],
                   Seq [NT KW_void, dot, NT KW_class]]},

  Rule {lhs = ParExpression,
        rhs = Seq [left_paren, NT Expression, right_paren]},

  Rule {lhs = Arguments,
        rhs = Seq [left_paren,
                   Opt [NT Expression, Rep [comma, NT Expression]],
                   right_paren]},

  Rule {lhs = SuperSuffix,
        rhs = Any [NT Arguments,
                   Seq [dot, NT Identifier, Opt [NT Arguments]]]},

  Rule {lhs = ExplicitGenericInvocationSuffix,
        rhs = Any [Seq [NT KW_super, NT SuperSuffix],
                   Seq [NT Identifier, NT Arguments]]}

  ]

%%% ========================================================================
%%% Literals
%%% ========================================================================

%%% ========================================================================
%%% Creator
%%% ========================================================================

op Creator                   : NonTerminal = nonTerminal "Creator"
op CreatedName               : NonTerminal = nonTerminal "CreatedName"
op ClassCreatorRest          : NonTerminal = nonTerminal "ClassCreatorRest"
op ArrayCreatorRest          : NonTerminal = nonTerminal "ArrayCreatorRest"
op IdentifierSuffix          : NonTerminal = nonTerminal "IdentifierSuffix"
op ExplicitGenericInvocation : NonTerminal = nonTerminal "ExplicitGenericInvocation"
op InnerCreator              : NonTerminal = nonTerminal "InnerCreator"
op Selector                  : NonTerminal = nonTerminal "Selector"

op Directives_Creator : Directives =
 [Header "Creator",

  Rule {lhs = Creator,
        rhs = Any [Seq [NT NonWildcardTypeArguments,
                        NT CreatedName,
                        NT ClassCreatorRest],
                   Seq [NT CreatedName,
                        Any [NT ClassCreatorRest, NT ArrayCreatorRest]]]},

  Rule {lhs = CreatedName,
        rhs = Seq [NT Identifier,
                   Opt [NT TypeArgumentsOrDiamond],
                   Rep [dot, NT Identifier, Opt [NT TypeArgumentsOrDiamond]]]},


  Rule {lhs = ClassCreatorRest,
        rhs = Seq [NT Arguments, Opt [NT ClassBody]]},

  Rule {lhs = ArrayCreatorRest,
        rhs = Seq [left_square,
                   Any [Seq [right_square,
                             Rep [left_square, right_square],
                             NT ArrayInitializer],
                        Seq [NT Expression,
                             right_square]],
                   Rep [left_square, NT Expression, right_square],
                   Rep [left_square, right_square]]},

  Rule {lhs = IdentifierSuffix,
        rhs = Any [Seq [left_square,
                        Any [Seq [Rep [left_square, right_square], dot, NT KW_class],
                             NT Expression],
                        right_square],
                   NT Arguments,
                   Seq [dot, Any [NT KW_class,
                                  NT ExplicitGenericInvocation,
                                  NT KW_this,
                                  Seq [NT KW_super, NT Arguments],
                                  Seq [NT KW_new, Opt [NT NonWildcardTypeArguments],
                                       NT InnerCreator]]]]},

  Rule {lhs = ExplicitGenericInvocation,
        rhs = Seq [NT NonWildcardTypeArguments,
                   NT ExplicitGenericInvocationSuffix]},

  Rule {lhs = InnerCreator,
        rhs = Seq [NT Identifier,
                   Opt [NT NonWildcardTypeArgumentsOrDiamond],
                   NT ClassCreatorRest]},

  Rule {lhs = Selector,
        rhs = Any [Seq [dot, NT Identifier, Opt [NT Arguments]],
                   Seq [dot, NT ExplicitGenericInvocation],
                   Seq [dot, NT KW_this],
                   Seq [dot, NT KW_super, NT SuperSuffix],
                   Seq [dot, NT KW_new, Opt [NT NonWildcardTypeArguments], NT InnerCreator],
                   Seq [left_square, NT Expression, right_square]]}
  ]


%%% ========================================================================
%%% Enum
%%% ========================================================================

op EnumBody             : NonTerminal = nonTerminal "EnumBody"
op EnumConstants        : NonTerminal = nonTerminal "EnumConstants"
op EnumConstant         : NonTerminal = nonTerminal "EnumConstant"
op EnumBodyDeclarations : NonTerminal = nonTerminal "EnumBodyDeclarations"

op Directives_Enum : Directives =
 [Header "Enum",

  Rule {lhs = EnumBody,
        rhs = Seq [left_curly,
                   Opt [NT EnumConstants],
                   Opt [comma],
                   Opt [NT EnumBodyDeclarations],
                   right_curly]},

  Rule {lhs = EnumConstants,
        rhs = Any [NT EnumConstant,
                   Seq [NT EnumConstants, comma, NT EnumConstant]]},

  Rule {lhs = EnumConstant,
        rhs = Seq [Opt [NT Annotations],
                   NT Identifier,
                   Opt [NT Arguments],
                   Opt [NT ClassBody]]},

  Rule {lhs = EnumBodyDeclarations,
        rhs = Seq [semicolon,
                   Rep [NT ClassBodyDeclaration]]}
  ]

%%% ========================================================================
%%% Annotation
%%% ========================================================================

op AnnotationTypeBody                : NonTerminal = nonTerminal "AnnotationTypeBody"
op AnnotationTypeElementDeclarations : NonTerminal = nonTerminal "AnnotationTypeElementDeclarations"
op AnnotationTypeElementDeclaration  : NonTerminal = nonTerminal "AnnotationTypeElementDeclaration"
op AnnotationTypeElementRest         : NonTerminal = nonTerminal "AnnotationTypeElementRest"
op AnnotationMethodOrConstantRest    : NonTerminal = nonTerminal "AnnotationMethodOrConstantRest"
op AnnotationMethodRest              : NonTerminal = nonTerminal "AnnotationMethodRest"

op Directives_Annotation : Directives =
 [Header "Annotation",

  Rule {lhs = AnnotationTypeBody,
        rhs = Seq [left_curly,
                   Rep [NT AnnotationTypeElementDeclarations],
                   right_curly]},

  Rule {lhs = AnnotationTypeElementDeclarations,
        rhs = Any [NT AnnotationTypeElementDeclaration,
                   Seq [NT AnnotationTypeElementDeclarations,
                        NT AnnotationTypeElementDeclaration]]},

  Rule {lhs = AnnotationTypeElementDeclaration,
        rhs = Seq [Rep [NT Modifier],
                   NT AnnotationTypeElementRest]},

  Rule {lhs = AnnotationTypeElementRest,
        rhs = Any [Seq [NT Type, NT Identifier, NT AnnotationMethodOrConstantRest],
                   NT ClassDeclaration,
                   NT InterfaceDeclaration,
                   NT EnumDeclaration,
                   NT AnnotationTypeDeclaration]},

  Rule {lhs = AnnotationMethodOrConstantRest,
        rhs = Any [NT AnnotationMethodRest,
                   NT ConstantDeclaratorsRest]},

  Rule {lhs = AnnotationMethodRest,
        rhs = Seq [left_paren,
                   right_paren,
                   Rep [left_square, right_square],
                   Opt [NT KW_default, NT ElementValue]]}
 ]

%%% ========================================================================
%%% Full grammar
%%% ========================================================================

op Java7ReferenceGrammar : ContextFreeGrammar =
 let directives = Directives_Java_Tokens
                  ++ Directives_Identifiers
                  ++ Directives_CompilationUnit
                  ++ Directives_Types
                  ++ Directives_TypeArguments
                  ++ Directives_Modifiers
                  ++ Directives_Classes
                  ++ Directives_Interfaces
                  ++ Directives_Parameters
                  ++ Directives_Statements
                  ++ Directives_Catches
                  ++ Directives_Switch
                  ++ Directives_For
                  ++ Directives_Expression
                  ++ Directives_Infix
                  ++ Directives_Primary
                  ++ Directives_Creator
                  ++ Directives_Enum
                  ++ Directives_Annotation
 in
 {name          = "Java7ReferenceGrammar",
  documentation = "todo",
  directives    = directives}

end-spec
