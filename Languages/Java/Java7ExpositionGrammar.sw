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

type Java7Exp.RHS        = Java7.RHS        Java7Exp.NonTerminal
type Java7Exp.Rule       = Java7.Rule       Java7Exp.NonTerminal
type Java7Exp.Directive  = Java7.Directive  Java7Exp.NonTerminal
type Java7Exp.Directives = Java7.Directives Java7Exp.NonTerminal
type Java7Exp.Grammar    = Java7.Grammar    Java7Exp.NonTerminal

%%% ========================================================================
%%% NonTerminals
%%% ========================================================================

type NonTerminal =

   %%% ========================================================================
   %%% 3.3 Unicode Escapes
   %%% ========================================================================

   | UnicodeInputCharacter
   | UnicodeEscape
   | UnicodeMarker
   | RawInputCharacter
   | HexDigit

   %%% ========================================================================
   %%% 3.4. Line Terminators
   %%% ========================================================================

   | LineTerminator
   | InputCharacter

   %%% ========================================================================
   %%% 3.5. Input Elements and Tokens
   %%% ========================================================================

   | Input
   | InputElements
   | InputElement
   | Token

   %%% ========================================================================
   %%% 3.6. White Space
   %%% ========================================================================

   | WhiteSpace

   %%% ========================================================================
   %%% 3.7. Comments
   %%% ========================================================================

   | Comment
   | TraditionalComment
   | EndOfLineComment
   | CommentTail
   | CommentTailStar
   | NotStar
   | NotStarNotSlash
   | CharactersInLine

   %%% ========================================================================
   %%% 3.8. Identifiers
   %%% ========================================================================

   | Identifier
   | IdentifierChars
   | JavaLetter
   | JavaLetterOrDigit

   %%% ========================================================================
   %%% 3.9. Keywords
   %%% ========================================================================

   | Keyword
   | KW_abstract
   | KW_assert
   | KW_boolean
   | KW_break
   | KW_byte
   | KW_case
   | KW_catch
   | KW_char
   | KW_class
   | KW_const
   | KW_continue
   | KW_default
   | KW_do
   | KW_double
   | KW_else
   | KW_enum
   | KW_extends
   | KW_final
   | KW_finally
   | KW_float
   | KW_for
   | KW_if
   | KW_goto
   | KW_implements
   | KW_import
   | KW_instanceof
   | KW_int
   | KW_interface
   | KW_long
   | KW_native
   | KW_new
   | KW_package
   | KW_private
   | KW_protected
   | KW_public
   | KW_return
   | KW_short
   | KW_static
   | KW_strictfp
   | KW_super
   | KW_switch
   | KW_synchronized
   | KW_this
   | KW_throw
   | KW_throws
   | KW_transient
   | KW_try
   | KW_void
   | KW_volatile
   | KW_while

   %%% ========================================================================
   %%% Misc Keywwords
   %%% ========================================================================

   | Ellipses

   %%% ========================================================================
   %%% 3.10. Literals
   %%% ========================================================================

   | Literal

   %%% ========================================================================
   %%% 3.10.1 Integer Literals
   %%% ========================================================================

   | IntegerLiteral
   | DecimalIntegerLiteral
   | HexIntegerLiteral
   | OctalIntegerLiteral
   | BinaryIntegerLiteral
   | IntegerTypeSuffix
   % --
   | DecimalNumeral
   | Digits
   | Digit
   | NonZeroDigit
   | DigitsAndUnderscores
   | DigitOrUnderscore
   | Underscores
   % --
   | HexNumeral
   | HexDigits
   | HexDigitsAndUnderscores
   | HexDigitOrUnderscore
   % --
   | OctalNumeral
   | OctalDigits
   | OctalDigit
   | OctalDigitsAndUnderscores
   | OctalDigitOrUnderscore
   % --
   | BinaryNumeral
   | BinaryDigits
   | BinaryDigit
   | BinaryDigitsAndUnderscores
   | BinaryDigitOrUnderscore

   %%% ========================================================================
   %%% 3.10.2 Floating-Point Literals
   %%% ========================================================================

   | FloatingPointLiteral
   | DecimalFloatingPointLiteral
   | ExponentPart
   | ExponentIndicator
   | SignedInteger
   | Sign
   | FloatTypeSuffix
   % --
   | HexadecimalFloatingPointLiteral
   | HexSignificand
   | BinaryExponent
   | BinaryExponentIndicator

   %%% ========================================================================
   %%% 3.10.3 Boolean Literals
   %%% ========================================================================

   | BooleanLiteral

   %%% ========================================================================
   %%% 3.10.4 Character Literals
   %%% ========================================================================

   | CharacterLiteral
   | SingleCharacter

   %%% ========================================================================
   %%% 3.10.5. String Literals
   %%% ========================================================================

   | StringLiteral
   | StringCharacters
   | StringCharacter

   %%% ========================================================================
   %%% 3.10.6. Escape Sequences for Character and String Literals
   %%% ========================================================================

   | EscapeSequence
   | OctalEscape

   %%% ========================================================================
   %%% OctalDigit           % identical definitions in [3.10.1] and [3.10.6]
   %%% ========================================================================

   | ZeroToThree

   %%% ========================================================================
   %%% 3.10.7. The Null Literal
   %%% ========================================================================

   | NullLiteral

   %%% ========================================================================
   %%% 3.11. Separators
   %%% ========================================================================

   | Separator

   %%% ========================================================================
   %%% 3.12. Operators
   %%% ========================================================================

   | Operator

   %%% ========================================================================
   %%% 4.1. The Kinds of Types and Values
   %%% ========================================================================

   | Type

   %%% ========================================================================
   %%% 4.2. Primitive Types and Values
   %%% ========================================================================

   | PrimitiveType
   | NumericType
   | IntegralType
   | FloatingPointType

   %%% ========================================================================
   %%% 4.3. Reference Types and Values
   %%% ========================================================================

   | ReferenceType
   | ClassOrInterfaceType
   | ClassType
   | InterfaceType
   | TypeDeclSpecifier
   | TypeNameNoPackage    % TypeName in [4.3] conflicts with a different TypeName in [6.5]
   | TypeVariable
   | ArrayType

   %%% ========================================================================
   %%% 4.4. Type Variables
   %%% ========================================================================

   | TypeParameter
   | TypeBound
   | AdditionalBoundList
   | AdditionalBound

   %%% ========================================================================
   %%% 4.5.1. Type Arguments and WildCards
   %%% ========================================================================

   | TypeArguments
   | TypeArgumentList
   | TypeArgument
   | Wildcard
   | WildcardBounds

   %%% ========================================================================
   %%%  6.5. -- Determining the Meaning of a Name
   %%% ========================================================================

   | PackageName
   | TypeName            % definintion in [6.5] overrides conflicting definition in [4.3]
   | ExpressionName
   | MethodName
   | PackageOrTypeName
   | AmbiguousName

   %%% ========================================================================
   %%%  7.3. Compilation Units
   %%% ========================================================================

   | CompilationUnit
   | ImportDeclarations
   | TypeDeclarations

   %%% ========================================================================
   %%%  7.4. Package Declarations
   %%% ========================================================================

   | PackageDeclaration

   %%% ========================================================================
   %%%  7.5. Import Declarations
   %%% ========================================================================

   | ImportDeclaration

   %%% ========================================================================
   %%%  7.5.1. Single-Type-Import Declarations
   %%% ========================================================================

   | SingleTypeImportDeclaration

   %%% ========================================================================
   %%%  7.5.2. Type-Import-on-Demand Declarations
   %%% ========================================================================

   | TypeImportOnDemandDeclaration

   %%% ========================================================================
   %%%  7.5.3. Single-Static-Import Declarations
   %%% ========================================================================

   | SingleStaticImportDeclaration

   %%% ========================================================================
   %%%  7.5.4. Static-Import-on-Demand Declarations
   %%% ========================================================================

   | StaticImportOnDemandDeclaration

   %%% ========================================================================
   %%%  7.6. -- Top Level Type Declarations
   %%% ========================================================================

   | TypeDeclaration

   %%% ========================================================================
   %%%  8.1. Class Declarations
   %%% ========================================================================

   | ClassDeclaration
   | NormalClassDeclaration

   %%% ========================================================================
   %%%  8.1.1. Class Modifiers
   %%% ========================================================================

   | ClassModifiers
   | ClassModifier

   %%% ========================================================================
   %%%  8.1.2. Gneric Classes and Type Parameters
   %%% ========================================================================

   | TypeParameters
   | TypeParameterList

   %%% ========================================================================
   %%%  8.1.4. Superclasses and Subclasses
   %%% ========================================================================

   | Super

   %%% ========================================================================
   %%%  8.1.5. Superinterfaces
   %%% ========================================================================

   | Interfaces
   | InterfaceTypeList

   %%% ========================================================================
   %%%  8.1.6. Class Body and Member Declarations
   %%% ========================================================================

   | ClassBody
   | ClassBodyDeclarations
   | ClassBodyDeclaration
   | ClassMemberDeclaration

   %%% ========================================================================
   %%%  8.3. Field Declarations
   %%% ========================================================================

   | FieldDeclaration
   | VariableDeclarators
   | VariableDeclarator
   | VariableDeclaratorId
   | VariableInitializer

   %%% ========================================================================
   %%%  8.3.1. Field Modifiers
   %%% ========================================================================

   | FieldModifiers
   | FieldModifier

   %%% ========================================================================
   %%%  8.4. Method Declarations
   %%% ========================================================================

   | MethodDeclaration
   | MethodHeader
   | MethodDeclarator

   %%% ========================================================================
   %%%  8.4.1. Formal Parameters
   %%% ========================================================================

   | FormalParameterList
   | FormalParameters
   | FormalParameter
   | VariableModifiers
   | VariableModifier
   | LastFormalParameter

   %%% ========================================================================
   %%%  8.4.3. Method Modifiers
   %%% ========================================================================

   | MethodModifiers
   | MethodModifier

   %%% ========================================================================
   %%%  8.4.5. Method Return Type
   %%% ========================================================================

   | Result

   %%% ========================================================================
   %%%  8.4.6. Method Throws
   %%% ========================================================================

   | Throws
   | ExceptionTypeList
   | ExceptionType

   %%% ========================================================================
   %%%  8.4.7. Method Body
   %%% ========================================================================

   | MethodBody

   %%% ========================================================================
   %%%  8.6. Instance Initializers
   %%% ========================================================================

   | InstanceInitializer

   %%% ========================================================================
   %%%  8.7. Static Initializers
   %%% ========================================================================

   | StaticInitializer

   %%% ========================================================================
   %%%  8.8. Constructor Declarations
   %%% ========================================================================

   | ConstructorDeclaration
   | ConstructorDeclarator

   %%% ========================================================================
   %%%  8.8.3. Constructor Modifiers
   %%% ========================================================================

   | ConstructorModifiers
   | ConstructorModifier

   %%% ========================================================================
   %%%  8.8.7. Constructor Modifiers
   %%% ========================================================================

   | ConstructorBody

   %%% ========================================================================
   %%%  8.8.7.1. Explicit Constructor Invocations
   %%% ========================================================================

   | ExplicitConstructorInvocation
   | NonWildTypeArguments
   | ReferenceTypeList

   %%% ========================================================================
   %%%  8.9. Enums
   %%% ========================================================================

   | EnumDeclaration
   | EnumBody

   %%% ========================================================================
   %%%  8.9.1. Enum Constants
   %%% ========================================================================

   | EnumConstants
   | EnumConstant
   | Arguments
   | EnumBodyDeclarations

   %%% ========================================================================
   %%% 9.1. Interface Declarations
   %%% ========================================================================

   | InterfaceDeclaration
   | NormalInterfaceDeclaration

   %%% ========================================================================
   %%% 9.1.1. Interface Modifiers
   %%% ========================================================================

   | InterfaceModifiers
   | InterfaceModifier

   %%% ========================================================================
   %%% 9.1.3. Superinterfaces and Subinterfaces
   %%% ========================================================================

   | ExtendsInterfaces

   %%% ========================================================================
   %%% 9.1.4. Interface Body and Member Declarations
   %%% ========================================================================

   | InterfaceBody
   | InterfaceMemberDeclarations
   | InterfaceMemberDeclaration

   %%% ========================================================================
   %%% 9.3. Field (Constant) Declarations
   %%% ========================================================================

   | ConstantDeclaration
   | ConstantModifiers
   | ConstantModifier

   %%% ========================================================================
   %%% 9.4. Abstract Mehtod Declarations
   %%% ========================================================================

   | AbstractMethodDeclaration
   | AbstractMethodModifiers
   | AbstractMethodModifier

   %%% ========================================================================
   %%% 9.6. Annotation Types
   %%% ========================================================================

   | AnnotationTypeDeclaration
   | AnnotationTypeBody
   | AnnotationTypeElementDeclarations

   %%% ========================================================================
   %%% 9.6.1. Annotation Type Elements
   %%% ========================================================================

   | AnnotationTypeElementDeclaration
   | DefaultValue

   %%% ========================================================================
   %%% 9.7. Annotations
   %%% ========================================================================

   | Annotations
   | Annotation

   %%% ========================================================================
   %%% 9.7.1. Normal Annotations
   %%% ========================================================================

   | NormalAnnotation
   | ElementValuePairs
   | ElementValuePair
   | ElementValue
   | ElementValueArrayInitializer
   | ElementValues

   %%% ========================================================================
   %%% 9.7.2. Marker Annotations
   %%% ========================================================================

   | MarkerAnnotation

   %%% ========================================================================
   %%% 9.7.3. Single-Element Annotations
   %%% ========================================================================

   | SingleElementAnnotation

   %%% ========================================================================
   %%% 10.6. Array Initializers
   %%% ========================================================================

   | ArrayInitializer
   | VariableInitializers

   %%% ========================================================================
   %%% 14.2. Blocks
   %%% ========================================================================

   | Block
   | BlockStatements
   | BlockStatement

   %%% ========================================================================
   %%% 14.4. Local Variable Declaration Statements
   %%% ========================================================================

   | LocalVariableDeclarationStatement
   | LocalVariableDeclaration

   %%% ========================================================================
   %%% 14.5. Statements
   %%% ========================================================================

   | Statement
   | StatementWithoutTrailingSubstatement
   | StatementNoShortIf

   %%% ========================================================================
   %%% 14.6. The Empty Statement
   %%% ========================================================================

   | EmptyStatement

   %%% ========================================================================
   %%% 14.7. Labeled Statements
   %%% ========================================================================

   | LabeledStatement
   | LabeledStatementNoShortIf

   %%% ========================================================================
   %%% 14.8. Expression Statements
   %%% ========================================================================

   | ExpressionStatement
   | StatementExpression

   %%% ========================================================================
   %%% 14.9. The if Statement
   %%% ========================================================================

   | IfThenStatement
   | IfThenElseStatement
   | IfThenElseStatementNoShortIf

   %%% ========================================================================
   %%% 14.10. The assert Statement
   %%% ========================================================================

   | AssertStatement
   | Expression1     % TODO: just Expression ?
   | Expression2     % TODO: just Expression ?

   %%% ========================================================================
   %%% 14.11. The switch Statement
   %%% ========================================================================

   | SwitchStatement
   | SwitchBlock
   | SwitchBlockStatementGroups
   | SwitchBlockStatementGroup
   | SwitchLabels
   | SwitchLabel
   | EnumConstantName

   %%% ========================================================================
   %%% 14.12. The while Statement
   %%% ========================================================================

   | WhileStatement
   | WhileStatementNoShortIf

   %%% ========================================================================
   %%% 14.13. The do Statement
   %%% ========================================================================

   | DoStatement

   %%% ========================================================================
   %%% 14.14. The for Statement
   %%% ========================================================================

   | ForStatement

   %%% ========================================================================
   %%% 14.14.1. The basic for Statement
   %%% ========================================================================

   | BasicForStatement
   | ForStatementNoShortIf
   | ForInit
   | ForUpdate
   | StatementExpressionList

   %%% ========================================================================
   %%% 14.14.2. The enhanced for statement
   %%% ========================================================================

   | EnhancedForStatement

   %%% ========================================================================
   %%% 14.15. The break Statement
   %%% ========================================================================

   | BreakStatement

   %%% ========================================================================
   %%% 14.16. The continue Statement
   %%% ========================================================================

   | ContinueStatement

   %%% ========================================================================
   %%% 14.17. The return Statement
   %%% ========================================================================

   | ReturnStatement

   %%% ========================================================================
   %%% 14.18. The throw Statement
   %%% ========================================================================

   | ThrowStatement

   %%% ========================================================================
   %%% 14.19. The synchronized Statement
   %%% ========================================================================

   | SynchronizedStatement

   %%% ========================================================================
   %%% 14.20. The try statement
   %%% ========================================================================

   | TryStatement
   | Catches
   | CatchClause
   | CatchClause
   | CatchFormalParameter
   | CatchType
   | Finally

   %%% ========================================================================
   %%% 14.20.3. try-with-resources
   %%% ========================================================================

   | TryWithResourcesStatement
   | ResourceSpecification
   | Resources
   | Resource

   %%% ========================================================================
   %%% 15.8. Primary Expressions
   %%% ========================================================================

   | Primary
   | PrimaryNoNewArray

   %%% ========================================================================
   %%% 15.9. Class Instance Creation Expressions
   %%% ========================================================================

   | ClassInstanceCreationExpression
   | TypeArgumentsOrDiamond
   | ArgumentList

   %%% ========================================================================
   %%% 15.10. Array Creation Expressions
   %%% ========================================================================

   | ArrayCreationExpression
   | DimExprs
   | DimExpr
   | Dims

   %%% ========================================================================
   %%% 15.11. Field Access Expressions
   %%% ========================================================================

   | FieldAccess

   %%% ========================================================================
   %%% 15.12. Method Invocation Expressions
   %%% ========================================================================

   | MethodInvocation

   %%% ========================================================================
   %%% 15.13. Array Access Expressions
   %%% ========================================================================

   | ArrayAccess

   %%% ========================================================================
   %%% 15.14. Postfix Expressions
   %%% ========================================================================

   | PostfixExpression

   %%% ========================================================================
   %%% 15.14.2. Postfix Incremement Operator ++
   %%% ========================================================================

   | PostIncrementExpression

   %%% ========================================================================
   %%% 15.14.3. Postfix Decremement Operator --
   %%% ========================================================================

   | PostDecrementExpression

   %%% ========================================================================
   %%% 15.15. Unary Operators
   %%% ========================================================================

   | UnaryExpression
   | PreIncrementExpression
   | PreDecrementExpression
   | UnaryExpressionNotPlusMinus

   %%% ========================================================================
   %%% 15.16. Cast Expressions
   %%% ========================================================================

   | CastExpression

   %%% ========================================================================
   %%% 15.17. Multiplicative Operators
   %%% ========================================================================

   | MultiplicativeExpression

   %%% ========================================================================
   %%% 15.18. Additive Operators
   %%% ========================================================================

   | AdditiveExpression

   %%% ========================================================================
   %%% 15.19. Shift Operators
   %%% ========================================================================

   | ShiftExpression

   %%% ========================================================================
   %%% 15.20. Relational Operators
   %%% ========================================================================

   | RelationalExpression

   %%% ========================================================================
   %%% 15.21. Equality Operators
   %%% ========================================================================

   | EqualityExpression

   %%% ========================================================================
   %%% 15.22. Bitwise and Logical Operators
   %%% ========================================================================

   | AndExpression
   | ExclusiveOrExpression
   | InclusiveOrExpression

   %%% ========================================================================
   %%% 15.23. Conditional-And Operator &&
   %%% ========================================================================

   | ConditionalAndExpression

   %%% ========================================================================
   %%% 15.24. Conditional-Or Operator ||
   %%% ========================================================================

   | ConditionalOrExpression

   %%% ========================================================================
   %%% 15.25. Conditional Operator ? :
   %%% ========================================================================

   | ConditionalExpression

   %%% ========================================================================
   %%% 15.26. Assignment Operators
   %%% ========================================================================

   | AssignmentExpression
   | Assignment
   | LeftHandSide
   | AssignmentOperator

   %%% ========================================================================
   %%% 15.27. Expression
   %%% ========================================================================

   | Expression

   %%% ========================================================================
   %%% 15.28. Constant Expressions
   %%% ========================================================================

   | ConstantExpression

   %%% ========================================================================
   %%% Misc
   %%% ========================================================================

   | ClassName
   | SimpleTypeName

%%% ========================================================================
%%% Ad Hoc Keywords
%%% ========================================================================

op Directives_Ad_Hoc_Keywords : Directives =
 [Header  "Ad_Hoc_Keywords",

  Rule {lhs = Ellipses,
        rhs = Seq [dot, dot, dot]}
  ]

%%% ========================================================================
%%% 3.3 Unicode Escapes
%%% ========================================================================

op Directives_3_3 : Directives =
 [Header  "3.3. Unicode Escapes",

  Rule {lhs = UnicodeInputCharacter,
        rhs = Any [NT UnicodeEscape,
                   NT RawInputCharacter]},

  Rule {lhs = UnicodeEscape,
        rhs = Seq [backslash, NT UnicodeMarker, NT HexDigit, NT HexDigit, NT HexDigit]},

  Rule {lhs = UnicodeMarker,
        rhs = Any [lower_u,
                   Seq [NT UnicodeMarker, lower_u]]},

  Rule {lhs = RawInputCharacter,
        rhs = any_unicode_char},

  Rule {lhs = HexDigit,
        rhs = Any [digit_0, digit_1, digit_2, digit_3, digit_4, digit_5, digit_6, digit_7,
                   digit_8, digit_9, lower_a, lower_b, lower_c, lower_d, lower_e, lower_f,
                   upper_A, upper_B, upper_C, upper_D, upper_E, upper_F]}
  ]

%%% ========================================================================
%%% 3.4. Line Terminators
%%% ========================================================================

op Directives_3_4 : Directives =
 [Header  "3.4. Line Terminators",

  Rule {lhs = LineTerminator,
        rhs = Any [LF,
                   CR,
                   Seq [LF, CR]]},

  Rule {lhs = InputCharacter,
        rhs = Diff (NT UnicodeInputCharacter, Any [LF, CR])}
  ]

%%% ========================================================================
%%% 3.5. Input Elements and Tokens
%%% ========================================================================

op Directives_3_5 : Directives =
 [Header  "3.5. Input Elements and Tokens",

  Rule {lhs = Input,
        rhs = Seq [Opt [NT InputElements],
                   Opt [Sub]]},

  Rule {lhs = InputElements,
        rhs = Any [NT InputElement,
                   Seq [NT InputElements, NT InputElement]]},

  Rule {lhs = InputElement,
        rhs = Any [NT WhiteSpace,
                   NT Comment,
                   NT Token]},

  Rule {lhs = Token,
        rhs = Any [NT Identifier,
                   NT Keyword,
                   NT Literal,
                   NT Separator,
                   NT Operator]}
  ]

%%% ========================================================================
%%% 3.6. White Space
%%% ========================================================================

op Directives_3_6 : Directives =
 [Header  "3.6. Whitepace",

  Rule {lhs = WhiteSpace,
        rhs = Any [SP, % space
                   HT, % tab
                   FF, % form feed
                   NT LineTerminator]}
  ]

%%% ========================================================================
%%% 3.7. Comments
%%% ========================================================================

op Directives_3_7 : Directives =
 [Header  "3.7. Comments",

  Rule {lhs = Comment,
        rhs = Any [NT TraditionalComment,
                   NT EndOfLineComment]},

  Rule {lhs = TraditionalComment,
        rhs = Seq [slash, star, NT CommentTail]},

  Rule {lhs = EndOfLineComment,
        rhs = Seq [slash, slash, Opt [NT CharactersInLine]]},

  Rule {lhs = CommentTail,
        rhs = Any [slash,
                   Seq [star,       NT CommentTailStar],
                   Seq [NT NotStar, NT CommentTail]]},

  Rule {lhs = NotStar,
        rhs = Any [Diff (NT InputCharacter, star),
                   NT LineTerminator]},

  Rule {lhs = NotStarNotSlash,
        rhs = Any [Diff (NT InputCharacter, Any [star, slash]),
                   NT LineTerminator]},

  Rule {lhs = CharactersInLine,
        rhs = Any [NT InputCharacter,
                   Seq [NT CharactersInLine, NT InputCharacter]]}
  ]

%%% ========================================================================
%%% 3.8. Identifiers
%%% ========================================================================

op java_letter? (rhs : RHS) : Bool =
  case rhs of
    | Terminal x -> ((uchar #A) <= x && x <= (uchar #Z))
                    ||
                    ((uchar #a) <= x && x <= (uchar #z))
    | _ -> false

op java_letter_or_digit? (rhs : RHS) : Bool =
  case rhs of
    | Terminal x -> ((uchar #A) <= x && x <= (uchar #Z))
                    ||
                    ((uchar #a) <= x && x <= (uchar #z))
                    ||
                    ((uchar #0) <= x && x <= (uchar #9))
    | _ -> false

op Directives_3_8 : Directives =
 [Header  "3.8. Identifiers",

  Rule {lhs = Identifier,
        rhs = Diff (NT IdentifierChars, Any [NT Keyword, NT BooleanLiteral, NT NullLiteral])},

  Rule {lhs = IdentifierChars,
        rhs = Any [NT JavaLetter,
                   Seq [NT IdentifierChars, NT JavaLetterOrDigit]]},

  Rule {lhs = JavaLetter,
        rhs = Restrict (any_unicode_char, java_letter?)},

  Rule {lhs = JavaLetterOrDigit,
        rhs = Restrict (any_unicode_char, java_letter_or_digit?)}
  ]

%%% ========================================================================
%%% 3.9. Keywords
%%% ========================================================================

op Directives_Keywords : Directives =
 [Header "3.9. Keywords",

  Rule {lhs = KW_abstract,
        rhs = keyword "abstract"},

  Rule {lhs = KW_assert       ,
        rhs = keyword "assert"},

  Rule {lhs = KW_boolean      ,
        rhs = keyword "boolean"},

  Rule {lhs = KW_break        ,
        rhs = keyword "break"},

  Rule {lhs = KW_byte         ,
        rhs = keyword "byte"},

  Rule {lhs = KW_case         ,
        rhs = keyword "case"},

  Rule {lhs = KW_catch        ,
        rhs = keyword "catch"},

  Rule {lhs = KW_char         ,
        rhs = keyword "char"},

  Rule {lhs = KW_class        ,
        rhs = keyword "class"},

  Rule {lhs = KW_const        ,
        rhs = keyword "const"},

  Rule {lhs = KW_continue     ,
        rhs = keyword "continue"},

  Rule {lhs = KW_default      ,
        rhs = keyword "default"},

  Rule {lhs = KW_do           ,
        rhs = keyword "do"},

  Rule {lhs = KW_double       ,
        rhs = keyword "double"},

  Rule {lhs = KW_else         ,
        rhs = keyword "else"},

  Rule {lhs = KW_enum         ,
        rhs = keyword "enum"},

  Rule {lhs = KW_extends      ,
        rhs = keyword "extends"},

  Rule {lhs = KW_final        ,
        rhs = keyword "final"},

  Rule {lhs = KW_finally      ,
        rhs = keyword "finally"},

  Rule {lhs = KW_float        ,
        rhs = keyword "float"},

  Rule {lhs = KW_for          ,
        rhs = keyword "for"},

  Rule {lhs = KW_if           ,
        rhs = keyword "if"},

  Rule {lhs = KW_goto         ,
        rhs = keyword "goto"},

  Rule {lhs = KW_implements   ,
        rhs = keyword "implements"},

  Rule {lhs = KW_import       ,
        rhs = keyword "import"},

  Rule {lhs = KW_instanceof   ,
        rhs = keyword "instanceof"},

  Rule {lhs = KW_int          ,
        rhs = keyword "int"},

  Rule {lhs = KW_interface    ,
        rhs = keyword "interface"},

  Rule {lhs = KW_long         ,
        rhs = keyword "long"},

  Rule {lhs = KW_native       ,
        rhs = keyword "native"},

  Rule {lhs = KW_new          ,
        rhs = keyword "new"},

  Rule {lhs = KW_package      ,
        rhs = keyword "package"},

  Rule {lhs = KW_private      ,
        rhs = keyword "private"},

  Rule {lhs = KW_protected    ,
        rhs = keyword "protected"},

  Rule {lhs = KW_public       ,
        rhs = keyword "public"},

  Rule {lhs = KW_return       ,
        rhs = keyword "return"},

  Rule {lhs = KW_short        ,
        rhs = keyword "short"},

  Rule {lhs = KW_static       ,
        rhs = keyword "static"},

  Rule {lhs = KW_strictfp     ,
        rhs = keyword "strictfp"},

  Rule {lhs = KW_super        ,
        rhs = keyword "super"},

  Rule {lhs = KW_switch       ,
        rhs = keyword "switch"},

  Rule {lhs = KW_synchronized ,
        rhs = keyword "synchronized"},

  Rule {lhs = KW_this         ,
        rhs = keyword "this"},

  Rule {lhs = KW_throw        ,
        rhs = keyword "throw"},

  Rule {lhs = KW_throws       ,
        rhs = keyword "throws"},

  Rule {lhs = KW_transient    ,
        rhs = keyword "transient"},

  Rule {lhs = KW_try          ,
        rhs = keyword "try"},

  Rule {lhs = KW_void         ,
        rhs = keyword "void"},

  Rule {lhs = KW_volatile     ,
        rhs = keyword "volatile"},

  Rule {lhs = KW_while,
        rhs = keyword "while"},

  Rule {lhs = Keyword,
        rhs = Any [NT KW_abstract,   NT KW_assert,       NT KW_boolean,   NT KW_break,      NT KW_byte,
                   NT KW_case,       NT KW_catch,        NT KW_char,      NT KW_class,      NT KW_const,
                   NT KW_continue,   NT KW_default,      NT KW_do,        NT KW_double,     NT KW_else,
                   NT KW_enum,       NT KW_extends,      NT KW_final,     NT KW_finally,    NT KW_float,
                   NT KW_for,        NT KW_if,           NT KW_goto,      NT KW_implements, NT KW_import,
                   NT KW_instanceof, NT KW_int,          NT KW_interface, NT KW_long,       NT KW_native,
                   NT KW_new,        NT KW_package,      NT KW_private,   NT KW_protected,  NT KW_public,
                   NT KW_return,     NT KW_short,        NT KW_static,    NT KW_strictfp,   NT KW_super,
                   NT KW_switch,     NT KW_synchronized, NT KW_this,      NT KW_throw,      NT KW_throws,
                   NT KW_transient,  NT KW_try,          NT KW_void,      NT KW_volatile,   NT KW_while]}
    ]

%%% ========================================================================
%%% 3.10. Literals
%%% ========================================================================

op Directives_3_10 : Directives =
 [Header "3.10. Literals",

  Rule {lhs = Literal,
        rhs = Any [NT IntegerLiteral,
                   NT FloatingPointLiteral,
                   NT BooleanLiteral,
                   NT CharacterLiteral,
                   NT StringLiteral,
                   NT NullLiteral]}
  ]

%%% ========================================================================
%%% 3.10.1 Integer Literals
%%% ========================================================================

op Directives_3_10_1 : Directives =
 [Header "3.10.1. Integer Literals",

  Rule {lhs = IntegerLiteral,
        rhs = Any [NT DecimalIntegerLiteral,
                   NT HexIntegerLiteral,
                   NT OctalIntegerLiteral,
                   NT BinaryIntegerLiteral]},

  Rule {lhs = DecimalIntegerLiteral,
        rhs = Seq [NT DecimalNumeral, Opt [NT IntegerTypeSuffix]]},

  Rule {lhs = HexIntegerLiteral,
        rhs = Seq [NT HexNumeral,     Opt [NT IntegerTypeSuffix]]},

  Rule {lhs = OctalIntegerLiteral,
        rhs = Seq [NT OctalNumeral,   Opt [NT IntegerTypeSuffix]]},

  Rule {lhs = BinaryIntegerLiteral,
        rhs = Seq [NT BinaryNumeral,  Opt [NT IntegerTypeSuffix]]},

  Rule {lhs = IntegerTypeSuffix,
        rhs = Any [lower_l, upper_L]},

  %%% Decimal

  Rule {lhs = DecimalNumeral,
        rhs = Any [digit_0,
                   Seq [NT NonZeroDigit, Opt [NT Digits]],
                   Seq [NT NonZeroDigit, NT Underscores, NT Digits]]},

  Rule {lhs = Digits,
        rhs = Any [NT Digit,
                   Seq [NT Digit, Opt [NT DigitsAndUnderscores], NT Digit]]},

  Rule {lhs = Digit,
        rhs = Any [digit_0,
                   NT NonZeroDigit]},

  Rule {lhs = NonZeroDigit,
        rhs = Any [digit_1, digit_2, digit_3, digit_4, digit_5, digit_6, digit_7, digit_8, digit_9]},

  Rule {lhs = DigitsAndUnderscores,
        rhs = Any [NT DigitOrUnderscore,
                   Seq [NT DigitsAndUnderscores, NT DigitOrUnderscore]]},

  Rule {lhs = DigitOrUnderscore,
        rhs = Any [NT Digit,
                   underscore]},

  Rule {lhs = Underscores,
        rhs = Any [underscore,
                   Seq [NT Underscores, underscore]]},

  %%% Hex

  Rule {lhs = HexNumeral,
        rhs = Any [Seq [digit_0, lower_x, NT HexDigits],
                   Seq [digit_0, upper_X, NT HexDigits]]},

  Rule {lhs = HexDigits,
        rhs = Any [NT HexDigit,
                   Seq [NT HexDigit, Opt [NT HexDigitsAndUnderscores], NT HexDigit]]},

  Rule {lhs = HexDigitsAndUnderscores,
        rhs = Any [NT HexDigitOrUnderscore,
                   Seq [NT HexDigitsAndUnderscores, NT HexDigitOrUnderscore]]},

  Rule {lhs = HexDigitOrUnderscore,
        rhs = Any [NT HexDigit,
                   underscore]},

  %%% Octal

  Rule {lhs = OctalNumeral,
        rhs = Any [Seq [digit_0, NT OctalDigits],
                   Seq [digit_0, NT OctalDigits]]},

  Rule {lhs = OctalDigits,
        rhs = Any [NT OctalDigit,
                   Seq [NT OctalDigit, Opt [NT OctalDigitsAndUnderscores], NT OctalDigit]]},

  Rule {lhs = OctalDigit,
        rhs = Any [digit_0, digit_1, digit_2, digit_3, digit_4, digit_5, digit_6, digit_7]},

  Rule {lhs = OctalDigitsAndUnderscores,
        rhs = Any [NT OctalDigitOrUnderscore,
                   Seq [NT OctalDigitsAndUnderscores, NT OctalDigitOrUnderscore]]},

  Rule {lhs = OctalDigitOrUnderscore,
        rhs = Any [NT OctalDigit,
                   underscore]},

  %%% Binary

  Rule {lhs = BinaryNumeral,
        rhs = Any [Seq [digit_0, lower_b, NT BinaryDigits],
                   Seq [digit_0, upper_B, NT BinaryDigits]]},

  Rule {lhs = BinaryDigits,
        rhs = Any [NT BinaryDigit,
                   Seq [NT BinaryDigit, Opt [NT BinaryDigitsAndUnderscores], NT BinaryDigit]]},

  Rule {lhs = BinaryDigit,
        rhs = Any [digit_0, digit_1]},

  Rule {lhs = BinaryDigitsAndUnderscores,
        rhs = Any [NT BinaryDigitOrUnderscore,
                   Seq [NT BinaryDigitsAndUnderscores, NT BinaryDigitOrUnderscore]]},

  Rule {lhs = BinaryDigitOrUnderscore,
        rhs = Any [NT BinaryDigit,
                   underscore]}

  ]

%%% ========================================================================
%%% 3.10.2 Floating-Point Literals
%%% ========================================================================

op Directives_3_10_2 : Directives =
 [Header "3.10.2. Floating-Point Literals",

  Rule {lhs = FloatingPointLiteral,
        rhs = Any [NT DecimalFloatingPointLiteral,
                   NT HexadecimalFloatingPointLiteral]},

  %% Decimal

  Rule {lhs = DecimalFloatingPointLiteral,
        rhs = Any [Seq [NT Digits, dot, Opt [NT Digits], Opt [NT ExponentPart], Opt [NT FloatTypeSuffix]],
                   Seq [           dot,      NT Digits,  Opt [NT ExponentPart], Opt [NT FloatTypeSuffix]],
                   Seq [NT Digits,                            NT ExponentPart,  Opt [NT FloatTypeSuffix]],
                   Seq [NT Digits,                       Opt [NT ExponentPart],      NT FloatTypeSuffix ]]},

  Rule {lhs = ExponentPart,
        rhs = Seq [NT ExponentIndicator, NT SignedInteger]},

  Rule {lhs = ExponentIndicator,
        rhs = Any [lower_e, upper_E]},

  Rule {lhs = SignedInteger,
        rhs = Seq [Opt [NT Sign], NT Digits]},

  Rule {lhs = Sign,
        rhs = Any [plus, minus]},

  Rule {lhs = FloatTypeSuffix,
        rhs = Any [lower_f, upper_F, lower_d, upper_D]},

  %% Hexadecimal

  Rule {lhs = HexadecimalFloatingPointLiteral,
        rhs = Seq [NT HexSignificand, NT BinaryExponent, Opt [NT FloatTypeSuffix]]},

  Rule {lhs = HexSignificand,
        rhs = Any [NT HexNumeral,
                   Seq [NT HexNumeral, dot],
                   Seq [digit_0, lower_x, Opt [NT HexDigits], dot, NT HexDigits],
                   Seq [digit_0, upper_X, Opt [NT HexDigits], dot, NT HexDigits]]},

  Rule {lhs = BinaryExponent,
        rhs = Seq [NT BinaryExponentIndicator, NT SignedInteger]},

  Rule {lhs = BinaryExponentIndicator,
        rhs = Any [lower_p, upper_P]}

  ]

%%% ========================================================================
%%% 3.10.3 Boolean Literals
%%% ========================================================================

op kw_true  : RHS = keyword "true"
op kw_false : RHS = keyword "false"

op Directives_3_10_3 : Directives =
 [Header "3.10.3. Boolean Literals",

  Rule {lhs = BooleanLiteral,
        rhs = Any [kw_true, kw_false]}
  ]

%%% ========================================================================
%%% 3.10.4 Character Literals
%%% ========================================================================

op Directives_3_10_4 : Directives =
 [Header "3.10.4. Character Literals",

  Rule {lhs = CharacterLiteral,
        rhs = Any [Seq [single_quote, NT SingleCharacter, single_quote],
                   Seq [single_quote, NT EscapeSequence,  single_quote]]},

  Rule {lhs = SingleCharacter,
        rhs = Diff (NT InputCharacter, Any [single_quote, backslash])}

  ]

%%% ========================================================================
%%% 3.10.5. String Literals
%%% ========================================================================

op Directives_3_10_5 : Directives =
 [Header "3.10.5. String Literals",

  Rule {lhs = StringLiteral,
        rhs = Seq [double_quote, Opt [NT StringCharacters], double_quote]},

  Rule {lhs = StringCharacters,
        rhs = Any [NT StringCharacter,
                   NT StringCharacters, NT StringCharacter]},

  Rule {lhs = StringCharacter,
        rhs = Any [Diff (NT InputCharacter, Any [double_quote, backslash]),
                   NT EscapeSequence]}

  ]

%%% ========================================================================
%%% 3.10.6. Escape Sequences for Character and String Literals
%%% ========================================================================

op Directives_3_10_6 : Directives =
 [Header "3.10.6. Escape Sequences for Character and String Literals",

  Rule {lhs = EscapeSequence,
        rhs = Any [backspace,        % \u0008: backspace
                   HT,               % \u0009: horizontal tab
                   LF,               % \u000a: linefeed
                   FF,               % \u000c: form feed
                   CR,               % \u000d: carriage return
                   double_quote,     % \u0027
                   single_quote,     % \u0027
                   backslash,        % \u005c
                   NT OctalEscape]}, % \u0000 to \u00ff from octal value

  Rule {lhs = OctalEscape,
        rhs = Any [Seq [backslash, NT OctalDigit],
                   Seq [backslash, NT OctalDigit, NT OctalDigit],
                   Seq [backslash, NT ZeroToThree, NT OctalDigit, NT OctalDigit]]},

  % identical rule at 3.10.1
  % Rule {lhs = OctalDigit,
  %       rhs = Any [digit_0, digit_1, digit_2, digit_3, digit_4, digit_5, digit_6, digit_7]},

  Rule {lhs = ZeroToThree,
        rhs = Any [digit_0, digit_1, digit_2, digit_3]}

 ]

%%% ========================================================================
%%% 3.10.7. The Null Literal
%%% ========================================================================

op Directives_3_10_7 : Directives =
 [Header "3.10.7. The Null Literal",

  Rule {lhs = NullLiteral,
        rhs = keyword "null"}
  ]

%%% ========================================================================
%%% 3.11. Separators
%%% ========================================================================

op Directives_3_11 : Directives =
 [Header "3.11. Separators",

  Rule {lhs = Separator,
        rhs = Any [left_paren,  right_paren,
                   left_curly,  right_curly,
                   left_square, right_square,
                   semicolon, comma, dot]}
  ]

%%% ========================================================================
%%% 3.12. Operators
%%% ========================================================================

op op_==         : RHS = keyword "=="
op op_<=         : RHS = keyword "<="
op op_>=         : RHS = keyword ">="
op op_!=         : RHS = keyword "!="
op op_&&         : RHS = keyword "&&"
op op_||         : RHS = keyword "||"
op op_++         : RHS = keyword "++"
op op_--         : RHS = keyword "--"
op op_<<         : RHS = keyword "<<"
op op_>>         : RHS = keyword ">>"
op op_>>>        : RHS = keyword ">>>"

op op_+=         : RHS = keyword "+="
op op_-=         : RHS = keyword "-="
op op_*=         : RHS = keyword "*="
op op_/=         : RHS = keyword "/="
op op_&=         : RHS = keyword "&="
op op_|=         : RHS = keyword "|="
op op_^=         : RHS = keyword "^="
op op_percent_=  : RHS = keyword "%="    % op_%= causes parsing problems
op op_<<=        : RHS = keyword "<<="
op op_>>=        : RHS = keyword ">>="
op op_>>>=       : RHS = keyword ">>>="

op Directives_3_12 : Directives =
 [Header "3.12. Operators",

  Rule {lhs = Separator,
        rhs = Any [equal_sign, right_angle, left_angle, exclamation, tilde, question_mark, colon          ,
                   op_==, op_<=, op_>=, op_!=, op_&&, op_||, op_++, op_--,
                   ampersand, bar, carrot, percent,
                   op_<<, op_>>, op_>>>, op_+=, op_-=, op_*=, op_/=, op_&=, op_|=, op_^=,
                   op_percent_=, op_<<=, op_>>=, op_>>>=]}
  ]

%%% ========================================================================
%%% 4.1. The Kinds of Types and Values
%%% ========================================================================

op Directives_4_1 : Directives =
 [Header "4.1. The Kinds of Types and Values",

  Rule {lhs = Type,
        rhs = Any [NT PrimitiveType,
                   NT ReferenceType]}

  ]

%%% ========================================================================
%%% 4.2. Primitive Types and Values
%%% ========================================================================

op Directives_4_2 : Directives =
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

op Directives_4_3 : Directives =
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
        rhs = Any [NT TypeName,
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

op Directives_4_4 : Directives =
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

op Directives_4_5_1 : Directives =
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

op Directives_6_5 : Directives =
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

op Directives_7_3 : Directives =
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

op Directives_7_4 : Directives =
 [Header "7.4. Package Declarations",

  Rule {lhs = PackageDeclaration,
        rhs = Seq [Opt [NT Annotations], NT KW_package, NT PackageName, semicolon]}
  ]

%%% ========================================================================
%%%  7.5. Import Declarations
%%% ========================================================================

op Directives_7_5 : Directives =
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

op Directives_7_5_1 : Directives =
 [Header "7.5.1. Single-Type-Import Declarations",

  Rule {lhs = SingleTypeImportDeclaration,
        rhs = Seq [NT KW_import, NT TypeName, semicolon]}
  ]

%%% ========================================================================
%%%  7.5.2. Type-Import-on-Demand Declarations
%%% ========================================================================

op Directives_7_5_2 : Directives =
 [Header "7.5.2. Type-Import-on-Demand Declarations",

  Rule {lhs = TypeImportOnDemandDeclaration,
        rhs = Seq [NT KW_import, NT PackageOrTypeName, dot, star, semicolon]}
  ]

%%% ========================================================================
%%%  7.5.3. Single-Static-Import Declarations
%%% ========================================================================

op Directives_7_5_3 : Directives =
 [Header "7.5.3. Single-Static-Import Declarations",

  Rule {lhs = SingleStaticImportDeclaration,
        rhs = Seq [NT KW_import, NT KW_static, NT TypeName, dot, NT Identifier, semicolon]}
  ]

%%% ========================================================================
%%%  7.5.4. Static-Import-on-Demand Declarations
%%% ========================================================================

op Directives_7_5_4 : Directives =
 [Header "7.5.4. Static-Import-on-Demand Declarations",

  Rule {lhs = StaticImportOnDemandDeclaration,
        rhs = Seq [NT KW_import, NT KW_static, NT TypeName, dot, star, semicolon]}
  ]

%%% ========================================================================
%%%  7.6. -- Top Level Type Declarations
%%% ========================================================================

op Directives_7_6 : Directives =
 [Header "7.6. -- Top Level Type Declarations",

  Rule {lhs = TypeDeclaration,
        rhs = Any [NT ClassDeclaration,
                   NT InterfaceDeclaration,
                   semicolon]}
  ]

%%% ========================================================================
%%%  8.1. Class Declarations
%%% ========================================================================

op Directives_8_1 : Directives =
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

op Directives_8_1_1 : Directives =
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
%%%  8.1.2. Gneric Classes and Type Parameters
%%% ========================================================================

op Directives_8_1_2 : Directives =
 [Header "8.1.2. Gneric Classes and Type Parameters",

  Rule {lhs = TypeParameters,
        rhs = Seq [left_angle, NT TypeParameterList, right_angle]},

  Rule {lhs = TypeParameterList,
        rhs = Any [Seq [NT TypeParameterList, comma, NT TypeParameter],
                   NT TypeParameter]}
  ]

%%% ========================================================================
%%%  8.1.4. Superclasses and Subclasses
%%% ========================================================================

op Directives_8_1_4 : Directives =
 [Header "8.1.4. Superclasses and Subclasses",

  Rule {lhs = TypeParameters,
        rhs = Seq [NT KW_extends, NT ClassType]}
  ]

%%% ========================================================================
%%%  8.1.5. Superinterfaces
%%% ========================================================================

op Directives_8_1_5 : Directives =
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

op Directives_8_1_6 : Directives =
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

op Directives_8_3 : Directives =
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

op Directives_8_3_1 : Directives =
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

op Directives_8_4 : Directives =
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

op Directives_8_4_1 : Directives =
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

op Directives_8_4_3 : Directives =
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

op Directives_8_4_5 : Directives =
 [Header "8.4.5. Method Return Type",

  Rule {lhs = Result,
        rhs = Any [NT Type,
                   NT KW_void]}
  ]

%%% ========================================================================
%%%  8.4.6. Method Throws
%%% ========================================================================

op Directives_8_4_6 : Directives =
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

op Directives_8_4_7 : Directives =
 [Header "8.4.7. Method Body",

  Rule {lhs = MethodBody,
        rhs = Any [NT Block,
                   semicolon]}
  ]

%%% ========================================================================
%%%  8.6. Instance Initializers
%%% ========================================================================

op Directives_8_6 : Directives =
 [Header "8.6. Instance Initializers",

  Rule {lhs = InstanceInitializer,
        rhs = NT Block}
  ]

%%% ========================================================================
%%%  8.7. Static Initializers
%%% ========================================================================

op Directives_8_7 : Directives =
 [Header "8.7. Static Initializers",

  Rule {lhs = StaticInitializer,
        rhs = Seq [NT KW_static, NT Block]}
  ]

%%% ========================================================================
%%%  8.8. Constructor Declarations
%%% ========================================================================

op Directives_8_8 : Directives =
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

op Directives_8_8_3 : Directives =
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
%%%  8.8.7. Constructor Modifiers
%%% ========================================================================

op Directives_8_8_7 : Directives =
 [Header "8.8.7. Constructor Modifiers",

  Rule {lhs = ConstructorBody,
        rhs = Seq [left_curly, Opt [NT ExplicitConstructorInvocation],
                   Opt [NT BlockStatements], right_curly]}
  ]

%%% ========================================================================
%%%  8.8.7.1. Explicit Constructor Invocations
%%% ========================================================================

op Directives_8_8_7_1 : Directives =
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

op Directives_8_9 : Directives =
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

op Directives_8_9_1 : Directives =
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

op Directives_9_1 : Directives =
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

op Directives_9_1_1 : Directives =
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

op Directives_9_1_3 : Directives =
 [Header "9.1.3. Superinterfaces and Subinterfaces",

  Rule {lhs = ExtendsInterfaces,
        rhs = Seq [NT KW_extends, NT InterfaceTypeList]}
  ]

%%% ========================================================================
%%% 9.1.4. Interface Body and Member Declarations
%%% ========================================================================

op Directives_9_1_4 : Directives =
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

op Directives_9_3 : Directives =
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

op Directives_9_4 : Directives =
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

op Directives_9_6 : Directives =
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

op Directives_9_6_1 : Directives =
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

op Directives_9_7 : Directives =
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

op Directives_9_7_1 : Directives =
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

op Directives_9_7_2 : Directives =
 [Header "9.7.2. Marker Annotations",

  Rule {lhs = MarkerAnnotation,
        rhs = Seq [at_sign, NT Identifier]}
  ]

%%% ========================================================================
%%% 9.7.3. Single-Element Annotations
%%% ========================================================================

op Directives_9_7_3 : Directives =
 [Header "9.7.3. Single-Element Annotations",

  Rule {lhs = SingleElementAnnotation,
        rhs = Seq [at_sign, NT Identifier, left_paren, NT ElementValue, right_paren]}
  ]

%%% ========================================================================
%%% 10.6. Array Initializers
%%% ========================================================================

op Directives_10_6 : Directives =
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

op Directives_14_2 : Directives =
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

op Directives_14_4 : Directives =
 [Header "14.4. Local Variable Declaration Statements",

  Rule {lhs = LocalVariableDeclarationStatement,
        rhs = Seq [NT LocalVariableDeclaration, semicolon]},

  Rule {lhs = LocalVariableDeclaration,
        rhs = Seq [Opt [NT VariableModifiers], NT Type, NT VariableDeclarators]}

  ]

%%% ========================================================================
%%% 14.5. Statements
%%% ========================================================================

op Directives_14_5 : Directives =
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

op Directives_14_6 : Directives =
 [Header "14.6. The Empty Statement",

  Rule {lhs = EmptyStatement,
        rhs = semicolon}
  ]

%%% ========================================================================
%%% 14.7. Labeled Statements
%%% ========================================================================

op Directives_14_7 : Directives =
 [Header "14.7. Labeled Statements",

  Rule {lhs = LabeledStatement,
        rhs = Seq [NT Identifier, colon, NT Statement]},

  Rule {lhs = LabeledStatementNoShortIf,
        rhs = Seq [NT Identifier, colon, NT StatementNoShortIf]}
  ]

%%% ========================================================================
%%% 14.8. Expression Statements
%%% ========================================================================

op Directives_14_8 : Directives =
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

op Directives_14_9 : Directives =
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

op Directives_14_10 : Directives =
 [Header "14.10. The assert Statement",

  Rule {lhs = AssertStatement,
        rhs = Any [Seq [NT KW_assert, NT Expression1, semicolon], % must return boolean or Boolean
                   Seq [NT KW_assert, NT Expression1, colon, NT Expression2, semicolon]]}
  ]

%%% ========================================================================
%%% 14.11. The switch Statement
%%% ========================================================================

op Directives_14_11 : Directives =
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

op Directives_14_12 : Directives =
 [Header "14.12. The while Statement",

  Rule {lhs = WhileStatement,
        rhs = Seq [NT KW_while, left_paren, NT Expression, right_paren, NT Statement]},

  Rule {lhs = WhileStatementNoShortIf,
        rhs = Seq [NT KW_while, left_paren, NT Expression, right_paren, NT StatementNoShortIf]}
  ]

%%% ========================================================================
%%% 14.13. The do Statement
%%% ========================================================================

op Directives_14_13 : Directives =
 [Header "14.13. The do Statement",

  Rule {lhs = DoStatement,
        rhs = Seq [NT KW_do, NT Statement, NT KW_while, left_paren, NT Expression, right_paren, NT Statement]}

  ]

%%% ========================================================================
%%% 14.14. The for Statement
%%% ========================================================================

op Directives_14_14 : Directives =
 [Header "14.14. The for Statement",

  Rule {lhs = ForStatement,
        rhs = Any [NT BasicForStatement,
                   NT EnhancedForStatement]}
  ]

%%% ========================================================================
%%% 14.14.1. The basic for Statement
%%% ========================================================================

op Directives_14_14_1 : Directives =
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

op Directives_14_14_2 : Directives =
 [Header "14.14.2. The enhanced for statement",

  Rule {lhs = EnhancedForStatement,
        rhs = Seq [NT KW_for, left_paren, NT FormalParameter, colon, NT Expression, right_paren, NT Statement]}
  ]

%%% ========================================================================
%%% 14.15. The break Statement
%%% ========================================================================

op Directives_14_15 : Directives =
 [Header "14.15. The break Statement",

  Rule {lhs = BreakStatement,
        rhs = Seq [NT KW_break, Opt [NT Identifier], semicolon]}
  ]

%%% ========================================================================
%%% 14.16. The continue Statement
%%% ========================================================================

op Directives_14_16 : Directives =
 [Header "14.16. The continue Statement",

  Rule {lhs = ContinueStatement,
        rhs = Seq [NT KW_continue, Opt [NT Identifier], semicolon]}
  ]

%%% ========================================================================
%%% 14.17. The return Statement
%%% ========================================================================

op Directives_14_17 : Directives =
 [Header "14.17. The return Statement",

  Rule {lhs = ReturnStatement,
        rhs = Seq [NT KW_return, Opt [NT Expression], semicolon]}
  ]

%%% ========================================================================
%%% 14.18. The throw Statement
%%% ========================================================================

op Directives_14_18 : Directives =
 [Header "14.18. The throw Statement",

  Rule {lhs = ThrowStatement,
        rhs = Seq [NT KW_throw, Opt [NT Expression], semicolon]}
  ]

%%% ========================================================================
%%% 14.19. The synchronized Statement
%%% ========================================================================

op Directives_14_19 : Directives =
 [Header "14.19. The synchronized Statement",

  Rule {lhs = SynchronizedStatement,
        rhs = Seq [NT KW_synchronized, left_paren, NT Expression, right_paren, NT Block]}
  ]

%%% ========================================================================
%%% 14.20. The try statement
%%% ========================================================================

op Directives_14_20 : Directives =
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

op Directives_14_20_3 : Directives =
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

op Directives_15_8 : Directives =
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
op Directives_15_9 : Directives =
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

op Directives_15_10 : Directives =
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

op Directives_15_11 : Directives =
 [Header "15.11. Field Access Expressions",

  Rule {lhs = FieldAccess,
        rhs = Any [Seq [NT Primary,                  dot, NT Identifier],
                   Seq [                   NT KW_super, dot, NT Identifier],
                   Seq [NT ClassName, dot, NT KW_super, dot, NT Identifier]]}
  ]

%%% ========================================================================
%%% 15.12. Method Invocation Expressions
%%% ========================================================================

op Directives_15_12 : Directives =
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

op Directives_15_13 : Directives =
 [Header "15.13. Array Access Expressions",

  Rule {lhs = ArrayAccess,
        rhs = Any [Seq [NT ExpressionName,    left_square, NT Expression, right_square],
                   Seq [NT PrimaryNoNewArray, left_square, NT Expression, right_square]]}
  ]

%%% ========================================================================
%%% 15.14. Postfix Expressions
%%% ========================================================================

op Directives_15_14 : Directives =
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

op Directives_15_14_2 : Directives =
 [Header "15.14.2. Postfix Incremement Operator ++",

  Rule {lhs = PostIncrementExpression,
        rhs = Seq [NT PostfixExpression, op_++]}
  ]

%%% ========================================================================
%%% 15.14.3. Postfix Decremement Operator --
%%% ========================================================================

op Directives_15_14_3 : Directives =
 [Header "15.14.3. Postfix Decremement Operator --",

  Rule {lhs = PostDecrementExpression,
        rhs = Seq [NT PostfixExpression, op_--]}
  ]

%%% ========================================================================
%%% 15.15. Unary Operators
%%% ========================================================================

op Directives_15_15 : Directives =
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

op Directives_15_16 : Directives =
 [Header "15.16. Cast Expressions",

  Rule {lhs = CastExpression,
        rhs = Any [Seq [left_paren, NT PrimitiveType, right_paren, NT UnaryExpression],
                   Seq [left_paren, NT ReferenceType, right_paren, NT UnaryExpressionNotPlusMinus]]}
  ]

%%% ========================================================================
%%% 15.17. Multiplicative Operators
%%% ========================================================================

op Directives_15_17 : Directives =
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

op Directives_15_18 : Directives =
 [Header "15.18. Additive Operators",

  Rule {lhs = AdditiveExpression,
        rhs = Any [NT MultiplicativeExpression,
                   Seq [NT AdditiveExpression, plus,  NT MultiplicativeExpression],
                   Seq [NT AdditiveExpression, minus, NT MultiplicativeExpression]]}
  ]

%%% ========================================================================
%%% 15.19. Shift Operators
%%% ========================================================================

op Directives_15_19 : Directives =
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

op Directives_15_20 : Directives =
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

op Directives_15_21 : Directives =
 [Header "15.21. Equality Operators",

  Rule {lhs = EqualityExpression,
        rhs = Any [NT RelationalExpression,
                   Seq [NT EqualityExpression, op_==, NT RelationalExpression],
                   Seq [NT EqualityExpression, op_!=, NT RelationalExpression]]}
  ]

%%% ========================================================================
%%% 15.22. Bitwise and Logical Operators
%%% ========================================================================

op Directives_15_22 : Directives =
 [Header "15.22. Bitwise and Logical Operators",

  Rule {lhs = AndExpression,
        rhs = Any [NT EqualityExpression,
                   Seq [NT AndExpression, ampersand, NT EqualityExpression]]},

  Rule {lhs = ExclusiveOrExpression,
        rhs = Any [NT AndExpression,
                   Seq [NT ExclusiveOrExpression, carrot, NT AndExpression]]},

  Rule {lhs = InclusiveOrExpression,
        rhs = Any [NT InclusiveOrExpression,
                   Seq [NT InclusiveOrExpression, bar, NT ExclusiveOrExpression]]}

  ]

%%% ========================================================================
%%% 15.23. Conditional-And Operator &&
%%% ========================================================================

op Directives_15_23 : Directives =
 [Header "15.23. Conditional-And Operator &&",

  Rule {lhs = ConditionalAndExpression,
        rhs = Any [NT InclusiveOrExpression,
                   Seq [NT ConditionalAndExpression, op_&&, NT InclusiveOrExpression]]}
  ]

%%% ========================================================================
%%% 15.24. Conditional-Or Operator ||
%%% ========================================================================

op Directives_15_24 : Directives =
 [Header "15.24. Conditional-Or Operator ||",

  Rule {lhs = ConditionalOrExpression,
        rhs = Any [NT ConditionalAndExpression,
                   Seq [NT ConditionalOrExpression, op_||, NT ConditionalAndExpression]]}
  ]

%%% ========================================================================
%%% 15.25. Conditional Operator ? :
%%% ========================================================================

op Directives_15_25 : Directives =
 [Header "15.25. Conditional Operator ? :",

  Rule {lhs = ConditionalExpression,
        rhs = Any [NT ConditionalOrExpression,
                   Seq [NT ConditionalOrExpression, question_mark, NT Expression, colon, NT ConditionalExpression]]}
  ]

%%% ========================================================================
%%% 15.26. Assignment Operators
%%% ========================================================================

op Directives_15_26 : Directives =
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

op Directives_15_27 : Directives =
 [Header "15.27. Expression",

  Rule {lhs = Expression,
        rhs = NT AssignmentExpression}

  ]

%%% ========================================================================
%%% 15.28. Constant Expressions
%%% ========================================================================

op Directives_15_28 : Directives =
 [Header "15.28. Constant Expressions",

  Rule {lhs = ConstantExpression,
        rhs = NT Expression}  % TODO: many restrictions

  ]

%%% ========================================================================
%%% Misc
%%% ========================================================================

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


op Java7ExpositionGrammar : Grammar =
 let directives = Directives_Ad_Hoc_Keywords
                  ++ Directives_3_3
                  ++ Directives_3_4
                  ++ Directives_3_5
                  ++ Directives_3_6
                  ++ Directives_3_7
                  ++ Directives_3_8
                  ++ Directives_Keywords
                  ++ Directives_3_10
                  ++ Directives_3_10_1
                  ++ Directives_3_10_2
                  ++ Directives_3_10_3
                  ++ Directives_3_10_4
                  ++ Directives_3_10_5
                  ++ Directives_3_10_6
                  ++ Directives_3_10_7
                  ++ Directives_3_11
                  ++ Directives_3_12
                  ++ Directives_4_1
                  ++ Directives_4_2
                  ++ Directives_4_3
                  ++ Directives_4_4
                  ++ Directives_4_5_1
                  ++ Directives_6_5
                  ++ Directives_7_3
                  ++ Directives_7_4
                  ++ Directives_7_5
                  ++ Directives_7_5_1
                  ++ Directives_7_5_2
                  ++ Directives_7_5_3
                  ++ Directives_7_5_4
                  ++ Directives_7_6
                  ++ Directives_8_1
                  ++ Directives_8_1_1
                  ++ Directives_8_1_2
                  ++ Directives_8_1_4
                  ++ Directives_8_1_5
                  ++ Directives_8_1_6
                  ++ Directives_8_3
                  ++ Directives_8_3_1
                  ++ Directives_8_4
                  ++ Directives_8_4_1
                  ++ Directives_8_4_3
                  ++ Directives_8_4_5
                  ++ Directives_8_4_6
                  ++ Directives_8_4_7
                  ++ Directives_8_6
                  ++ Directives_8_7
                  ++ Directives_8_8
                  ++ Directives_8_8_3
                  ++ Directives_8_8_7
                  ++ Directives_8_8_7_1
                  ++ Directives_8_9
                  ++ Directives_8_9_1
                  ++ Directives_9_1
                  ++ Directives_9_1_1
                  ++ Directives_9_1_3
                  ++ Directives_9_1_4
                  ++ Directives_9_3
                  ++ Directives_9_4
                  ++ Directives_9_6
                  ++ Directives_9_6_1
                  ++ Directives_9_7
                  ++ Directives_9_7_1
                  ++ Directives_9_7_2
                  ++ Directives_9_7_3
                  ++ Directives_10_6
                  ++ Directives_14_2
                  ++ Directives_14_4
                  ++ Directives_14_5
                  ++ Directives_14_6
                  ++ Directives_14_7
                  ++ Directives_14_8
                  ++ Directives_14_9
                  ++ Directives_14_10
                  ++ Directives_14_11
                  ++ Directives_14_12
                  ++ Directives_14_13
                  ++ Directives_14_14
                  ++ Directives_14_14_1
                  ++ Directives_14_14_2
                  ++ Directives_14_15
                  ++ Directives_14_16
                  ++ Directives_14_17
                  ++ Directives_14_18
                  ++ Directives_14_19
                  ++ Directives_14_20
                  ++ Directives_14_20_3
                  ++ Directives_15_8
                  ++ Directives_15_9
                  ++ Directives_15_10
                  ++ Directives_15_11
                  ++ Directives_15_12
                  ++ Directives_15_13
                  ++ Directives_15_14
                  ++ Directives_15_14_2
                  ++ Directives_15_14_3
                  ++ Directives_15_15
                  ++ Directives_15_16
                  ++ Directives_15_17
                  ++ Directives_15_18
                  ++ Directives_15_19
                  ++ Directives_15_20
                  ++ Directives_15_21
                  ++ Directives_15_22
                  ++ Directives_15_23
                  ++ Directives_15_24
                  ++ Directives_15_25
                  ++ Directives_15_26
                  ++ Directives_15_27
                  ++ Directives_15_28
                  ++ Directives_Misc
                  ++ Directives_Ad_Hoc_Keywords
 in
 {name          = "Java7ExpositionGrammar",
  documentation = "todo",
  directives    = directives}

end-spec
