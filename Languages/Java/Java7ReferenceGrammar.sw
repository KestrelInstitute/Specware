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

type Java7Ref.RHS        = Java7.RHS        Java7Ref.NonTerminal
type Java7Ref.Rule       = Java7.Rule       Java7Ref.NonTerminal
type Java7Ref.Directive  = Java7.Directive  Java7Ref.NonTerminal
type Java7Ref.Directives = Java7.Directives Java7Ref.NonTerminal
type Java7Ref.Grammar    = Java7.Grammar    Java7Ref.NonTerminal

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
   %%% Identifiers
   %%% ========================================================================

   | QualifiedIdentifier
   | QualifiedIdentifierList

   %%% ========================================================================
   %%% Compilation Unit
   %%% ========================================================================

   | CompilationUnit
   | ImportDeclaration
   | TypeDeclaration
   | ClassOrInterfaceDeclaration
   | ClassDeclaration
   | InterfaceDeclaration
   | NormalClassDeclaration
   | EnumDeclaration
   | NormalInterfaceDeclaration
   | AnnotationTypeDeclaration

   %%% ========================================================================
   %%% Types
   %%% ========================================================================

   | Type
   | BasicType
   | ReferenceType
   | TypeArguments
   | TypeArgument

   %%% ========================================================================
   %%% Type Arguments
   %%% ========================================================================

   | NonWildcardTypeArguments
   | TypeList
   | TypeArgumentsOrDiamond
   | NonWildcardTypeArgumentsOrDiamond
   | TypeParameters
   | TypeParameter
   | Bound

   %%% ========================================================================
   %%% Modifiers
   %%% ========================================================================

   | Modifier
   | Annotations
   | Annotation
   | AnnotationElement
   | ElementValuePairs
   | ElementValuePair
   | ElementValue
   | ElementValueArrayInitializer
   | ElementValues

   %%% ========================================================================
   %%% Classes
   %%% ========================================================================

   | ClassBody
   | ClassBodyDeclaration
   | MemberDecl
   | MethodOrFieldDecl
   | MethodOrFieldRest
   | FieldDeclaratorsRest
   | MethodDeclaratorRest
   | VoidMethodDeclaratorRest
   | ConstructorDeclaratorRest
   | GenericMethodOrConstructorDecl
   | GenericMethodOrConstructorRest

   %%% ========================================================================
   %%% Interfaces
   %%% ========================================================================

   | InterfaceBody
   | InterfaceBodyDeclaration
   | InterfaceMemberDecl
   | InterfaceMethodOrFieldDecl
   | InterfaceMethodOrFieldRest
   | ConstantDeclaratorsRest
   | ConstantDeclaratorRest
   | ConstantDeclarator
   | InterfaceMethodDeclaratorRest
   | VoidInterfaceMethodDeclaratorRest
   | InterfaceGenericMethodDecl

   %%% ========================================================================
   %%% Parameters
   %%% ========================================================================

   | FormalParameters
   | FormalParameterDecls
   | VariableModifier
   | FormalParameterDeclsRest
   | VariableDeclaratorId
   | VariableDeclarators
   | VariableDeclarator
   | VariableDeclaratorRest
   | VariableInitializer
   | ArrayInitializer

   %%% ========================================================================
   %%% Statements
   %%% ========================================================================

   | Block
   | BlockStatements
   | BlockStatement
   | LocalVariableDeclarationStatement
   | Statement
   | StatementExpression

   %%% ========================================================================
   %%% Catches
   %%% ========================================================================

   | Catches
   | CatchClause
   | CatchType
   | Finally
   | ResourceSpecification
   | Resources
   | Resource

   %%% ========================================================================
   %%% Switch
   %%% ========================================================================

   | SwitchBlockStatementGroups
   | SwitchBlockStatementGroup
   | SwitchLabels
   | SwitchLabel
   | EnumConstantName

   %%% ========================================================================
   %%% For
   %%% ========================================================================

   | ForControl
   | ForVarControl
   | ForVarControlRest
   | ForVariableDeclaratorsRest
   | ForInit
   | ForUpdate

   %%% ========================================================================
   %%% Expression
   %%% ========================================================================

   | Expression
   | AssignmentOperator
   | Expression1
   | Expression1Rest
   | Expression2
   | Expression2Rest

   %%% ========================================================================
   %%% Infix
   %%% ========================================================================

   | InfixOp
   | Expression3
   | PrefixOp
   | PostfixOp

   %%% ========================================================================
   %%% Primary
   %%% ========================================================================

   | Primary
   | ParExpression
   | Arguments
   | SuperSuffix
   | ExplicitGenericInvocationSuffix

   %%% ========================================================================
   %%% Creator
   %%% ========================================================================

   | Creator
   | CreatedName
   | ClassCreatorRest
   | ArrayCreatorRest
   | IdentifierSuffix
   | ExplicitGenericInvocation
   | InnerCreator
   | Selector

   %%% ========================================================================
   %%% Enum
   %%% ========================================================================

   | EnumBody
   | EnumConstants
   | EnumConstant
   | EnumBodyDeclarations

   %%% ========================================================================
   %%% Annotation
   %%% ========================================================================

   | AnnotationTypeBody
   | AnnotationTypeElementDeclarations
   | AnnotationTypeElementDeclaration
   | AnnotationTypeElementRest
   | AnnotationMethodOrConstantRest
   | AnnotationMethodRest

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

op op_==        : RHS = keyword "=="
op op_<=        : RHS = keyword "<="
op op_>=        : RHS = keyword ">="
op op_!=        : RHS = keyword "!="
op op_&&        : RHS = keyword "&&"
op op_||        : RHS = keyword "||"
op op_++        : RHS = keyword "++"
op op_--        : RHS = keyword "--"
op op_<<        : RHS = keyword "<<"
op op_>>        : RHS = keyword ">>"
op op_>>>       : RHS = keyword ">>>"

op op_+=        : RHS = keyword "+="
op op_-=        : RHS = keyword "-="
op op_*=        : RHS = keyword "*="
op op_/=        : RHS = keyword "/="
op op_&=        : RHS = keyword "&="
op op_|=        : RHS = keyword "|="
op op_^=        : RHS = keyword "^="
op op_percent_= : RHS = keyword "%="    % op_%= would cause parsing problems
op op_<<=       : RHS = keyword "<<="
op op_>>=       : RHS = keyword ">>="
op op_>>>=      : RHS = keyword ">>>="

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
%%% Identifiers
%%% ========================================================================

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

  Rule {lhs = Literal,
        rhs = Any [NT IntegerLiteral,
                   NT FloatingPointLiteral,
                   NT CharacterLiteral,
                   NT StringLiteral,
                   NT BooleanLiteral,
                   NT NullLiteral]},

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

op Java7ReferenceGrammar : Grammar =
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
                  ++ Directives_3_10_6
                  ++ Directives_3_10_7
                  ++ Directives_3_11
                  ++ Directives_3_12
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
