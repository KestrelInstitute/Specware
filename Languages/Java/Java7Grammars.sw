(* Copyright 2015 Kestrel Institute. See file LICENSE.text for license details *)

Java7 qualifying spec

import /Languages/Grammars/ContextFree
import /Library/IO/Unicode/UnicodeSig

type CFG.Terminal = | Some UChar | AnyChar

op token (char : Char) : RHS =
 Terminal (Some (uchar char))

op keyword (key  : String) : RHS =
 Seq (map (fn char ->
             Terminal (Some (uchar char)))
          (explode key))

%%% ========================================================================
%%% Terminals
%%% ========================================================================

%% digits and letters

op digit_0   : RHS = token #0
op digit_1   : RHS = token #1
op digit_2   : RHS = token #2
op digit_3   : RHS = token #3
op digit_4   : RHS = token #4
op digit_5   : RHS = token #5
op digit_6   : RHS = token #6
op digit_7   : RHS = token #7
op digit_8   : RHS = token #8
op digit_9   : RHS = token #9

op lower_a   : RHS = token #a
op lower_b   : RHS = token #b
op lower_c   : RHS = token #c
op lower_d   : RHS = token #d
op lower_e   : RHS = token #e
op lower_f   : RHS = token #f

op lower_l   : RHS = token #l
op lower_p   : RHS = token #p
op lower_u   : RHS = token #u
op lower_x   : RHS = token #x

op upper_A   : RHS = token #A
op upper_B   : RHS = token #B
op upper_C   : RHS = token #C
op upper_D   : RHS = token #D
op upper_E   : RHS = token #E
op upper_F   : RHS = token #F

op upper_L   : RHS = token #L
op upper_P   : RHS = token #P
op upper_U   : RHS = token #U
op upper_X   : RHS = token #X

%% control characters

op backspace : RHS = token #\x08
op Sub       : RHS = token #\x26  % aka control-z
op LF        : RHS = token #\n    % aka newline
op CR        : RHS = token #\r    % aka return
op SP        : RHS = token #\s    % space
op HT        : RHS = token #\t    % horizontal tab
op FF        : RHS = token #\f    % form feed

%% brackets

op right_paren    : RHS = token #)
op left_paren     : RHS = token #(
op right_angle    : RHS = token #>
op left_angle     : RHS = token #<
op left_square    : RHS = token #[
op right_square   : RHS = token #]
op left_curly     : RHS = token #{
op right_curly    : RHS = token #}

%% misc punctuation

op ampersand      : RHS = token #&
op at_sign        : RHS = token #@
op backslash      : RHS = token #\\
op bar            : RHS = token #|
op carrot         : RHS = token #^
op colon          : RHS = token #:
op comma          : RHS = token #,
op dot            : RHS = token #.
op double_quote   : RHS = token #"
op equal_sign     : RHS = token #=
op exclamation    : RHS = token #!
op minus          : RHS = token #-
op percent        : RHS = token #%
op plus           : RHS = token #+
op question_mark  : RHS = token #?
op semicolon      : RHS = token #;
op single_quote   : RHS = token #'
op slash          : RHS = token #/
op star           : RHS = token #*
op tilde          : RHS = token #~
op underscore     : RHS = token #_

op any_unicode_char : RHS = Terminal AnyChar

%%% ========================================================================
%%% Ad Hoc Keywords
%%% ========================================================================

op Ellipses : NonTerminal = nonTerminal "Ellipses"

op Directives_Ad_Hoc_Keywords : Directives = 
 [Header  "Ad Hoc Keywords",

  Rule {lhs = Ellipses,
        rhs = Seq [dot, dot, dot]}
  ]

%%% ========================================================================
%%% 3.3 Unicode Escapes
%%% ========================================================================

op UnicodeInputCharacter : NonTerminal = nonTerminal "UnicodeInputCharacter"
op UnicodeEscape         : NonTerminal = nonTerminal "UnicodeEscape"
op UnicodeMarker         : NonTerminal = nonTerminal "UnicodeMarker"
op RawInputCharacter     : NonTerminal = nonTerminal "RawInputCharacter"
op HexDigit              : NonTerminal = nonTerminal "HexDigit"

op Directives_3_3_Unicode_Escapes : Directives =
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

op LineTerminator : NonTerminal = nonTerminal "LineTerminator"
op InputCharacter : NonTerminal = nonTerminal "InputCharacter"

op Directives_3_4_Line_Terminators : Directives =
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

op Input         : NonTerminal = nonTerminal "Input"
op InputElements : NonTerminal = nonTerminal "InputElements"
op InputElement  : NonTerminal = nonTerminal "InputElement"
op Token         : NonTerminal = nonTerminal "Token"

op Directives_3_5_Input_Elements : Directives =
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

op WhiteSpace : NonTerminal = nonTerminal "WhiteSpace"

op Directives_3_6_WhiteSpace : Directives =
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

op Comment            : NonTerminal = nonTerminal "Comment"
op TraditionalComment : NonTerminal = nonTerminal "TraditionalComment"
op EndOfLineComment   : NonTerminal = nonTerminal "EndOfLineComment"
op CommentTail        : NonTerminal = nonTerminal "CommentTail"
op CommentTailStar    : NonTerminal = nonTerminal "CommentTailStar"
op NotStar            : NonTerminal = nonTerminal "NotStar"
op NotStarNotSlash    : NonTerminal = nonTerminal "NotStarNotSlash"
op CharactersInLine   : NonTerminal = nonTerminal "CharactersInLine"

op Directives_3_7_Comments : Directives =
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

op Identifier        : NonTerminal = nonTerminal "Identifier"
op IdentifierChars   : NonTerminal = nonTerminal "IdentifierChars"
op JavaLetter        : NonTerminal = nonTerminal "JavaLetter"
op JavaLetterOrDigit : NonTerminal = nonTerminal "JavaLetterOrDigit"

op java_letter? (rhs : RHS) : Bool =
  case rhs of
    | Terminal (Some x) -> ((uchar #A) <= x && x <= (uchar #Z))
                           ||
                           ((uchar #a) <= x && x <= (uchar #z))
    | _ -> false

op java_letter_or_digit? (rhs : RHS) : Bool =
  case rhs of
    | Terminal (Some x) -> ((uchar #A) <= x && x <= (uchar #Z))
                           ||
                           ((uchar #a) <= x && x <= (uchar #z))
                           ||
                           ((uchar #0) <= x && x <= (uchar #9))
    | _ -> false

op Directives_3_8_Identifiers : Directives =
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

op Keyword          : NonTerminal = nonTerminal "Keyword"
op KW_abstract      : NonTerminal = nonTerminal "KW_abstract" 
op KW_assert        : NonTerminal = nonTerminal "KW_assert"
op KW_boolean       : NonTerminal = nonTerminal "KW_boolean"
op KW_break         : NonTerminal = nonTerminal "KW_break"
op KW_byte          : NonTerminal = nonTerminal "KW_byte"
op KW_case          : NonTerminal = nonTerminal "KW_case"
op KW_catch         : NonTerminal = nonTerminal "KW_catch"
op KW_char          : NonTerminal = nonTerminal "KW_char"
op KW_class         : NonTerminal = nonTerminal "KW_class"
op KW_const         : NonTerminal = nonTerminal "KW_const"
op KW_continue      : NonTerminal = nonTerminal "KW_continue"
op KW_default       : NonTerminal = nonTerminal "KW_default"
op KW_do            : NonTerminal = nonTerminal "KW_do"
op KW_double        : NonTerminal = nonTerminal "KW_double"
op KW_else          : NonTerminal = nonTerminal "KW_enumop KW_else"
op KW_enum          : NonTerminal = nonTerminal "KW_enum"
op KW_extends       : NonTerminal = nonTerminal "KW_extends"
op KW_final         : NonTerminal = nonTerminal "KW_final"
op KW_finally       : NonTerminal = nonTerminal "KW_finally"
op KW_float         : NonTerminal = nonTerminal "KW_float"
op KW_for           : NonTerminal = nonTerminal "KW_for"
op KW_if            : NonTerminal = nonTerminal "KW_if"
op KW_goto          : NonTerminal = nonTerminal "KW_goto"
op KW_implements    : NonTerminal = nonTerminal "KW_implements"
op KW_import        : NonTerminal = nonTerminal "KW_import"
op KW_instanceof    : NonTerminal = nonTerminal "KW_instanceof"
op KW_int           : NonTerminal = nonTerminal "KW_int"
op KW_interface     : NonTerminal = nonTerminal "KW_interface"
op KW_long          : NonTerminal = nonTerminal "KW_long"
op KW_native        : NonTerminal = nonTerminal "KW_native"
op KW_new           : NonTerminal = nonTerminal "KW_new"
op KW_package       : NonTerminal = nonTerminal "KW_package"
op KW_private       : NonTerminal = nonTerminal "KW_private"
op KW_protected     : NonTerminal = nonTerminal "KW_protected"
op KW_public        : NonTerminal = nonTerminal "KW_public"
op KW_return        : NonTerminal = nonTerminal "KW_return"
op KW_short         : NonTerminal = nonTerminal "KW_short"
op KW_static        : NonTerminal = nonTerminal "KW_static"
op KW_strictfp      : NonTerminal = nonTerminal "KW_strictfp"
op KW_super         : NonTerminal = nonTerminal "KW_super"
op KW_switch        : NonTerminal = nonTerminal "KW_switch"
op KW_synchronized  : NonTerminal = nonTerminal "KW_synchronized"
op KW_this          : NonTerminal = nonTerminal "KW_this"
op KW_throw         : NonTerminal = nonTerminal "KW_throw"
op KW_throws        : NonTerminal = nonTerminal "KW_throws"
op KW_transient     : NonTerminal = nonTerminal "KW_transient"
op KW_try           : NonTerminal = nonTerminal "KW_try"
op KW_void          : NonTerminal = nonTerminal "KW_void"
op KW_volatile      : NonTerminal = nonTerminal "KW_volatile"
op KW_while         : NonTerminal = nonTerminal "KW_while"

op Directives_3_9_Keywords : Directives =
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

op Literal : NonTerminal = nonTerminal "Literal"

op Directives_3_10_Literals : Directives =
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

op IntegerLiteral             : NonTerminal = nonTerminal "IntegerLiteral"
op DecimalIntegerLiteral      : NonTerminal = nonTerminal "DecimalIntegerLiteral"
op HexIntegerLiteral          : NonTerminal = nonTerminal "HexIntegerLiteral"
op OctalIntegerLiteral        : NonTerminal = nonTerminal "OctalIntegerLiteral"
op BinaryIntegerLiteral       : NonTerminal = nonTerminal "BinaryIntegerLiteral"
op IntegerTypeSuffix          : NonTerminal = nonTerminal "IntegerTypeSuffix"
   % --
op DecimalNumeral             : NonTerminal = nonTerminal "DecimalNumeral"
op Digits                     : NonTerminal = nonTerminal "Digits"
op Digit                      : NonTerminal = nonTerminal "Digit"
op NonZeroDigit               : NonTerminal = nonTerminal "NonZeroDigit"
op DigitsAndUnderscores       : NonTerminal = nonTerminal "DigitsAndUnderscores"
op DigitOrUnderscore          : NonTerminal = nonTerminal "DigitOrUnderscore"
op Underscores                : NonTerminal = nonTerminal "Underscores"
   % --
op HexNumeral                 : NonTerminal = nonTerminal "HexNumeral"
op HexDigits                  : NonTerminal = nonTerminal "HexDigits"
op HexDigitsAndUnderscores    : NonTerminal = nonTerminal "HexDigitsAndUnderscores"
op HexDigitOrUnderscore       : NonTerminal = nonTerminal "HexDigitOrUnderscore"
   % --
op OctalNumeral               : NonTerminal = nonTerminal "OctalNumeral"
op OctalDigits                : NonTerminal = nonTerminal "OctalDigits"
op OctalDigit                 : NonTerminal = nonTerminal "OctalDigit"
op OctalDigitsAndUnderscores  : NonTerminal = nonTerminal "OctalDigitsAndUnderscores"
op OctalDigitOrUnderscore     : NonTerminal = nonTerminal "OctalDigitOrUnderscore"
   % --
op BinaryNumeral              : NonTerminal = nonTerminal "BinaryNumeral"
op BinaryDigits               : NonTerminal = nonTerminal "BinaryDigits"
op BinaryDigit                : NonTerminal = nonTerminal "BinaryDigit"
op BinaryDigitsAndUnderscores : NonTerminal = nonTerminal "BinaryDigitsAndUnderscores"
op BinaryDigitOrUnderscore    : NonTerminal = nonTerminal "BinaryDigitOrUnderscore"

op Directives_3_10_1_Integer_Literals : Directives =
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

op FloatingPointLiteral            : NonTerminal = nonTerminal "FloatingPointLiteral"
op DecimalFloatingPointLiteral     : NonTerminal = nonTerminal "DecimalFloatingPointLiteral"
op ExponentPart                    : NonTerminal = nonTerminal "ExponentPart"
op ExponentIndicator               : NonTerminal = nonTerminal "ExponentIndicator"
op SignedInteger                   : NonTerminal = nonTerminal "SignedInteger"
op Sign                            : NonTerminal = nonTerminal "Sign"
op FloatTypeSuffix                 : NonTerminal = nonTerminal "FloatTypeSuffix"
% --
op HexadecimalFloatingPointLiteral : NonTerminal = nonTerminal "HexadecimalFloatingPointLiteral"
op HexSignificand                  : NonTerminal = nonTerminal "HexSignificand"
op BinaryExponent                  : NonTerminal = nonTerminal "BinaryExponent"
op BinaryExponentIndicator         : NonTerminal = nonTerminal "BinaryExponentIndicator"

op Directives_3_10_2_Floating_Point_Literals : Directives =
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

op BooleanLiteral : NonTerminal = nonTerminal "BooleanLiteral"

op Directives_3_10_3_Boolean_Literals : Directives =
 [Header "3.10.3. Boolean Literals",

  Rule {lhs = BooleanLiteral,
        rhs = Any [kw_true, kw_false]}
  ]

%%% ========================================================================
%%% 3.10.4 Character Literals
%%% ========================================================================

op CharacterLiteral : NonTerminal = nonTerminal "CharacterLiteral"
op SingleCharacter  : NonTerminal = nonTerminal "SingleCharacter"

op Directives_3_10_4_Character_Literals : Directives =
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

op StringLiteral    : NonTerminal = nonTerminal "StringLiteral"
op StringCharacters : NonTerminal = nonTerminal "StringCharacters"
op StringCharacter  : NonTerminal = nonTerminal "StringCharacter"

op Directives_3_10_5_String_Literals : Directives =
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

op EscapeSequence : NonTerminal = nonTerminal "EscapeSequence"
op OctalEscape    : NonTerminal = nonTerminal "OctalEscape"
op ZeroToThree    : NonTerminal = nonTerminal "ZeroToThree"

op Directives_3_10_6_Escape_Sequences : Directives =
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

op NullLiteral : NonTerminal = nonTerminal "NullLiteral"

op Directives_3_10_7_Null_LIteral : Directives =
 [Header "3.10.7. The Null Literal",

  Rule {lhs = NullLiteral,
        rhs = keyword "null"}
  ]

%%% ========================================================================
%%% 3.11. Separators
%%% ========================================================================

op Separator : NonTerminal = nonTerminal "Separator"

op Directives_3_11_Separators : Directives =
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

op Operator : NonTerminal = nonTerminal "Operator"

op Directives_3_12_Operators : Directives =
 [Header "3.12. Operators",

  Rule {lhs = Separator,
        rhs = Any [equal_sign, right_angle, left_angle, exclamation, tilde, question_mark, colon          ,
                   op_==, op_<=, op_>=, op_!=, op_&&, op_||, op_++, op_--,
                   ampersand, bar, carrot, percent,
                   op_<<, op_>>, op_>>>, op_+=, op_-=, op_*=, op_/=, op_&=, op_|=, op_^=,
                   op_percent_=, op_<<=, op_>>=, op_>>>=]}
  ]

%%% ========================================================================
%%% 3.12. Operators
%%% ========================================================================

op Directives_Java_Tokens : Directives =
 Directives_Ad_Hoc_Keywords
 ++ Directives_3_3_Unicode_Escapes 
 ++ Directives_3_4_Line_Terminators
 ++ Directives_3_5_Input_Elements
 ++ Directives_3_6_WhiteSpace
 ++ Directives_3_7_Comments
 ++ Directives_3_8_Identifiers 
 ++ Directives_3_9_Keywords 
 ++ Directives_3_10_Literals
 ++ Directives_3_10_1_Integer_Literals
 ++ Directives_3_10_2_Floating_Point_Literals
 ++ Directives_3_10_3_Boolean_Literals 
 ++ Directives_3_10_4_Character_Literals
 ++ Directives_3_10_5_String_Literals 
 ++ Directives_3_10_6_Escape_Sequences
 ++ Directives_3_10_7_Null_LIteral
 ++ Directives_3_11_Separators
 ++ Directives_3_12_Operators

end-spec
