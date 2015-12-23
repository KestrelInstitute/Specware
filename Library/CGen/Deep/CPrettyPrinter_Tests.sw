(* Copyright 2015 Kestrel Institute. See file LICENSE for license details *)

PP qualifying spec

import CPrettyPrinter
import /Library/Legacy/Utilities/System  %to get writeLine

(* This spec contains various tests for the C pretty printer.

Each test consists of a name (a string) to identify the test and a boolean
expression that must yield true for the test to succeed. The tests are organized
as a list of (string, boolean) pairs.

Since the pretty printing ops are monadic, the following op turns an element M
of the monad into text by applying M to a state consisting of the empty text and
of the indentation size and level given by the arguments, and then returning the
obtained text. This is useful for unit testing of the pretty printing ops. *)

op text (indLev:Nat) (indSize:Nat) (m:PP0) : Text =
  (m {text = emptyText, indentLevel = indLev, indentSize = indSize}).1.text

(* The following are the tests. We try to exercise all the ops that comprise the
pretty printer, in the order they appear in the code of the pretty printer. We
try to exercise all the control paths of these ops. *)

op tests : List (String * Bool) =
[(
"empty_text",
emptyText = ""
),(
"init_state_1",
initState 0 = {text = emptyText, indentLevel = 0, indentSize = 0}
),(
"init_state_2",
initState 1 = {text = emptyText, indentLevel = 0, indentSize = 1}
),(
"init_state_3",
initState 100 = {text = emptyText, indentLevel = 0, indentSize = 100}
),(
"monad_bind",
{x <- fn st -> (st << {text = st.text ^ "abc",
                       indentLevel = st.indentLevel + 3,
                       indentSize = st.indentSize + 1},
                st.indentLevel + st.indentSize);
 fn st -> (st << {text = "G",
                  indentLevel = x,
                  indentSize = 2 * x},
           length st.text)}
{text = "0123456789", indentLevel = 8, indentSize = 14} =
({text = "G", indentLevel = 22, indentSize = 44}, 13)
),(
"print_1",
(print "ABC") {text = "123", indentLevel = 8, indentSize = 14} =
({text = "123ABC", indentLevel = 8, indentSize = 14}, ())
),(
"print_2",
{print "ABC"; print "DEF"; print "GHI"}
{text = "123", indentLevel = 8, indentSize = 14} =
({text = "123ABCDEFGHI", indentLevel = 8, indentSize = 14}, ())
),(
"indent_in_1",
indentIn {text = "abc", indentLevel = 15, indentSize = 9} =
({text = "abc", indentLevel = 16, indentSize = 9}, ())
),(
"indent_in_2",
indentIn {text = "QQ", indentLevel = 15, indentSize = 20} =
({text = "QQ", indentLevel = 16, indentSize = 20}, ())
),(
"indent_out_1",
indentOut {text = "abc", indentLevel = 15, indentSize = 9} =
({text = "abc", indentLevel = 14, indentSize = 9}, ())
),(
"indent_out_2",
indentOut {text = "QQ", indentLevel = 15, indentSize = 20} =
({text = "QQ", indentLevel = 14, indentSize = 20}, ())
),(
"indent_in_out_1",
{indentIn; indentIn; indentOut; indentIn; indentIn}
{text = "64738", indentLevel = 2, indentSize = 3} =
({text = "64738", indentLevel = 5, indentSize = 3}, ())
),(
"indent_in_out_2",
{indentIn; indentIn; indentOut; indentIn; indentIn}
{text = "64738", indentLevel = 2, indentSize = 33} =
({text = "64738", indentLevel = 5, indentSize = 33}, ())
),(
"indentation_level",
indentationLevel {text = "a", indentLevel = 115, indentSize = 4} =
({text = "a", indentLevel = 115, indentSize = 4}, 115)
),(
"indentation_size",
indentationSize {text = "a", indentLevel = 8, indentSize = 127} =
({text = "a", indentLevel = 8, indentSize = 127}, 127)
),(
"nothing",
text 0 0 printNothing = ""
),(
"nothing'",
text 3 4 printNothing = ""
),(
"space",
text 0 0 printSpace = " "
),(
"space'",
text 3 4 printSpace = " "
),(
"spaces_1",
text 0 0 (printSpaces 0) = ""
),(
"spaces_1'",
text 3 4 (printSpaces 0) = ""
),(
"spaces_2",
text 0 0 (printSpaces 1) = " "
),(
"spaces_2'",
text 3 4 (printSpaces 1) = " "
),(
"spaces_3",
text 0 0 (printSpaces 2) = "  "
),(
"spaces_3'",
text 3 4 (printSpaces 2) = "  "
),(
"spaces_4",
text 0 0 (printSpaces 8) = "        "
),(
"spaces_4'",
text 3 4 (printSpaces 8) = "        "
),(
"newline",
text 0 0 printNewline = "
"
),(
"newline'",
text 3 4 printNewline = "
"
),(
"start_line_1",
text 0 0 startLine = ""
),(
"start_line_2",
text 0 4 startLine = ""
),(
"start_line_3",
text 2 0 startLine = ""
),(
"start_line_4",
text 2 4 startLine = "        "
),(
"start_line_5",
text 1 6 startLine = "      "
),(
"identifier",
text 0 0 (printIdentifier "abcde") = "abcde"
),(
"identifier'",
text 3 4 (printIdentifier "abcde") = "abcde"
),(
"constant",
text 0 0 (printConstant "123UL") = "123UL"
),(
"constant'",
text 3 4 (printConstant "123UL") = "123UL"
),(
"ADDR",
text 0 0 (printUnaryOp ADDR) = "&"
),(
"ADDR'",
text 3 4 (printUnaryOp ADDR) = "&"
),(
"STAR",
text 0 0 (printUnaryOp STAR) = "*"
),(
"STAR'",
text 3 4 (printUnaryOp STAR) = "*"
),(
"PLUS",
text 0 0 (printUnaryOp PLUS) = "+"
),(
"PLUS'",
text 3 4 (printUnaryOp PLUS) = "+"
),(
"MINUS",
text 0 0 (printUnaryOp MINUS) = "-"
),(
"MINUS'",
text 3 4 (printUnaryOp MINUS) = "-"
),(
"NOT",
text 0 0 (printUnaryOp NOT) = "~"
),(
"NOT'",
text 3 4 (printUnaryOp NOT) = "~"
),(
"NEG",
text 0 0 (printUnaryOp NEG) = "!"
),(
"NEG'",
text 3 4 (printUnaryOp NEG) = "!"
),(
"MUL",
text 0 0 (printBinaryOp MUL) = "*"
),(
"MUL'",
text 3 4 (printBinaryOp MUL) = "*"
),(
"DIV",
text 0 0 (printBinaryOp DIV) = "/"
),(
"DIV'",
text 3 4 (printBinaryOp DIV) = "/"
),(
"REM",
text 0 0 (printBinaryOp REM) = "%"
),(
"REM'",
text 3 4 (printBinaryOp REM) = "%"
),(
"ADD",
text 0 0 (printBinaryOp ADD) = "+"
),(
"ADD'",
text 3 4 (printBinaryOp ADD) = "+"
),(
"SUB",
text 0 0 (printBinaryOp SUB) = "-"
),(
"SUB'",
text 3 4 (printBinaryOp SUB) = "-"
),(
"SHL",
text 0 0 (printBinaryOp SHL) = "<<"
),(
"SHL'",
text 3 4 (printBinaryOp SHL) = "<<"
),(
"SHR",
text 0 0 (printBinaryOp SHR) = ">>"
),(
"SHR'",
text 3 4 (printBinaryOp SHR) = ">>"
),(
"LT",
text 0 0 (printBinaryOp LT) = "<"
),(
"LT'",
text 3 4 (printBinaryOp LT) = "<"
),(
"GT",
text 0 0 (printBinaryOp GT) = ">"
),(
"GT'",
text 3 4 (printBinaryOp GT) = ">"
),(
"LE",
text 0 0 (printBinaryOp LE) = "<="
),(
"LE'",
text 3 4 (printBinaryOp LE) = "<="
),(
"GE",
text 0 0 (printBinaryOp GE) = ">="
),(
"GE'",
text 3 4 (printBinaryOp GE) = ">="
),(
"EQ",
text 0 0 (printBinaryOp EQ) = "=="
),(
"EQ'",
text 3 4 (printBinaryOp EQ) = "=="
),(
"NE",
text 0 0 (printBinaryOp NE) = "!="
),(
"NE'",
text 3 4 (printBinaryOp NE) = "!="
),(
"AND",
text 0 0 (printBinaryOp AND) = "&"
),(
"AND'",
text 3 4 (printBinaryOp AND) = "&"
),(
"XOR",
text 0 0 (printBinaryOp XOR) = "^"
),(
"XOR'",
text 3 4 (printBinaryOp XOR) = "^"
),(
"IOR",
text 0 0 (printBinaryOp IOR) = "|"
),(
"IOR'",
text 3 4 (printBinaryOp IOR) = "|"
),(
"LAND",
text 0 0 (printBinaryOp LAND) = "&&"
),(
"LAND'",
text 3 4 (printBinaryOp LAND) = "&&"
),(
"LOR",
text 0 0 (printBinaryOp LOR) = "||"
),(
"LOR'",
text 3 4 (printBinaryOp LOR) = "||"
),(
"kind_precedence_EXPR",
kindPrec EXPR = 0
),(
"kind_precedence_COND",
kindPrec COND = 1
),(
"kind_precedence_LOR",
kindPrec LOR = 2
),(
"kind_precedence_LAND",
kindPrec LAND = 3
),(
"kind_precedence_IOR",
kindPrec IOR = 4
),(
"kind_precedence_XOR",
kindPrec XOR = 5
),(
"kind_precedence_AND",
kindPrec AND = 6
),(
"kind_precedence_EQ",
kindPrec (embed EQ) = 7
),(
"kind_precedence_REL",
kindPrec REL = 8
),(
"kind_precedence_SHIFT",
kindPrec SHIFT = 9
),(
"kind_precedence_ADD",
kindPrec ADD = 10
),(
"kind_precedence_MUL",
kindPrec MUL = 11
),(
"kind_precedence_CAST",
kindPrec CAST = 12
),(
"kind_precedence_UNARY",
kindPrec UNARY = 13
),(
"kind_precedence_POST",
kindPrec POST = 14
),(
"kind_precedence_PRIM",
kindPrec PRIM = 15
),(
"expression_kind_1",
exprKind (ident "x") = PRIM
),(
"expression_kind_2",
exprKind (const "0") = PRIM
),(
"expression_kind_3",
exprKind (unary (NOT, ident "x")) = UNARY
),(
"expression_kind_4",
exprKind (binary (ident "x", MUL, ident "x")) = MUL
),(
"expression_kind_5",
exprKind (binary (ident "x", DIV, ident "x")) = MUL
),(
"expression_kind_6",
exprKind (binary (ident "x", REM, ident "x")) = MUL
),(
"expression_kind_7",
exprKind (binary (ident "x", ADD, ident "x")) = ADD
),(
"expression_kind_8",
exprKind (binary (ident "x", SUB, ident "x")) = ADD
),(
"expression_kind_9",
exprKind (binary (ident "x", SHL, ident "x")) = SHIFT
),(
"expression_kind_10",
exprKind (binary (ident "x", SHR, ident "x")) = SHIFT
),(
"expression_kind_11",
exprKind (binary (ident "x", LT, ident "x")) = REL
),(
"expression_kind_12",
exprKind (binary (ident "x", GT, ident "x")) = REL
),(
"expression_kind_13",
exprKind (binary (ident "x", LE, ident "x")) = REL
),(
"expression_kind_14",
exprKind (binary (ident "x", GE, ident "x")) = REL
),(
"expression_kind_15",
exprKind (binary (ident "x", EQ, ident "x")) = EQ
),(
"expression_kind_16",
exprKind (binary (ident "x", NE, ident "x")) = EQ
),(
"expression_kind_17",
exprKind (binary (ident "x", AND, ident "x")) = AND
),(
"expression_kind_18",
exprKind (binary (ident "x", XOR, ident "x")) = XOR
),(
"expression_kind_19",
exprKind (binary (ident "x", IOR, ident "x")) = IOR
),(
"expression_kind_20",
exprKind (binary (ident "x", LAND, ident "x")) = LAND
),(
"expression_kind_21",
exprKind (binary (ident "x", LOR, ident "x")) = LOR
),(
"expression_kind_22",
exprKind (cond (ident "x", ident "x", ident "x", char)) = COND
),(
"expression_kind_23",
exprKind (member (ident "x", "m")) = POST
),(
"expression_kind_24",
exprKind (memberp (ident "x", "m")) = POST
),(
"expression_kind_25",
exprKind (subscript (ident "x", ident "i")) = POST
),(
"expression_kind_26",
exprKind nullconst = CAST
),(
"expression_precedence_1",
exprPrec (binary (ident "x", GT, ident "x")) = 8
),(
"expression_precedence_2",
exprPrec (member (ident "x", "m")) = 14
),(
"binary_expected_MUL",
binaryExpected MUL = (MUL, CAST)
),(
"binary_expected_DIV",
binaryExpected DIV = (MUL, CAST)
),(
"binary_expected_REM",
binaryExpected REM = (MUL, CAST)
),(
"binary_expected_ADD",
binaryExpected ADD = (ADD, MUL)
),(
"binary_expected_SUB",
binaryExpected SUB = (ADD, MUL)
),(
"binary_expected_SHL",
binaryExpected SHL = (SHIFT, ADD)
),(
"binary_expected_SHR",
binaryExpected SHR = (SHIFT, ADD)
),(
"binary_expected_LT",
binaryExpected LT = (REL, SHIFT)
),(
"binary_expected_GT",
binaryExpected GT = (REL, SHIFT)
),(
"binary_expected_LE",
binaryExpected LE = (REL, SHIFT)
),(
"binary_expected_GE",
binaryExpected GE = (REL, SHIFT)
),(
"binary_expected_EQ",
binaryExpected (embed EQ) = (EQ, REL)
),(
"binary_expected_NE",
binaryExpected NE = (EQ, REL)
),(
"binary_expected_AND",
binaryExpected AND = (AND, EQ)
),(
"binary_expected_XOR",
binaryExpected XOR = (XOR, AND)
),(
"binary_expected_IOR",
binaryExpected IOR = (IOR, XOR)
),(
"binary_expected_LAND",
binaryExpected LAND = (LAND, IOR)
),(
"binary_expected_LOR",
binaryExpected LOR = (LOR, LAND)
),(
"expression_1",
text 0 0 (printExpression (binary (ident "x", ADD, ident "y"), MUL)) =
"(x + y)"
),(
"expression_1'",
text 3 4 (printExpression (binary (ident "x", ADD, ident "y"), MUL)) =
"(x + y)"
),(
"expression_2",
text 0 0 (printExpression (ident "uu", POST)) = "uu"
),(
"expression_2'",
text 3 4 (printExpression (ident "var", EQ)) = "var"
),(
"expression_3",
text 0 0 (printExpression (const "5", SHIFT)) = "5"
),(
"expression_3'",
text 3 4 (printExpression (const "0777", COND)) = "0777"
),(
"expression_4",
text 0 0 (printExpression (unary (STAR, ident "pfile"), IOR)) = "*pfile"
),(
"expression_4'",
text 3 4 (printExpression (unary (MINUS, ident "g"), IOR)) = "-g"
),(
"expression_5",
text 0 0 (printExpression (binary (ident "x", ADD, ident "y"), ADD)) = "x + y"
),(
"expression_5'",
text 3 4 (printExpression (binary (ident "x", XOR, ident "y"), EXPR)) = "x ^ y"
),(
"expression_6",
text 0 0 (printExpression
           (cond (ident "a", ident "b", ident "c", char), COND)) =
"a ? b : c"
),(
"expression_6'",
text 3 4 (printExpression
           (cond (ident "a", ident "b", ident "c", char), EXPR)) =
"a ? b : c"
),(
"expression_7",
text 0 0 (printExpression (member (ident "r", "f"), LAND)) = "r.f"
),(
"expression_7'",
text 3 4 (printExpression (member (ident "rec", "fld"), SHIFT)) = "rec.fld"
),(
"expression_8",
text 0 0 (printExpression (memberp (ident "p", "g"), REL)) = "p->g"
),(
"expression_8'",
text 3 4 (printExpression (memberp (ident "prec", "go"), LOR)) = "prec->go"
),(
"expression_9",
text 0 0 (printExpression (subscript (ident "a", ident "i"), UNARY)) = "a[i]"
),(
"expression_9'",
text 3 4 (printExpression (subscript (ident "b", ident "j"), POST)) = "b[j]"
),(
"expression_10",
text 0 0 (printExpression (nullconst, MUL)) = "(void*) 0"
),(
"expression_10'",
text 3 4 (printExpression (nullconst, COND)) = "(void*) 0"
),(
"expression_11",
text 0 0
  (printTopExpression
    (binary (ident "x", ADD, binary (ident "y", SUB, ident "z")))) =
"x + (y - z)"
),(
"expression_11'",
text 3 4
  (printTopExpression
    (binary (ident "x", ADD, binary (ident "y", SUB, ident "z")))) =
"x + (y - z)"
),(
"expression_12",
text 0 0
  (printTopExpression
    (binary (binary (ident "x", MUL, ident "y"), DIV, ident "z"))) =
"x * y / z"
),(
"expression_12'",
text 3 4
  (printTopExpression
    (binary (binary (ident "x", MUL, ident "y"), DIV, ident "z"))) =
"x * y / z"
),(
"expression_13",
text 0 0
  (printTopExpression
    (binary (ident "x", SHL, binary (ident "y", LT, ident "z")))) =
"x << (y < z)"
),(
"expression_13'",
text 3 4
  (printTopExpression
    (binary (ident "x", SHL, binary (ident "y", LT, ident "z")))) =
"x << (y < z)"
),(
"expression_14",
text 0 0
  (printTopExpression
    (member (subscript (unary (STAR, ident "p"),
                        binary (ident "i", ADD, const "1")),
             "memb"))) =
"(*p)[i + 1].memb"
),(
"expression_14'",
text 3 4
  (printTopExpression
    (member (subscript (unary (STAR, ident "p"),
                        binary (ident "i", ADD, const "1")),
             "memb"))) =
"(*p)[i + 1].memb"
),(
"expression_15",
text 0 0
  (printTopExpression
    (binary (binary (const "2", MUL, ident "i"), ADD, const "1"))) =
"2 * i + 1"
),(
"expression_15'",
text 3 4
  (printTopExpression
    (binary (binary (const "2", MUL, ident "i"), ADD, const "1"))) =
"2 * i + 1"
),(
"expression_16",
text 0 0
  (printTopExpression
    (binary (const "2", MUL, binary (ident "i", ADD, const "1")))) =
"2 * (i + 1)"
),(
"expression_16'",
text 3 4
  (printTopExpression
    (binary (const "2", MUL, binary (ident "i", ADD, const "1")))) =
"2 * (i + 1)"
),(
"expression_17",
text 0 0
  (printTopExpression
    (binary (binary (ident "i", ADD, ident "j"), DIV, const "2"))) =
"(i + j) / 2"
),(
"expression_17'",
text 3 4
  (printTopExpression
    (binary (binary (ident "i", ADD, ident "j"), DIV, const "2"))) =
"(i + j) / 2"
),(
"expression_18",
text 0 0
  (printTopExpression
    (binary (ident "i", ADD, binary (ident "j", DIV, const "2")))) =
"i + j / 2"
),(
"expression_18'",
text 3 4
  (printTopExpression
    (binary (ident "i", ADD, binary (ident "j", DIV, const "2")))) =
"i + j / 2"
),(
"expression_19",
text 0 0 (printTopExpression (unary (NEG, nullconst))) = "!((void*) 0)"
),(
"expression_19'",
text 3 4 (printTopExpression (unary (NEG, nullconst))) = "!((void*) 0)"
),(
"expression_20",
text 0 0
  (printTopExpression
    (binary (binary (ident "x", GT, const "0"),
             LAND,
             binary (ident "y", EQ, const "3")))) =
"x > 0 && y == 3"
),(
"expression_20'",
text 3 4
  (printTopExpression
    (binary (binary (ident "x", GT, const "0"),
             LAND,
             binary (ident "y", EQ, const "3")))) =
"x > 0 && y == 3"
),(
"split_type_name_1",
splitTypeName (char, "x") = (char, ident "x")
),(
"split_type_name_2",
splitTypeName (uchar, "x") = (uchar, ident "x")
),(
"split_type_name_3",
splitTypeName (schar, "x") = (schar, ident "x")
),(
"split_type_name_4",
splitTypeName (ushort, "x") = (ushort, ident "x")
),(
"split_type_name_5",
splitTypeName (sshort, "x") = (sshort, ident "x")
),(
"split_type_name_6",
splitTypeName (uint, "x") = (uint, ident "x")
),(
"split_type_name_7",
splitTypeName (sint, "x") = (sint, ident "x")
),(
"split_type_name_8",
splitTypeName (ulong, "x") = (ulong, ident "x")
),(
"split_type_name_9",
splitTypeName (slong, "x") = (slong, ident "x")
),(
"split_type_name_10",
splitTypeName (ullong, "x") = (ullong, ident "x")
),(
"split_type_name_11",
splitTypeName (sllong, "x") = (sllong, ident "x")
),(
"split_type_name_12",
splitTypeName (void, "x") = (void, ident "x")
),(
"split_type_name_13",
splitTypeName (typedef "T", "x") = (typedef "T", ident "x")
),(
"split_type_name_14",
splitTypeName (struct "S", "x") = (struct "S", ident "x")
),(
"split_type_name_15",
splitTypeName (pointer uchar, "x") = (uchar, pointer (ident "x"))
),(
"split_type_name_16",
splitTypeName (array (char, 10), "x") = (char, array (ident "x", 10))
),(
"split_type_name_17",
splitTypeName (array (pointer char, 10), "x") =
(char, pointer (array (ident "x", 10)))
),(
"split_type_name_18",
splitTypeName (pointer (array (char, 10)), "x") =
(char, array (pointer (ident "x"), 10))
),(
"split_type_name_19",
splitTypeName (pointer (array (pointer sint, 22)), "x") =
(sint, pointer (array (pointer (ident "x"), 22)))
),(
"split_type_name_20",
splitTypeName (array (array (sint, 2), 20), "x") =
(sint, array (array (ident "x", 20), 2))
),(
"split_type_name_21",
splitTypeName (array (pointer (array (ullong, 10)), 100), "x") =
(ullong, array (pointer (array (ident "x", 100)), 10))
),(
"char",
text 0 0 (printNonSplitTypeName char) = "char"
),(
"char'",
text 3 4 (printNonSplitTypeName char) = "char"
),(
"uchar",
text 0 0 (printNonSplitTypeName uchar) = "unsigned char"
),(
"uchar'",
text 3 4 (printNonSplitTypeName uchar) = "unsigned char"
),(
"schar",
text 0 0 (printNonSplitTypeName schar) = "signed char"
),(
"schar'",
text 3 4 (printNonSplitTypeName schar) = "signed char"
),(
"ushort",
text 0 0 (printNonSplitTypeName ushort) = "unsigned short"
),(
"ushort'",
text 3 4 (printNonSplitTypeName ushort) = "unsigned short"
),(
"sshort",
text 0 0 (printNonSplitTypeName sshort) = "short"
),(
"sshort'",
text 3 4 (printNonSplitTypeName sshort) = "short"
),(
"uint",
text 0 0 (printNonSplitTypeName uint) = "unsigned int"
),(
"uint'",
text 3 4 (printNonSplitTypeName uint) = "unsigned int"
),(
"sint",
text 0 0 (printNonSplitTypeName sint) = "int"
),(
"sint'",
text 3 4 (printNonSplitTypeName sint) = "int"
),(
"ulong",
text 0 0 (printNonSplitTypeName ulong) = "unsigned long"
),(
"ulong'",
text 3 4 (printNonSplitTypeName ulong) = "unsigned long"
),(
"slong",
text 0 0 (printNonSplitTypeName slong) = "long"
),(
"slong'",
text 3 4 (printNonSplitTypeName slong) = "long"
),(
"ullong",
text 0 0 (printNonSplitTypeName ullong) = "unsigned long long"
),(
"ullong'",
text 3 4 (printNonSplitTypeName ullong) = "unsigned long long"
),(
"sllong",
text 0 0 (printNonSplitTypeName sllong) = "long long"
),(
"sllong'",
text 3 4 (printNonSplitTypeName sllong) = "long long"
),(
"void",
text 0 0 (printNonSplitTypeName void) = "void"
),(
"void'",
text 3 4 (printNonSplitTypeName void) = "void"
),(
"typedef",
text 0 0 (printNonSplitTypeName (typedef "u1")) = "u1"
),(
"typedef'",
text 3 4 (printNonSplitTypeName (typedef "u1")) = "u1"
),(
"struct",
text 0 0 (printNonSplitTypeName (struct "node")) = "struct node"
),(
"struct'",
text 3 4 (printNonSplitTypeName (struct "node")) = "struct node"
),(
"declarator_1",
text 0 0 (printDeclarator (ident "c")) = "c"
),(
"declarator_1'",
text 3 4 (printDeclarator (ident "c")) = "c"
),(
"declarator_2",
text 0 0 (printDeclarator (pointer (ident "c"))) = "*c"
),(
"declarator_2'",
text 3 4 (printDeclarator (pointer (ident "c"))) = "*c"
),(
"declarator_3",
text 0 0 (printDeclarator (array (ident "c", 100))) = "c[100]"
),(
"declarator_3'",
text 3 4 (printDeclarator (array (ident "c", 100))) = "c[100]"
),(
"declarator_4",
text 0 0 (printDeclarator (array (pointer (ident "c"), 100))) = "(*c)[100]"
),(
"declarator_4'",
text 3 4 (printDeclarator (array (pointer (ident "c"), 100))) = "(*c)[100]"
),(
"declarator_5",
text 0 0 (printDeclarator (pointer (pointer (ident "c")))) = "**c"
),(
"declarator_5'",
text 3 4 (printDeclarator (pointer (pointer (ident "c")))) = "**c"
),(
"declarator_6",
text 0 0 (printDeclarator (pointer (array (ident "c", 100)))) = "*c[100]"
),(
"declarator_6'",
text 3 4 (printDeclarator (pointer (array (ident "c", 100)))) = "*c[100]"
),(
"type_name_and_name_1",
text 0 0 (printTypeNameAndName (sshort, "sh")) = "short sh"
),(
"type_name_and_name_1'",
text 3 4 (printTypeNameAndName (sshort, "sh")) = "short sh"
),(
"type_name_and_name_2",
text 0 0 (printTypeNameAndName (pointer (pointer uchar), "argv")) =
"unsigned char **argv"
),(
"type_name_and_name_2'",
text 3 4 (printTypeNameAndName (pointer (pointer uchar), "argv")) =
"unsigned char **argv"
),(
"type_name_and_name_3",
text 0 0 (printTypeNameAndName (pointer (array (sint, 5)), "c")) =
"int (*c)[5]"
),(
"type_name_and_name_3'",
text 3 4 (printTypeNameAndName (pointer (array (sint, 5)), "c")) =
"int (*c)[5]"
),(
"type_name_and_name_4",
text 0 0 (printTypeNameAndName (array (array (uint, 10), 100), "a")) =
"unsigned int a[100][10]"
),(
"type_name_and_name_4'",
text 0 0 (printTypeNameAndName (array (array (uint, 10), 100), "a")) =
"unsigned int a[100][10]"
),(
"object_declaration_1",
text 0 0 (printObjectDeclaration {typE = pointer sint, name = "pi"}) =
"int *pi;
"
),(
"object_declaration_2",
text 0 4 (printObjectDeclaration {typE = pointer sint, name = "pi"}) =
"int *pi;
"
),(
"object_declaration_3",
text 2 0 (printObjectDeclaration {typE = pointer sint, name = "pi"}) =
"int *pi;
"
),(
"object_declaration_4",
text 2 4 (printObjectDeclaration {typE = pointer sint, name = "pi"}) =
"        int *pi;
"
),(
"object_declaration_5",
text 1 6 (printObjectDeclaration {typE = pointer sint, name = "pi"}) =
"      int *pi;
"
),(
"member_declaration",
text 0 0 (printMemberDeclaration {typE = typedef "bool", name = "flag"}) =
"bool flag"
),(
"member_declaration'",
text 3 4 (printMemberDeclaration {typE = typedef "bool", name = "flag"}) =
"bool flag"
),(
"member_declarations_1_1",
text 0 0 (printMemberDeclarations []) = ""
),(
"member_declarations_2_1",
text 0 0 (printMemberDeclarations [{typE = struct "S", name = "f"}]) =
"struct S f
"
),(
"member_declarations_3_1",
text 0 0 (printMemberDeclarations [{typE = struct "S", name = "f"},
                                   {typE = array (uchar, 30), name = "g"}]) =
"struct S f,
unsigned char g[30]
"
),(
"member_declarations_4_1",
text 0 0 (printMemberDeclarations
            [{typE = struct "S", name = "f"},
             {typE = array (uchar, 30), name = "g"},
             {typE = sint, name = "h"},
             {typE = pointer (struct "node"), name = "j"}]) =
"struct S f,
unsigned char g[30],
int h,
struct node *j
"
),(
"member_declarations_1_2",
text 0 4 (printMemberDeclarations []) = ""
),(
"member_declarations_2_2",
text 0 4 (printMemberDeclarations [{typE = struct "S", name = "f"}]) =
"struct S f
"
),(
"member_declarations_3_2",
text 0 4 (printMemberDeclarations [{typE = struct "S", name = "f"},
                                   {typE = array (uchar, 30), name = "g"}]) =
"struct S f,
unsigned char g[30]
"
),(
"member_declarations_4_2",
text 0 4 (printMemberDeclarations
            [{typE = struct "S", name = "f"},
             {typE = array (uchar, 30), name = "g"},
             {typE = sint, name = "h"},
             {typE = pointer (struct "node"), name = "j"}]) =
"struct S f,
unsigned char g[30],
int h,
struct node *j
"
),(
"member_declarations_1_3",
text 2 0 (printMemberDeclarations []) = ""
),(
"member_declarations_2_3",
text 2 0 (printMemberDeclarations [{typE = struct "S", name = "f"}]) =
"struct S f
"
),(
"member_declarations_3_3",
text 2 0 (printMemberDeclarations [{typE = struct "S", name = "f"},
                                   {typE = array (uchar, 30), name = "g"}]) =
"struct S f,
unsigned char g[30]
"
),(
"member_declarations_4_3",
text 2 0 (printMemberDeclarations
            [{typE = struct "S", name = "f"},
             {typE = array (uchar, 30), name = "g"},
             {typE = sint, name = "h"},
             {typE = pointer (struct "node"), name = "j"}]) =
"struct S f,
unsigned char g[30],
int h,
struct node *j
"
),(
"member_declarations_1_4",
text 2 4 (printMemberDeclarations []) = ""
),(
"member_declarations_2_4",
text 2 4 (printMemberDeclarations [{typE = struct "S", name = "f"}]) =
"        struct S f
"
),(
"member_declarations_3_4",
text 2 4 (printMemberDeclarations [{typE = struct "S", name = "f"},
                                   {typE = array (uchar, 30), name = "g"}]) =
"        struct S f,
        unsigned char g[30]
"
),(
"member_declarations_4_4",
text 2 4 (printMemberDeclarations
            [{typE = struct "S", name = "f"},
             {typE = array (uchar, 30), name = "g"},
             {typE = sint, name = "h"},
             {typE = pointer (struct "node"), name = "j"}]) =
"        struct S f,
        unsigned char g[30],
        int h,
        struct node *j
"
),(
"member_declarations_1_5",
text 1 6 (printMemberDeclarations []) = ""
),(
"member_declarations_2_5",
text 1 6 (printMemberDeclarations [{typE = struct "S", name = "f"}]) =
"      struct S f
"
),(
"member_declarations_3_5",
text 1 6 (printMemberDeclarations [{typE = struct "S", name = "f"},
                                   {typE = array (uchar, 30), name = "g"}]) =
"      struct S f,
      unsigned char g[30]
"
),(
"member_declarations_4_5",
text 1 6 (printMemberDeclarations
            [{typE = struct "S", name = "f"},
             {typE = array (uchar, 30), name = "g"},
             {typE = sint, name = "h"},
             {typE = pointer (struct "node"), name = "j"}]) =
"      struct S f,
      unsigned char g[30],
      int h,
      struct node *j
"
),(
"struct_specifier_1_1",
text 0 0 (printStructSpecifier
          {tag = "Node",
           members = []}) =
"struct Node {
};
"
),(
"struct_specifier_2_1",
text 0 0 (printStructSpecifier
          {tag = "Node",
           members = [{typE = struct "S", name = "f"}]}) =
"struct Node {
struct S f
};
"
),(
"struct_specifier_3_1",
text 0 0 (printStructSpecifier
          {tag = "Node",
           members = [{typE = struct "S", name = "f"},
                      {typE = array (uchar, 30), name = "g"}]}) =
"struct Node {
struct S f,
unsigned char g[30]
};
"
),(
"struct_specifier_4_1",
text 0 0 (printStructSpecifier
          {tag = "Node",
           members = [{typE = struct "S", name = "f"},
                      {typE = array (uchar, 30), name = "g"},
                      {typE = sint, name = "h"},
                      {typE = pointer (struct "node"), name = "j"}]}) =
"struct Node {
struct S f,
unsigned char g[30],
int h,
struct node *j
};
"
),(
"struct_specifier_1_2",
text 0 4 (printStructSpecifier
          {tag = "Node",
           members = []}) =
"struct Node {
};
"
),(
"struct_specifier_2_2",
text 0 4 (printStructSpecifier
          {tag = "Node",
           members = [{typE = struct "S", name = "f"}]}) =
"struct Node {
    struct S f
};
"
),(
"struct_specifier_3_2",
text 0 4 (printStructSpecifier
          {tag = "Node",
           members = [{typE = struct "S", name = "f"},
                      {typE = array (uchar, 30), name = "g"}]}) =
"struct Node {
    struct S f,
    unsigned char g[30]
};
"
),(
"struct_specifier_4_2",
text 0 4 (printStructSpecifier
          {tag = "Node",
           members = [{typE = struct "S", name = "f"},
                      {typE = array (uchar, 30), name = "g"},
                      {typE = sint, name = "h"},
                      {typE = pointer (struct "node"), name = "j"}]}) =
"struct Node {
    struct S f,
    unsigned char g[30],
    int h,
    struct node *j
};
"
),(
"struct_specifier_1_3",
text 2 0 (printStructSpecifier
          {tag = "Node",
           members = []}) =
"struct Node {
};
"
),(
"struct_specifier_2_3",
text 2 0 (printStructSpecifier
          {tag = "Node",
           members = [{typE = struct "S", name = "f"}]}) =
"struct Node {
struct S f
};
"
),(
"struct_specifier_3_3",
text 2 0 (printStructSpecifier
          {tag = "Node",
           members = [{typE = struct "S", name = "f"},
                      {typE = array (uchar, 30), name = "g"}]}) =
"struct Node {
struct S f,
unsigned char g[30]
};
"
),(
"struct_specifier_4_3",
text 2 0 (printStructSpecifier
          {tag = "Node",
           members = [{typE = struct "S", name = "f"},
                      {typE = array (uchar, 30), name = "g"},
                      {typE = sint, name = "h"},
                      {typE = pointer (struct "node"), name = "j"}]}) =
"struct Node {
struct S f,
unsigned char g[30],
int h,
struct node *j
};
"
),(
"struct_specifier_1_4",
text 2 4 (printStructSpecifier
          {tag = "Node",
           members = []}) =
"        struct Node {
        };
"
),(
"struct_specifier_2_4",
text 2 4 (printStructSpecifier
          {tag = "Node",
           members = [{typE = struct "S", name = "f"}]}) =
"        struct Node {
            struct S f
        };
"
),(
"struct_specifier_3_4",
text 2 4 (printStructSpecifier
          {tag = "Node",
           members = [{typE = struct "S", name = "f"},
                      {typE = array (uchar, 30), name = "g"}]}) =
"        struct Node {
            struct S f,
            unsigned char g[30]
        };
"
),(
"struct_specifier_4_4",
text 2 4 (printStructSpecifier
          {tag = "Node",
           members = [{typE = struct "S", name = "f"},
                      {typE = array (uchar, 30), name = "g"},
                      {typE = sint, name = "h"},
                      {typE = pointer (struct "node"), name = "j"}]}) =
"        struct Node {
            struct S f,
            unsigned char g[30],
            int h,
            struct node *j
        };
"
),(
"struct_specifier_1_5",
text 1 6 (printStructSpecifier
          {tag = "Node",
           members = []}) =
"      struct Node {
      };
"
),(
"struct_specifier_2_5",
text 1 6 (printStructSpecifier
          {tag = "Node",
           members = [{typE = struct "S", name = "f"}]}) =
"      struct Node {
            struct S f
      };
"
),(
"struct_specifier_3_5",
text 1 6 (printStructSpecifier
          {tag = "Node",
           members = [{typE = struct "S", name = "f"},
                      {typE = array (uchar, 30), name = "g"}]}) =
"      struct Node {
            struct S f,
            unsigned char g[30]
      };
"
),(
"struct_specifier_4_5",
text 1 6 (printStructSpecifier
          {tag = "Node",
           members = [{typE = struct "S", name = "f"},
                      {typE = array (uchar, 30), name = "g"},
                      {typE = sint, name = "h"},
                      {typE = pointer (struct "node"), name = "j"}]}) =
"      struct Node {
            struct S f,
            unsigned char g[30],
            int h,
            struct node *j
      };
"
),(
"type_definition_1",
text 0 0 (printTypeDefinition {typE = ushort, name = "u2"}) =
"typedef unsigned short u2;
"
),(
"type_definition_2",
text 2 0 (printTypeDefinition {typE = ushort, name = "u2"}) =
"typedef unsigned short u2;
"
),(
"type_definition_3",
text 0 4 (printTypeDefinition {typE = ushort, name = "u2"}) =
"typedef unsigned short u2;
"
),(
"type_definition_4",
text 2 4 (printTypeDefinition {typE = ushort, name = "u2"}) =
"        typedef unsigned short u2;
"
),(
"type_definition_5",
text 1 6 (printTypeDefinition {typE = ushort, name = "u2"}) =
"      typedef unsigned short u2;
"
),(
"declaration_1_1",
text 0 0 (printDeclaration (object {typE = pointer sint, name = "pi"})) =
"int *pi;
"
),(
"declaration_2_1",
text 0 0 (printDeclaration (typedef {typE = ushort, name = "u2"})) =
"typedef unsigned short u2;
"
),(
"declaration_3_1",
text 0 0 (printDeclaration
           (struct {tag = "Node",
                    members = [{typE = struct "S", name = "f"},
                               {typE = array (uchar, 30), name = "g"}]})) =
"struct Node {
struct S f,
unsigned char g[30]
};
"
),(
"declaration_1_2",
text 0 4 (printDeclaration (object {typE = pointer sint, name = "pi"})) =
"int *pi;
"
),(
"declaration_2_2",
text 0 4 (printDeclaration (typedef {typE = ushort, name = "u2"})) =
"typedef unsigned short u2;
"
),(
"declaration_3_2",
text 0 4 (printDeclaration
           (struct {tag = "Node",
                    members = [{typE = struct "S", name = "f"},
                               {typE = array (uchar, 30), name = "g"}]})) =
"struct Node {
    struct S f,
    unsigned char g[30]
};
"
),(
"declaration_1_3",
text 2 0 (printDeclaration (object {typE = pointer sint, name = "pi"})) =
"int *pi;
"
),(
"declaration_2_3",
text 2 0 (printDeclaration (typedef {typE = ushort, name = "u2"})) =
"typedef unsigned short u2;
"
),(
"declaration_3_3",
text 2 0 (printDeclaration
           (struct {tag = "Node",
                    members = [{typE = struct "S", name = "f"},
                               {typE = array (uchar, 30), name = "g"}]})) =
"struct Node {
struct S f,
unsigned char g[30]
};
"
),(
"declaration_1_4",
text 2 4 (printDeclaration (object {typE = pointer sint, name = "pi"})) =
"        int *pi;
"
),(
"declaration_2_4",
text 2 4 (printDeclaration (typedef {typE = ushort, name = "u2"})) =
"        typedef unsigned short u2;
"
),(
"declaration_3_4",
text 2 4 (printDeclaration
           (struct {tag = "Node",
                    members = [{typE = struct "S", name = "f"},
                               {typE = array (uchar, 30), name = "g"}]})) =
"        struct Node {
            struct S f,
            unsigned char g[30]
        };
"
),(
"declaration_1_5",
text 1 6 (printDeclaration (object {typE = pointer sint, name = "pi"})) =
"      int *pi;
"
),(
"declaration_2_5",
text 1 6 (printDeclaration (typedef {typE = ushort, name = "u2"})) =
"      typedef unsigned short u2;
"
),(
"declaration_3_5",
text 1 6 (printDeclaration
           (struct {tag = "Node",
                    members = [{typE = struct "S", name = "f"},
                               {typE = array (uchar, 30), name = "g"}]})) =
"      struct Node {
            struct S f,
            unsigned char g[30]
      };
"
),(
"arguments_1",
text 0 0 (printArguments []) = ""
),(
"arguments_1'",
text 3 4 (printArguments []) = ""
),(
"arguments_2",
text 0 0 (printArguments [binary (ident "i", ADD, const "1")]) =
"i + 1"
),(
"arguments_2'",
text 3 4 (printArguments [binary (ident "i", ADD, const "1")]) =
"i + 1"
),(
"arguments_3",
text 0 0 (printArguments [binary (ident "i", ADD, const "1"),
                          unary (NOT, ident "z")]) =
"i + 1, ~z"
),(
"arguments_3'",
text 3 4 (printArguments [binary (ident "i", ADD, const "1"),
                          unary (NOT, ident "z")]) =
"i + 1, ~z"
),(
"arguments_4",
text 0 0 (printArguments [binary (ident "i", ADD, const "1"),
                          unary (NOT, ident "z"),
                          unary (STAR, ident "p"),
                          ident "o"]) =
"i + 1, ~z, *p, o"
),(
"arguments_4'",
text 3 4 (printArguments [binary (ident "i", ADD, const "1"),
                          unary (NOT, ident "z"),
                          unary (STAR, ident "p"),
                          ident "o"]) =
"i + 1, ~z, *p, o"
),(
"assignment_1",
text 0 0 (printAssignmentAsExpression (unary (STAR, ident "q"))
                                      (const "33")) =
"*q = 33"
),(
"assignment_1'",
text 3 4 (printAssignmentAsExpression (unary (STAR, ident "q"))
                                      (const "33")) =
"*q = 33"
),(
"assignment_2",
text 0 0 (printAssignmentAsExpression (member (ident "r", "f"))
                                      (cond (ident "a",
                                             ident "b",
                                             ident "c",
                                             char))) =
"r.f = a ? b : c"
),(
"assignment_2'",
text 3 4 (printAssignmentAsExpression (member (ident "r", "f"))
                                      (cond (ident "a",
                                             ident "b",
                                             ident "c",
                                             char))) =
"r.f = a ? b : c"
),(
"call_1",
text 0 0 (printCallAsExpression None "do_it" []) =
"do_it()"
),(
"call_1'",
text 3 4 (printCallAsExpression None "do_it" []) =
"do_it()"
),(
"call_2",
text 0 0 (printCallAsExpression (Some (ident "new"))
                                "quick_sort"
                                [ident "old", const "100"]) =
"new = quick_sort(old, 100)"
),(
"call_2'",
text 3 4 (printCallAsExpression (Some (ident "new"))
                                "quick_sort"
                                [ident "old", const "100"]) =
"new = quick_sort(old, 100)"
),(
"statement_for_1",
text 0 0 (printStatementAsForExpression None) =
""
),(
"statement_for_1",
text 3 4 (printStatementAsForExpression None) =
""
),(
"statement_for_2",
text 0 0 (printStatementAsForExpression
           (Some (assign (unary (STAR, ident "q"), const "33")))) =
"*q = 33"
),(
"statement_for_2'",
text 3 4 (printStatementAsForExpression
           (Some (assign (unary (STAR, ident "q"), const "33")))) =
"*q = 33"
),(
"statement_for_3",
text 0 0 (printStatementAsForExpression
           (Some (call (None, "do_it", [])))) =
"do_it()"
),(
"statement_for_3'",
text 3 4 (printStatementAsForExpression
           (Some (call (None, "do_it", [])))) =
"do_it()"
),(
"statement_for_4",
text 0 0 (printStatementAsForExpression
           (Some (call (Some (ident "new"),
                        "quick_sort",
                        [ident "old", const "100"])))) =
"new = quick_sort(old, 100)"
),(
"statement_for_4'",
text 3 4 (printStatementAsForExpression
           (Some (call (Some (ident "new"),
                        "quick_sort",
                        [ident "old", const "100"])))) =
"new = quick_sort(old, 100)"
),(
"statement_for_5",
text 0 0 (printStatementAsForExpression
           (Some (iF (unary (STAR, ident "q"),
                      assign (ident "y", const "2"),
                      None)))) =
""
),(
"statement_for_5'",
text 3 4 (printStatementAsForExpression
           (Some (iF (unary (STAR, ident "q"),
                      assign (ident "y", const "2"),
                      None)))) =
""
),(
"statement_for_5",
text 0 0 (printStatementAsForExpression (Some (return None))) =
""
),(
"statement_for_5'",
text 3 4 (printStatementAsForExpression (Some (return None))) =
""
),(
"statement_for_6",
text 0 0 (printStatementAsForExpression (Some (while (ident "aq", block [])))) =
""
),(
"statement_for_6'",
text 3 4 (printStatementAsForExpression (Some (while (ident "aq", block [])))) =
""
),(
"statement_for_7",
text 0 0 (printStatementAsForExpression (Some (do (block [], ident "aq")))) =
""
),(
"statement_for_7'",
text 3 4 (printStatementAsForExpression (Some (do (block [], ident "aq")))) =
""
),(
"statement_for_8",
text 0 0 (printStatementAsForExpression
           (Some (for (None, None, None, block [])))) =
""
),(
"statement_for_8'",
text 3 4 (printStatementAsForExpression
           (Some (for (None, None, None, block [])))) =
""
),(
"statement_for_9",
text 0 0 (printStatementAsForExpression (Some (block []))) =
""
),(
"statement_for_9'",
text 3 4 (printStatementAsForExpression (Some (block []))) =
""
),(
"statement_1_1",
text 0 0 (printStatement (assign (unary (STAR, ident "q"),
                                  const "33"))) =
"*q = 33;
"
),(
"statement_2_1",
text 0 0 (printStatement (call (None, "do_it", []))) =
"do_it();
"
),(
"statement_3_1",
text 0 0 (printStatement (call (Some (ident "new"),
                                "quick_sort",
                                [ident "old", const "100"]))) =
"new = quick_sort(old, 100);
"
),(
"statement_4_1",
text 0 0 (printStatement (return None)) =
"return;
"
),(
"statement_5_1",
text 0 0 (printStatement (return (Some (binary (ident "x", MUL, ident "y"))))) =
"return x * y;
"
),(
"statement_6_1",
text 0 0 (printBlockItem (declaration {typE = sint, name = "y"})) =
"int y;
"
),(
"statement_7_1",
text 0 0 (printBlockItem (statement (return (Some (const "0"))))) =
"return 0;
"
),(
"statement_8_1",
text 0 0 (printBlockItems []) = ""
),(
"statement_9_1",
text 0 0 (printBlockItems [statement (return (Some (const "0")))]) =
"return 0;
"
),(
"statement_10_1",
text 0 0 (printBlockItems [statement (return (Some (const "0"))),
                           declaration {typE = sint, name = "y"},
                           statement (assign (ident "a", ident "b"))]) =
"return 0;
int y;
a = b;
"
),(
"statement_11_1",
text 0 0 (printStatement (block [])) =
"{
}
"
),(
"statement_12_1",
text 0 0 (printStatement (block
                          [statement (return (Some (const "0"))),
                           declaration {typE = sint, name = "y"},
                           statement (assign (ident "a", ident "b"))])) =
"{
return 0;
int y;
a = b;
}
"
),(
"statement_13_1",
text 0 0 (printStatement (iF (binary (ident "x", GE, const "0"),
                              assign (ident "y", const "0"),
                              None))) =
"if (x >= 0)
y = 0;
"
),(
"statement_14_1",
text 0 0 (printStatement (iF (binary (ident "x", GE, const "0"),
                              block [],
                              None))) =
"if (x >= 0) {
}
"
),(
"statement_15_1",
text 0 0 (printStatement (iF (binary (ident "x", GE, const "0"),
                              block
                               [statement (return (Some (const "0"))),
                                declaration {typE = sint, name = "y"},
                                statement (assign (ident "a", ident "b"))],
                              None))) =
"if (x >= 0) {
return 0;
int y;
a = b;
}
"
),(
"statement_16_1",
text 0 0 (printStatement (iF (binary (ident "x", GE, const "0"),
                              assign (ident "y", const "0"),
                              Some (call (None, "f", [const "1"]))))) =
"if (x >= 0)
y = 0;
else
f(1);
"
),(
"statement_17_1",
text 0 0 (printStatement (iF (binary (ident "x", GE, const "0"),
                              block [],
                              Some (call (None, "f", [const "1"]))))) =
"if (x >= 0) {
} else
f(1);
"
),(
"statement_18_1",
text 0 0 (printStatement (iF (binary (ident "x", GE, const "0"),
                              block
                               [statement (return (Some (const "0"))),
                                declaration {typE = sint, name = "y"},
                                statement (assign (ident "a", ident "b"))],
                              Some (call (None, "f", [const "1"]))))) =
"if (x >= 0) {
return 0;
int y;
a = b;
} else
f(1);
"
),(
"statement_19_1",
text 0 0 (printStatement (iF (binary (ident "x", GE, const "0"),
                              assign (ident "y", const "0"),
                              Some (block [])))) =
"if (x >= 0)
y = 0;
else {
}
"
),(
"statement_20_1",
text 0 0 (printStatement (iF (binary (ident "x", GE, const "0"),
                              block [],
                              Some (block [])))) =
"if (x >= 0) {
} else {
}
"
),(
"statement_21_1",
text 0 0 (printStatement (iF (binary (ident "x", GE, const "0"),
                              block
                               [statement (return (Some (const "0"))),
                                declaration {typE = sint, name = "y"},
                                statement (assign (ident "a", ident "b"))],
                              Some (block [])))) =
"if (x >= 0) {
return 0;
int y;
a = b;
} else {
}
"
),(
"statement_22_1",
text 0 0 (printStatement
           (iF (binary (ident "x", GE, const "0"),
                assign (ident "y", const "0"),
                Some (block [statement (return (Some (const "0"))),
                             declaration {typE = sint, name = "y"},
                             statement (assign (ident "a", ident "b"))])))) =
"if (x >= 0)
y = 0;
else {
return 0;
int y;
a = b;
}
"
),(
"statement_23_1",
text 0 0 (printStatement
           (iF (binary (ident "x", GE, const "0"),
                block [],
                Some (block [statement (return (Some (const "0"))),
                             declaration {typE = sint, name = "y"},
                             statement (assign (ident "a", ident "b"))])))) =
"if (x >= 0) {
} else {
return 0;
int y;
a = b;
}
"
),(
"statement_24_1",
text 0 0 (printStatement
           (iF (binary (ident "x", GE, const "0"),
                block [statement (return (Some (const "0"))),
                       declaration {typE = sint, name = "y"},
                       statement (assign (ident "a", ident "b"))],
                Some (block [statement (return (Some (const "0"))),
                             declaration {typE = sint, name = "y"},
                             statement (assign (ident "a", ident "b"))])))) =
"if (x >= 0) {
return 0;
int y;
a = b;
} else {
return 0;
int y;
a = b;
}
"
),(
"statement_25_1",
text 0 0 (printStatement
           (while (binary (ident "x", GE, const "0"),
                   assign (ident "y", const "0")))) =
"while (x >= 0)
y = 0;
"
),(
"statement_26_1",
text 0 0 (printStatement
           (while (binary (ident "x", GE, const "0"),
                   block [statement (return (Some (const "0"))),
                          declaration {typE = sint, name = "y"},
                          statement (assign (ident "a", ident "b"))]))) =
"while (x >= 0) {
return 0;
int y;
a = b;
}
"
),(
"statement_27_1",
text 0 0 (printStatement
           (do (assign (ident "y", const "0"),
                binary (ident "x", GE, const "0")))) =
"do
y = 0;
while (x >= 0);
"
),(
"statement_28_1",
text 0 0 (printStatement
           (do (block [statement (return (Some (const "0"))),
                       declaration {typE = sint, name = "y"},
                       statement (assign (ident "a", ident "b"))],
                binary (ident "x", GE, const "0")))) =
"do {
return 0;
int y;
a = b;
} while (x >= 0);
"
),(
"statement_29_1",
text 0 0 (printStatement
           (for (None,
                 None,
                 None,
                 assign (ident "y", const "0")))) =
"for ( ; ; )
y = 0;
"
),(
"statement_30_1",
text 0 0 (printStatement
           (for (None,
                 None,
                 None,
                 block [statement (return (Some (const "0"))),
                        declaration {typE = sint, name = "y"},
                        statement (assign (ident "a", ident "b"))]))) =
"for ( ; ; ) {
return 0;
int y;
a = b;
}
"
),(
"statement_31_1",
text 0 0 (printStatement
           (for (None,
                 None,
                 Some (assign (ident "i", binary (ident "i", ADD, const "1"))),
                 assign (ident "y", const "0")))) =
"for ( ; ; i = i + 1)
y = 0;
"
),(
"statement_32_1",
text 0 0 (printStatement
           (for (None,
                 None,
                 Some (assign (ident "i", binary (ident "i", ADD, const "1"))),
                 block [statement (return (Some (const "0"))),
                        declaration {typE = sint, name = "y"},
                        statement (assign (ident "a", ident "b"))]))) =
"for ( ; ; i = i + 1) {
return 0;
int y;
a = b;
}
"
),(
"statement_33_1",
text 0 0 (printStatement
           (for (None,
                 Some (binary (ident "i", LT, const "10")),
                 None,
                 assign (ident "y", const "0")))) =
"for ( ; i < 10; )
y = 0;
"
),(
"statement_34_1",
text 0 0 (printStatement
           (for (None,
                 Some (binary (ident "i", LT, const "10")),
                 None,
                 block [statement (return (Some (const "0"))),
                        declaration {typE = sint, name = "y"},
                        statement (assign (ident "a", ident "b"))]))) =
"for ( ; i < 10; ) {
return 0;
int y;
a = b;
}
"
),(
"statement_35_1",
text 0 0 (printStatement
           (for (None,
                 Some (binary (ident "i", LT, const "10")),
                 Some (assign (ident "i", binary (ident "i", ADD, const "1"))),
                 assign (ident "y", const "0")))) =
"for ( ; i < 10; i = i + 1)
y = 0;
"
),(
"statement_36_1",
text 0 0 (printStatement
           (for (None,
                 Some (binary (ident "i", LT, const "10")),
                 Some (assign (ident "i", binary (ident "i", ADD, const "1"))),
                 block [statement (return (Some (const "0"))),
                        declaration {typE = sint, name = "y"},
                        statement (assign (ident "a", ident "b"))]))) =
"for ( ; i < 10; i = i + 1) {
return 0;
int y;
a = b;
}
"
),(
"statement_37_1",
text 0 0 (printStatement
           (for (Some (assign (ident "i", const "0")),
                 None,
                 None,
                 assign (ident "y", const "0")))) =
"for (i = 0; ; )
y = 0;
"
),(
"statement_38_1",
text 0 0 (printStatement
           (for (Some (assign (ident "i", const "0")),
                 None,
                 None,
                 block [statement (return (Some (const "0"))),
                        declaration {typE = sint, name = "y"},
                        statement (assign (ident "a", ident "b"))]))) =
"for (i = 0; ; ) {
return 0;
int y;
a = b;
}
"
),(
"statement_39_1",
text 0 0 (printStatement
           (for (Some (assign (ident "i", const "0")),
                 None,
                 Some (assign (ident "i", binary (ident "i", ADD, const "1"))),
                 assign (ident "y", const "0")))) =
"for (i = 0; ; i = i + 1)
y = 0;
"
),(
"statement_40_1",
text 0 0 (printStatement
           (for (Some (assign (ident "i", const "0")),
                 None,
                 Some (assign (ident "i", binary (ident "i", ADD, const "1"))),
                 block [statement (return (Some (const "0"))),
                        declaration {typE = sint, name = "y"},
                        statement (assign (ident "a", ident "b"))]))) =
"for (i = 0; ; i = i + 1) {
return 0;
int y;
a = b;
}
"
),(
"statement_41_1",
text 0 0 (printStatement
           (for (Some (assign (ident "i", const "0")),
                 Some (binary (ident "i", LT, const "10")),
                 None,
                 assign (ident "y", const "0")))) =
"for (i = 0; i < 10; )
y = 0;
"
),(
"statement_42_1",
text 0 0 (printStatement
           (for (Some (assign (ident "i", const "0")),
                 Some (binary (ident "i", LT, const "10")),
                 None,
                 block [statement (return (Some (const "0"))),
                        declaration {typE = sint, name = "y"},
                        statement (assign (ident "a", ident "b"))]))) =
"for (i = 0; i < 10; ) {
return 0;
int y;
a = b;
}
"
),(
"statement_43_1",
text 0 0 (printStatement
           (for (Some (assign (ident "i", const "0")),
                 Some (binary (ident "i", LT, const "10")),
                 Some (assign (ident "i", binary (ident "i", ADD, const "1"))),
                 assign (ident "y", const "0")))) =
"for (i = 0; i < 10; i = i + 1)
y = 0;
"
),(
"statement_44_1",
text 0 0 (printStatement
           (for (Some (assign (ident "i", const "0")),
                 Some (binary (ident "i", LT, const "10")),
                 Some (assign (ident "i", binary (ident "i", ADD, const "1"))),
                 block [statement (return (Some (const "0"))),
                        declaration {typE = sint, name = "y"},
                        statement (assign (ident "a", ident "b"))]))) =
"for (i = 0; i < 10; i = i + 1) {
return 0;
int y;
a = b;
}
"
),(
"statement_45_1",
text 0 0 (printStatement
           (iF (ident "outer_test",
                iF (ident "inner_test",
                    call (None, "inner", []),
                    None),
                Some (call (None, "outer", []))))) =
"if (outer_test) {
if (inner_test)
inner();
} else
outer();
"
),(
"statement_46_1",
text 0 0 (printStatement
           (iF (ident "outer_test",
                iF (ident "inner_test",
                    call (None, "inner", []),
                    None),
                None))) =
"if (outer_test)
if (inner_test)
inner();
"
),(
"statement_47_1",
text 0 0 (printStatement
           (iF (ident "outer_test",
                iF (ident "inner_test",
                    call (None, "inner", []),
                    Some (call (None, "inner2", []))),
                None))) =
"if (outer_test)
if (inner_test)
inner();
else
inner2();
"
),(
"statement_48_1",
text 0 0 (printStatement
           (iF (ident "outer_test",
                iF (ident "inner_test",
                    call (None, "inner", []),
                    Some (call (None, "inner2", []))),
                Some (call (None, "outer", []))))) =
"if (outer_test)
if (inner_test)
inner();
else
inner2();
else
outer();
"
),(
"statement_49_1",
text 0 0 (printStatement
           (iF (ident "outer_test",
                iF (ident "inner_test",
                    call (None, "inner", []),
                    Some (call (None, "inner2", []))),
                Some (iF (ident "inner_test2",
                          call (None, "inner3", []),
                          None))))) =
"if (outer_test)
if (inner_test)
inner();
else
inner2();
else
if (inner_test2)
inner3();
"
),(
"statement_50_1",
text 0 0 (printStatement
           (iF (ident "outer_test",
                iF (ident "inner_test",
                    call (None, "inner", []),
                    Some (call (None, "inner2", []))),
                Some (iF (ident "inner_test2",
                          call (None, "inner3", []),
                          Some (call (None, "inner4", []))))))) =
"if (outer_test)
if (inner_test)
inner();
else
inner2();
else
if (inner_test2)
inner3();
else
inner4();
"
),(
"statement_1_2",
text 0 4 (printStatement (assign (unary (STAR, ident "q"),
                                  const "33"))) =
"*q = 33;
"
),(
"statement_2_2",
text 0 4 (printStatement (call (None, "do_it", []))) =
"do_it();
"
),(
"statement_3_2",
text 0 4 (printStatement (call (Some (ident "new"),
                                "quick_sort",
                                [ident "old", const "100"]))) =
"new = quick_sort(old, 100);
"
),(
"statement_4_2",
text 0 4 (printStatement (return None)) =
"return;
"
),(
"statement_5_2",
text 0 4 (printStatement (return (Some (binary (ident "x", MUL, ident "y"))))) =
"return x * y;
"
),(
"statement_6_2",
text 0 4 (printBlockItem (declaration {typE = sint, name = "y"})) =
"int y;
"
),(
"statement_7_2",
text 0 4 (printBlockItem (statement (return (Some (const "0"))))) =
"return 0;
"
),(
"statement_8_2",
text 0 4 (printBlockItems []) = ""
),(
"statement_9_2",
text 0 4 (printBlockItems [statement (return (Some (const "0")))]) =
"return 0;
"
),(
"statement_10_2",
text 0 4 (printBlockItems [statement (return (Some (const "0"))),
                           declaration {typE = sint, name = "y"},
                           statement (assign (ident "a", ident "b"))]) =
"return 0;
int y;
a = b;
"
),(
"statement_11_2",
text 0 4 (printStatement (block [])) =
"{
}
"
),(
"statement_12_2",
text 0 4 (printStatement (block
                          [statement (return (Some (const "0"))),
                           declaration {typE = sint, name = "y"},
                           statement (assign (ident "a", ident "b"))])) =
"{
    return 0;
    int y;
    a = b;
}
"
),(
"statement_13_2",
text 0 4 (printStatement (iF (binary (ident "x", GE, const "0"),
                              assign (ident "y", const "0"),
                              None))) =
"if (x >= 0)
    y = 0;
"
),(
"statement_14_2",
text 0 4 (printStatement (iF (binary (ident "x", GE, const "0"),
                              block [],
                              None))) =
"if (x >= 0) {
}
"
),(
"statement_15_2",
text 0 4 (printStatement (iF (binary (ident "x", GE, const "0"),
                              block
                               [statement (return (Some (const "0"))),
                                declaration {typE = sint, name = "y"},
                                statement (assign (ident "a", ident "b"))],
                              None))) =
"if (x >= 0) {
    return 0;
    int y;
    a = b;
}
"
),(
"statement_16_2",
text 0 4 (printStatement (iF (binary (ident "x", GE, const "0"),
                              assign (ident "y", const "0"),
                              Some (call (None, "f", [const "1"]))))) =
"if (x >= 0)
    y = 0;
else
    f(1);
"
),(
"statement_17_2",
text 0 4 (printStatement (iF (binary (ident "x", GE, const "0"),
                              block [],
                              Some (call (None, "f", [const "1"]))))) =
"if (x >= 0) {
} else
    f(1);
"
),(
"statement_18_2",
text 0 4 (printStatement (iF (binary (ident "x", GE, const "0"),
                              block
                               [statement (return (Some (const "0"))),
                                declaration {typE = sint, name = "y"},
                                statement (assign (ident "a", ident "b"))],
                              Some (call (None, "f", [const "1"]))))) =
"if (x >= 0) {
    return 0;
    int y;
    a = b;
} else
    f(1);
"
),(
"statement_19_2",
text 0 4 (printStatement (iF (binary (ident "x", GE, const "0"),
                              assign (ident "y", const "0"),
                              Some (block [])))) =
"if (x >= 0)
    y = 0;
else {
}
"
),(
"statement_20_2",
text 0 4 (printStatement (iF (binary (ident "x", GE, const "0"),
                              block [],
                              Some (block [])))) =
"if (x >= 0) {
} else {
}
"
),(
"statement_21_2",
text 0 4 (printStatement (iF (binary (ident "x", GE, const "0"),
                              block
                               [statement (return (Some (const "0"))),
                                declaration {typE = sint, name = "y"},
                                statement (assign (ident "a", ident "b"))],
                              Some (block [])))) =
"if (x >= 0) {
    return 0;
    int y;
    a = b;
} else {
}
"
),(
"statement_22_2",
text 0 4 (printStatement
           (iF (binary (ident "x", GE, const "0"),
                assign (ident "y", const "0"),
                Some (block [statement (return (Some (const "0"))),
                             declaration {typE = sint, name = "y"},
                             statement (assign (ident "a", ident "b"))])))) =
"if (x >= 0)
    y = 0;
else {
    return 0;
    int y;
    a = b;
}
"
),(
"statement_23_2",
text 0 4 (printStatement
           (iF (binary (ident "x", GE, const "0"),
                block [],
                Some (block [statement (return (Some (const "0"))),
                             declaration {typE = sint, name = "y"},
                             statement (assign (ident "a", ident "b"))])))) =
"if (x >= 0) {
} else {
    return 0;
    int y;
    a = b;
}
"
),(
"statement_24_2",
text 0 4 (printStatement
           (iF (binary (ident "x", GE, const "0"),
                block [statement (return (Some (const "0"))),
                       declaration {typE = sint, name = "y"},
                       statement (assign (ident "a", ident "b"))],
                Some (block [statement (return (Some (const "0"))),
                             declaration {typE = sint, name = "y"},
                             statement (assign (ident "a", ident "b"))])))) =
"if (x >= 0) {
    return 0;
    int y;
    a = b;
} else {
    return 0;
    int y;
    a = b;
}
"
),(
"statement_25_2",
text 0 4 (printStatement
           (while (binary (ident "x", GE, const "0"),
                   assign (ident "y", const "0")))) =
"while (x >= 0)
    y = 0;
"
),(
"statement_26_2",
text 0 4 (printStatement
           (while (binary (ident "x", GE, const "0"),
                   block [statement (return (Some (const "0"))),
                          declaration {typE = sint, name = "y"},
                          statement (assign (ident "a", ident "b"))]))) =
"while (x >= 0) {
    return 0;
    int y;
    a = b;
}
"
),(
"statement_27_2",
text 0 4 (printStatement
           (do (assign (ident "y", const "0"),
                binary (ident "x", GE, const "0")))) =
"do
    y = 0;
while (x >= 0);
"
),(
"statement_28_2",
text 0 4 (printStatement
           (do (block [statement (return (Some (const "0"))),
                       declaration {typE = sint, name = "y"},
                       statement (assign (ident "a", ident "b"))],
                binary (ident "x", GE, const "0")))) =
"do {
    return 0;
    int y;
    a = b;
} while (x >= 0);
"
),(
"statement_29_2",
text 0 4 (printStatement
           (for (None,
                 None,
                 None,
                 assign (ident "y", const "0")))) =
"for ( ; ; )
    y = 0;
"
),(
"statement_30_2",
text 0 4 (printStatement
           (for (None,
                 None,
                 None,
                 block [statement (return (Some (const "0"))),
                        declaration {typE = sint, name = "y"},
                        statement (assign (ident "a", ident "b"))]))) =
"for ( ; ; ) {
    return 0;
    int y;
    a = b;
}
"
),(
"statement_31_2",
text 0 4 (printStatement
           (for (None,
                 None,
                 Some (assign (ident "i", binary (ident "i", ADD, const "1"))),
                 assign (ident "y", const "0")))) =
"for ( ; ; i = i + 1)
    y = 0;
"
),(
"statement_32_2",
text 0 4 (printStatement
           (for (None,
                 None,
                 Some (assign (ident "i", binary (ident "i", ADD, const "1"))),
                 block [statement (return (Some (const "0"))),
                        declaration {typE = sint, name = "y"},
                        statement (assign (ident "a", ident "b"))]))) =
"for ( ; ; i = i + 1) {
    return 0;
    int y;
    a = b;
}
"
),(
"statement_33_2",
text 0 4 (printStatement
           (for (None,
                 Some (binary (ident "i", LT, const "10")),
                 None,
                 assign (ident "y", const "0")))) =
"for ( ; i < 10; )
    y = 0;
"
),(
"statement_34_2",
text 0 4 (printStatement
           (for (None,
                 Some (binary (ident "i", LT, const "10")),
                 None,
                 block [statement (return (Some (const "0"))),
                        declaration {typE = sint, name = "y"},
                        statement (assign (ident "a", ident "b"))]))) =
"for ( ; i < 10; ) {
    return 0;
    int y;
    a = b;
}
"
),(
"statement_35_2",
text 0 4 (printStatement
           (for (None,
                 Some (binary (ident "i", LT, const "10")),
                 Some (assign (ident "i", binary (ident "i", ADD, const "1"))),
                 assign (ident "y", const "0")))) =
"for ( ; i < 10; i = i + 1)
    y = 0;
"
),(
"statement_36_2",
text 0 4 (printStatement
           (for (None,
                 Some (binary (ident "i", LT, const "10")),
                 Some (assign (ident "i", binary (ident "i", ADD, const "1"))),
                 block [statement (return (Some (const "0"))),
                        declaration {typE = sint, name = "y"},
                        statement (assign (ident "a", ident "b"))]))) =
"for ( ; i < 10; i = i + 1) {
    return 0;
    int y;
    a = b;
}
"
),(
"statement_37_2",
text 0 4 (printStatement
           (for (Some (assign (ident "i", const "0")),
                 None,
                 None,
                 assign (ident "y", const "0")))) =
"for (i = 0; ; )
    y = 0;
"
),(
"statement_38_2",
text 0 4 (printStatement
           (for (Some (assign (ident "i", const "0")),
                 None,
                 None,
                 block [statement (return (Some (const "0"))),
                        declaration {typE = sint, name = "y"},
                        statement (assign (ident "a", ident "b"))]))) =
"for (i = 0; ; ) {
    return 0;
    int y;
    a = b;
}
"
),(
"statement_39_2",
text 0 4 (printStatement
           (for (Some (assign (ident "i", const "0")),
                 None,
                 Some (assign (ident "i", binary (ident "i", ADD, const "1"))),
                 assign (ident "y", const "0")))) =
"for (i = 0; ; i = i + 1)
    y = 0;
"
),(
"statement_40_2",
text 0 4 (printStatement
           (for (Some (assign (ident "i", const "0")),
                 None,
                 Some (assign (ident "i", binary (ident "i", ADD, const "1"))),
                 block [statement (return (Some (const "0"))),
                        declaration {typE = sint, name = "y"},
                        statement (assign (ident "a", ident "b"))]))) =
"for (i = 0; ; i = i + 1) {
    return 0;
    int y;
    a = b;
}
"
),(
"statement_41_2",
text 0 4 (printStatement
           (for (Some (assign (ident "i", const "0")),
                 Some (binary (ident "i", LT, const "10")),
                 None,
                 assign (ident "y", const "0")))) =
"for (i = 0; i < 10; )
    y = 0;
"
),(
"statement_42_2",
text 0 4 (printStatement
           (for (Some (assign (ident "i", const "0")),
                 Some (binary (ident "i", LT, const "10")),
                 None,
                 block [statement (return (Some (const "0"))),
                        declaration {typE = sint, name = "y"},
                        statement (assign (ident "a", ident "b"))]))) =
"for (i = 0; i < 10; ) {
    return 0;
    int y;
    a = b;
}
"
),(
"statement_43_2",
text 0 4 (printStatement
           (for (Some (assign (ident "i", const "0")),
                 Some (binary (ident "i", LT, const "10")),
                 Some (assign (ident "i", binary (ident "i", ADD, const "1"))),
                 assign (ident "y", const "0")))) =
"for (i = 0; i < 10; i = i + 1)
    y = 0;
"
),(
"statement_44_2",
text 0 4 (printStatement
           (for (Some (assign (ident "i", const "0")),
                 Some (binary (ident "i", LT, const "10")),
                 Some (assign (ident "i", binary (ident "i", ADD, const "1"))),
                 block [statement (return (Some (const "0"))),
                        declaration {typE = sint, name = "y"},
                        statement (assign (ident "a", ident "b"))]))) =
"for (i = 0; i < 10; i = i + 1) {
    return 0;
    int y;
    a = b;
}
"
),(
"statement_45_2",
text 0 4 (printStatement
           (iF (ident "outer_test",
                iF (ident "inner_test",
                    call (None, "inner", []),
                    None),
                Some (call (None, "outer", []))))) =
"if (outer_test) {
    if (inner_test)
        inner();
} else
    outer();
"
),(
"statement_46_2",
text 0 4 (printStatement
           (iF (ident "outer_test",
                iF (ident "inner_test",
                    call (None, "inner", []),
                    None),
                None))) =
"if (outer_test)
    if (inner_test)
        inner();
"
),(
"statement_47_2",
text 0 4 (printStatement
           (iF (ident "outer_test",
                iF (ident "inner_test",
                    call (None, "inner", []),
                    Some (call (None, "inner2", []))),
                None))) =
"if (outer_test)
    if (inner_test)
        inner();
    else
        inner2();
"
),(
"statement_48_2",
text 0 4 (printStatement
           (iF (ident "outer_test",
                iF (ident "inner_test",
                    call (None, "inner", []),
                    Some (call (None, "inner2", []))),
                Some (call (None, "outer", []))))) =
"if (outer_test)
    if (inner_test)
        inner();
    else
        inner2();
else
    outer();
"
),(
"statement_49_2",
text 0 4 (printStatement
           (iF (ident "outer_test",
                iF (ident "inner_test",
                    call (None, "inner", []),
                    Some (call (None, "inner2", []))),
                Some (iF (ident "inner_test2",
                          call (None, "inner3", []),
                          None))))) =
"if (outer_test)
    if (inner_test)
        inner();
    else
        inner2();
else
    if (inner_test2)
        inner3();
"
),(
"statement_50_2",
text 0 4 (printStatement
           (iF (ident "outer_test",
                iF (ident "inner_test",
                    call (None, "inner", []),
                    Some (call (None, "inner2", []))),
                Some (iF (ident "inner_test2",
                          call (None, "inner3", []),
                          Some (call (None, "inner4", []))))))) =
"if (outer_test)
    if (inner_test)
        inner();
    else
        inner2();
else
    if (inner_test2)
        inner3();
    else
        inner4();
"
),(
"statement_1_3",
text 2 0 (printStatement (assign (unary (STAR, ident "q"),
                                  const "33"))) =
"*q = 33;
"
),(
"statement_2_3",
text 2 0 (printStatement (call (None, "do_it", []))) =
"do_it();
"
),(
"statement_3_3",
text 2 0 (printStatement (call (Some (ident "new"),
                                "quick_sort",
                                [ident "old", const "100"]))) =
"new = quick_sort(old, 100);
"
),(
"statement_4_3",
text 2 0 (printStatement (return None)) =
"return;
"
),(
"statement_5_3",
text 2 0 (printStatement (return (Some (binary (ident "x", MUL, ident "y"))))) =
"return x * y;
"
),(
"statement_6_3",
text 2 0 (printBlockItem (declaration {typE = sint, name = "y"})) =
"int y;
"
),(
"statement_7_3",
text 2 0 (printBlockItem (statement (return (Some (const "0"))))) =
"return 0;
"
),(
"statement_8_3",
text 2 0 (printBlockItems []) = ""
),(
"statement_9_3",
text 2 0 (printBlockItems [statement (return (Some (const "0")))]) =
"return 0;
"
),(
"statement_10_3",
text 2 0 (printBlockItems [statement (return (Some (const "0"))),
                           declaration {typE = sint, name = "y"},
                           statement (assign (ident "a", ident "b"))]) =
"return 0;
int y;
a = b;
"
),(
"statement_11_3",
text 2 0 (printStatement (block [])) =
"{
}
"
),(
"statement_12_3",
text 2 0 (printStatement (block
                          [statement (return (Some (const "0"))),
                           declaration {typE = sint, name = "y"},
                           statement (assign (ident "a", ident "b"))])) =
"{
return 0;
int y;
a = b;
}
"
),(
"statement_13_3",
text 2 0 (printStatement (iF (binary (ident "x", GE, const "0"),
                              assign (ident "y", const "0"),
                              None))) =
"if (x >= 0)
y = 0;
"
),(
"statement_14_3",
text 2 0 (printStatement (iF (binary (ident "x", GE, const "0"),
                              block [],
                              None))) =
"if (x >= 0) {
}
"
),(
"statement_15_3",
text 2 0 (printStatement (iF (binary (ident "x", GE, const "0"),
                              block
                               [statement (return (Some (const "0"))),
                                declaration {typE = sint, name = "y"},
                                statement (assign (ident "a", ident "b"))],
                              None))) =
"if (x >= 0) {
return 0;
int y;
a = b;
}
"
),(
"statement_16_3",
text 2 0 (printStatement (iF (binary (ident "x", GE, const "0"),
                              assign (ident "y", const "0"),
                              Some (call (None, "f", [const "1"]))))) =
"if (x >= 0)
y = 0;
else
f(1);
"
),(
"statement_17_3",
text 2 0 (printStatement (iF (binary (ident "x", GE, const "0"),
                              block [],
                              Some (call (None, "f", [const "1"]))))) =
"if (x >= 0) {
} else
f(1);
"
),(
"statement_18_3",
text 2 0 (printStatement (iF (binary (ident "x", GE, const "0"),
                              block
                               [statement (return (Some (const "0"))),
                                declaration {typE = sint, name = "y"},
                                statement (assign (ident "a", ident "b"))],
                              Some (call (None, "f", [const "1"]))))) =
"if (x >= 0) {
return 0;
int y;
a = b;
} else
f(1);
"
),(
"statement_19_3",
text 2 0 (printStatement (iF (binary (ident "x", GE, const "0"),
                              assign (ident "y", const "0"),
                              Some (block [])))) =
"if (x >= 0)
y = 0;
else {
}
"
),(
"statement_20_3",
text 2 0 (printStatement (iF (binary (ident "x", GE, const "0"),
                              block [],
                              Some (block [])))) =
"if (x >= 0) {
} else {
}
"
),(
"statement_21_3",
text 2 0 (printStatement (iF (binary (ident "x", GE, const "0"),
                              block
                               [statement (return (Some (const "0"))),
                                declaration {typE = sint, name = "y"},
                                statement (assign (ident "a", ident "b"))],
                              Some (block [])))) =
"if (x >= 0) {
return 0;
int y;
a = b;
} else {
}
"
),(
"statement_22_3",
text 2 0 (printStatement
           (iF (binary (ident "x", GE, const "0"),
                assign (ident "y", const "0"),
                Some (block [statement (return (Some (const "0"))),
                             declaration {typE = sint, name = "y"},
                             statement (assign (ident "a", ident "b"))])))) =
"if (x >= 0)
y = 0;
else {
return 0;
int y;
a = b;
}
"
),(
"statement_23_3",
text 2 0 (printStatement
           (iF (binary (ident "x", GE, const "0"),
                block [],
                Some (block [statement (return (Some (const "0"))),
                             declaration {typE = sint, name = "y"},
                             statement (assign (ident "a", ident "b"))])))) =
"if (x >= 0) {
} else {
return 0;
int y;
a = b;
}
"
),(
"statement_24_3",
text 2 0 (printStatement
           (iF (binary (ident "x", GE, const "0"),
                block [statement (return (Some (const "0"))),
                       declaration {typE = sint, name = "y"},
                       statement (assign (ident "a", ident "b"))],
                Some (block [statement (return (Some (const "0"))),
                             declaration {typE = sint, name = "y"},
                             statement (assign (ident "a", ident "b"))])))) =
"if (x >= 0) {
return 0;
int y;
a = b;
} else {
return 0;
int y;
a = b;
}
"
),(
"statement_25_3",
text 2 0 (printStatement
           (while (binary (ident "x", GE, const "0"),
                   assign (ident "y", const "0")))) =
"while (x >= 0)
y = 0;
"
),(
"statement_26_3",
text 2 0 (printStatement
           (while (binary (ident "x", GE, const "0"),
                   block [statement (return (Some (const "0"))),
                          declaration {typE = sint, name = "y"},
                          statement (assign (ident "a", ident "b"))]))) =
"while (x >= 0) {
return 0;
int y;
a = b;
}
"
),(
"statement_27_3",
text 2 0 (printStatement
           (do (assign (ident "y", const "0"),
                binary (ident "x", GE, const "0")))) =
"do
y = 0;
while (x >= 0);
"
),(
"statement_28_3",
text 2 0 (printStatement
           (do (block [statement (return (Some (const "0"))),
                       declaration {typE = sint, name = "y"},
                       statement (assign (ident "a", ident "b"))],
                binary (ident "x", GE, const "0")))) =
"do {
return 0;
int y;
a = b;
} while (x >= 0);
"
),(
"statement_29_3",
text 2 0 (printStatement
           (for (None,
                 None,
                 None,
                 assign (ident "y", const "0")))) =
"for ( ; ; )
y = 0;
"
),(
"statement_30_3",
text 2 0 (printStatement
           (for (None,
                 None,
                 None,
                 block [statement (return (Some (const "0"))),
                        declaration {typE = sint, name = "y"},
                        statement (assign (ident "a", ident "b"))]))) =
"for ( ; ; ) {
return 0;
int y;
a = b;
}
"
),(
"statement_31_3",
text 2 0 (printStatement
           (for (None,
                 None,
                 Some (assign (ident "i", binary (ident "i", ADD, const "1"))),
                 assign (ident "y", const "0")))) =
"for ( ; ; i = i + 1)
y = 0;
"
),(
"statement_32_3",
text 2 0 (printStatement
           (for (None,
                 None,
                 Some (assign (ident "i", binary (ident "i", ADD, const "1"))),
                 block [statement (return (Some (const "0"))),
                        declaration {typE = sint, name = "y"},
                        statement (assign (ident "a", ident "b"))]))) =
"for ( ; ; i = i + 1) {
return 0;
int y;
a = b;
}
"
),(
"statement_33_3",
text 2 0 (printStatement
           (for (None,
                 Some (binary (ident "i", LT, const "10")),
                 None,
                 assign (ident "y", const "0")))) =
"for ( ; i < 10; )
y = 0;
"
),(
"statement_34_3",
text 2 0 (printStatement
           (for (None,
                 Some (binary (ident "i", LT, const "10")),
                 None,
                 block [statement (return (Some (const "0"))),
                        declaration {typE = sint, name = "y"},
                        statement (assign (ident "a", ident "b"))]))) =
"for ( ; i < 10; ) {
return 0;
int y;
a = b;
}
"
),(
"statement_35_3",
text 2 0 (printStatement
           (for (None,
                 Some (binary (ident "i", LT, const "10")),
                 Some (assign (ident "i", binary (ident "i", ADD, const "1"))),
                 assign (ident "y", const "0")))) =
"for ( ; i < 10; i = i + 1)
y = 0;
"
),(
"statement_36_3",
text 2 0 (printStatement
           (for (None,
                 Some (binary (ident "i", LT, const "10")),
                 Some (assign (ident "i", binary (ident "i", ADD, const "1"))),
                 block [statement (return (Some (const "0"))),
                        declaration {typE = sint, name = "y"},
                        statement (assign (ident "a", ident "b"))]))) =
"for ( ; i < 10; i = i + 1) {
return 0;
int y;
a = b;
}
"
),(
"statement_37_3",
text 2 0 (printStatement
           (for (Some (assign (ident "i", const "0")),
                 None,
                 None,
                 assign (ident "y", const "0")))) =
"for (i = 0; ; )
y = 0;
"
),(
"statement_38_3",
text 2 0 (printStatement
           (for (Some (assign (ident "i", const "0")),
                 None,
                 None,
                 block [statement (return (Some (const "0"))),
                        declaration {typE = sint, name = "y"},
                        statement (assign (ident "a", ident "b"))]))) =
"for (i = 0; ; ) {
return 0;
int y;
a = b;
}
"
),(
"statement_39_3",
text 2 0 (printStatement
           (for (Some (assign (ident "i", const "0")),
                 None,
                 Some (assign (ident "i", binary (ident "i", ADD, const "1"))),
                 assign (ident "y", const "0")))) =
"for (i = 0; ; i = i + 1)
y = 0;
"
),(
"statement_40_3",
text 2 0 (printStatement
           (for (Some (assign (ident "i", const "0")),
                 None,
                 Some (assign (ident "i", binary (ident "i", ADD, const "1"))),
                 block [statement (return (Some (const "0"))),
                        declaration {typE = sint, name = "y"},
                        statement (assign (ident "a", ident "b"))]))) =
"for (i = 0; ; i = i + 1) {
return 0;
int y;
a = b;
}
"
),(
"statement_41_3",
text 2 0 (printStatement
           (for (Some (assign (ident "i", const "0")),
                 Some (binary (ident "i", LT, const "10")),
                 None,
                 assign (ident "y", const "0")))) =
"for (i = 0; i < 10; )
y = 0;
"
),(
"statement_42_3",
text 2 0 (printStatement
           (for (Some (assign (ident "i", const "0")),
                 Some (binary (ident "i", LT, const "10")),
                 None,
                 block [statement (return (Some (const "0"))),
                        declaration {typE = sint, name = "y"},
                        statement (assign (ident "a", ident "b"))]))) =
"for (i = 0; i < 10; ) {
return 0;
int y;
a = b;
}
"
),(
"statement_43_3",
text 2 0 (printStatement
           (for (Some (assign (ident "i", const "0")),
                 Some (binary (ident "i", LT, const "10")),
                 Some (assign (ident "i", binary (ident "i", ADD, const "1"))),
                 assign (ident "y", const "0")))) =
"for (i = 0; i < 10; i = i + 1)
y = 0;
"
),(
"statement_44_3",
text 2 0 (printStatement
           (for (Some (assign (ident "i", const "0")),
                 Some (binary (ident "i", LT, const "10")),
                 Some (assign (ident "i", binary (ident "i", ADD, const "1"))),
                 block [statement (return (Some (const "0"))),
                        declaration {typE = sint, name = "y"},
                        statement (assign (ident "a", ident "b"))]))) =
"for (i = 0; i < 10; i = i + 1) {
return 0;
int y;
a = b;
}
"
),(
"statement_45_3",
text 2 0 (printStatement
           (iF (ident "outer_test",
                iF (ident "inner_test",
                    call (None, "inner", []),
                    None),
                Some (call (None, "outer", []))))) =
"if (outer_test) {
if (inner_test)
inner();
} else
outer();
"
),(
"statement_46_3",
text 2 0 (printStatement
           (iF (ident "outer_test",
                iF (ident "inner_test",
                    call (None, "inner", []),
                    None),
                None))) =
"if (outer_test)
if (inner_test)
inner();
"
),(
"statement_47_3",
text 2 0 (printStatement
           (iF (ident "outer_test",
                iF (ident "inner_test",
                    call (None, "inner", []),
                    Some (call (None, "inner2", []))),
                None))) =
"if (outer_test)
if (inner_test)
inner();
else
inner2();
"
),(
"statement_48_3",
text 2 0 (printStatement
           (iF (ident "outer_test",
                iF (ident "inner_test",
                    call (None, "inner", []),
                    Some (call (None, "inner2", []))),
                Some (call (None, "outer", []))))) =
"if (outer_test)
if (inner_test)
inner();
else
inner2();
else
outer();
"
),(
"statement_49_3",
text 2 0 (printStatement
           (iF (ident "outer_test",
                iF (ident "inner_test",
                    call (None, "inner", []),
                    Some (call (None, "inner2", []))),
                Some (iF (ident "inner_test2",
                          call (None, "inner3", []),
                          None))))) =
"if (outer_test)
if (inner_test)
inner();
else
inner2();
else
if (inner_test2)
inner3();
"
),(
"statement_50_3",
text 2 0 (printStatement
           (iF (ident "outer_test",
                iF (ident "inner_test",
                    call (None, "inner", []),
                    Some (call (None, "inner2", []))),
                Some (iF (ident "inner_test2",
                          call (None, "inner3", []),
                          Some (call (None, "inner4", []))))))) =
"if (outer_test)
if (inner_test)
inner();
else
inner2();
else
if (inner_test2)
inner3();
else
inner4();
"
),(
"statement_1_4",
text 2 4 (printStatement (assign (unary (STAR, ident "q"),
                                  const "33"))) =
"        *q = 33;
"
),(
"statement_2_4",
text 2 4 (printStatement (call (None, "do_it", []))) =
"        do_it();
"
),(
"statement_3_4",
text 2 4 (printStatement (call (Some (ident "new"),
                                "quick_sort",
                                [ident "old", const "100"]))) =
"        new = quick_sort(old, 100);
"
),(
"statement_4_4",
text 2 4 (printStatement (return None)) =
"        return;
"
),(
"statement_5_4",
text 2 4 (printStatement (return (Some (binary (ident "x", MUL, ident "y"))))) =
"        return x * y;
"
),(
"statement_6_4",
text 2 4 (printBlockItem (declaration {typE = sint, name = "y"})) =
"        int y;
"
),(
"statement_7_4",
text 2 4 (printBlockItem (statement (return (Some (const "0"))))) =
"        return 0;
"
),(
"statement_8_4",
text 2 4 (printBlockItems []) = ""
),(
"statement_9_4",
text 2 4 (printBlockItems [statement (return (Some (const "0")))]) =
"        return 0;
"
),(
"statement_10_4",
text 2 4 (printBlockItems [statement (return (Some (const "0"))),
                           declaration {typE = sint, name = "y"},
                           statement (assign (ident "a", ident "b"))]) =
"        return 0;
        int y;
        a = b;
"
),(
"statement_11_4",
text 2 4 (printStatement (block [])) =
"        {
        }
"
),(
"statement_12_4",
text 2 4 (printStatement (block
                          [statement (return (Some (const "0"))),
                           declaration {typE = sint, name = "y"},
                           statement (assign (ident "a", ident "b"))])) =
"        {
            return 0;
            int y;
            a = b;
        }
"
),(
"statement_13_4",
text 2 4 (printStatement (iF (binary (ident "x", GE, const "0"),
                              assign (ident "y", const "0"),
                              None))) =
"        if (x >= 0)
            y = 0;
"
),(
"statement_14_4",
text 2 4 (printStatement (iF (binary (ident "x", GE, const "0"),
                              block [],
                              None))) =
"        if (x >= 0) {
        }
"
),(
"statement_15_4",
text 2 4 (printStatement (iF (binary (ident "x", GE, const "0"),
                              block
                               [statement (return (Some (const "0"))),
                                declaration {typE = sint, name = "y"},
                                statement (assign (ident "a", ident "b"))],
                              None))) =
"        if (x >= 0) {
            return 0;
            int y;
            a = b;
        }
"
),(
"statement_16_4",
text 2 4 (printStatement (iF (binary (ident "x", GE, const "0"),
                              assign (ident "y", const "0"),
                              Some (call (None, "f", [const "1"]))))) =
"        if (x >= 0)
            y = 0;
        else
            f(1);
"
),(
"statement_17_4",
text 2 4 (printStatement (iF (binary (ident "x", GE, const "0"),
                              block [],
                              Some (call (None, "f", [const "1"]))))) =
"        if (x >= 0) {
        } else
            f(1);
"
),(
"statement_18_4",
text 2 4 (printStatement (iF (binary (ident "x", GE, const "0"),
                              block
                               [statement (return (Some (const "0"))),
                                declaration {typE = sint, name = "y"},
                                statement (assign (ident "a", ident "b"))],
                              Some (call (None, "f", [const "1"]))))) =
"        if (x >= 0) {
            return 0;
            int y;
            a = b;
        } else
            f(1);
"
),(
"statement_19_4",
text 2 4 (printStatement (iF (binary (ident "x", GE, const "0"),
                              assign (ident "y", const "0"),
                              Some (block [])))) =
"        if (x >= 0)
            y = 0;
        else {
        }
"
),(
"statement_20_4",
text 2 4 (printStatement (iF (binary (ident "x", GE, const "0"),
                              block [],
                              Some (block [])))) =
"        if (x >= 0) {
        } else {
        }
"
),(
"statement_21_4",
text 2 4 (printStatement (iF (binary (ident "x", GE, const "0"),
                              block
                               [statement (return (Some (const "0"))),
                                declaration {typE = sint, name = "y"},
                                statement (assign (ident "a", ident "b"))],
                              Some (block [])))) =
"        if (x >= 0) {
            return 0;
            int y;
            a = b;
        } else {
        }
"
),(
"statement_22_4",
text 2 4 (printStatement
           (iF (binary (ident "x", GE, const "0"),
                assign (ident "y", const "0"),
                Some (block [statement (return (Some (const "0"))),
                             declaration {typE = sint, name = "y"},
                             statement (assign (ident "a", ident "b"))])))) =
"        if (x >= 0)
            y = 0;
        else {
            return 0;
            int y;
            a = b;
        }
"
),(
"statement_23_4",
text 2 4 (printStatement
           (iF (binary (ident "x", GE, const "0"),
                block [],
                Some (block [statement (return (Some (const "0"))),
                             declaration {typE = sint, name = "y"},
                             statement (assign (ident "a", ident "b"))])))) =
"        if (x >= 0) {
        } else {
            return 0;
            int y;
            a = b;
        }
"
),(
"statement_24_4",
text 2 4 (printStatement
           (iF (binary (ident "x", GE, const "0"),
                block [statement (return (Some (const "0"))),
                       declaration {typE = sint, name = "y"},
                       statement (assign (ident "a", ident "b"))],
                Some (block [statement (return (Some (const "0"))),
                             declaration {typE = sint, name = "y"},
                             statement (assign (ident "a", ident "b"))])))) =
"        if (x >= 0) {
            return 0;
            int y;
            a = b;
        } else {
            return 0;
            int y;
            a = b;
        }
"
),(
"statement_25_4",
text 2 4 (printStatement
           (while (binary (ident "x", GE, const "0"),
                   assign (ident "y", const "0")))) =
"        while (x >= 0)
            y = 0;
"
),(
"statement_26_4",
text 2 4 (printStatement
           (while (binary (ident "x", GE, const "0"),
                   block [statement (return (Some (const "0"))),
                          declaration {typE = sint, name = "y"},
                          statement (assign (ident "a", ident "b"))]))) =
"        while (x >= 0) {
            return 0;
            int y;
            a = b;
        }
"
),(
"statement_27_4",
text 2 4 (printStatement
           (do (assign (ident "y", const "0"),
                binary (ident "x", GE, const "0")))) =
"        do
            y = 0;
        while (x >= 0);
"
),(
"statement_28_4",
text 2 4 (printStatement
           (do (block [statement (return (Some (const "0"))),
                       declaration {typE = sint, name = "y"},
                       statement (assign (ident "a", ident "b"))],
                binary (ident "x", GE, const "0")))) =
"        do {
            return 0;
            int y;
            a = b;
        } while (x >= 0);
"
),(
"statement_29_4",
text 2 4 (printStatement
           (for (None,
                 None,
                 None,
                 assign (ident "y", const "0")))) =
"        for ( ; ; )
            y = 0;
"
),(
"statement_30_4",
text 2 4 (printStatement
           (for (None,
                 None,
                 None,
                 block [statement (return (Some (const "0"))),
                        declaration {typE = sint, name = "y"},
                        statement (assign (ident "a", ident "b"))]))) =
"        for ( ; ; ) {
            return 0;
            int y;
            a = b;
        }
"
),(
"statement_31_4",
text 2 4 (printStatement
           (for (None,
                 None,
                 Some (assign (ident "i", binary (ident "i", ADD, const "1"))),
                 assign (ident "y", const "0")))) =
"        for ( ; ; i = i + 1)
            y = 0;
"
),(
"statement_32_4",
text 2 4 (printStatement
           (for (None,
                 None,
                 Some (assign (ident "i", binary (ident "i", ADD, const "1"))),
                 block [statement (return (Some (const "0"))),
                        declaration {typE = sint, name = "y"},
                        statement (assign (ident "a", ident "b"))]))) =
"        for ( ; ; i = i + 1) {
            return 0;
            int y;
            a = b;
        }
"
),(
"statement_33_4",
text 2 4 (printStatement
           (for (None,
                 Some (binary (ident "i", LT, const "10")),
                 None,
                 assign (ident "y", const "0")))) =
"        for ( ; i < 10; )
            y = 0;
"
),(
"statement_34_4",
text 2 4 (printStatement
           (for (None,
                 Some (binary (ident "i", LT, const "10")),
                 None,
                 block [statement (return (Some (const "0"))),
                        declaration {typE = sint, name = "y"},
                        statement (assign (ident "a", ident "b"))]))) =
"        for ( ; i < 10; ) {
            return 0;
            int y;
            a = b;
        }
"
),(
"statement_35_4",
text 2 4 (printStatement
           (for (None,
                 Some (binary (ident "i", LT, const "10")),
                 Some (assign (ident "i", binary (ident "i", ADD, const "1"))),
                 assign (ident "y", const "0")))) =
"        for ( ; i < 10; i = i + 1)
            y = 0;
"
),(
"statement_36_4",
text 2 4 (printStatement
           (for (None,
                 Some (binary (ident "i", LT, const "10")),
                 Some (assign (ident "i", binary (ident "i", ADD, const "1"))),
                 block [statement (return (Some (const "0"))),
                        declaration {typE = sint, name = "y"},
                        statement (assign (ident "a", ident "b"))]))) =
"        for ( ; i < 10; i = i + 1) {
            return 0;
            int y;
            a = b;
        }
"
),(
"statement_37_4",
text 2 4 (printStatement
           (for (Some (assign (ident "i", const "0")),
                 None,
                 None,
                 assign (ident "y", const "0")))) =
"        for (i = 0; ; )
            y = 0;
"
),(
"statement_38_4",
text 2 4 (printStatement
           (for (Some (assign (ident "i", const "0")),
                 None,
                 None,
                 block [statement (return (Some (const "0"))),
                        declaration {typE = sint, name = "y"},
                        statement (assign (ident "a", ident "b"))]))) =
"        for (i = 0; ; ) {
            return 0;
            int y;
            a = b;
        }
"
),(
"statement_39_4",
text 2 4 (printStatement
           (for (Some (assign (ident "i", const "0")),
                 None,
                 Some (assign (ident "i", binary (ident "i", ADD, const "1"))),
                 assign (ident "y", const "0")))) =
"        for (i = 0; ; i = i + 1)
            y = 0;
"
),(
"statement_40_4",
text 2 4 (printStatement
           (for (Some (assign (ident "i", const "0")),
                 None,
                 Some (assign (ident "i", binary (ident "i", ADD, const "1"))),
                 block [statement (return (Some (const "0"))),
                        declaration {typE = sint, name = "y"},
                        statement (assign (ident "a", ident "b"))]))) =
"        for (i = 0; ; i = i + 1) {
            return 0;
            int y;
            a = b;
        }
"
),(
"statement_41_4",
text 2 4 (printStatement
           (for (Some (assign (ident "i", const "0")),
                 Some (binary (ident "i", LT, const "10")),
                 None,
                 assign (ident "y", const "0")))) =
"        for (i = 0; i < 10; )
            y = 0;
"
),(
"statement_42_4",
text 2 4 (printStatement
           (for (Some (assign (ident "i", const "0")),
                 Some (binary (ident "i", LT, const "10")),
                 None,
                 block [statement (return (Some (const "0"))),
                        declaration {typE = sint, name = "y"},
                        statement (assign (ident "a", ident "b"))]))) =
"        for (i = 0; i < 10; ) {
            return 0;
            int y;
            a = b;
        }
"
),(
"statement_43_4",
text 2 4 (printStatement
           (for (Some (assign (ident "i", const "0")),
                 Some (binary (ident "i", LT, const "10")),
                 Some (assign (ident "i", binary (ident "i", ADD, const "1"))),
                 assign (ident "y", const "0")))) =
"        for (i = 0; i < 10; i = i + 1)
            y = 0;
"
),(
"statement_44_4",
text 2 4 (printStatement
           (for (Some (assign (ident "i", const "0")),
                 Some (binary (ident "i", LT, const "10")),
                 Some (assign (ident "i", binary (ident "i", ADD, const "1"))),
                 block [statement (return (Some (const "0"))),
                        declaration {typE = sint, name = "y"},
                        statement (assign (ident "a", ident "b"))]))) =
"        for (i = 0; i < 10; i = i + 1) {
            return 0;
            int y;
            a = b;
        }
"
),(
"statement_45_4",
text 2 4 (printStatement
           (iF (ident "outer_test",
                iF (ident "inner_test",
                    call (None, "inner", []),
                    None),
                Some (call (None, "outer", []))))) =
"        if (outer_test) {
            if (inner_test)
                inner();
        } else
            outer();
"
),(
"statement_46_4",
text 2 4 (printStatement
           (iF (ident "outer_test",
                iF (ident "inner_test",
                    call (None, "inner", []),
                    None),
                None))) =
"        if (outer_test)
            if (inner_test)
                inner();
"
),(
"statement_47_4",
text 2 4 (printStatement
           (iF (ident "outer_test",
                iF (ident "inner_test",
                    call (None, "inner", []),
                    Some (call (None, "inner2", []))),
                None))) =
"        if (outer_test)
            if (inner_test)
                inner();
            else
                inner2();
"
),(
"statement_48_4",
text 2 4 (printStatement
           (iF (ident "outer_test",
                iF (ident "inner_test",
                    call (None, "inner", []),
                    Some (call (None, "inner2", []))),
                Some (call (None, "outer", []))))) =
"        if (outer_test)
            if (inner_test)
                inner();
            else
                inner2();
        else
            outer();
"
),(
"statement_49_4",
text 2 4 (printStatement
           (iF (ident "outer_test",
                iF (ident "inner_test",
                    call (None, "inner", []),
                    Some (call (None, "inner2", []))),
                Some (iF (ident "inner_test2",
                          call (None, "inner3", []),
                          None))))) =
"        if (outer_test)
            if (inner_test)
                inner();
            else
                inner2();
        else
            if (inner_test2)
                inner3();
"
),(
"statement_50_4",
text 2 4 (printStatement
           (iF (ident "outer_test",
                iF (ident "inner_test",
                    call (None, "inner", []),
                    Some (call (None, "inner2", []))),
                Some (iF (ident "inner_test2",
                          call (None, "inner3", []),
                          Some (call (None, "inner4", []))))))) =
"        if (outer_test)
            if (inner_test)
                inner();
            else
                inner2();
        else
            if (inner_test2)
                inner3();
            else
                inner4();
"
),(
"statement_1_5",
text 1 6 (printStatement (assign (unary (STAR, ident "q"),
                                  const "33"))) =
"      *q = 33;
"
),(
"statement_2_5",
text 1 6 (printStatement (call (None, "do_it", []))) =
"      do_it();
"
),(
"statement_3_5",
text 1 6 (printStatement (call (Some (ident "new"),
                                "quick_sort",
                                [ident "old", const "100"]))) =
"      new = quick_sort(old, 100);
"
),(
"statement_4_5",
text 1 6 (printStatement (return None)) =
"      return;
"
),(
"statement_5_5",
text 1 6 (printStatement (return (Some (binary (ident "x", MUL, ident "y"))))) =
"      return x * y;
"
),(
"statement_6_5",
text 1 6 (printBlockItem (declaration {typE = sint, name = "y"})) =
"      int y;
"
),(
"statement_7_5",
text 1 6 (printBlockItem (statement (return (Some (const "0"))))) =
"      return 0;
"
),(
"statement_8_5",
text 1 6 (printBlockItems []) = ""
),(
"statement_9_5",
text 1 6 (printBlockItems [statement (return (Some (const "0")))]) =
"      return 0;
"
),(
"statement_10_5",
text 1 6 (printBlockItems [statement (return (Some (const "0"))),
                           declaration {typE = sint, name = "y"},
                           statement (assign (ident "a", ident "b"))]) =
"      return 0;
      int y;
      a = b;
"
),(
"statement_11_5",
text 1 6 (printStatement (block [])) =
"      {
      }
"
),(
"statement_12_5",
text 1 6 (printStatement (block
                          [statement (return (Some (const "0"))),
                           declaration {typE = sint, name = "y"},
                           statement (assign (ident "a", ident "b"))])) =
"      {
            return 0;
            int y;
            a = b;
      }
"
),(
"statement_13_5",
text 1 6 (printStatement (iF (binary (ident "x", GE, const "0"),
                              assign (ident "y", const "0"),
                              None))) =
"      if (x >= 0)
            y = 0;
"
),(
"statement_14_5",
text 1 6 (printStatement (iF (binary (ident "x", GE, const "0"),
                              block [],
                              None))) =
"      if (x >= 0) {
      }
"
),(
"statement_15_5",
text 1 6 (printStatement (iF (binary (ident "x", GE, const "0"),
                              block
                               [statement (return (Some (const "0"))),
                                declaration {typE = sint, name = "y"},
                                statement (assign (ident "a", ident "b"))],
                              None))) =
"      if (x >= 0) {
            return 0;
            int y;
            a = b;
      }
"
),(
"statement_16_5",
text 1 6 (printStatement (iF (binary (ident "x", GE, const "0"),
                              assign (ident "y", const "0"),
                              Some (call (None, "f", [const "1"]))))) =
"      if (x >= 0)
            y = 0;
      else
            f(1);
"
),(
"statement_17_5",
text 1 6 (printStatement (iF (binary (ident "x", GE, const "0"),
                              block [],
                              Some (call (None, "f", [const "1"]))))) =
"      if (x >= 0) {
      } else
            f(1);
"
),(
"statement_18_5",
text 1 6 (printStatement (iF (binary (ident "x", GE, const "0"),
                              block
                               [statement (return (Some (const "0"))),
                                declaration {typE = sint, name = "y"},
                                statement (assign (ident "a", ident "b"))],
                              Some (call (None, "f", [const "1"]))))) =
"      if (x >= 0) {
            return 0;
            int y;
            a = b;
      } else
            f(1);
"
),(
"statement_19_5",
text 1 6 (printStatement (iF (binary (ident "x", GE, const "0"),
                              assign (ident "y", const "0"),
                              Some (block [])))) =
"      if (x >= 0)
            y = 0;
      else {
      }
"
),(
"statement_20_5",
text 1 6 (printStatement (iF (binary (ident "x", GE, const "0"),
                              block [],
                              Some (block [])))) =
"      if (x >= 0) {
      } else {
      }
"
),(
"statement_21_5",
text 1 6 (printStatement (iF (binary (ident "x", GE, const "0"),
                              block
                               [statement (return (Some (const "0"))),
                                declaration {typE = sint, name = "y"},
                                statement (assign (ident "a", ident "b"))],
                              Some (block [])))) =
"      if (x >= 0) {
            return 0;
            int y;
            a = b;
      } else {
      }
"
),(
"statement_22_5",
text 1 6 (printStatement
           (iF (binary (ident "x", GE, const "0"),
                assign (ident "y", const "0"),
                Some (block [statement (return (Some (const "0"))),
                             declaration {typE = sint, name = "y"},
                             statement (assign (ident "a", ident "b"))])))) =
"      if (x >= 0)
            y = 0;
      else {
            return 0;
            int y;
            a = b;
      }
"
),(
"statement_23_5",
text 1 6 (printStatement
           (iF (binary (ident "x", GE, const "0"),
                block [],
                Some (block [statement (return (Some (const "0"))),
                             declaration {typE = sint, name = "y"},
                             statement (assign (ident "a", ident "b"))])))) =
"      if (x >= 0) {
      } else {
            return 0;
            int y;
            a = b;
      }
"
),(
"statement_24_5",
text 1 6 (printStatement
           (iF (binary (ident "x", GE, const "0"),
                block [statement (return (Some (const "0"))),
                       declaration {typE = sint, name = "y"},
                       statement (assign (ident "a", ident "b"))],
                Some (block [statement (return (Some (const "0"))),
                             declaration {typE = sint, name = "y"},
                             statement (assign (ident "a", ident "b"))])))) =
"      if (x >= 0) {
            return 0;
            int y;
            a = b;
      } else {
            return 0;
            int y;
            a = b;
      }
"
),(
"statement_25_5",
text 1 6 (printStatement
           (while (binary (ident "x", GE, const "0"),
                   assign (ident "y", const "0")))) =
"      while (x >= 0)
            y = 0;
"
),(
"statement_26_5",
text 1 6 (printStatement
           (while (binary (ident "x", GE, const "0"),
                   block [statement (return (Some (const "0"))),
                          declaration {typE = sint, name = "y"},
                          statement (assign (ident "a", ident "b"))]))) =
"      while (x >= 0) {
            return 0;
            int y;
            a = b;
      }
"
),(
"statement_27_5",
text 1 6 (printStatement
           (do (assign (ident "y", const "0"),
                binary (ident "x", GE, const "0")))) =
"      do
            y = 0;
      while (x >= 0);
"
),(
"statement_28_5",
text 1 6 (printStatement
           (do (block [statement (return (Some (const "0"))),
                       declaration {typE = sint, name = "y"},
                       statement (assign (ident "a", ident "b"))],
                binary (ident "x", GE, const "0")))) =
"      do {
            return 0;
            int y;
            a = b;
      } while (x >= 0);
"
),(
"statement_29_5",
text 1 6 (printStatement
           (for (None,
                 None,
                 None,
                 assign (ident "y", const "0")))) =
"      for ( ; ; )
            y = 0;
"
),(
"statement_30_5",
text 1 6 (printStatement
           (for (None,
                 None,
                 None,
                 block [statement (return (Some (const "0"))),
                        declaration {typE = sint, name = "y"},
                        statement (assign (ident "a", ident "b"))]))) =
"      for ( ; ; ) {
            return 0;
            int y;
            a = b;
      }
"
),(
"statement_31_5",
text 1 6 (printStatement
           (for (None,
                 None,
                 Some (assign (ident "i", binary (ident "i", ADD, const "1"))),
                 assign (ident "y", const "0")))) =
"      for ( ; ; i = i + 1)
            y = 0;
"
),(
"statement_32_5",
text 1 6 (printStatement
           (for (None,
                 None,
                 Some (assign (ident "i", binary (ident "i", ADD, const "1"))),
                 block [statement (return (Some (const "0"))),
                        declaration {typE = sint, name = "y"},
                        statement (assign (ident "a", ident "b"))]))) =
"      for ( ; ; i = i + 1) {
            return 0;
            int y;
            a = b;
      }
"
),(
"statement_33_5",
text 1 6 (printStatement
           (for (None,
                 Some (binary (ident "i", LT, const "10")),
                 None,
                 assign (ident "y", const "0")))) =
"      for ( ; i < 10; )
            y = 0;
"
),(
"statement_34_5",
text 1 6 (printStatement
           (for (None,
                 Some (binary (ident "i", LT, const "10")),
                 None,
                 block [statement (return (Some (const "0"))),
                        declaration {typE = sint, name = "y"},
                        statement (assign (ident "a", ident "b"))]))) =
"      for ( ; i < 10; ) {
            return 0;
            int y;
            a = b;
      }
"
),(
"statement_35_5",
text 1 6 (printStatement
           (for (None,
                 Some (binary (ident "i", LT, const "10")),
                 Some (assign (ident "i", binary (ident "i", ADD, const "1"))),
                 assign (ident "y", const "0")))) =
"      for ( ; i < 10; i = i + 1)
            y = 0;
"
),(
"statement_36_5",
text 1 6 (printStatement
           (for (None,
                 Some (binary (ident "i", LT, const "10")),
                 Some (assign (ident "i", binary (ident "i", ADD, const "1"))),
                 block [statement (return (Some (const "0"))),
                        declaration {typE = sint, name = "y"},
                        statement (assign (ident "a", ident "b"))]))) =
"      for ( ; i < 10; i = i + 1) {
            return 0;
            int y;
            a = b;
      }
"
),(
"statement_37_5",
text 1 6 (printStatement
           (for (Some (assign (ident "i", const "0")),
                 None,
                 None,
                 assign (ident "y", const "0")))) =
"      for (i = 0; ; )
            y = 0;
"
),(
"statement_38_5",
text 1 6 (printStatement
           (for (Some (assign (ident "i", const "0")),
                 None,
                 None,
                 block [statement (return (Some (const "0"))),
                        declaration {typE = sint, name = "y"},
                        statement (assign (ident "a", ident "b"))]))) =
"      for (i = 0; ; ) {
            return 0;
            int y;
            a = b;
      }
"
),(
"statement_39_5",
text 1 6 (printStatement
           (for (Some (assign (ident "i", const "0")),
                 None,
                 Some (assign (ident "i", binary (ident "i", ADD, const "1"))),
                 assign (ident "y", const "0")))) =
"      for (i = 0; ; i = i + 1)
            y = 0;
"
),(
"statement_40_5",
text 1 6 (printStatement
           (for (Some (assign (ident "i", const "0")),
                 None,
                 Some (assign (ident "i", binary (ident "i", ADD, const "1"))),
                 block [statement (return (Some (const "0"))),
                        declaration {typE = sint, name = "y"},
                        statement (assign (ident "a", ident "b"))]))) =
"      for (i = 0; ; i = i + 1) {
            return 0;
            int y;
            a = b;
      }
"
),(
"statement_41_5",
text 1 6 (printStatement
           (for (Some (assign (ident "i", const "0")),
                 Some (binary (ident "i", LT, const "10")),
                 None,
                 assign (ident "y", const "0")))) =
"      for (i = 0; i < 10; )
            y = 0;
"
),(
"statement_42_5",
text 1 6 (printStatement
           (for (Some (assign (ident "i", const "0")),
                 Some (binary (ident "i", LT, const "10")),
                 None,
                 block [statement (return (Some (const "0"))),
                        declaration {typE = sint, name = "y"},
                        statement (assign (ident "a", ident "b"))]))) =
"      for (i = 0; i < 10; ) {
            return 0;
            int y;
            a = b;
      }
"
),(
"statement_43_5",
text 1 6 (printStatement
           (for (Some (assign (ident "i", const "0")),
                 Some (binary (ident "i", LT, const "10")),
                 Some (assign (ident "i", binary (ident "i", ADD, const "1"))),
                 assign (ident "y", const "0")))) =
"      for (i = 0; i < 10; i = i + 1)
            y = 0;
"
),(
"statement_44_5",
text 1 6 (printStatement
           (for (Some (assign (ident "i", const "0")),
                 Some (binary (ident "i", LT, const "10")),
                 Some (assign (ident "i", binary (ident "i", ADD, const "1"))),
                 block [statement (return (Some (const "0"))),
                        declaration {typE = sint, name = "y"},
                        statement (assign (ident "a", ident "b"))]))) =
"      for (i = 0; i < 10; i = i + 1) {
            return 0;
            int y;
            a = b;
      }
"
),(
"statement_45_5",
text 1 6 (printStatement
           (iF (ident "outer_test",
                iF (ident "inner_test",
                    call (None, "inner", []),
                    None),
                Some (call (None, "outer", []))))) =
"      if (outer_test) {
            if (inner_test)
                  inner();
      } else
            outer();
"
),(
"statement_46_5",
text 1 6 (printStatement
           (iF (ident "outer_test",
                iF (ident "inner_test",
                    call (None, "inner", []),
                    None),
                None))) =
"      if (outer_test)
            if (inner_test)
                  inner();
"
),(
"statement_47_5",
text 1 6 (printStatement
           (iF (ident "outer_test",
                iF (ident "inner_test",
                    call (None, "inner", []),
                    Some (call (None, "inner2", []))),
                None))) =
"      if (outer_test)
            if (inner_test)
                  inner();
            else
                  inner2();
"
),(
"statement_48_5",
text 1 6 (printStatement
           (iF (ident "outer_test",
                iF (ident "inner_test",
                    call (None, "inner", []),
                    Some (call (None, "inner2", []))),
                Some (call (None, "outer", []))))) =
"      if (outer_test)
            if (inner_test)
                  inner();
            else
                  inner2();
      else
            outer();
"
),(
"statement_49_5",
text 1 6 (printStatement
           (iF (ident "outer_test",
                iF (ident "inner_test",
                    call (None, "inner", []),
                    Some (call (None, "inner2", []))),
                Some (iF (ident "inner_test2",
                          call (None, "inner3", []),
                          None))))) =
"      if (outer_test)
            if (inner_test)
                  inner();
            else
                  inner2();
      else
            if (inner_test2)
                  inner3();
"
),(
"statement_50_5",
text 1 6 (printStatement
           (iF (ident "outer_test",
                iF (ident "inner_test",
                    call (None, "inner", []),
                    Some (call (None, "inner2", []))),
                Some (iF (ident "inner_test2",
                          call (None, "inner3", []),
                          Some (call (None, "inner4", []))))))) =
"      if (outer_test)
            if (inner_test)
                  inner();
            else
                  inner2();
      else
            if (inner_test2)
                  inner3();
            else
                  inner4();
"
),(
"parameter_declaration",
text 0 0 (printParameterDeclaration
            {typE = pointer (pointer char), name = "argv"}) =
"char **argv"
),(
"parameter_declaration'",
text 3 4 (printParameterDeclaration
            {typE = pointer (pointer char), name = "argv"}) =
"char **argv"
),(
"parameter_list_1",
text 0 0 (printParameterList []) = ""
),(
"parameter_list_1'",
text 3 4 (printParameterList []) = ""
),(
"parameter_list_2",
text 0 0 (printParameterList [{typE = pointer (pointer char), name = "argv"}]) =
"char **argv"
),(
"parameter_list_2'",
text 3 4 (printParameterList [{typE = pointer (pointer char), name = "argv"}]) =
"char **argv"
),(
"parameter_list_3",
text 0 0 (printParameterList [{typE = pointer (pointer char), name = "argv"},
                              {typE = uint, name = "argc"}]) =
"char **argv, unsigned int argc"
),(
"parameter_list_3'",
text 3 4 (printParameterList [{typE = pointer (pointer char), name = "argv"},
                              {typE = uint, name = "argc"}]) =
"char **argv, unsigned int argc"
),(
"parameter_list_4",
text 0 0 (printParameterList [{typE = pointer (pointer char), name = "argv"},
                              {typE = uint, name = "argc"},
                              {typE = array (sllong, 10), name = "a"},
                              {typE = pointer void, name = "v"}]) =
"char **argv, unsigned int argc, long long a[10], void *v"
),(
"parameter_list_4'",
text 3 4 (printParameterList [{typE = pointer (pointer char), name = "argv"},
                              {typE = uint, name = "argc"},
                              {typE = array (sllong, 10), name = "a"},
                              {typE = pointer void, name = "v"}]) =
"char **argv, unsigned int argc, long long a[10], void *v"
),(
"function_definition_1_1",
text 0 0 (printFunctionDefinition
           {return = void,
            name = "fff",
            parameters = [],
            body = block [statement (return (Some (ident "G")))]}) =
"void fff() {
return G;
}
"
),(
"function_definition_2_1",
text 0 0 (printFunctionDefinition
           {return = pointer char,
            name = "ggg",
            parameters = [{typE = sint, name = "x"},
                          {typE = struct "S", name = "s"}],
            body = block [declaration {typE = sint, name = "y"},
                          statement (assign (ident "y", ident "x")),
                          statement (return (Some (ident "G")))]}) =
"char *ggg(int x, struct S s) {
int y;
y = x;
return G;
}
"
),(
"function_definition_1_2",
text 0 4 (printFunctionDefinition
           {return = void,
            name = "fff",
            parameters = [],
            body = block [statement (return (Some (ident "G")))]}) =
"void fff() {
    return G;
}
"
),(
"function_definition_2_2",
text 0 4 (printFunctionDefinition
           {return = pointer char,
            name = "ggg",
            parameters = [{typE = sint, name = "x"},
                          {typE = struct "S", name = "s"}],
            body = block [declaration {typE = sint, name = "y"},
                          statement (assign (ident "y", ident "x")),
                          statement (return (Some (ident "G")))]}) =
"char *ggg(int x, struct S s) {
    int y;
    y = x;
    return G;
}
"
),(
"function_definition_1_3",
text 2 0 (printFunctionDefinition
           {return = void,
            name = "fff",
            parameters = [],
            body = block [statement (return (Some (ident "G")))]}) =
"void fff() {
return G;
}
"
),(
"function_definition_2_3",
text 2 0 (printFunctionDefinition
           {return = pointer char,
            name = "ggg",
            parameters = [{typE = sint, name = "x"},
                          {typE = struct "S", name = "s"}],
            body = block [declaration {typE = sint, name = "y"},
                          statement (assign (ident "y", ident "x")),
                          statement (return (Some (ident "G")))]}) =
"char *ggg(int x, struct S s) {
int y;
y = x;
return G;
}
"
),(
"function_definition_1_4",
text 2 4 (printFunctionDefinition
           {return = void,
            name = "fff",
            parameters = [],
            body = block [statement (return (Some (ident "G")))]}) =
"        void fff() {
            return G;
        }
"
),(
"function_definition_2_4",
text 2 4 (printFunctionDefinition
           {return = pointer char,
            name = "ggg",
            parameters = [{typE = sint, name = "x"},
                          {typE = struct "S", name = "s"}],
            body = block [declaration {typE = sint, name = "y"},
                          statement (assign (ident "y", ident "x")),
                          statement (return (Some (ident "G")))]}) =
"        char *ggg(int x, struct S s) {
            int y;
            y = x;
            return G;
        }
"
),(
"function_definition_1_5",
text 1 6 (printFunctionDefinition
           {return = void,
            name = "fff",
            parameters = [],
            body = block [statement (return (Some (ident "G")))]}) =
"      void fff() {
            return G;
      }
"
),(
"function_definition_2_5",
text 1 6 (printFunctionDefinition
           {return = pointer char,
            name = "ggg",
            parameters = [{typE = sint, name = "x"},
                          {typE = struct "S", name = "s"}],
            body = block [declaration {typE = sint, name = "y"},
                          statement (assign (ident "y", ident "x")),
                          statement (return (Some (ident "G")))]}) =
"      char *ggg(int x, struct S s) {
            int y;
            y = x;
            return G;
      }
"
),(
"external_declaration_1_1",
text 0 0 (printExternalDeclaration
           (declaration (object {typE = sint, name = "x"}))) =
"int x;
"
),(
"external_declaration_1_1",
text 0 0 (printExternalDeclaration
           (function
             {return = pointer char,
              name = "ggg",
              parameters = [{typE = sint, name = "x"},
                            {typE = struct "S", name = "s"}],
              body = block [declaration {typE = sint, name = "y"},
                            statement (assign (ident "y", ident "x")),
                            statement (return (Some (ident "G")))]})) =
"char *ggg(int x, struct S s) {
int y;
y = x;
return G;
}
"
),(
"external_declaration_1_2",
text 0 4 (printExternalDeclaration
           (declaration (object {typE = sint, name = "x"}))) =
"int x;
"
),(
"external_declaration_1_2",
text 0 4 (printExternalDeclaration
           (function
             {return = pointer char,
              name = "ggg",
              parameters = [{typE = sint, name = "x"},
                            {typE = struct "S", name = "s"}],
              body = block [declaration {typE = sint, name = "y"},
                            statement (assign (ident "y", ident "x")),
                            statement (return (Some (ident "G")))]})) =
"char *ggg(int x, struct S s) {
    int y;
    y = x;
    return G;
}
"
),(
"external_declaration_1_3",
text 2 0 (printExternalDeclaration
           (declaration (object {typE = sint, name = "x"}))) =
"int x;
"
),(
"external_declaration_1_3",
text 2 0 (printExternalDeclaration
           (function
             {return = pointer char,
              name = "ggg",
              parameters = [{typE = sint, name = "x"},
                            {typE = struct "S", name = "s"}],
              body = block [declaration {typE = sint, name = "y"},
                            statement (assign (ident "y", ident "x")),
                            statement (return (Some (ident "G")))]})) =
"char *ggg(int x, struct S s) {
int y;
y = x;
return G;
}
"
),(
"external_declaration_1_4",
text 2 4 (printExternalDeclaration
           (declaration (object {typE = sint, name = "x"}))) =
"        int x;
"
),(
"external_declaration_1_4",
text 2 4 (printExternalDeclaration
           (function
             {return = pointer char,
              name = "ggg",
              parameters = [{typE = sint, name = "x"},
                            {typE = struct "S", name = "s"}],
              body = block [declaration {typE = sint, name = "y"},
                            statement (assign (ident "y", ident "x")),
                            statement (return (Some (ident "G")))]})) =
"        char *ggg(int x, struct S s) {
            int y;
            y = x;
            return G;
        }
"
),(
"external_declaration_1_5",
text 1 6 (printExternalDeclaration
           (declaration (object {typE = sint, name = "x"}))) =
"      int x;
"
),(
"external_declaration_1_5",
text 1 6 (printExternalDeclaration
           (function
             {return = pointer char,
              name = "ggg",
              parameters = [{typE = sint, name = "x"},
                            {typE = struct "S", name = "s"}],
              body = block [declaration {typE = sint, name = "y"},
                            statement (assign (ident "y", ident "x")),
                            statement (return (Some (ident "G")))]})) =
"      char *ggg(int x, struct S s) {
            int y;
            y = x;
            return G;
      }
"
),(
"translation_unit_1_1",
text 0 0 (printTranslationUnit []) = ""
),(
"translation_unit_2_1",
text 0 0 (printTranslationUnit
           [declaration (object {typE = sint, name = "x"}),
            declaration (struct {tag = "Node",
                                 members = [{typE = struct "S",
                                             name = "f"}]})]) =
"int x;

struct Node {
struct S f
};
"
),(
"translation_unit_3_1",
text 0 0 (printTranslationUnit
           [declaration (object {typE = sint, name = "x"}),
            declaration (struct {tag = "Node",
                                 members = [{typE = struct "S",
                                             name = "f"}]}),
            function
             {return = pointer char,
              name = "ggg",
              parameters = [{typE = sint, name = "x"},
                            {typE = struct "S", name = "s"}],
              body = block [declaration {typE = sint, name = "y"},
                            statement (assign (ident "y", ident "x")),
                            statement (return (Some (ident "G")))]},
            declaration (typedef {typE = ulong, name = "u4"})]) =
"int x;

struct Node {
struct S f
};

char *ggg(int x, struct S s) {
int y;
y = x;
return G;
}

typedef unsigned long u4;
"
),(
"translation_unit_1_2",
text 0 4 (printTranslationUnit []) = ""
),(
"translation_unit_2_2",
text 0 4 (printTranslationUnit
           [declaration (object {typE = sint, name = "x"}),
            declaration (struct {tag = "Node",
                                 members = [{typE = struct "S",
                                             name = "f"}]})]) =
"int x;

struct Node {
    struct S f
};
"
),(
"translation_unit_3_2",
text 0 4 (printTranslationUnit
           [declaration (object {typE = sint, name = "x"}),
            declaration (struct {tag = "Node",
                                 members = [{typE = struct "S", name = "f"}]}),
            function
             {return = pointer char,
              name = "ggg",
              parameters = [{typE = sint, name = "x"},
                            {typE = struct "S", name = "s"}],
              body = block [declaration {typE = sint, name = "y"},
                            statement (assign (ident "y", ident "x")),
                            statement (return (Some (ident "G")))]},
            declaration (typedef {typE = ulong, name = "u4"})]) =
"int x;

struct Node {
    struct S f
};

char *ggg(int x, struct S s) {
    int y;
    y = x;
    return G;
}

typedef unsigned long u4;
"
),(
"translation_unit_1_3",
text 2 0 (printTranslationUnit []) = ""
),(
"translation_unit_2_3",
text 2 0 (printTranslationUnit
           [declaration (object {typE = sint, name = "x"}),
            declaration (struct {tag = "Node",
                                 members = [{typE = struct "S",
                                             name = "f"}]})]) =
"int x;

struct Node {
struct S f
};
"
),(
"translation_unit_3_3",
text 2 0 (printTranslationUnit
           [declaration (object {typE = sint, name = "x"}),
            declaration (struct {tag = "Node",
                                 members = [{typE = struct "S",
                                             name = "f"}]}),
            function
             {return = pointer char,
              name = "ggg",
              parameters = [{typE = sint, name = "x"},
                            {typE = struct "S", name = "s"}],
              body = block [declaration {typE = sint, name = "y"},
                            statement (assign (ident "y", ident "x")),
                            statement (return (Some (ident "G")))]},
            declaration (typedef {typE = ulong, name = "u4"})]) =
"int x;

struct Node {
struct S f
};

char *ggg(int x, struct S s) {
int y;
y = x;
return G;
}

typedef unsigned long u4;
"
),(
"translation_unit_1_4",
text 2 4 (printTranslationUnit []) = ""
),(
"translation_unit_2_4",
text 2 4 (printTranslationUnit
           [declaration (object {typE = sint, name = "x"}),
            declaration (struct {tag = "Node",
                                 members = [{typE = struct "S",
                                             name = "f"}]})]) =
"        int x;

        struct Node {
            struct S f
        };
"
),(
"translation_unit_3_4",
text 2 4 (printTranslationUnit
           [declaration (object {typE = sint, name = "x"}),
            declaration (struct {tag = "Node",
                                 members = [{typE = struct "S",
                                             name = "f"}]}),
            function
             {return = pointer char,
              name = "ggg",
              parameters = [{typE = sint, name = "x"},
                            {typE = struct "S", name = "s"}],
              body = block [declaration {typE = sint, name = "y"},
                            statement (assign (ident "y", ident "x")),
                            statement (return (Some (ident "G")))]},
            declaration (typedef {typE = ulong, name = "u4"})]) =
"        int x;

        struct Node {
            struct S f
        };

        char *ggg(int x, struct S s) {
            int y;
            y = x;
            return G;
        }

        typedef unsigned long u4;
"
),(
"translation_unit_1_5",
text 1 6 (printTranslationUnit []) = ""
),(
"translation_unit_2_5",
text 1 6 (printTranslationUnit
           [declaration (object {typE = sint, name = "x"}),
            declaration (struct {tag = "Node",
                                 members = [{typE = struct "S",
                                             name = "f"}]})]) =
"      int x;

      struct Node {
            struct S f
      };
"
),(
"translation_unit_3_5",
text 1 6 (printTranslationUnit
           [declaration (object {typE = sint, name = "x"}),
            declaration (struct {tag = "Node",
                                 members = [{typE = struct "S",
                                             name = "f"}]}),
            function
             {return = pointer char,
              name = "ggg",
              parameters = [{typE = sint, name = "x"},
                            {typE = struct "S", name = "s"}],
              body = block [declaration {typE = sint, name = "y"},
                            statement (assign (ident "y", ident "x")),
                            statement (return (Some (ident "G")))]},
            declaration (typedef {typE = ulong, name = "u4"})]) =
"      int x;

      struct Node {
            struct S f
      };

      char *ggg(int x, struct S s) {
            int y;
            y = x;
            return G;
      }

      typedef unsigned long u4;
"
),(
"program_1",
printProgram
 0
 [declaration (object {typE = sint, name = "x"}),
  declaration (struct {tag = "Node",
                       members = [{typE = struct "S", name = "f"}]}),
  function
   {return = pointer char,
    name = "ggg",
    parameters = [{typE = sint, name = "x"},
                  {typE = struct "S", name = "s"}],
    body = block [declaration {typE = sint, name = "y"},
                  statement (assign (ident "y", ident "x")),
                  statement (return (Some (ident "G")))]},
  declaration (typedef {typE = ulong, name = "u4"})] =
"int x;

struct Node {
struct S f
};

char *ggg(int x, struct S s) {
int y;
y = x;
return G;
}

typedef unsigned long u4;
"
),(
"program_2",
printProgram
 1
 [declaration (object {typE = sint, name = "x"}),
  declaration (struct {tag = "Node",
                       members = [{typE = struct "S", name = "f"}]}),
  function
   {return = pointer char,
    name = "ggg",
    parameters = [{typE = sint, name = "x"},
                  {typE = struct "S", name = "s"}],
    body = block [declaration {typE = sint, name = "y"},
                  statement (assign (ident "y", ident "x")),
                  statement (return (Some (ident "G")))]},
  declaration (typedef {typE = ulong, name = "u4"})] =
"int x;

struct Node {
 struct S f
};

char *ggg(int x, struct S s) {
 int y;
 y = x;
 return G;
}

typedef unsigned long u4;
"
),(
"program_3",
printProgram
 2
 [declaration (object {typE = sint, name = "x"}),
  declaration (struct {tag = "Node",
                       members = [{typE = struct "S", name = "f"}]}),
  function
   {return = pointer char,
    name = "ggg",
    parameters = [{typE = sint, name = "x"},
                  {typE = struct "S", name = "s"}],
    body = block [declaration {typE = sint, name = "y"},
                  statement (assign (ident "y", ident "x")),
                  statement (return (Some (ident "G")))]},
  declaration (typedef {typE = ulong, name = "u4"})] =
"int x;

struct Node {
  struct S f
};

char *ggg(int x, struct S s) {
  int y;
  y = x;
  return G;
}

typedef unsigned long u4;
"
),(
"program_4",
printProgram
 4
 [declaration (object {typE = sint, name = "x"}),
  declaration (struct {tag = "Node",
                       members = [{typE = struct "S", name = "f"}]}),
  function
   {return = pointer char,
    name = "ggg",
    parameters = [{typE = sint, name = "x"},
                  {typE = struct "S", name = "s"}],
    body = block [declaration {typE = sint, name = "y"},
                  statement (assign (ident "y", ident "x")),
                  statement (return (Some (ident "G")))]},
  declaration (typedef {typE = ulong, name = "u4"})] =
"int x;

struct Node {
    struct S f
};

char *ggg(int x, struct S s) {
    int y;
    y = x;
    return G;
}

typedef unsigned long u4;
"
)]

(* True iff all the tests in the list pass. *)

op passed : Bool = forall? id (map (project 2) tests)

(* Total number of tests. *)

op total : Nat = length tests

(* Find first test that fails. *)

op failing : Option (String * Bool) =
  findLeftmost (fn t -> t.2 = false) tests

%% This prints "ERROR:" if a test fails, to be caught by the testing framework.
op run_test : () =
  if passed then 
    () 
  else 
    let Some(testname, _) = failing in let _ = writeLine ("ERROR: Test "^testname^" failed.") in ()

endspec
