/*
 * MetaSlangTokenContext.java
 *
 * $Id$
 *
 *
 *
 * $Log$
 * Revision 1.1  2003/01/30 02:01:52  gilham
 * Initial version.
 *
 *
 *
 */

package edu.kestrel.netbeans.editor;

import java.util.HashMap;
import org.netbeans.editor.BaseTokenCategory;
import org.netbeans.editor.BaseTokenID;
import org.netbeans.editor.TokenID;
import org.netbeans.editor.BaseImageTokenID;
import org.netbeans.editor.TokenContext;
import org.netbeans.editor.TokenContextPath;

/**
* MetaSlang token-context defines token-ids and token-categories
* used in MetaSlang language.
*
*/

public class MetaSlangTokenContext extends TokenContext {

    // Token category-ids
    public static final int KEYWORDS_ID           = 1;
    public static final int OPERATORS_ID          = KEYWORDS_ID + 1;
    public static final int NUMERIC_LITERALS_ID   = OPERATORS_ID + 1;
    public static final int ERRORS_ID             = NUMERIC_LITERALS_ID + 1;

    // Incomplete tokens
    public static final int INCOMPLETE_STRING_LITERAL_ID = ERRORS_ID + 1;
    public static final int INCOMPLETE_CHAR_LITERAL_ID = INCOMPLETE_STRING_LITERAL_ID + 1;
    public static final int INVALID_CHAR_ID = INCOMPLETE_CHAR_LITERAL_ID + 1;
    public static final int INVALID_OPERATOR_ID = INVALID_CHAR_ID + 1;
    public static final int INVALID_COMMENT_END_ID = INVALID_OPERATOR_ID + 1;

    // Numeric-ids for token-ids
    public static final int WHITESPACE_ID         = INVALID_COMMENT_END_ID + 1;
    public static final int IDENTIFIER_ID         = WHITESPACE_ID + 1;
    public static final int LINE_COMMENT_ID       = IDENTIFIER_ID + 1;
    public static final int BLOCK_COMMENT_ID      = LINE_COMMENT_ID + 1;
    public static final int CHAR_LITERAL_ID       = BLOCK_COMMENT_ID + 1;
    public static final int STRING_LITERAL_ID     = CHAR_LITERAL_ID + 1;
    public static final int INT_LITERAL_ID        = STRING_LITERAL_ID + 1;

    // Operator numeric-ids - do not modify //GEN-BEGIN
    public static final int LPAREN_ID = INT_LITERAL_ID + 1;    // (
    public static final int RPAREN_ID = LPAREN_ID + 1;         // )
    public static final int COMMA_ID = RPAREN_ID + 1;          // ,
    public static final int DOT_ID = COMMA_ID + 1;             // .
    public static final int DOTDOT_ID = DOT_ID + 1;            // ..
    public static final int SEMICOLON_ID = DOTDOT_ID + 1;      // ;
    public static final int LBRACKET_ID = SEMICOLON_ID + 1;    // [
    public static final int RBRACKET_ID = LBRACKET_ID + 1;     // ]
    public static final int UBAR_ID = RBRACKET_ID + 1;         // _
    public static final int LBRACE_ID = UBAR_ID + 1;           // {
    public static final int RBRACE_ID = LBRACE_ID + 1;         // }
    // End of Operator numeric-ids //GEN-END

    // Keywords numeric-ids - do not modify //GEN-BEGIN
    public static final int AS_ID = RBRACE_ID + 1;
    public static final int AXIOM_ID = AS_ID + 1;
    public static final int CASE_ID = AXIOM_ID + 1;
    public static final int CHOOSE_ID = CASE_ID + 1;
    public static final int CONJECTURE_ID = CHOOSE_ID + 1;
    public static final int DEF_ID = CONJECTURE_ID + 1;
    public static final int ELSE_ID = DEF_ID + 1;
    public static final int EMBED_ID = ELSE_ID + 1;
    public static final int EMBEDP_ID = EMBED_ID + 1;
    public static final int ENDSPEC_ID = EMBEDP_ID + 1;
    public static final int EX_ID = ENDSPEC_ID + 1;
    public static final int FA_ID = EX_ID + 1;
    public static final int FALSE_ID = FA_ID + 1;
    public static final int FN_ID = FALSE_ID + 1;
    public static final int IF_ID = FN_ID + 1;
    public static final int IMPORT_ID = IF_ID + 1;
    public static final int IN_ID = IMPORT_ID + 1;
    public static final int IS_ID = IN_ID + 1;
    public static final int LET_ID = IS_ID + 1;
    public static final int OF_ID = LET_ID + 1;
    public static final int OP_ID = OF_ID + 1;
    public static final int PROJECT_ID = OP_ID + 1;
    public static final int QUOTIENT_ID = PROJECT_ID + 1;
    public static final int RELAX_ID = QUOTIENT_ID + 1;
    public static final int RESTRICT_ID = RELAX_ID + 1;
    public static final int SORT_ID = RESTRICT_ID + 1;
    public static final int SPEC_ID = SORT_ID + 1;
    public static final int THEN_ID = SPEC_ID + 1;
    public static final int THEOREM_ID = THEN_ID + 1;
    public static final int TRUE_ID = THEOREM_ID + 1;
    public static final int WHERE_ID = TRUE_ID + 1;
    // End of Keywords numeric-ids //GEN-END


    // Token-categories
    /** All the keywords belong to this category. */
    public static final BaseTokenCategory KEYWORDS
    = new BaseTokenCategory("keywords", KEYWORDS_ID);

    /** All the operators belong to this category. */
    public static final BaseTokenCategory OPERATORS
    = new BaseTokenCategory("operators", OPERATORS_ID);

    /** All the numeric literals belong to this category. */
    public static final BaseTokenCategory NUMERIC_LITERALS
    = new BaseTokenCategory("numeric-literals", NUMERIC_LITERALS_ID);

    /** All the errorneous constructions and incomplete tokens
     * belong to this category.
     */
    public static final BaseTokenCategory ERRORS
    = new BaseTokenCategory("errors", ERRORS_ID);


    // Token-ids
    public static final BaseTokenID WHITESPACE = new BaseTokenID("whitespace", WHITESPACE_ID);

    public static final BaseTokenID IDENTIFIER = new BaseTokenID("identifier", IDENTIFIER_ID);

    /** Comment with the '%' prefix */
    public static final BaseTokenID LINE_COMMENT = new BaseTokenID("line-comment", LINE_COMMENT_ID);

    /** Block comment */
    public static final BaseTokenID BLOCK_COMMENT = new BaseTokenID("block-comment", BLOCK_COMMENT_ID);

    /** Character literal e.g. 'c' */
    public static final BaseTokenID CHAR_LITERAL = new BaseTokenID("char-literal", CHAR_LITERAL_ID);

    /** MetaSlang string literal e.g. "hello" */
    public static final BaseTokenID STRING_LITERAL = new BaseTokenID("string-literal", STRING_LITERAL_ID);

    /** MetaSlang integer literal e.g. 1234 */
    public static final BaseTokenID INT_LITERAL = new BaseTokenID("int-literal", INT_LITERAL_ID);

    // Operator token-ids - do not modify //GEN-BEGIN
    public static final BaseImageTokenID LPAREN = new BaseImageTokenID("lparen", LPAREN_ID, OPERATORS, "(");
    public static final BaseImageTokenID RPAREN = new BaseImageTokenID("rparen", RPAREN_ID, OPERATORS, ")");
    public static final BaseImageTokenID COMMA = new BaseImageTokenID("comma", COMMA_ID, OPERATORS, ",");
    public static final BaseImageTokenID DOT = new BaseImageTokenID("dot", DOT_ID, OPERATORS, ".");
    public static final BaseImageTokenID DOTDOT = new BaseImageTokenID("dotdot", DOTDOT_ID, OPERATORS, "..");
    public static final BaseImageTokenID SEMICOLON = new BaseImageTokenID("semicolon", SEMICOLON_ID, OPERATORS, ";");
    public static final BaseImageTokenID LBRACKET = new BaseImageTokenID("lbracket", LBRACKET_ID, OPERATORS, "[");
    public static final BaseImageTokenID RBRACKET = new BaseImageTokenID("rbracket", RBRACKET_ID, OPERATORS, "]");
    public static final BaseImageTokenID UBAR = new BaseImageTokenID("ubar", UBAR_ID, OPERATORS, "_");
    public static final BaseImageTokenID LBRACE = new BaseImageTokenID("lbrace", LBRACE_ID, OPERATORS, "{");
    public static final BaseImageTokenID RBRACE = new BaseImageTokenID("rbrace", RBRACE_ID, OPERATORS, "}");
    // End of Operator token-ids //GEN-END

    // Keyword token-ids - do not modify //GEN-BEGIN
    public static final BaseImageTokenID AS = new BaseImageTokenID("as", AS_ID, KEYWORDS);
    public static final BaseImageTokenID AXIOM = new BaseImageTokenID("axiom", AXIOM_ID, KEYWORDS);
    public static final BaseImageTokenID CASE = new BaseImageTokenID("case", CASE_ID, KEYWORDS);
    public static final BaseImageTokenID CHOOSE = new BaseImageTokenID("choose", CHOOSE_ID, KEYWORDS);
    public static final BaseImageTokenID CONJECTURE = new BaseImageTokenID("conjecture", CONJECTURE_ID, KEYWORDS);
    public static final BaseImageTokenID DEF = new BaseImageTokenID("def", DEF_ID, KEYWORDS);
    public static final BaseImageTokenID ELSE = new BaseImageTokenID("else", ELSE_ID, KEYWORDS);
    public static final BaseImageTokenID EMBED = new BaseImageTokenID("embed", EMBED_ID, KEYWORDS);
    public static final BaseImageTokenID EMBEDP = new BaseImageTokenID("embed?", EMBEDP_ID, KEYWORDS);
    public static final BaseImageTokenID ENDSPEC = new BaseImageTokenID("endspec", ENDSPEC_ID, KEYWORDS);
    public static final BaseImageTokenID EX = new BaseImageTokenID("ex", EX_ID, KEYWORDS);
    public static final BaseImageTokenID FA = new BaseImageTokenID("fa", FA_ID, KEYWORDS);
    public static final BaseImageTokenID FALSE = new BaseImageTokenID("false", FALSE_ID, KEYWORDS);
    public static final BaseImageTokenID FN = new BaseImageTokenID("fn", FN_ID, KEYWORDS);
    public static final BaseImageTokenID IF = new BaseImageTokenID("if", IF_ID, KEYWORDS);
    public static final BaseImageTokenID IMPORT = new BaseImageTokenID("import", IMPORT_ID, KEYWORDS);
    public static final BaseImageTokenID IN = new BaseImageTokenID("in", IN_ID, KEYWORDS);
    public static final BaseImageTokenID IS = new BaseImageTokenID("is", IS_ID, KEYWORDS);
    public static final BaseImageTokenID LET = new BaseImageTokenID("let", LET_ID, KEYWORDS);
    public static final BaseImageTokenID OF = new BaseImageTokenID("of", OF_ID, KEYWORDS);
    public static final BaseImageTokenID OP = new BaseImageTokenID("op", OP_ID, KEYWORDS);
    public static final BaseImageTokenID PROJECT = new BaseImageTokenID("project", PROJECT_ID, KEYWORDS);
    public static final BaseImageTokenID QUOTIENT = new BaseImageTokenID("quotient", QUOTIENT_ID, KEYWORDS);
    public static final BaseImageTokenID RELAX = new BaseImageTokenID("relax", RELAX_ID, KEYWORDS);
    public static final BaseImageTokenID RESTRICT = new BaseImageTokenID("restrict", RESTRICT_ID, KEYWORDS);
    public static final BaseImageTokenID SORT = new BaseImageTokenID("sort", SORT_ID, KEYWORDS);
    public static final BaseImageTokenID SPEC = new BaseImageTokenID("spec", SPEC_ID, KEYWORDS);
    public static final BaseImageTokenID THEN = new BaseImageTokenID("then", THEN_ID, KEYWORDS);
    public static final BaseImageTokenID THEOREM = new BaseImageTokenID("theorem", THEOREM_ID, KEYWORDS);
    public static final BaseImageTokenID TRUE = new BaseImageTokenID("true", TRUE_ID, KEYWORDS);
    public static final BaseImageTokenID WHERE = new BaseImageTokenID("where", WHERE_ID, KEYWORDS);
    // End of Keyword token-ids //GEN-END

    // Incomplete and error token-ids
    public static final BaseImageTokenID INCOMPLETE_STRING_LITERAL = new BaseImageTokenID("incomplete-string-literal", INCOMPLETE_STRING_LITERAL_ID, ERRORS);
    public static final BaseImageTokenID INCOMPLETE_CHAR_LITERAL = new BaseImageTokenID("incomplete-char-literal", INCOMPLETE_CHAR_LITERAL_ID, ERRORS);
    public static final BaseImageTokenID INVALID_CHAR = new BaseImageTokenID("invalid-char", INVALID_CHAR_ID, ERRORS);
    public static final BaseImageTokenID INVALID_OPERATOR = new BaseImageTokenID("invalid-operator", INVALID_OPERATOR_ID, ERRORS);
    public static final BaseImageTokenID INVALID_COMMENT_END = new BaseImageTokenID("invalid-comment-end", INVALID_COMMENT_END_ID, ERRORS);

    // Context instance declaration
    public static final MetaSlangTokenContext context = new MetaSlangTokenContext();

    public static final TokenContextPath contextPath = context.getContextPath();

    private static final HashMap str2kwd = new HashMap();

    static {
        BaseImageTokenID[] kwds = new BaseImageTokenID[] {//GEN-BEGIN
            AS, AXIOM, CASE, CHOOSE, CONJECTURE, DEF, ELSE, EMBED, 
            EMBEDP, ENDSPEC, EX, FA, FALSE, FN, IF, IMPORT, IN, IS, LET, 
            OF, OP, PROJECT, QUOTIENT, RELAX, RESTRICT, SORT, SPEC, THEN, 
            THEOREM, TRUE, WHERE
        };//GEN-END

        for (int i = kwds.length - 1; i >= 0; i--) {
            str2kwd.put(kwds[i].getImage(), kwds[i]);
        }
    }

    /** Checks whether the given token-id is a keyword.
    * @return true when the given token-id is a keyword.
    */
    public static boolean isKeyword(TokenID keywordTokenID) {
        int numID = (keywordTokenID != null) ? keywordTokenID.getNumericID() : -1;  //GEN-BEGIN
        return (numID >= AS_ID && numID <= WHERE_ID);
	//GEN-END
    }

    /** Checks whether the given string is a keyword. */
    public static boolean isKeyword(String s) {
        return isKeyword((TokenID)str2kwd.get(s));
    }

    /** Get the keyword token-id from string */
    public static TokenID getKeyword(String s) {
        return (TokenID)str2kwd.get(s);
    }

    private MetaSlangTokenContext() {
        super("meta-slang-");

        try {
            addDeclaredTokenIDs();
        } catch (Exception e) {
            if (Boolean.getBoolean("netbeans.debug.exceptions")) { // NOI18N
                e.printStackTrace();
            }
        }

    }

}
