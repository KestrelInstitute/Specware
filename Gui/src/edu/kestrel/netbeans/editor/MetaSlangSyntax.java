/*
 * MetaSlangSyntax.java
 *
 * $Id$
 *
 *
 *
 * $Log$
 *
 *
 */
package edu.kestrel.netbeans.editor;

import org.netbeans.editor.Syntax;
import org.netbeans.editor.TokenID;

import edu.kestrel.netbeans.Util;

/**
 * Syntax analyzes for MetaSlang source files.
 * Tokens and internal states are given below. 
 *
 */

public class MetaSlangSyntax extends Syntax {

    // Internal states
    private static final int ISI_WHITESPACE = 2; // inside white space
    private static final int ISI_LINE_COMMENT = ISI_WHITESPACE + 1; // inside line comment //
    private static final int ISI_BLOCK_COMMENT = ISI_LINE_COMMENT + 1; // inside block comment (* ... *)
    private static final int ISI_STRING = ISI_BLOCK_COMMENT + 1; // inside string constant
    private static final int ISI_STRING_A_BSLASH = ISI_STRING + 1; // inside string constant after backslash
    private static final int ISI_CHAR = ISI_STRING_A_BSLASH + 1; // inside char constant
    private static final int ISI_CHAR_A_BSLASH = ISI_CHAR + 1; // inside char constant after backslash
    private static final int ISI_WORD_SYMBOL = ISI_CHAR_A_BSLASH + 1; // inside word symbol
    private static final int ISI_NON_WORD_SYMBOL = ISI_WORD_SYMBOL + 1; // inside non word symbol
    private static final int ISA_STAR_I_BLOCK_COMMENT = ISI_NON_WORD_SYMBOL + 1; // after '*'
    private static final int ISI_INT = ISA_STAR_I_BLOCK_COMMENT + 1; // integer number
    private static final int ISA_LPAREN = ISI_INT + 1; // after '('

    public MetaSlangSyntax() {
        tokenContextPath = MetaSlangTokenContext.contextPath;
    }

    protected TokenID parseToken() {
        char actChar;

        while(offset < stopOffset) {
            actChar = buffer[offset];

            switch (state) {
            case INIT:
                switch (actChar) {
                case '"': // NOI18N
                    state = ISI_STRING;
                    break;
                case '#':
                    state = ISI_CHAR;
                    break;
                case '%':
                    state = ISI_LINE_COMMENT;
                    break;
                case '_':
                    offset++;
                    return MetaSlangTokenContext.UBAR;
                case '(':
                    state = ISA_LPAREN;
		    break;
                case ')':
                    offset++;
                    return MetaSlangTokenContext.RPAREN;
                case '[':
                    offset++;
                    return MetaSlangTokenContext.LBRACKET;
                case ']':
                    offset++;
                    return MetaSlangTokenContext.RBRACKET;
                case '{':
                    offset++;
                    return MetaSlangTokenContext.LBRACE;
                case '}':
                    offset++;
                    return MetaSlangTokenContext.RBRACE;
                case ',':
                    offset++;
                    return MetaSlangTokenContext.COMMA;
                case ';':
                    offset++;
                    return MetaSlangTokenContext.SEMICOLON;
                case '.':
                    offset++;
                    return MetaSlangTokenContext.DOT;

                default:
                    // Check for whitespace
                    if (Character.isWhitespace(actChar)) {
                        state = ISI_WHITESPACE;
                        break;
                    }

                    // Check for digit
                    if (Character.isDigit(actChar)) {
                        state = ISI_INT;
                        break;
                    }

                    // Check for word symbol
                    if (isMetaSlangWordSymbolStart(actChar)) {
                        state = ISI_WORD_SYMBOL;
                        break;
                    }

                    // Check for non-word symbol
                    if (isMetaSlangNonWordSymbolPart(actChar)) {
                        state = ISI_NON_WORD_SYMBOL;
                        break;
                    }

                    offset++;
                    return MetaSlangTokenContext.INVALID_CHAR;
                }
                break;

            case ISI_WHITESPACE: // white space
                if (!Character.isWhitespace(actChar)) {
                    state = INIT;
                    return MetaSlangTokenContext.WHITESPACE;
                }
                break;

            case ISI_LINE_COMMENT:
                switch (actChar) {
                case '\n':
                    state = INIT;
                    return MetaSlangTokenContext.LINE_COMMENT;
                }
                break;

            case ISI_BLOCK_COMMENT:
                switch (actChar) {
                case '*':
                    state = ISA_STAR_I_BLOCK_COMMENT;
                    break;
                }
                break;

            case ISI_STRING:
                switch (actChar) {
                case '\\':
                    state = ISI_STRING_A_BSLASH;
                    break;
                case '\n':
                    state = INIT;
                    supposedTokenID = MetaSlangTokenContext.STRING_LITERAL;
		    //!!!                    return MetaSlangTokenContext.INCOMPLETE_STRING_LITERAL;
                    return supposedTokenID;
                case '"': // NOI18N
                    offset++;
                    state = INIT;
                    return MetaSlangTokenContext.STRING_LITERAL;
                }
                break;

            case ISI_STRING_A_BSLASH:
                switch (actChar) {
                case '"': // NOI18N
                case '\\':
                    break;
                default:
                    offset--;
                    break;
                }
                state = ISI_STRING;
                break;

            case ISI_CHAR:
                switch (actChar) {
                case '\\':
                    state = ISI_CHAR_A_BSLASH;
                    break;
                case '\n':
                    state = INIT;
                    supposedTokenID = MetaSlangTokenContext.CHAR_LITERAL;
		    // !!!                    return MetaSlangTokenContext.INCOMPLETE_CHAR_LITERAL;
                    return supposedTokenID;
		default:
                    offset++;
                    state = INIT;
                    return MetaSlangTokenContext.CHAR_LITERAL;
                }
                break;

            case ISI_CHAR_A_BSLASH:
                switch (actChar) {
                case '\'':
                case '\\':
                    break;
                default:
                    offset--;
                    break;
                }
                state = ISI_CHAR;
                break;

            case ISI_WORD_SYMBOL:
                if (!isMetaSlangWordSymbolPart(actChar)) {
                    state = INIT;
                    TokenID tid = matchKeyword(buffer, tokenOffset, offset - tokenOffset);
                    return (tid != null) ? tid : MetaSlangTokenContext.IDENTIFIER;
                }
                break;

            case ISI_NON_WORD_SYMBOL:
                if (!isMetaSlangNonWordSymbolPart(actChar)) {
                    state = INIT;
                    return MetaSlangTokenContext.IDENTIFIER;
                }
                break;

            case ISA_LPAREN:
                switch (actChar) {
                case '*':
                    state = ISI_BLOCK_COMMENT;
                    break;
                default:
                    state = INIT;
                    return MetaSlangTokenContext.LPAREN;
                }
                break;
               
            case ISA_STAR_I_BLOCK_COMMENT:
                switch (actChar) {
                case ')':
                    offset++;
                    state = INIT;
                    return MetaSlangTokenContext.BLOCK_COMMENT;
                default:
                    offset--;
                    state = ISI_BLOCK_COMMENT;
                    break;
                }
                break;

            case ISI_INT:
		if (!(actChar >= '0' && actChar <= '9')) {
		    state = INIT;
		    return MetaSlangTokenContext.INT_LITERAL;
                }
                break;

            } // end of switch(state)

            offset++;
        } // end of while(offset...)

        /** At this stage there's no more text in the scanned buffer.
	 * Scanner first checks whether this is completely the last
	 * available buffer.
	 */

	if (lastBuffer) {
	    switch(state) {
	    case ISI_WHITESPACE:
		state = INIT;
		return MetaSlangTokenContext.WHITESPACE;
	    case ISI_WORD_SYMBOL:
		state = INIT;
		TokenID kwd = matchKeyword(buffer, tokenOffset, offset - tokenOffset);
		return (kwd != null) ? kwd : MetaSlangTokenContext.IDENTIFIER;
	    case ISI_NON_WORD_SYMBOL:
		state = INIT;
		return MetaSlangTokenContext.IDENTIFIER;
	    case ISI_LINE_COMMENT:
		return MetaSlangTokenContext.LINE_COMMENT; // stay in line-comment state
	    case ISI_BLOCK_COMMENT:
	    case ISA_STAR_I_BLOCK_COMMENT:
		return MetaSlangTokenContext.BLOCK_COMMENT; // stay in block-comment state
	    case ISI_STRING:
	    case ISI_STRING_A_BSLASH:
		return MetaSlangTokenContext.STRING_LITERAL; // hold the state
	    case ISI_CHAR:
	    case ISI_CHAR_A_BSLASH:
		return MetaSlangTokenContext.CHAR_LITERAL; // hold the state
	    case ISI_INT:
		state = INIT;
		return MetaSlangTokenContext.INT_LITERAL;
	    case ISA_LPAREN:
		state = INIT;
		return MetaSlangTokenContext.LPAREN;
	    }
	}

	/* At this stage there's no more text in the scanned buffer, but
	 * this buffer is not the last so the scan will continue on another buffer.
	 * The scanner tries to minimize the amount of characters
	 * that will be prescanned in the next buffer by returning the token
	 * where possible.
	 */

	switch (state) {
	case ISI_WHITESPACE:
	    return MetaSlangTokenContext.WHITESPACE;
	}

	return null; // nothing found
    }

    public String getStateName(int stateNumber) {
        switch(stateNumber) {
        case ISI_WHITESPACE:
            return "ISI_WHITESPACE"; // NOI18N
        case ISI_LINE_COMMENT:
            return "ISI_LINE_COMMENT"; // NOI18N
        case ISI_BLOCK_COMMENT:
            return "ISI_BLOCK_COMMENT"; // NOI18N
        case ISI_STRING:
            return "ISI_STRING"; // NOI18N
        case ISI_STRING_A_BSLASH:
            return "ISI_STRING_A_BSLASH"; // NOI18N
        case ISI_CHAR:
            return "ISI_CHAR"; // NOI18N
        case ISI_CHAR_A_BSLASH:
            return "ISI_CHAR_A_BSLASH"; // NOI18N
        case ISI_WORD_SYMBOL:
            return "ISI_WORD_SYMBOL"; // NOI18N
        case ISI_NON_WORD_SYMBOL:
            return "ISI_NON_WORD_SYMBOL"; // NOI18N
        case ISA_STAR_I_BLOCK_COMMENT:
            return "ISA_STAR_I_BLOCK_COMMENT"; // NOI18N
        case ISI_INT:
            return "ISI_INT"; // NOI18N
        case ISA_LPAREN:
            return "ISA_LPAREN"; // NOI18N

        default:
            return super.getStateName(stateNumber);
        }
    }

    public static final boolean isMetaSlangWordSymbolStart(char ch) {
        return java.lang.Character.isLetter(ch);
    }

    public static final boolean isMetaSlangWordSymbolPart(char ch) {
        return (java.lang.Character.isLetterOrDigit(ch) || ch == '_' || ch == '?');
    }

    public static final boolean isMetaSlangNonWordSymbolPart(char ch) {
        return (ch == '`' ||
		ch == '~' ||
		ch == '!' ||
		ch == '@' ||
		ch == '$' ||
		ch == '^' ||
		ch == '&' ||
		ch == '*' ||
		ch == '-' ||
		ch == '=' ||
		ch == '+' ||
		ch == '\\' ||
		ch == '|' ||
		ch == ':' ||
		ch == '<' ||
		ch == '>' ||
		ch == '/' ||
		ch == '?');
    }

    public static final boolean isMetaSlangIdentifier(String id) {
        if (id == null) return false;
        if (id.equals("")) return false; // NOI18N
        char ch = id.charAt(0);
        if (isMetaSlangWordSymbolStart(ch)) {
	    for (int i = 1; i < id.length(); i++) {
		ch = id.charAt(i);
		if (!isMetaSlangWordSymbolPart(ch))
		    return false;
	    }
	    // test if id is a keyword
	    if (MetaSlangTokenContext.isKeyword(id)) return false;
	    return true;
	} 
	if (isMetaSlangNonWordSymbolPart(ch)) {
	    for (int i = 1; i < id.length(); i++) {
		ch = id.charAt(i);
		if (!isMetaSlangNonWordSymbolPart(ch))
		    return false;
	    }
	    return true;
	}
	return false;
    }

    // Generated code for matchKeyword - do not modify //GEN-BEGIN
    public static TokenID matchKeyword(char[] buffer, int offset, int len) {
        if (len > 8)
            return null;
        if (len <= 1)
            return null;
        switch (buffer[offset++]) {
            case 'a':
                return (len == 2
                    && buffer[offset++] == 's')
                        ? MetaSlangTokenContext.AS : null;
            case 'c':
                if (len <= 3)
                    return null;
                switch (buffer[offset++]) {
                    case 'a':
                        return (len == 4
                            && buffer[offset++] == 's'
                            && buffer[offset++] == 'e')
                                ? MetaSlangTokenContext.CASE : null;
                    case 'h':
                        return (len == 6
                            && buffer[offset++] == 'o'
                            && buffer[offset++] == 'o'
                            && buffer[offset++] == 's'
                            && buffer[offset++] == 'e')
                                ? MetaSlangTokenContext.CHOOSE : null;
                    default:
                        return null;
                }
            case 'd':
                return (len == 3
                    && buffer[offset++] == 'e'
                    && buffer[offset++] == 'f')
                        ? MetaSlangTokenContext.DEF : null;
            case 'e':
                switch (buffer[offset++]) {
                    case 'l':
                        return (len == 4
                            && buffer[offset++] == 's'
                            && buffer[offset++] == 'e')
                                ? MetaSlangTokenContext.ELSE : null;
                    case 'm':
                        if (len <= 4)
                            return null;
                        if (buffer[offset++] != 'b'
                            || buffer[offset++] != 'e'
                            || buffer[offset++] != 'd')
                                return null;
                        if (len == 5)
                            return MetaSlangTokenContext.EMBED;
                        if (buffer[offset++] != '?')
                                return null;
                        if (len == 6)
                            return MetaSlangTokenContext.EMBEDP;
                        return null;
                    case 'n':
                        return (len == 7
                            && buffer[offset++] == 'd'
                            && buffer[offset++] == 's'
                            && buffer[offset++] == 'p'
                            && buffer[offset++] == 'e'
                            && buffer[offset++] == 'c')
                                ? MetaSlangTokenContext.ENDSPEC : null;
                    case 'x':
                        return (len == 2)
                                ? MetaSlangTokenContext.EX : null;
                    default:
                        return null;
                }
            case 'f':
                switch (buffer[offset++]) {
                    case 'a':
                        if (len == 2)
                            return MetaSlangTokenContext.FA;
                        switch (buffer[offset++]) {
                            case 'l':
                                return (len == 5
                                    && buffer[offset++] == 's'
                                    && buffer[offset++] == 'e')
                                        ? MetaSlangTokenContext.FALSE : null;
                            default:
                                return null;
                        }
                    case 'n':
                        return (len == 2)
                                ? MetaSlangTokenContext.FN : null;
                    default:
                        return null;
                }
            case 'i':
                switch (buffer[offset++]) {
                    case 'f':
                        return (len == 2)
                                ? MetaSlangTokenContext.IF : null;
                    case 'm':
                        return (len == 6
                            && buffer[offset++] == 'p'
                            && buffer[offset++] == 'o'
                            && buffer[offset++] == 'r'
                            && buffer[offset++] == 't')
                                ? MetaSlangTokenContext.IMPORT : null;
                    case 'n':
                        return (len == 2)
                                ? MetaSlangTokenContext.IN : null;
                    case 's':
                        return (len == 2)
                                ? MetaSlangTokenContext.IS : null;
                    default:
                        return null;
                }
            case 'l':
                return (len == 3
                    && buffer[offset++] == 'e'
                    && buffer[offset++] == 't')
                        ? MetaSlangTokenContext.LET : null;
            case 'o':
                switch (buffer[offset++]) {
                    case 'f':
                        return (len == 2)
                                ? MetaSlangTokenContext.OF : null;
                    case 'p':
                        return (len == 2)
                                ? MetaSlangTokenContext.OP : null;
                    default:
                        return null;
                }
            case 'p':
                return (len == 7
                    && buffer[offset++] == 'r'
                    && buffer[offset++] == 'o'
                    && buffer[offset++] == 'j'
                    && buffer[offset++] == 'e'
                    && buffer[offset++] == 'c'
                    && buffer[offset++] == 't')
                        ? MetaSlangTokenContext.PROJECT : null;
            case 'q':
                return (len == 8
                    && buffer[offset++] == 'u'
                    && buffer[offset++] == 'o'
                    && buffer[offset++] == 't'
                    && buffer[offset++] == 'i'
                    && buffer[offset++] == 'e'
                    && buffer[offset++] == 'n'
                    && buffer[offset++] == 't')
                        ? MetaSlangTokenContext.QUOTIENT : null;
            case 'r':
                if (len <= 4)
                    return null;
                if (buffer[offset++] != 'e')
                        return null;
                switch (buffer[offset++]) {
                    case 'l':
                        return (len == 5
                            && buffer[offset++] == 'a'
                            && buffer[offset++] == 'x')
                                ? MetaSlangTokenContext.RELAX : null;
                    case 's':
                        return (len == 8
                            && buffer[offset++] == 't'
                            && buffer[offset++] == 'r'
                            && buffer[offset++] == 'i'
                            && buffer[offset++] == 'c'
                            && buffer[offset++] == 't')
                                ? MetaSlangTokenContext.RESTRICT : null;
                    default:
                        return null;
                }
            case 's':
                if (len <= 3)
                    return null;
                switch (buffer[offset++]) {
                    case 'o':
                        return (len == 4
                            && buffer[offset++] == 'r'
                            && buffer[offset++] == 't')
                                ? MetaSlangTokenContext.SORT : null;
                    case 'p':
                        return (len == 4
                            && buffer[offset++] == 'e'
                            && buffer[offset++] == 'c')
                                ? MetaSlangTokenContext.SPEC : null;
                    default:
                        return null;
                }
            case 't':
                if (len <= 3)
                    return null;
                switch (buffer[offset++]) {
                    case 'h':
                        return (len == 4
                            && buffer[offset++] == 'e'
                            && buffer[offset++] == 'n')
                                ? MetaSlangTokenContext.THEN : null;
                    case 'r':
                        return (len == 4
                            && buffer[offset++] == 'u'
                            && buffer[offset++] == 'e')
                                ? MetaSlangTokenContext.TRUE : null;
                    default:
                        return null;
                }
            case 'w':
                return (len == 5
                    && buffer[offset++] == 'h'
                    && buffer[offset++] == 'e'
                    && buffer[offset++] == 'r'
                    && buffer[offset++] == 'e')
                        ? MetaSlangTokenContext.WHERE : null;
            default:
                return null;
        }
    }
    // End of matchKeyword //GEN-END
}
