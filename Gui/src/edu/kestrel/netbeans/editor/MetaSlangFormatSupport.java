/*
 * MetaSlangFormatSupport.java
 *
 * $Id$
 *
 *
 *
 * $Log$
 * Revision 1.2  2003/06/23 18:00:14  weilyn
 * internal release version
 *
 * Revision 1.1  2003/01/30 02:01:48  gilham
 * Initial version.
 *
 *
 *
 */

package edu.kestrel.netbeans.editor;

import org.netbeans.editor.TokenID;
import org.netbeans.editor.TokenItem;
import org.netbeans.editor.TokenContextPath;
import org.netbeans.editor.ext.FormatTokenPosition;
import org.netbeans.editor.ext.ExtFormatSupport;
import org.netbeans.editor.ext.FormatWriter;

import edu.kestrel.netbeans.editor.MetaSlangTokenContext;
import edu.kestrel.netbeans.Util;

/**
 * MetaSlang indentation services are located here
 *
 */

public class MetaSlangFormatSupport extends ExtFormatSupport {

    private TokenContextPath tokenContextPath;

    private boolean DEBUG = true;

    public MetaSlangFormatSupport(FormatWriter formatWriter) {
        this(formatWriter, MetaSlangTokenContext.contextPath);
    }

    public MetaSlangFormatSupport(FormatWriter formatWriter, TokenContextPath tokenContextPath) {
        super(formatWriter);
        this.tokenContextPath = tokenContextPath;
    }

    public TokenContextPath getTokenContextPath() {
        return tokenContextPath;
    }

    public boolean isComment(TokenItem token, int offset) {
        TokenID tokenID = token.getTokenID();
        return (token.getTokenContextPath() == tokenContextPath
                && (tokenID == MetaSlangTokenContext.LINE_COMMENT
                    || tokenID == MetaSlangTokenContext.BLOCK_COMMENT));
    }

    public boolean isMultiLineComment(TokenItem token) {
        return (token.getTokenID() == MetaSlangTokenContext.BLOCK_COMMENT);
    }

    public boolean isMultiLineComment(FormatTokenPosition pos) {
        TokenItem token = pos.getToken();
        return (token == null) ? false : isMultiLineComment(token);
    }

    public TokenID getWhitespaceTokenID() {
        return MetaSlangTokenContext.WHITESPACE;
    }

    public TokenContextPath getWhitespaceTokenContextPath() {
        return tokenContextPath;
    }

    public boolean canModifyWhitespace(TokenItem inToken) {
        if (inToken.getTokenContextPath() == MetaSlangTokenContext.contextPath) {
            switch (inToken.getTokenID().getNumericID()) {
	    case MetaSlangTokenContext.BLOCK_COMMENT_ID:
	    case MetaSlangTokenContext.WHITESPACE_ID:
		return true;
            }
        }

        return false;
    }


    /** Find the starting token of the syntactic block before
     * the given position and also return all the command
     * delimiters. It searches in the backward direction
     * for all the delimiters and statement starts and
     * return all the tokens that are either command starts
     * or delimiters. As the first step it uses
     * <code>getPreviousToken()</code> so it ignores the initial token.
     * @param token token before which the statement-start
     *  and delimiter is being searched.
     * @return token that is start of the given statement
     *  or command delimiter.
     *  If the start of the statement is not found, null is retrurned.
     */
    public TokenItem findSyntacticBlock(TokenItem token) {
	return findSyntacticBlock(token, true);
    }

    public TokenItem findSyntacticBlock(TokenItem token, boolean ignoreInitial) {
        TokenItem t = (ignoreInitial) ? getPreviousToken(token) : token; 
	if (DEBUG) {
	    Util.log("***     findSyntacticBlock: token="+token+", start token="+t);
	}
	int specDepth = 0;
	int braceDepth = 0;
	int braces = 0;

        while (t != null) {
            if (t.getTokenContextPath() == tokenContextPath) {

		switch (t.getTokenID().getNumericID()) {
		    /*
		case MetaSlangTokenContext.EQ_ID:
		case MetaSlangTokenContext.IS_ID:
		    if (specDepth == 0 && serviceMatchDepth == 0 && providerRecordDepth == 0 && braceDepth == 0) {
			TokenItem pt = getPreviousImportant(t);
			if (pt != null && pt.getTokenID().getNumericID() == MetaSlangTokenContext.IDENTIFIER_ID) {
			    TokenItem ppt = getPreviousImportant(pt);
			    if (ppt == null || isEndUnitKeyword(ppt)) {
				if (DEBUG) {
				    Util.log("***     findSyntacticBlock: return null");
				}
				return null;
			    }
			}
		    }
		    break;
		    */
		case MetaSlangTokenContext.SPEC_ID:
		    if (specDepth == 0) {
			if (DEBUG) {
			    Util.log("***     findSyntacticBlock: return "+t);
			}
			return t;
		    }
		    specDepth--;
		    break;
		case MetaSlangTokenContext.LBRACE_ID:
		    if (braceDepth == 0) {
			FormatTokenPosition firstNWSPos = findLineFirstNonWhitespace(getPosition(t, -1));
			if (DEBUG) {
			    Util.log("***     findSyntacticBlock: findLineFirstNonWhitespace()="+firstNWSPos);
			}
			if (firstNWSPos == null || firstNWSPos.getToken() == t) {
			    if (DEBUG) {
				Util.log("***     findSyntacticBlock: return "+t);
			    }
			    return t;
			}
		    } else {
			braceDepth--;
		    }
		    braces++;
		    break;
		case MetaSlangTokenContext.RBRACE_ID:
		    braceDepth++;
		    braces++;
		    break;
		}
	    }
	    t = getPreviousImportant(t);
	}

	if (DEBUG) {
	    Util.log("***     findSyntacticBlock: return "+t);
	}
	return t;
    }

    public TokenItem getPreviousImportant(TokenItem token) {
	TokenItem t = token.getPrevious();
        while (t != null && !isImportant(t, 0)) {
	    t = t.getPrevious();
	}
	return t;
    }

    public boolean isEndUnitKeyword(TokenItem token) {
	int id = token.getTokenID().getNumericID();	
	return id == MetaSlangTokenContext.ENDSPEC_ID;
    }

    /** Get the indentation for the given token.
     * It first searches whether there's an non-whitespace and a non-leftbrace
     * character on the line with the token and if so,
     * it takes indent of the non-ws char instead.
     * @param token token for which the indent is being searched.
     *  The token itself is ignored and the previous token
     *  is used as a base for the search.
     * @param forceFirstNonWhitespace set true to ignore leftbrace and search 
     * directly for first non-whitespace
     */
    public int getTokenIndent(TokenItem token, boolean forceFirstNonWhitespace) {
	FormatTokenPosition tp = getPosition(token, 0);
	// this is fix for bugs: 7980 and 9111
	// see the findLineFirstNonWhitespaceAndNonLeftBrace definition
	// for more info about the fix
	FormatTokenPosition fnw;
	if (forceFirstNonWhitespace)
	    fnw = findLineFirstNonWhitespace(tp);
	else
	    fnw = findLineFirstNonWhitespaceAndNonLeftBrace(tp);
        
	if (fnw != null) { // valid first non-whitespace
	    tp = fnw;
	}
	if (DEBUG) {
	    Util.log("***     getTokenIndent: token="+token+" forceFirstNonWhitespace="+forceFirstNonWhitespace+" fnw="+fnw+" return "+getVisualColumnOffset(tp));
	}
	return getVisualColumnOffset(tp);
    }

    public int getTokenIndent(TokenItem token) {
	return getTokenIndent(token, false);
    }   
    
    /** Find the indentation for the first token on the line.
     * The given token is also examined in some cases.
     */
    public int findIndent(TokenItem token) {
	if (DEBUG) {
	    Util.log("***   MetaSlangFormatSupport.findIndent(): token= "+token);
	}
	int indent = -1; // assign invalid indent
	TokenItem t;

	// First check the given token
	if (token != null) {
	    switch (token.getTokenID().getNumericID()) {
	    case MetaSlangTokenContext.LBRACE_ID:
		t = findSyntacticBlock(token);
		if (t == null) {
		    indent = 0;
		} else {
		    indent = getTokenIndent(t) + getShiftWidth();
		}
		break;
	    case MetaSlangTokenContext.RBRACE_ID:
		TokenItem mt = findMatchingToken(token, null, MetaSlangTokenContext.LBRACE, true);
		if (mt != null) { // valid matching left-brace
		    if (mt == findLineFirstNonWhitespace(getPosition(mt, 0)).getToken()) {
			indent = getTokenIndent(mt);
		    } else {
			t = findSyntacticBlock(mt);
			if (t == null) {
			    indent = getTokenIndent(mt);
			} else {
			    indent = getTokenIndent(t) + getShiftWidth();
			}
		    }
		} else { // no matching left brace
		    indent = getTokenIndent(token); // leave as is
		}
		break;
	    case MetaSlangTokenContext.ENDSPEC_ID:
		mt = findMatchingToken(token, null, MetaSlangTokenContext.SPEC, true);
		if (mt != null) { // valid spec
		    indent = getTokenIndent(mt);
		} else { // no matching spec
		    indent = getTokenIndent(token); // leave as is
		}
		break;
	    }
	}

	// If indent not found, search back for the first important token
	if (indent < 0) { // if not yet resolved
	    t = findImportantToken(token, null, true);
	    if (t != null) {
		TokenItem bt = findSyntacticBlock(t, false);
		if (bt != null) {
                    if (DEBUG) {
                        Util.log("MetaSlangFormatSupport.findIndent: getTokenIndent = "+getTokenIndent(bt)+", getShiftWidth = "+getShiftWidth());
                    }
		    indent = getTokenIndent(bt) + getShiftWidth();
		} 
	    }
	}
	
	if (indent < 0) { // no important token found
	    indent = 0;
	}

	if (DEBUG) {
	    Util.log("***   MetaSlangFormatSupport.findIndent(): return "+indent);
	}
	return indent;
    }

    public FormatTokenPosition indentLine(FormatTokenPosition pos) {
        int indent = 0; // Desired indent

        // Get the first non-whitespace position on the line
        FormatTokenPosition firstNWS = findLineFirstNonWhitespace(pos);
        if (firstNWS != null) { // some non-WS on the line
            if (isComment(firstNWS)) { // comment is first on the line
                if (isMultiLineComment(firstNWS) && firstNWS.getOffset() != 0) {

                    // Indent the inner lines of the multi-line comment by one
                    indent = getLineIndent(getPosition(firstNWS.getToken(), 0), true) + 1;

                    // If the line is inside multi-line comment and doesn't contain '*'
                    if (!isIndentOnly()) {
                        indent = getLineIndent(pos, true);
                    }

                } else if (!isMultiLineComment(firstNWS)) { // line-comment
                    indent = findIndent(firstNWS.getToken());
                } else { // multi-line comment
		    // check whether the multiline comment isn't finished on the same line (see issue 12821)
		    if (firstNWS.getToken().getImage().indexOf('\n') == -1)
			indent = findIndent(firstNWS.getToken());
		    else
			indent = getLineIndent(firstNWS, true);
		}

            } else { // first non-WS char is not comment
		if (DEBUG) {
		    Util.log("*** MetaSlangFormatSupport.indentLine: pos="+pos+" first non whitespace token= "+firstNWS.getToken());
		}
                indent = findIndent(firstNWS.getToken());
            }

        } else { // whole line is WS
            // Can be empty line inside multi-line comment
            TokenItem token = pos.getToken();
            if (token == null) {
                token = findLineStart(pos).getToken();
                if (token == null) { // empty line
                    token = getLastToken();
                }
            }

            if (token != null && isMultiLineComment(token)) {
                // Indent the multi-comment 
                indent = getVisualColumnOffset(getPosition(token, 0));

            } else { // non-multi-line comment
		if (DEBUG) {
		    Util.log("*** MetaSlangFormatSupport.indentLine: pos="+pos);
		}
                indent = findIndent(pos.getToken());
            }
        }

        // For indent-only always indent
	pos = changeLineIndent(pos, indent);
	if (DEBUG) {
	    Util.log("*** MetaSlangFormatSupport.indentLine: indent="+indent+" return "+pos);
	}
        return pos;
    }

    /** Check whether the given semicolon is inside
     * the for() statement.
     * @param token token to check. It must be a semicolon.
     * @return true if the given semicolon is inside
     *  the for() statement, or false otherwise.
     */
    /*
    public boolean isArgumentListComma(TokenItem token) {
        if (token == null 
	    || !tokenEquals(token, JavaTokenContext.COMMA, tokenContextPath)) {
            throw new IllegalArgumentException("Only accept ','.");
        }

        int parDepth = 0; // parenthesis depth
        int braceDepth = 0; // brace depth
        boolean commaFound = false; // next comma
        token = token.getPrevious(); // ignore this comma
        while (token != null) {
            if (tokenEquals(token, JavaTokenContext.LPAREN, tokenContextPath)) {
                if (parDepth == 0) { // could be a 'for ('
                    return true;
                } else { // non-zero depth
                    parDepth--;
                }

            } else if (tokenEquals(token, JavaTokenContext.RPAREN, tokenContextPath)) {
                parDepth++;

            } else if (tokenEquals(token, JavaTokenContext.LBRACE, tokenContextPath)) {
                if (braceDepth == 0) { // unclosed left brace
                    return false;
                }
                braceDepth--;

            } else if (tokenEquals(token, JavaTokenContext.RBRACE, tokenContextPath)) {
                braceDepth++;

            }

            token = token.getPrevious();
        }

        return false;
    }
    */

    public boolean getFormatSpaceAfterComma() {
        return getSettingBoolean(MetaSlangSettingsNames.META_SLANG_FORMAT_SPACE_AFTER_COMMA,
                                 MetaSlangSettingsDefaults.defaultMetaSlangFormatSpaceAfterComma);
    }

    public boolean getFormatLeadingSpaceInComment() {
        return getSettingBoolean(MetaSlangSettingsNames.META_SLANG_FORMAT_LEADING_SPACE_IN_COMMENT,
                                 MetaSlangSettingsDefaults.defaultMetaSlangFormatLeadingSpaceInComment);
    }

    
    /*   this is fix for bugs: 7980 and 9111. if user enters
     *        {   foo();
     *   and press enter at the end of the line, she wants
     *   to be indented just under "f" in "foo();" and not under the "{" 
     *   as it happens now. and this is what findLineFirstNonWhitespaceAndNonLeftBrace checks
     */    
    public FormatTokenPosition findLineFirstNonWhitespaceAndNonLeftBrace(FormatTokenPosition pos) {
        // first call the findLineFirstNonWhitespace
        FormatTokenPosition ftp = super.findLineFirstNonWhitespace(pos);
        if (ftp == null) { // no line start, no WS
            return null;
        }

        // now checks if the first non-whitespace char is "{"
        // if it is, find the next non-whitespace char
        if (!ftp.getToken().getImage().startsWith("{"))
            return ftp;

        // if the left brace is closed on the same line - "{ foo(); }"
        // it must be ignored. otherwise next statement is incorrectly indented 
        // under the "f" and not under the "{" as expected
        FormatTokenPosition eolp = findNextEOL(ftp);
        TokenItem mt = findMatchingToken(ftp.getToken(), 
					   eolp != null ? eolp.getToken() : null, MetaSlangTokenContext.RBRACE, false);
        if (mt != null)
            return ftp;
        
        FormatTokenPosition ftp_next = getNextPosition(ftp);
        if (ftp_next == null)
            return ftp;
        
        FormatTokenPosition ftp2 = findImportant(ftp_next, null, true, false);
        if (ftp2 != null)
            return ftp2;
        else
            return ftp;
    }

    }
