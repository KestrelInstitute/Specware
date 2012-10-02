/*
 * MetaSlangSyntaxSupport.java
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

import java.util.List;
import java.util.Map;
import java.util.HashMap;
import javax.swing.text.BadLocationException;
import javax.swing.event.DocumentEvent;
import org.netbeans.editor.BaseDocument;
import org.netbeans.editor.TextBatchProcessor;
import org.netbeans.editor.FinderFactory;
import org.netbeans.editor.TokenID;
import org.netbeans.editor.ext.ExtSyntaxSupport;

/**
 * Support methods for syntax analyzes
 *
 */

public class MetaSlangSyntaxSupport extends ExtSyntaxSupport {
    
    // Internal meta-slang declaration token processor states
    static final int INIT = 0;
    static final int AFTER_TYPE = 1;
    static final int AFTER_VARIABLE = 2;
    static final int AFTER_COMMA = 3;
    static final int AFTER_DOT = 4;
    static final int AFTER_TYPE_LSB = 5;
    static final int AFTER_MATCHING_VARIABLE_LSB = 6;
    static final int AFTER_MATCHING_VARIABLE = 7;
    static final int AFTER_EQUAL = 8; // in decl after "var ="
    
    private static final TokenID[] COMMENT_TOKENS = new TokenID[] {
        MetaSlangTokenContext.LINE_COMMENT,
        MetaSlangTokenContext.BLOCK_COMMENT
    };
    
    private static final TokenID[] BRACKET_SKIP_TOKENS = new TokenID[] {
        MetaSlangTokenContext.LINE_COMMENT,
        MetaSlangTokenContext.BLOCK_COMMENT,
        MetaSlangTokenContext.CHAR_LITERAL,
        MetaSlangTokenContext.STRING_LITERAL
    };
    
    private static final char[] COMMAND_SEPARATOR_CHARS = new char[] {
        ';', '{', '}'
    };
    
    public MetaSlangSyntaxSupport(BaseDocument doc) {
        super(doc);
        
        tokenNumericIDsValid = true;
    }
    
    protected void documentModified(DocumentEvent evt) {
        super.documentModified(evt);
    }
    
    public TokenID[] getCommentTokens() {
        return COMMENT_TOKENS;
    }
    
    public TokenID[] getBracketSkipTokens() {
        return BRACKET_SKIP_TOKENS;
    }
    
    /** Return the position of the last command separator before
     * the given position.
     */
    public int getLastCommandSeparator(int pos)
    throws BadLocationException {
        TextBatchProcessor tbp = new TextBatchProcessor() {
            public int processTextBatch(BaseDocument doc, int startPos, int endPos,
            boolean lastBatch) {
                try {
                    int[] blks = getCommentBlocks(endPos, startPos);
                    FinderFactory.CharArrayBwdFinder cmdFinder
                    = new FinderFactory.CharArrayBwdFinder(COMMAND_SEPARATOR_CHARS);
                    return findOutsideBlocks(cmdFinder, startPos, endPos, blks);
                } catch (BadLocationException e) {
                    e.printStackTrace();
                    return -1;
                }
            }
        };
        return getDocument().processText(tbp, pos, 0);
    }
    
}
