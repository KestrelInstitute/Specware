/*
 * MetaSlangFormatter.java
 *
 * $Id$
 *
 *
 *
 * $Log$
 * Revision 1.1  2003/01/30 02:01:48  gilham
 * Initial version.
 *
 *
 *
 */

package edu.kestrel.netbeans.editor;

import javax.swing.text.JTextComponent;
import javax.swing.text.BadLocationException;
import org.netbeans.editor.TokenItem;
import org.netbeans.editor.BaseDocument;
import org.netbeans.editor.Utilities;
import org.netbeans.editor.Syntax;
import org.netbeans.editor.ext.AbstractFormatLayer;
import org.netbeans.editor.ext.FormatTokenPosition;
import org.netbeans.editor.ext.ExtFormatter;
import org.netbeans.editor.ext.FormatSupport;
import org.netbeans.editor.ext.FormatWriter;

/**
 * MetaSlang indentation services are located here
 *
 */

public class MetaSlangFormatter extends ExtFormatter {

    public MetaSlangFormatter(Class kitClass) {
        super(kitClass);
    }

    protected boolean acceptSyntax(Syntax syntax) {
        return (syntax instanceof MetaSlangSyntax);
    }

    public int[] getReformatBlock(JTextComponent target, String typedText) {
        int[] ret = null;
        BaseDocument doc = Utilities.getDocument(target);
        int dotPos = target.getCaret().getDot();
        if (doc != null) {
            /* Check whether the user has written the ending 'e'
             * of the first 'else' on the line.
             */
            if ("e".equals(typedText)) {
                try {
                    int fnw = Utilities.getRowFirstNonWhite(doc, dotPos);
		    if (fnw >= 0) {
			int offset = dotPos - fnw;
			if (offset == 7 && "endspec".equals(doc.getText(fnw, 7))) {
			    ret = new int[] { fnw, dotPos };
			}
		    }
                } catch (BadLocationException e) {
                }
            } else {
                ret = super.getReformatBlock(target, typedText);
            }
        }
        
        return ret;
    }

    protected void initFormatLayers() {
        addFormatLayer(new StripEndWhitespaceLayer());
        addFormatLayer(new MetaSlangLayer());
    }

    public FormatSupport createFormatSupport(FormatWriter fw) {
        return new MetaSlangFormatSupport(fw);
    }

    public class StripEndWhitespaceLayer extends AbstractFormatLayer {

        public StripEndWhitespaceLayer() {
            super("meta-slang-strip-whitespace-at-line-end");
        }

        protected FormatSupport createFormatSupport(FormatWriter fw) {
            return new MetaSlangFormatSupport(fw);
        }

        public void format(FormatWriter fw) {
            MetaSlangFormatSupport fs = (MetaSlangFormatSupport)createFormatSupport(fw);
            FormatTokenPosition pos = fs.getFormatStartPosition();
            if (fs.isIndentOnly()) { // don't do anything

            } else { // remove end-line whitespace
                while (pos.getToken() != null) {
                    FormatTokenPosition startPos = pos;
                    pos = fs.removeLineEndWhitespace(pos);
                    if (pos.getToken() != null) {
                        pos = fs.getNextPosition(pos);
                    }
                    // fix for issue 14725
                    // this is more hack than correct fix. It happens that 
                    // fs.removeLineEndWhitespace() does not move to next
                    // position. The reason is that token from which the 
                    // endline whitespaces must be removed is not 'modifiable' - 
                    // FormatWritter.canModifyToken() returns false in
                    // FormatWritter.remove. I don't dare to fix this problem 
                    // in ExtFormatSupport and so I'm patching this
                    // loop to check whether we are still on the same position
                    // and if we are, let's do break. If similar problem reappear
                    // we will have to find better fix. Hopefully, with the planned
                    // conversion of indentation engines to new lexel module
                    // all this code will be replaced in next verison.
                    if (startPos.equals(pos)) {
                        break;
                    }
                }
            }
        }

    }

    public class MetaSlangLayer extends AbstractFormatLayer {

        public MetaSlangLayer() {
            super("meta-slang-layer");
        }

        protected FormatSupport createFormatSupport(FormatWriter fw) {
            return new MetaSlangFormatSupport(fw);
        }

        public void format(FormatWriter fw) {
            try {
                MetaSlangFormatSupport fs = (MetaSlangFormatSupport)createFormatSupport(fw);

                FormatTokenPosition pos = fs.getFormatStartPosition();

                if (fs.isIndentOnly()) {  // create indentation only
                    fs.indentLine(pos);

                } else { // regular formatting

                    while (pos != null) {

                        // Indent the current line
                        fs.indentLine(pos);

                        // Format the line by additional rules
                        formatLine(fs, pos);

                        // Goto next line
                        FormatTokenPosition pos2 = fs.findLineEnd(pos);
                        if (pos2 == null || pos2.getToken() == null)
                            break; // the last line was processed
                        
                        pos = fs.getNextPosition(pos2, javax.swing.text.Position.Bias.Forward);
                        if (pos == pos2)
                            break; // in case there is no next position
                        if (pos == null || pos.getToken() == null)
                            break; // there is nothing after the end of line
                        
                        FormatTokenPosition fnw = fs.findLineFirstNonWhitespace(pos);
                        if (fnw != null) {
			    pos = fnw;
                        } else { // no non-whitespace char on the line
			    pos = fs.findLineStart(pos);
                        }
                    }
                }
            } catch (IllegalStateException e) {
            }
        }


        protected void formatLine(MetaSlangFormatSupport fs, FormatTokenPosition pos) {
            TokenItem token = fs.findLineStart(pos).getToken();
            while (token != null) {
		/*                if (fs.findLineEnd(fs.getPosition(token, 0)).getToken() == token) {
				  break; // at line end
				  }
		*/

                if (token.getTokenContextPath() == fs.getTokenContextPath()) {
                    switch (token.getTokenID().getNumericID()) {
		    case MetaSlangTokenContext.LBRACE_ID: // '{'
			if (!fs.isIndentOnly()) {
			    FormatTokenPosition lbracePos = fs.getPosition(token, 0);
                                
			    // Check that nothing exists before "{"
			    if (fs.findNonWhitespace(lbracePos, null, true, true) != null)
				break;
			    // Check that nothing exists after "{", but ignore comments
			    if (fs.getNextPosition(lbracePos) != null)
				if (fs.findImportant(fs.getNextPosition(lbracePos), null, true, false) != null)
				    break;
                                
			    // check that on previous line is some stmt
			    FormatTokenPosition ftp = fs.findLineStart(lbracePos); // find start of current line
			    FormatTokenPosition endOfPreviousLine = fs.getPreviousPosition(ftp); // go one position back - means previous line
			    if (endOfPreviousLine == null || endOfPreviousLine.getToken().getTokenID() != MetaSlangTokenContext.WHITESPACE)
				break;
			    ftp = fs.findLineStart(endOfPreviousLine); // find start of the previous line - now we have limit position
			    ftp = fs.findImportant(lbracePos, ftp, false, true); // find something important till the limit
			    if (ftp == null)
				break;
                                
			    // check that previous line does not end with "{" or line comment
			    ftp = fs.findNonWhitespace(endOfPreviousLine, null, true, true);
			    if (ftp.getToken().getTokenID() == MetaSlangTokenContext.LINE_COMMENT ||
				ftp.getToken().getTokenID() == MetaSlangTokenContext.LBRACE)
				break;

			    // now move the "{" to the end of previous line
			    boolean remove = true;
			    while (remove)
                                {
                                    if (token.getPrevious() == endOfPreviousLine.getToken())
                                        remove = false;
                                    if (fs.canRemoveToken(token.getPrevious()))
                                        fs.removeToken(token.getPrevious());
                                    else
                                        break;  // should never get here!
                                }
			    // insert one space before "{"
			    if (fs.canInsertToken(token))
				fs.insertSpaces(token, 1);

			} // !fs.isIndentOnly()
			break;

		    case MetaSlangTokenContext.LPAREN_ID:
			// bugfix 9813: remove space before left parenthesis
			TokenItem prevToken = token.getPrevious();
			if (prevToken != null && prevToken.getTokenID() == MetaSlangTokenContext.WHITESPACE &&
			    prevToken.getImage().length() == 1) {
			    TokenItem prevprevToken = prevToken.getPrevious();
			    if (prevprevToken != null && 
				prevprevToken.getTokenID() == MetaSlangTokenContext.IDENTIFIER)
				{
				    if (fs.canRemoveToken(prevToken)) {
					fs.removeToken(prevToken);
				    }
				}
			}
                                
			break;
                    }
                }

                token = token.getNext();
            }
        }

    }

}
