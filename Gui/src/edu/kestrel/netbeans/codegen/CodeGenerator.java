/*
 * CodeGenerator.java
 *
 * $Id$
 *
 *
 *
 * $Log$
 * Revision 1.1  2003/01/30 02:01:39  gilham
 * Initial version.
 *
 *
 *
 */

package edu.kestrel.netbeans.codegen;

import java.io.*;
import java.util.*;
import javax.swing.text.BadLocationException;
import javax.swing.text.Document;
import javax.swing.text.Position;
import javax.swing.text.StyledDocument;

import org.openide.*;
import org.openide.text.*;
import org.openide.src.SourceException;
import org.openide.src.ElementPrinterInterruptException;

import edu.kestrel.netbeans.model.*;

/** An implementation of ElementPrinter which chaches the tokens
* between marks.
*/
class CodeGenerator {
    /** Bounds for the whole element.
     */
    static final int BOUNDS_ALL = 0;
    
    /** Bounds that will contain the header of a method, declarator of a field,
     * or header of a class.
     */
    static final int BOUNDS_HEADER = 1;
    
    /** Bounds for body of a constructor/method/initializer/class, or init value
     * for a field. Undefined otherwise.
     */
    static final int BOUNDS_BODY = 2;

    /** 
     * Helper function: finds and initializes appropriate indenting writer for the document.
     * and initializes it with the specified context & output stream.
     * @param doc the document
     * @param offset offset where should the text appear.
     * @param writer writer for the identator's output
     * @return indenting writer.
     */
    static Writer findIndentWriter(Document doc, int offset, Writer writer) {
        if (Boolean.getBoolean("edu.kestrel.netbeans.DontUseIndentEngine")) {
            return new FilterWriter(writer) {};
        } else {
            IndentEngine engine = IndentEngine.find(doc); // NOI18N
            return engine.createWriter(doc, offset, writer);
        }
    }

    /**
     * Obtains a document based on pos' CloneableEditorSupport. If the document cannot be
     * loaded, the method wraps the IOException into SourceException.
     * @param poss positions to extract CloneableEditorSupport from
     * @throw SourceException in case that the document cannot be opened.
     */
    static StyledDocument getDocument(ElementBinding b) throws SourceException {
        return getDocument(b.wholeBounds.getBegin());
    }
    
    static StyledDocument getDocument(PositionRef pos) throws SourceException {
        try {
            CloneableEditorSupport supp = pos.getCloneableEditorSupport();
            return supp.openDocument();
        } catch (IOException ex) {
            SourceText.rethrowException(ex);
        }
        return null;
    }
    
    static final void fillTextBounds(PositionBounds range, String text) 
        throws BadLocationException, java.io.IOException {
        range.setText(text);
    }
    
    static final String readTextBounds(PositionBounds range) throws SourceException {
        try {
            return range.getText();
        } catch (Exception ex) {
            SourceText.rethrowException(ex);
        }
        return null;
    }
    
    /** Generates the javadoc for the given element.
    * @param element The element which is used for printing
    * @param impl The implementation where is the printed text inserted
    public static void regenerateJavaDoc(final Element element, final ElementImpl impl) throws SourceException {
        try {
            final PositionRef docBegin;

            if (impl.docBounds != null) {
                docBegin = impl.docBounds.getBegin();
            } else {
                docBegin = null;
            }
            final StyledDocument doc = impl.bounds.getBegin().getEditorSupport().openDocument();
            Util.ExceptionRunnable run = new Util.ExceptionRunnable() {
                public void run() throws Exception {
                    PositionRef begin;
                    PositionBounds bounds;
                    
                    if (docBegin != null) {
                        begin = docBegin;
                        bounds = impl.docBounds;
                    } else {
                        bounds = SourceElementImpl.createNewLineBoundsAt(
                        impl.getJavaDocPosition(),
                        ElementImpl.BOUNDS_JAVADOC
                        );
                        begin = bounds.getBegin();
                    }
                    StringWriter stringWriter = new StringWriter();
                    Writer indentWriter = Util.findIndentWriter(doc, begin.getOffset(), stringWriter);
                    ElementPrinterImpl printer = new ElementPrinterImpl(indentWriter, element, ElementPrinter.JAVADOC_BEGIN, ElementPrinter.JAVADOC_END);
                    try {
                        element.print(printer);
                    }
                    catch (ElementPrinterInterruptException e) {
                    }
		    indentWriter.close();
                    bounds.setText(stringWriter.toString());
                    if (impl.docBounds == null) {
                        impl.docBounds = bounds;
                        
                        final EditorSupport editor = begin.getEditorSupport();
                        // adjust overall bounds, too:
                        impl.bounds = new PositionBounds(
                            editor.createPositionRef(bounds.getBegin().getOffset(),
                                Position.Bias.Backward
                            ),
                            impl.bounds.getEnd()
                        );
                    }
                }
            };
            Util.runAtomic(doc, run);
        }
	catch (SourceException e) {
	    throw e;
	}
        catch (Exception e) {
	    throw (SourceException)TopManager.getDefault().getErrorManager().annotate(
                new SourceException("JavaDoc generation failed"), e // NOI18N
            );
        }
    }
    */
    
    public static String safeIndent(String text, Document doc, int offset) {
        try {
            StringWriter writer = new StringWriter();
            Writer indentator = findIndentWriter(doc, offset, writer);
            indentator.write(text);
            indentator.close();
            return writer.toString();
        } catch (Exception ex) {
            // PENDING: report the exception (somehow).
            /*
	    TopManager.getDefault().getErrorManager().annotate(
		ex, ErrorManager.WARNING, "Indentation engine error",  // NOI18N
                    Util.getString("EXMSG_IndentationEngineError"), ex, null);
            TopManager.getDefault().notifyException(ex);
             */
            return text;
        }
    }

    static PositionBounds addDelimiter (PositionRef where, String delimiter) throws SourceException {
        CloneableEditorSupport support = where.getCloneableEditorSupport();
        StyledDocument doc = getDocument(where);
	int begin = where.getOffset();
	try {
	    doc.insertString(begin, delimiter, null);
	    int end = begin + delimiter.length();
	    return new PositionBounds(support.createPositionRef(end, Position.Bias.Forward),
				      support.createPositionRef(end, Position.Bias.Backward));
        } catch (Exception e) {
            if (Boolean.getBoolean("netbeans.debug.exceptions")) // NOI18N
                e.printStackTrace();
            SourceText.rethrowException(e);
        }
	return null;
    }

    static void removeDelimiter (PositionRef beginPos, PositionRef endPos, String delimiter, boolean forward) throws SourceException {
        CloneableEditorSupport support = beginPos.getCloneableEditorSupport();
        StyledDocument doc = getDocument(beginPos);
	int begin = beginPos.getOffset();
	int end = endPos.getOffset();
	try {
	    String text = doc.getText(begin, end - begin);
	    int pos = (forward) ? text.indexOf(delimiter) : text.lastIndexOf(delimiter);
	    if (pos >= 0) {
		doc.remove(begin + pos, delimiter.length());
	    }
	} catch (Exception e) {
            if (Boolean.getBoolean("netbeans.debug.exceptions")) // NOI18N
                e.printStackTrace();
            SourceText.rethrowException(e);
        }
    }
    
    static PositionBounds createNewLineBounds(PositionRef where, int boundsType)
    throws SourceException {
        boolean empty = boundsType == BOUNDS_ALL;
        return createNewLineBounds(where, boundsType, empty, empty);
    }
    
    static PositionBounds createNewLineBounds(PositionRef where, int boundsType,
        boolean emptyBefore, boolean emptyAfter) 
        throws SourceException {
	return createNewLineBounds(where, boundsType, emptyBefore, emptyAfter, true);
    }

    static PositionBounds createNewLineBounds(PositionRef where, int boundsType,
        boolean emptyBefore, boolean emptyAfter, boolean newLineAfter) 
        throws SourceException {
        CloneableEditorSupport support = where.getCloneableEditorSupport();
        StyledDocument doc = getDocument(where);

        try {
            int beginText = where.getOffset();
            int lineIndex = NbDocument.findLineNumber(doc, beginText);
            javax.swing.text.Element rootElement = NbDocument.findLineRootElement(doc);
            javax.swing.text.Element line = rootElement.getElement(lineIndex);
            int lineBegin = line.getStartOffset();
            int lineEnd = line.getEndOffset();
            int myLineIndex = lineIndex;

            // if we are on an completely empty line, skip to the next one.
            // Also, if we are at the end of the line (or only whitespaces follow) and the next one
            // is empty, skip it to maintain text readability.
            String trimmedText;
            int textOffset;
            int insertionOffset;
            String lineText = doc.getText(lineBegin, lineEnd - lineBegin);

            trimmedText = lineText.trim();
            textOffset = lineText.lastIndexOf(trimmedText);
            insertionOffset = beginText - lineBegin;
            String formatted;
            PositionBounds bnds;
            int newBlockOffset;
            
            if (trimmedText.length() == 0 || textOffset >= insertionOffset) {
                // check: if the previous line is not empty,
                if (emptyBefore && lineBegin > 0) {
                    javax.swing.text.Element prevLine = rootElement.getElement(myLineIndex - 1);
                    String prevContents =
                        doc.getText(prevLine.getStartOffset(),
                            prevLine.getEndOffset() - prevLine.getStartOffset()
                        ).trim();
                    if (!"".equals(prevContents)) {
                        // insert a newline before the text:
                        // this line's begin is after the prev line's end
                        doc.insertString(lineBegin, "\n", null); // NOI18N
                        line = rootElement.getElement(++myLineIndex);
                        lineBegin = line.getStartOffset();
                    }
                }
                // Nonwhitespace after the insertion point, all whitespace before
                // insert separating newline at the beginning of this line:
                doc.insertString(lineBegin, formatText(doc, lineBegin, "\n"), null); // NOI18N
                formatted = formatText(doc, lineBegin, "\n"); // NOI18N
                formatted = formatted.substring(formatted.indexOf('\n') + 1);
                doc.insertString(lineBegin, formatted, null);
                newBlockOffset = lineBegin + formatted.length();
            } else if (textOffset + trimmedText.length() <= insertionOffset) {
                // Nonwhitespace before the insertion point, only whitespace after
                // retain only indentation
                boolean includingNewline = emptyBefore;
                if (doc.getLength() >= lineEnd) {
                    if (emptyBefore) {
                        javax.swing.text.Element nextLine = rootElement.getElement(myLineIndex + 1);
                        String nextContents = doc.getText(nextLine.getStartOffset(),
                            nextLine.getEndOffset() - nextLine.getStartOffset()).trim();
                        if ("".equals(nextContents)) {
                            // adjust positions after the next (empty) line:
                            lineEnd = nextLine.getEndOffset();
                            lineBegin = nextLine.getStartOffset();
                            includingNewline = false;
                        }
                        myLineIndex++;
                    }
                }
		if (doc.getLength() < lineEnd) {
		    // special case
                    if (emptyBefore && includingNewline) {
                        formatted = formatText(doc, lineEnd-1, "\n\n"); // NOI18N
                        myLineIndex += 2;
                    } else {
                        formatted = formatText(doc, lineEnd-1, "\n"); // NOI18N
                        myLineIndex++;
                    }
		    doc.insertString(lineEnd-1, formatted, null);
		    newBlockOffset = lineEnd-1 + formatted.length();
		    myLineIndex += emptyBefore ? 2 : 1;
		} else {
        	    formatted = formatText(doc, lineEnd, "\n"); // NOI18N
            	    if (!includingNewline)
                	formatted = formatted.substring(formatted.indexOf('\n') + 1);
                    doc.insertString(lineEnd, formatted, null);
	            newBlockOffset = lineEnd + formatted.length();
    		    myLineIndex++;
            	    doc.insertString(newBlockOffset, formatText(
                	doc, newBlockOffset, "\n"), null); // NOI18N
		}
            } else {
                // Whitespace before and after.
                if (emptyBefore) {
                    formatted = formatText(doc, beginText, "\n\n");  // NOI18N
                    myLineIndex++;
                } else {
                    formatted = formatText(doc, beginText, "\n");  // NOI18N
                }
                    
                doc.insertString(beginText, formatted, null);
                // remember THIS offset; the text will be inserted there.
                newBlockOffset = beginText + formatted.length();
                myLineIndex++;
                if (newLineAfter) {
		    doc.insertString(newBlockOffset, formatText(doc, newBlockOffset, "\n"), null); // NOI18N
		}
            }
            
            // IF creating a whole new element AND the following line (at newBlockOffset + 1)
            // is not empty, add a additional newline
            if (emptyAfter) {
                if (doc.getLength() > newBlockOffset + 1) {
                    line = rootElement.getElement(myLineIndex + 1);
                    lineBegin = line.getStartOffset();
                    lineEnd = line.getEndOffset();
                    lineText = doc.getText(lineBegin, lineEnd - lineBegin);
                    trimmedText = lineText.trim();
                    if (!"".equals(trimmedText)) {
                        // add a additional newline
                        doc.insertString(newBlockOffset, "\n", null); // NOI18N
                    }
                } else {
                    // try to maintain a newline at the end of the file
                    // which is recommended anyway.
                    doc.insertString(newBlockOffset, "\n", null); // NOI18N
                }
            }
            Position.Bias startBias, endBias;
            switch (boundsType) {
                case BOUNDS_BODY:
                    startBias = Position.Bias.Forward;
                    endBias = Position.Bias.Backward;
                    break;
                default:
                    startBias = Position.Bias.Backward;
                    endBias = Position.Bias.Forward;
                    break;
            }
            PositionRef posBegin = support.createPositionRef(newBlockOffset, startBias);
            PositionRef posEnd = support.createPositionRef(newBlockOffset, endBias);
            PositionBounds blockBounds = new PositionBounds(posBegin, posEnd);
            return blockBounds;
        } catch (Exception e) {
            if (Boolean.getBoolean("netbeans.debug.exceptions")) // NOI18N
                e.printStackTrace();
            SourceText.rethrowException(e);
        }
        return null;
    }

    
    /**
     * "Normalizes" the body. Until some additional options are created for code generation,
     * the implementation will force newline after the opening curly brace and before the
     * closing curly brace. If there are some newlines, they are retained. Note that the
     * function appends '{' at the beginning and '}' at the end of string for formatting efficiency, if the parameter is
     * true.
     */
    /*
    static String normalizeBody(String s, boolean braces) {
	int begin, end;
	int l = s.length();
        char c = 0, c2 = 0;
	
	begin = 0;
	while (begin < l) {
	    c = s.charAt(begin);
	    if (c == '\n' || c > ' ')
		break;
	    begin++;
	}
	
	end = l - 1;
	while (end >= begin) {
	    c2 = s.charAt(end);
	    if (c2 == '\n' || c2 > ' ')
		break;
	    end--;
	}
	if (begin > end || (begin == end && c == '\n')) {
	    // empty body --> normalize to a newline after the opening curly brace
	    if (braces) {
                return "{\n}"; // NOI18N
	    } else {
		return "\n"; // NOI18N
	    }
	} else if (c == '\n' && c2 == '\n' && !braces) {
	    return s;
        } else {
	    StringBuffer sb = new StringBuffer();
            if (braces)
                sb.append("{"); // NOI18N
	    if (c != '\n') {
		sb.append('\n');
	    }
	    sb.append(s.substring(begin, end + 1));
	    if (c2 != '\n') {
		sb.append('\n');
	    }
	    if (braces) {
    	        sb.append('}');
	    }
	    return sb.toString();
	}
    }
    */
    
    /**
     * Removes the lines of the passed bounds, possibly collapsing empty previous and/or 
     * following line. The method assumes that the caller has locked out the document
     * (that implies that the document was already loaded by the caller)
     */
    static void clearBounds(PositionBounds bounds, boolean collapseLines) throws BadLocationException {
        StyledDocument doc = bounds.getBegin().getCloneableEditorSupport().getDocument();

        int p1 = bounds.getBegin().getOffset();
        int p2 = bounds.getEnd().getOffset();
        int p3 = 0;
        doc.remove(p1, p2 - p1);

        // remove empty space where was the element placed
        int lineIndex = NbDocument.findLineNumber(doc, p1);
        javax.swing.text.Element lineRoot;
        lineRoot = NbDocument.findLineRootElement(doc);
        int lineCount = lineRoot.getElementCount();
        javax.swing.text.Element line = lineRoot.getElement(lineIndex);
        p1 = line.getStartOffset();
        p2 = line.getEndOffset();
        try {
           if (doc.getText(p1, p2 - p1).trim().length() != 0)
               return;
           doc.remove(p1, p2 - p1);
        } catch (BadLocationException e) {
           return;
        }
        // p1-p2 clears the element together with the
        if (collapseLines) {
           line = lineRoot.getElement(lineIndex);
           try {
               if ("".equals(
               doc.getText(p1 = line.getStartOffset(),
               (p2 = line.getEndOffset()) - line.getStartOffset()).trim())) {
                   doc.remove(p1, p2 - p1);
               } else if (lineIndex > 0) {
                   // try the prev line:
                   line = lineRoot.getElement(lineIndex - 1);
                   if ("".equals(
                   doc.getText(p1 = line.getStartOffset(),
                   (p2 = line.getEndOffset()) - line.getStartOffset()).trim())) {
                       doc.remove(p1, p2 - p1);
                   }
               }
           } catch (BadLocationException e) {
           }
        }
    }
    

    static String formatText(StyledDocument doc, PositionRef pos, String text) {
        return formatText(doc, pos.getOffset(), text);
    }
    
    static String formatText(StyledDocument doc, int pos, String text) {        
	try {
             StringWriter stringWriter = new StringWriter();
             Writer indentWriter = findIndentWriter(doc, pos, stringWriter);
             indentWriter.write(text);
             indentWriter.close();
             
             String context = null;
	     /*
             if (pos > 10) {
                 context = doc.getText(pos - 10, 10);
             }
             System.out.println("[formatText] input = `" + text + "' pos = " + pos.getOffset() +  // NOI18N
                " context = `" + context + "' result = `" + stringWriter.toString() + "'"); // NOI18N
		*/
             return stringWriter.toString();
         } catch (Exception ex) {
             if (Boolean.getBoolean("netbeans.debug.exceptions")) { // NOI18N
                 System.err.println("Error in Indentation engine: "); // NOI18N
                 ex.printStackTrace(System.err);
             }
             return text;
         }
    }
}
