/*
 * ParseSourceRequest.java
 *
 * $Id$
 *
 *
 *
 * $Log$
 * Revision 1.3  2003/03/13 01:23:59  gilham
 * Handle Latex comments.
 * Report Lexer errors.
 * Always display parser messages (not displayed before if the parsing succeeded
 * and the parser output window is not open).
 *
 * Revision 1.2  2003/02/19 18:56:37  weilyn
 * Added temporary static method to allow Specware error messages to be displayed in the parser output window.
 *
 * Revision 1.1  2003/01/30 02:02:23  gilham
 * Initial version.
 *
 *
 *
 */
package edu.kestrel.netbeans.parser;

import java.io.IOException;
import java.io.InputStream;
import java.io.Reader;
import java.util.*;
import javax.swing.SwingUtilities;
import javax.swing.event.ChangeListener;
import javax.swing.event.ChangeEvent;

import org.openide.filesystems.FileObject;
import org.openide.filesystems.FileSystemCapability;
import org.openide.text.CloneableEditorSupport;
import org.openide.text.DataEditorSupport;

import edu.kestrel.netbeans.Util;
import edu.kestrel.netbeans.editor.MetaSlangEditorSupport;
import edu.kestrel.netbeans.settings.MetaSlangSettings;

public class ParseSourceRequest implements ParsableObjectRequest {
    public static final int     STATE_WAITING = 0;
    public static final int     STATE_READING = 1;
    public static final int     STATE_CANCELLED = 2;
    public static final int     STATE_ANALYSIS = 3;
    public static final int     STATE_UPDATING = 4;
    public static final int     STATE_COMPLETED = 10;
    
    private static final int READ_THRESHOLD = 2048;
    private static final boolean DEBUG = false;
    
    private static ParserDisplayer parserDisplayer = new ParserDisplayer();

    MetaSlangParser.Env     environment;
    ChangeListener          listener;
    int                     state;
    boolean                 valid;
    int                     syntaxErrors;
    ElementFactory          builder;
    CloneableEditorSupport  editSupp;
    public  int             annotatedErrors=0;
    private Map             annotations=null;
    private String          sourceName=null;
    private Collection      sources;
    
    public ParseSourceRequest() {
        MetaSlangSettings settings=MetaSlangSettings.getDefault();
	annotatedErrors = settings.getParsingErrors();
        
        state = STATE_WAITING;
        valid = true;
        sources = new LinkedList();
        for (Enumeration en = FileSystemCapability.COMPILE.fileSystems(); en.hasMoreElements(); ) {
            sources.add(en.nextElement());
        }
    }

    public ParseSourceRequest(int errors, String name) {
        this();
        annotatedErrors = errors;
        sourceName = name;
    }
    
    ParseSourceRequest(MetaSlangParser.Env env, CloneableEditorSupport editSupp) {
        this();
        this.editSupp = editSupp;
        this.environment = env;
    }
    
    public synchronized void addChangeListener(ChangeListener l) throws TooManyListenersException {
        if (listener != null)
            throw new TooManyListenersException();
        listener = l;
    }
    
    public synchronized void removeChangeListener(ChangeListener l) {
        if (listener == l)
            listener = null;
    }
    
    public void setEnvironment(MetaSlangParser.Env env) {
        environment = env;
    }
    
    public void setEditorSupport(CloneableEditorSupport editor) {
        editSupp = editor;
    }

    /**
     * Notifies the request that the source text has been changed. This causes
     * cancellation of the request in some cases.
     */
    public void sourceChanged() {
        if (state == STATE_READING) {
            // cancel the request only in reading state; if the text is already
            // read, the request can still be cariied out.
            valid = false;
        }
    }
    
    public void modelChanged() {
        if (state != STATE_WAITING && state != STATE_COMPLETED) {
            valid = false;
        }
    }
        
    public void setSyntaxErrors(int errors) {
	if (DEBUG) {
	    Util.log("*** ParseSourceRequest.setSyntaxErrors(): errors="+errors);
	}
        this.syntaxErrors = errors;
    }
    
    public int getSyntaxErrors() {
        return syntaxErrors;
    }
    
    public void setSemanticErrors(int errors) {
        // ignore - for now.
    }
    
    /**
     * DocumentModelBuilder actually carries out tasks associated with the Factory.
     */
    public ElementFactory getFactory() {
        if (builder == null)
            builder = createBuilder(editSupp);
        return builder;
    }
    
    public DocumentModelUpdater getUpdater() {
        DocumentModelUpdater result = null;
        ElementFactory builder = getFactory();
        if (builder instanceof DocumentModelUpdater) result = (DocumentModelUpdater)builder;
        return result;
    }

    protected ElementFactory createBuilder(CloneableEditorSupport supp) {
        return new DocumentModelBuilder(supp);
    }

    public void notifyReschedule() {
        // clear old data.
        builder = null;
        enterState(STATE_WAITING);
    }
    
    protected void enterState(int state) {
        this.state = state;
        if (listener != null)
            listener.stateChanged(new ChangeEvent(this));
    }
    
    /**
     * The method is implemented so that it reads the whole contents from the environment's
     * Reader and returns the resulting char array.
     */
    public char[] getSource() throws IOException {
        // unsynchronized; the exact sequence really does not matter here too much;
        // the real problem arises that AFTER the contents is read.
        valid = true;
        enterState(STATE_READING);
        
        Reader r = environment.getSourceText();
        
        List buffers = new LinkedList();
        char[] buf;
        int read;
        int offset;
        int total = 0;

        do {
            offset = 0;
            buf = new char[READ_THRESHOLD];
            do {
                read = r.read(buf);
                if (read == -1)
                    break;
                offset += read;
            } while (offset < buf.length);
            if (offset > 0)
                buffers.add(buf);
            total += offset;
        } while (read > 0);
        
        r.close();
        
        buf = new char[total];
        read = 0;
        for (Iterator it = buffers.iterator(); it.hasNext(); ) {
            char[] b = (char[])it.next();
            int size = it.hasNext() ? b.length : total - read;
            System.arraycopy(b, 0, buf, read, size);
            read += size;
        }
        ElementFactory builder = getFactory();
        if (builder instanceof DocumentModelBuilder) {
            ((DocumentModelBuilder)builder).setContent(buf, editSupp.isDocumentLoaded());
        }
        return buf;
    }

    /** 
     * Called to obtain reader for the data to be parsed. 
     * @throws IOException if the reader can't be returned.
    */
    public Reader getSourceReader() throws IOException {
	return environment.getSourceText();
    }

    public FileObject getSourceFile() {
	return environment.getSourceFile();
    }

    /**
     * Returns true, IF the request was not invalidated by the ParserSupport,
     * or because of change in the document while parsing.
     */
    public boolean isValid() {
        return this.valid;
    }
    
    public boolean needsProcessing() {
        // always needs to process (?)
        return this.valid;
    }
    
    public void notifyStart() {
	invokeLater(new Runnable() {
		public void run() {
		    parserDisplayer.parsingStarted(getSourceFile());
		}
	    });
    }
    
    public void notifyComplete() {
        // safepoint: everything was processed.
        enterState(STATE_COMPLETED);
        if (annotations==null)
            annotations=new HashMap();
	invokeLater(new Runnable() {
		public void run() {
		    parserDisplayer.parsingFinished(getSourceFile(), (syntaxErrors == 0), false);
		}
	    });
    }

    public Object getParserType() {
        if (annotatedErrors!=0)
            return MetaSlangParser.DEEP_PARSER;
        return MetaSlangParser.SHALLOW_PARSER;
    }
    
    public void pushError(int line, int column, String message) {
	pushError(null, line, column, message);
    }

    public void pushError(FileObject errorFile, final int line, final int column, final String message) {
        setSyntaxErrors(getSyntaxErrors() + 1);
	if (annotatedErrors!=0) {
	    if (DEBUG) {
		Util.log("*** ParseSourceRequest.pushError: file="+errorFile+" line="+line+" column="+column+" message="+message);
	    }
	    Integer lineInt;
	    ParserAnnotation oldAnn,newAnn;
        
	    if (errorFile!=null && !errorFile.getNameExt().equals(sourceName)) 
		return;             // error in different file
	    if (line<=0) 
		return;             // no line number available    
	    if (annotations==null)
		annotations=new HashMap();
	    lineInt=new Integer(line);
	    newAnn=new ParserAnnotation(line,column,message);
	    oldAnn=(ParserAnnotation)annotations.get(lineInt);
	    if (oldAnn!=null)
		oldAnn.chain(newAnn);
	    else if (annotations.size()<annotatedErrors)
		annotations.put(lineInt,newAnn);

	    invokeLater(new Runnable() {
		    public void run() {
			parserDisplayer.reportError(getSourceFile(), line, column, message);
		    }
		});
	}
    }
    
    // This method displays Specware's error messages in the parser output window.
    // TODO: Create a separate class to do this because the Netbeans parser shouldn't be displaying Specware errors.
    public static void pushProcessUnitError(final FileObject errorFile, final int line, final int column, final String message) {

        if (line<=0) 
            return;             // no line number available    

	invokeLater(new Runnable() {
		public void run() {
		    parserDisplayer.reportError(errorFile, line, column, message);
		}
	    });
    }   
   
    /** Getter for property annotations.
     * @return Value of property annotations.
     */
    public Collection getAnnotations() {
        if (annotations!=null)
            return annotations.values();
        return null;
    }
    
    public String getSourceName() {
        return sourceName;
    }

    public Collection getSourcePath() {
        return sources;
    }
        
    private static void invokeLater(Runnable runnable) {
	if (SwingUtilities.isEventDispatchThread()) {
	    runnable.run();
	} else {
            SwingUtilities.invokeLater(runnable);
	}
    }

}
