/*
 * ParserDisplayer.java
 *
 * $Id$
 *
 *
 *
 * $Log$
 *
 *
 */

package edu.kestrel.netbeans.parser;

import java.io.IOException;
import java.text.MessageFormat;
import java.util.ResourceBundle;
import java.util.Map;
import java.util.HashMap;
import java.awt.event.ActionListener;
import java.awt.event.ActionEvent;
import java.beans.PropertyChangeListener;
import java.beans.PropertyChangeEvent;
import javax.swing.Timer;
import javax.swing.SwingUtilities;

import org.openide.loaders.DataObject;
import org.openide.text.Line;
import org.openide.text.Annotation;
import org.openide.text.Annotatable;
import org.openide.ErrorManager;
import org.openide.TopManager;
import org.openide.cookies.LineCookie;
import org.openide.filesystems.FileObject;
import org.openide.windows.TopComponent;
import org.openide.windows.InputOutput;
import org.openide.windows.OutputEvent;
import org.openide.windows.OutputListener;
import org.openide.windows.OutputWriter;
import org.openide.util.NbBundle;
import org.openide.util.Mutex;

import edu.kestrel.netbeans.Util;

/** This class is responsible for displaying the messages
* as a reactions to the state changes and errors produced by
* the parser.
*
*/
public final class ParserDisplayer extends Object implements ActionListener {
    /** output tab */
    private InputOutput parserIO;
    /** writer to that tab */
    private OutputWriter ow = null;
    /** format for errors */
    private MessageFormat errorMsg;
    /** format for error description */
    private MessageFormat errorDescr;
    /** message for parsing */
    private MessageFormat parsingMsg;
    /** parsing successful */
    private MessageFormat parseSuccess;
    /** parsing unsuccessful */
    private MessageFormat parseUnsuccess;
    /** parsing started */
    private MessageFormat parseStarted;
    
    /** Swing Timer which posts setStatusText only every 100 ms */
    private Timer statusTextTimer;
    /** Text to set */
    private String statusText;
    /** List of ErrorEvents */
    private ErrorCtl lastError;

    /** flag to test whether the tab is visible or not */
    private boolean visible = false;

    private boolean DEBUG = false;
    
    public ParserDisplayer() {
        // bundle
        final ResourceBundle bundle = NbBundle.getBundle(ParserDisplayer.class);
        errorMsg = new MessageFormat(bundle.getString("MSG_ParseError"));
        errorDescr = new MessageFormat(bundle.getString("MSG_ParseErrorDescr"));
        parsingMsg = new MessageFormat(bundle.getString("MSG_Parsing"));
        parseSuccess = new MessageFormat(bundle.getString("MSG_ParsingSuccessful"));
        parseUnsuccess = new MessageFormat(bundle.getString("MSG_ParsingUnsuccessful"));
        parseStarted = new MessageFormat(bundle.getString("MSG_ParsingStarted"));
	initialize();
    }

    /** Displayes error line in output window as a reaction to the
    * notification that an error occured in the parser.
    */
    public void reportError(FileObject file, int line, int column, String message) {
	if (DEBUG) Util.log("*** ParserDisplayer.reportError(): file="+file+", line="+line+", column="+column+", message="+message);
	ensureVisible();
	Object[] args = new Object[] {
	    file.getNameExt(),
	    new Integer(line),
	    new Integer(column),
	    message
	};
	String text = errorMsg.format(args);
	int line2 = line - 1;
	int column2 = Math.max(column - 1, 0);
	try {
	    ErrorCtl ec = new ErrorCtl(file, line2, column2, message);
	    println(text, ec);
	} catch(IOException ex) {
	    println(text);
	}

	String refText = getReferenceText(file, line2, column2);
	if (refText != null && ! refText.equals("")) { // NOI18N
	    if (refText.startsWith("\n")) // NOI18N
		refText = refText.substring(1);
	    println (errorDescr.format (new Object[] { refText }));
	}
	// ow.println(""); // NOI18N
    }

    String getReferenceText(FileObject file, int line, int column) {
	try {
	    DataObject data = DataObject.find(file);
	    LineCookie cookie =(LineCookie)data.getCookie(LineCookie.class);
	    if (cookie == null) {
		return null;
	    }
	    StringBuffer buffer = new StringBuffer(cookie.getLineSet().getOriginal(line).getText());
	    for (int i = 0; i < column; i++) {
		buffer.append(" ");
	    }
	    buffer.append("^");
	    return buffer.toString();
	} catch (Exception e) {
	    return null;
	}
    }
    
    /** Displayes information that parsing has just started. */
    void parsingStarted(FileObject file) {
        //initialize();
	if (DEBUG) Util.log("*** ParserDisplayer.parsingStarted(): file="+file);
        setStatusText(parseStarted.format(fileToArgs(file)));
        try {
            ow.reset();
            visible = false;
        } catch(java.io.IOException ex) {
            ErrorManager.getDefault().notify(ex);
        }
        lastError = null;
    }
    
    private void ensureVisible() {
	if (parserIO.isClosed()) {
	    visible = false;
	    ((TopComponent)parserIO).open();
	}
        if (!visible) {
            visible = true;
	    Mutex.EVENT.readAccess(new Runnable() {
		    public void run() {
			    ((TopComponent)parserIO).requestVisible();
		    }
		});
        }
    }

    /** Displayes information that parsing has finished,
    * and whether succesfully or not. */
    public void parsingFinished(FileObject file, boolean successful, boolean uptodate) {
	if (DEBUG) Util.log("*** ParserDisplayer.parsingFinished(): file="+file+", successful="+successful+", uptodate="+uptodate);
        boolean always_print = true;
        if ( successful && parserIO.isClosed() )
            always_print = false;

	//initialize();
	MessageFormat msg = successful ? parseSuccess : parseUnsuccess;
	Object[] args = fileToArgs(file);
	String fimsg = msg.format(args);
	setStatusText(fimsg);
	if (always_print) {
	    ensureVisible();
	    if (uptodate) {
		println(NbBundle.getBundle(ParserDisplayer.class).getString("MSG_UpToDate"));
	    }
	    println(fimsg);
	}
	AnnotationImpl impl = AnnotationImpl.getAnnotation();
	impl.detach(null);
	/*
	// OW needs to know, when parsing finished
	if ( parserIO instanceof OutputTabTerm ) {
	((OutputTabTerm)parserIO).setCompilationFinished();
	}
	*/
    }

    private static Object[] fileToArgs(FileObject file) {
	String fileName = (file == null) ? null : file.getNameExt();
	return new Object[]{fileName,
				(fileName == null) ? new Integer(0) : new Integer(1)};
    }

    private void initialize() {
	if (DEBUG) Util.log("*** ParserDisplayer.initialize()");
        if (ow == null) {
	    if (DEBUG) Util.trace("*** ParserDisplayer.initialize(): ow = null");
            synchronized(this) {
                // prepare output tab
		if (DEBUG) Util.log("*** ParserDisplayer.initialize(): inside synchronized");
                setOw(NbBundle.getBundle(ParserDisplayer.class).getString("CTL_ParseTab"));
	    }
        }
    }

    private void setOw(String name) {
        if (ow != null) return;
	if (DEBUG) Util.log("*** ParserDisplayer.setOw() name="+name);
	parserIO = TopManager.getDefault().getIO(name, false);
	if (DEBUG) Util.log("*** ParserDisplayer.setOw(): parserIO="+parserIO.getClass());
        parserIO.setFocusTaken(false);
	if (DEBUG) Util.log("*** ParserDisplayer.setOw(): setFocusTaken()");
        ow = parserIO.getOut();
    }
    
    private long lastTime = 0;

    /** Sets text to status line
    */
    public void setStatusText (String text) {
        statusText = text;
        long currentTime = System.currentTimeMillis();
        if ((currentTime - lastTime) > 250) {
            lastTime = lastTime;
            actionPerformed(null);
        } else {
            getStatusTextTimer().restart();
        }
    }

    private Timer getStatusTextTimer() {
        if (statusTextTimer == null) {
            statusTextTimer = new Timer(250, this);
            statusTextTimer.setRepeats(false);
        }
        return statusTextTimer;
    }
    
    public void actionPerformed(java.awt.event.ActionEvent p1) {
        if (statusText == null) {
            return;
        }
        
        TopManager.getDefault().setStatusText(oneLine(statusText));
        statusText = null;
        lastTime = System.currentTimeMillis();
    }
    
    /** Removes newlines from the string */
    private static String oneLine(final String txt) {
        StringBuffer sb = new StringBuffer(txt.length());
        boolean lastIsNewline = false;
        for (int i = 0; i < txt.length(); i++) {
            char ch = txt.charAt(i);
            if (ch == '\n' || ch == '\r') {
                if (! lastIsNewline) {
                    lastIsNewline = true;
                    sb.append(' ');
                }
            } else {
                sb.append(ch);
                lastIsNewline = false;
            }
        }
        return sb.toString();
    }

    /*
    private static boolean alwaysOpenAfterParse() {
        OutputSettings settings =(OutputSettings)OutputSettings.findObject(OutputSettings.class, true);
        if ( settings != null )
            return settings.isAlwaysOpenAfterParse();
        return true;
    }
    */

    /** Prints the text */
    final void println(String msg) {
	ow.println(msg);
	/*
        if (lastError != null) {
            ErrorCtl ctl = new ErrorCtl(lastError);
            lastError = null;
            try {
                println(msg, ctl);
            } catch(IOException e) {
                println(msg);
            }
        } else {
            ow.println(msg);
        }
	*/
    }

    /** Prints the text */
    final void println(final String msg, OutputListener err) throws IOException {
        if (err instanceof ErrorCtl) {
            lastError =(ErrorCtl) err;
        }
        ow.println(msg, err);
    }
        
    final class ErrorCtl implements OutputListener {
        /** file we check */
        FileObject file;

        /** line we check */
        Line xline;

        /** column with the err */
        int column;

        /** text to display */
        private String message;

        /**
        * @param file is a FileObject with an error
        * @param line is a line with the error
        * @param column is a column with the error
        * @param message text to display to status line
        * @exception FileNotFoundException
        */
        public ErrorCtl(FileObject file, int line, int column, String message)
        throws java.io.IOException {
            this.file = file;
            this.column = column;
            DataObject data = DataObject.find(file);
            LineCookie cookie =(LineCookie)data.getCookie(LineCookie.class);
            if (cookie == null) {
                throw new java.io.FileNotFoundException();
            }
            xline = cookie.getLineSet().getOriginal(line);
            this.message = message;
        }

        public void outputLineSelected(OutputEvent ev) {
            AnnotationImpl impl = AnnotationImpl.getAnnotation();
            impl.setShortDescription(message);
            setStatusText(message);
            impl.attach(this, xline);
	    if (DEBUG) Util.log("*** ParserDisplayer$ErrorCtl.outputLineSelected(): xline="+xline);
            xline.show(Line.SHOW_TRY_SHOW, column);
        }

        public void outputLineAction(OutputEvent ev) {
            AnnotationImpl impl = AnnotationImpl.getAnnotation();
            impl.setShortDescription(message);
            setStatusText(message);
            impl.attach(this, xline);
	    if (DEBUG) Util.log("*** ParserDisplayer$ErrorCtl.outputLineSelected(): xline="+xline);
            xline.show(Line.SHOW_GOTO, column);
        }

        public void outputLineCleared(OutputEvent ev) {
            AnnotationImpl impl = AnnotationImpl.getAnnotation();
            impl.detach(this);
        }
        
    } // end of ErrorCtl inner class

    /** Implements Annotation */
    static final class AnnotationImpl extends Annotation implements PropertyChangeListener {
        private static AnnotationImpl INSTANCE;
        
        private String text;
        private ErrorCtl currentCtl;
        
        public static AnnotationImpl getAnnotation() {
            if (INSTANCE == null) {
                INSTANCE = new AnnotationImpl();
            }
            
            return INSTANCE;
        }
        
        /** Returns name of the file which describes the annotation type.
         * The file must be defined in module installation layer in the
         * directory "Editors/AnnotationTypes"
         * @return  name of the anotation type */
        public String getAnnotationType() {
            return "edu-kestrel-netbeans-parser-error"; // NOI18N
        }
        
        /** Returns the tooltip text for this annotation.
         * @return  tooltip for this annotation */
        public String getShortDescription() {
            return text;
        }
        
        /** Sets the tooltip text */
        public void setShortDescription(String text) {
            this.text = text;
        }
        
        public void attach(ErrorCtl ctl, Line line) {
            if (currentCtl != null) {
                detach(currentCtl);
            }
            currentCtl = ctl;
            attach(line);
            line.addPropertyChangeListener(this);
        }
        
        public void detach(ErrorCtl ectl) {
            if (ectl == currentCtl || ectl == null) {
                currentCtl = null;
                Annotatable at = getAttachedAnnotatable();
                if (at != null) {
                    at.removePropertyChangeListener(this);
                }
                detach();
            }
        }
        
        public void propertyChange(PropertyChangeEvent ev) {
            if (Annotatable.PROP_TEXT.equals(ev.getPropertyName())) {
                detach(null);
            }
        }
    } // end of AnnotationImpl inner class
}
