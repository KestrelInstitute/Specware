/*
 * MetaSlangEditorSupport.java
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

import java.beans.PropertyChangeEvent;
import java.io.*;
import java.util.*;
import java.awt.event.ActionListener;
import java.awt.event.ActionEvent;
import javax.swing.SwingUtilities;
import javax.swing.JEditorPane;
import javax.swing.Timer;
import javax.swing.text.*;
import javax.swing.event.*;

import org.openide.TopManager;
import org.openide.ErrorManager;
import org.openide.cookies.*;
import org.openide.filesystems.FileLock;
import org.openide.filesystems.FileObject;
import org.openide.loaders.DataObject;
import org.openide.nodes.Node;
import org.openide.text.*;
import org.openide.windows.CloneableOpenSupport;
import org.openide.windows.CloneableTopComponent;
import org.openide.util.Task;
import org.openide.util.TaskListener;
import org.openide.util.actions.SystemAction;

import org.netbeans.editor.BaseKit;
import org.netbeans.editor.LocaleSupport;
import org.netbeans.modules.editor.NbLocalizer;
import org.netbeans.modules.editor.NbEditorDocument;

import edu.kestrel.netbeans.MetaSlangDataObject;
import edu.kestrel.netbeans.MetaSlangOpenSupport;
import edu.kestrel.netbeans.cookies.SourceCookie;
import edu.kestrel.netbeans.model.*;
import edu.kestrel.netbeans.nodes.ElementNodeFactory;
import edu.kestrel.netbeans.parser.*;
import edu.kestrel.netbeans.settings.MetaSlangSettings;

/** Support for editing a data object as text.
 *
 */
// Replace OpenCookie with EditCookie or maybe ViewCookie as desired:
public class MetaSlangEditorSupport extends DataEditorSupport implements EditorCookie, EditCookie, PrintCookie {

    private static boolean inited = false;

    /** The hook to the parsed hierarchy - it shouldn't be released
     * when document is loaded.
     */
    Object parsedHook;
    
    /** Timer which countdowns the auto-reparsing time. */
    Timer timer;

    /* List of annotations attached to this document */
    private ArrayList annotations=new ArrayList();

    /** Create a new editor support.
     * @param obj the data object whose primary file will be edited as text
     */
    public MetaSlangEditorSupport(MetaSlangDataObject obj) {
        super(obj, new MetaSlangEnv(obj));
        // Set a MIME type as needed, e.g.:
        setMIMEType(MetaSlangEditorKit.META_SLANG_MIME_TYPE);

	if (!inited) {
	    // HACK!!! This should be automatically done by EditorModule.
	    LocaleSupport.addLocalizer(new NbLocalizer(BaseKit.class));

	    JEditorPane.registerEditorKitForContentType(MetaSlangEditorKit.META_SLANG_MIME_TYPE,
							"edu.kestrel.netbeans.editor.MetaSlangEditorKit",
							MetaSlangEditorKit.class.getClassLoader()
							//TopManager.getDefault().currentClassLoader()
							);
	    inited = true;
	}
    }
    
    protected boolean canClose() {
	MetaSlangOpenSupport mos = (MetaSlangOpenSupport)getDataObject().getCookie(MetaSlangOpenSupport.class);
	if (mos != null && mos.isOpen() && !getDataObject().isModified()) {
	    mos.close();
	    return true;
	} else {
	    return superCanClose();
	}
    }
    // For access from MetaSlangOpenSupport:
    public boolean superCanClose() {
        return super.canClose();
    }
    
    /** Called when the document is modified.
     * Here, adding a save cookie to the object and marking it modified.
     * @return true if the modification is acceptable
     */
    protected boolean notifyModified() {
        if (! super.notifyModified()) {
            return false;
        }
        MetaSlangDataObject obj = (MetaSlangDataObject) getDataObject();
        if (obj.getCookie(SaveCookie.class) == null) {
            obj.setModified(true);
            // You must implement this method on the object:
            obj.addSaveCookie(new Save());
        }
        return true;
    }
    
    /** Called when the document becomes unmodified.
     * Here, removing the save cookie from the object and marking it unmodified.
     */
    protected void notifyUnmodified() {
        MetaSlangDataObject obj = (MetaSlangDataObject) getDataObject();
        SaveCookie save = (SaveCookie) obj.getCookie(SaveCookie.class);
        if (save != null) {
            // You must implement this method on the object:
            obj.removeSaveCookie(save);
            obj.setModified(false);
        }
        super.notifyUnmodified();
    }
    
    /** A save cookie to use for the editor support.
     * When saved, saves the document to disk and marks the object unmodified.
     */
    private class Save implements SaveCookie {
        public void save() throws IOException {
            saveDocument();
            getDataObject().setModified(false);
        }
    }
    
    /** A description of the binding between the editor support and the object.
     * Note this may be serialized as part of the window system and so
     * should be static, and use the transient modifier where needed.
     */
    private static class MetaSlangEnv extends DataEditorSupport.Env {
        
        private static final long serialVersionUID = 1L;
        
        /** Create a new environment based on the data object.
         * @param obj the data object to edit
         */
        public MetaSlangEnv(MetaSlangDataObject obj) {
            super(obj);            
        }
        
        /** Get the file to edit.
         * @return the primary file normally
         */
        protected FileObject getFile() {
            return getDataObject().getPrimaryFile();
        }
        
        /** Lock the file to edit.
         * Should be taken from the file entry if possible, helpful during
         * e.g. deletion of the file.
         * @return a lock on the primary file normally
         * @throws IOException if the lock could not be taken
         */
        protected FileLock takeLock() throws IOException {
            return ((MetaSlangDataObject) getDataObject()).getPrimaryEntry().takeLock();
        }
        
        /** Find the editor support this environment represents.
         * Note that we have to look it up, as keeping a direct
         * reference would not permit this environment to be serialized.
         * @return the editor support
         */
        public CloneableOpenSupport findCloneableOpenSupport() {
            return (MetaSlangEditorSupport) getDataObject().getCookie(MetaSlangEditorSupport.class);
        }
        
    }
    
	
    private MetaSlangParser findParser() {
        return (MetaSlangParser)getDataObject().getCookie(MetaSlangParser.class);
    }

    private void changeTimeoutElapsed() {
        parseSource(MetaSlangParser.PRIORITY_REFRESH, false);
    }
    
    private void parsingErrorsChanged(PropertyChangeEvent evt) {
        int errors=MetaSlangSettings.getDefault().getParsingErrors();
        Integer old=(Integer)evt.getOldValue();
        int oldErrors=MetaSlangSettings.DEFAULT_PARSING_ERRORS;
        
        if (old!=null) {
            oldErrors=old.intValue();
        }
        if (oldErrors==errors) // no change
            return;
        if (errors==0 && !annotations.isEmpty()) { // dettach all annotations
            detachAnnotations(annotations);
            annotations.clear();
            return;
        }
        if (oldErrors==annotations.size() || errors<annotations.size()) { // parse source
            parseSource(MetaSlangParser.PRIORITY_BACKGROUND,true);
        }
    }
    
    public void parseSource(int priority, boolean ignoreClean) {
        MetaSlangParser parser = findParser();
        Task t;
        final ParseSourceRequest req;
        int errors;
        
        if (parser == null)
            return;
        errors=MetaSlangSettings.getDefault().getParsingErrors();
        if (getOpenedPanes()!=null && errors>0) {
            String fileName= getDataObject().getPrimaryFile().getNameExt();
            
            req=new ParseSourceRequest(errors,fileName);
        }
        else
            req=new ParseSourceRequest();
        t = parser.parse(priority,ignoreClean,false,req);
        parsedHook = parser.getSourceImpl();
        t.addTaskListener(new TaskListener() {
		public void taskFinished(Task t2) {
		    t2.removeTaskListener(this);
		    notifyParsingDone();
		    if (req.getErrConsumer()!=null) {
			SwingUtilities.invokeLater(new Runnable() {
				public void run() {
				    if (isDocumentLoaded())
					processAnnotations(req);
				}
			    });
		    }
		}
	    });
    }

    /** Restart the timer which starts the parser after the specified delay.
     * @param onlyIfRunning Restarts the timer only if it is already running
     */
    public void restartTimer(boolean onlyIfRunning) {
        int delay;
        
        if (onlyIfRunning && (timer==null || !timer.isRunning()))
            return;
        delay = MetaSlangSettings.getDefault().getAutoParsingDelay();
        if (delay<=0)
            return;
        if (timer==null) {  // initialize timer
            timer = new Timer(0, new ActionListener() {
		    public void actionPerformed(ActionEvent e) {
			changeTimeoutElapsed();
		    }
		});
            timer.setRepeats(false);
        }
        timer.setInitialDelay(delay);
        timer.restart();
    }

    /** Notify that parsing task has been finished; some dependent data may now
	be refreshed from up-to-date parsing info 
    */
    protected void notifyParsingDone() {
    }

    private void processAnnotations(ParseSourceRequest req) {
        ArrayList added,removed,unchanged;
        Iterator i;
        Collection newAnnotations=req.getAnnotations();

        if (newAnnotations==null) {   // request processed by someone else
            ErrorManager.getDefault().log("request "+req.getSourceName()+" processed by someone else");
            parseSource(MetaSlangParser.PRIORITY_NORMAL,true);
            return;
        }
        added=new ArrayList(newAnnotations);
        added.removeAll(annotations);
        unchanged=new ArrayList(annotations);
        unchanged.retainAll(newAnnotations);
        removed=annotations;
        removed.removeAll(newAnnotations);
        detachAnnotations(removed);
        if (!added.isEmpty()) {
            LineCookie cookie = (LineCookie)getDataObject().getCookie(LineCookie.class);
            Line.Set lines = cookie.getLineSet();

            for (i=added.iterator();i.hasNext();) {
                ParserAnnotation ann=(ParserAnnotation)i.next();

                ann.attachToLineSet(lines);
            }
        }
        annotations=unchanged;
        annotations.addAll(added);
    }
    
    private static void detachAnnotations(Collection anns) {
        Iterator i;

        for (i=anns.iterator();i.hasNext();) {
            Annotation ann=(Annotation)i.next();
            
            ann.detach();
        }
    }
        
    /**
     * Finds a position not obscured by a guarded block that is inside the given
     * bounds. Favors positions at the beginning of the passed bounds. Returns null,
     * if the document cannot be loaded.
     * @param bnds bounds to search within
     * @return PositionRef that can be safely written into.
     */
    public PositionRef findFreePosition(PositionBounds bnds) {
        StyledDocument doc;
        try {
            doc = openDocument();
        } catch (IOException ex) {
            return null;
        }
        
        PositionRef beginPos = bnds.getBegin();
	/*
	int startOffs = beginPos.getOffset();
        
	TreeSet set = new TreeSet(SECTION_COMPARATOR);
	set.addAll(this.sections.values());
	for (Iterator it = set.iterator(); it.hasNext(); ) {
	    GuardedSection s = (GuardedSection)it.next();
	    PositionRef start = s.getBegin();
	    if (start.getOffset() > startOffs) {
		// no section at the start.
		break;
	    }
	    if (s.contains(beginPos, false)) {
		// got guarded block that contains
		PositionRef after = s.getPositionAfter();
		if (after.getOffset() > bnds.getEnd().getOffset()) {
		    return null;
		}
		return after;
	    }
	}
	*/
        return beginPos;
    }

    protected CloneableEditor createCloneableEditor () {
        return new MetaSlangEditor(this);
    }
    
    protected void initializeCloneableEditor (CloneableEditor editor) {
    }

    private CloneableEditor openEditorComponent() {
        synchronized (getLock()) {
            CloneableEditor ce = getAnyEditor();
            
            if(ce != null) {
                ce.open();
                return ce;
            } else {
                // no opened editor
                String msg = messageOpening ();
                if (msg != null) {
                    TopManager.getDefault().setStatusText(msg);
                }

                // initializes the document if not initialized
                prepareDocument();

                ce = createCloneableEditor ();
                initializeCloneableEditor(ce);
                ce.setReference(allEditors);
                ce.open();

                msg = messageOpened ();
                if (msg == null) {
                    msg = ""; // NOI18N
                }
                TopManager.getDefault ().setStatusText (msg);
                return ce;
            }
        }
    }
    
    /** Access to lock on operations on the support
    */
    Object getLock () {
        return allEditors;
    }

    /** If one or more editors are opened finds one.
    * @return an editor or null if none is opened
    */
    CloneableEditor getAnyEditor () {
        CloneableTopComponent ctc;
        try {
            ctc = allEditors.getAnyComponent();
        } catch (java.util.NoSuchElementException e) {
            return null;
        }

        if(ctc instanceof CloneableEditor) {
            return (CloneableEditor)ctc;
        } else {
            Enumeration en = allEditors.getComponents();
            while(en.hasMoreElements()) {
                Object o = en.nextElement();
                if(o instanceof CloneableEditor) {
                    return (CloneableEditor)o;
                }
            }

            return null;
        }
    }

    /** Forcibly create one editor component. Then set the caret
    * to the given position.
    * @param pos where to place the caret
    * @return always non-<code>null</code> editor
    */
    public final CloneableEditor openAt(final PositionRef pos, final int column) {
        final MetaSlangEditor e = (MetaSlangEditor) openEditorComponent();
        final Task t = prepareDocument ();
        e.open();
        e.requestVisible();
        
        class Selector implements TaskListener, Runnable {
            public void taskFinished (org.openide.util.Task t2) {
                javax.swing.SwingUtilities.invokeLater (this);
                t2.removeTaskListener (this);
            }
            
            public void run () {
                // #25435. Pane can be null.
                JEditorPane ePane = e.getEditorPane();
                if(ePane == null) {
                    return;
                }
                Caret caret = ePane.getCaret();
                if(caret == null) {
                    return;
                }
                
                int offset;
                if (column >= 0) {
                    javax.swing.text.Element el = NbDocument.findLineRootElement (getDocument ());
                    el = el.getElement (el.getElementIndex (pos.getOffset ()));
                    offset = el.getStartOffset () + column;
                    if (offset > el.getEndOffset ()) {
                        offset = el.getEndOffset ();
                    }
                } else {
                    offset = pos.getOffset ();
                }
                
                caret.setDot(offset);
            }
        }
        
        
        t.addTaskListener (new Selector ());
	e.requestFocus();
	//e.selectElementsAtOffset(pos.getOffset());
        return e;
    }

    public static class MetaSlangEditor extends CloneableEditor {
        /** Default delay between cursor movement and updating selected element nodes. */
        static final int SELECTED_NODES_DELAY = 1000;

        /** Timer which countdowns the "update selected element node" time. */ // NOI18N
        Timer timerSelNodes;

        /** The support, subclass of EditorSupport */
        MetaSlangEditorSupport support;

        /** Listener on caret movements */
        CaretListener caretListener;

        Parsing.Listener parsingListener;
        
        /**
         * Toolbar that is displayed at the top of the editor window.
         * Lazily initialized in enableToolBar / createToolBar.
         */
        java.awt.Component toolBar;

        /** The last caret offset position. */
        int lastCaretOffset = -1;

        static final long serialVersionUID =6223349196427270209L;

        /** Only for externalization */
        public MetaSlangEditor () {
            super();
        }

        /** Creates new editor */
        public MetaSlangEditor (MetaSlangEditorSupport support) {
            super(support);
	    this.support = support;
            initialize();
        }
        
        private transient org.openide.util.RequestProcessor.Task selectionTask = null;

        /** Selects element at the given position. */
        void selectElementsAtOffset(final int offset) {
            SourceElement.Impl holder = support.findParser().getSourceImpl();
            
            if (holder == null)
                return;
            if (getRegistry().getActivated() != MetaSlangEditor.this ||
                !support.getDataObject().isValid()) {
              return;
            }
            SourceCookie.Editor seditor = (SourceCookie.Editor)support.getDataObject().
                getCookie(SourceCookie.Editor.class);
            
            edu.kestrel.netbeans.model.Element element = seditor.findElement(offset);
            ElementNodeFactory factory = MetaSlangDataObject.getExplorerFactory();
            Node n = null;
            
            if (element instanceof SpecElement) {
                n = factory.createSpecNode((SpecElement)element);
            }
            else if (element instanceof SortElement) {
                n = factory.createSortNode((SortElement)element);
            }
            else if (element instanceof OpElement) {
                n = factory.createOpNode((OpElement)element);
            }
            else if (element instanceof SourceElement) {
                n = support.getDataObject().getNodeDelegate();
            }
            setActivatedNodes((n != null) ? new Node[] { n } : new Node[] {} );
        }

        protected void notifyParsingDone() {
            if (lastCaretOffset != -1) {                
                SwingUtilities.invokeLater(new Runnable() {
                    public void run() {
                        selectElementsAtOffset(lastCaretOffset);
                    }
                });
            }
        }
        
        /**
         * Refreshes the activated node immediately. Provides system actions
         * based on the node activated at the time of popu invoke.
         */
        public SystemAction[] getSystemActions() {
            selectElementsAtOffset(lastCaretOffset);
            timerSelNodes.stop();
            return super.getSystemActions();
        }
                
        /** Obtain a support for this component */
        private void initialize () {
	    support.prepareDocument();
            timerSelNodes = new Timer(100, new java.awt.event.ActionListener() {
                                          public void actionPerformed(java.awt.event.ActionEvent e) {
                                              if (lastCaretOffset == -1 && pane != null) {
                                                  Caret caret = pane.getCaret();
                                                  if (caret != null)
                                                    lastCaretOffset = caret.getDot();
                                              }
                                              selectElementsAtOffset(lastCaretOffset);
                                          }
                                      });
            timerSelNodes.setInitialDelay(100);
            timerSelNodes.setRepeats(false);
            caretListener = new CaretListener() {
                                public void caretUpdate(CaretEvent e) {
                                    support.restartTimer(true);
                                    restartTimerSelNodes(e.getDot());
                                }
                            };
            timerSelNodes.restart();

            parsingListener = new Parsing.Listener() {
                                  public void objectParsed(Parsing.Event info) {
                                      if (info.getSource() == support.getDataObject()) {
                                          notifyParsingDone();
                                      }
                                  }
                              };
            
        }

        /** Restart the timer which updates the selected nodes after the specified delay from
        * last caret movement.
        */
        void restartTimerSelNodes(int pos) {
            timerSelNodes.setInitialDelay(SELECTED_NODES_DELAY);
            timerSelNodes.restart();
            lastCaretOffset = pos;
        }

        /** Returns Editor pane for private use.
        * @return Editor pane for private use.
        */
        private JEditorPane getEditorPane () {
            return pane;
        }

        /* Is called from the clone method to create new component from this one.
        * This implementation only clones the object by calling super.clone method.
        * @return the copy of this object
        */
        protected CloneableTopComponent createClonedObject () {
            return support.createCloneableEditor();
        }

        /* This method is called when parent window of this component has focus,
        * and this component is preferred one in it. This implementation adds 
        * performer to the ToggleBreakpointAction.
        */
        protected void componentActivated () {
            getEditorPane().addCaretListener(caretListener);
            Parsing.addParsingListener(parsingListener);
            super.componentActivated ();
        }

        /*
        * This method is called when parent window of this component losts focus,
        * or when this component losts preferrence in the parent window. This 
        * implementation removes performer from the ToggleBreakpointAction.
        */
        protected void componentDeactivated () {
            getEditorPane().removeCaretListener(caretListener);
            Parsing.removeParsingListener(parsingListener);
            synchronized (this) {
                if (selectionTask != null) {
                    selectionTask.cancel();
                    selectionTask = null;
                }
            }
            super.componentDeactivated ();
        }

        /** Deserialize this top component.
        * @param in the stream to deserialize from
        */
        public void readExternal (ObjectInput in)
        throws IOException, ClassNotFoundException {
            super.readExternal(in);
	    support = (MetaSlangEditorSupport) cloneableEditorSupport();
            initialize();
        }

    }
}
