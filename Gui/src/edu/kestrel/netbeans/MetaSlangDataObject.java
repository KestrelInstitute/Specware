/*
 * MetaSlangDataObject.java
 *
 * $Id$
 *
 *
 *
 * $Log$
 *
 *
 */

package edu.kestrel.netbeans;

import org.openide.actions.*;
import org.openide.cookies.*;
import org.openide.filesystems.*;
import org.openide.loaders.*;
import org.openide.nodes.*;
import org.openide.util.HelpCtx;
import org.openide.text.CloneableEditorSupport;

import edu.kestrel.netbeans.cookies.SourceCookie;
import edu.kestrel.netbeans.model.SourceElement;
import edu.kestrel.netbeans.editor.MetaSlangEditorSupport;
import edu.kestrel.netbeans.parser.MetaSlangParser;
import edu.kestrel.netbeans.nodes.*;

/** Represents a MetaSlang object in the Repository.
 *
 * @author  becker
 */
public class MetaSlangDataObject extends MultiDataObject implements CookieSet.Factory {
    
    /**
     * Holds a reference to editor support class. Lazy initialized from getMeraSlangEditor,
     * or a getter for EditorSupport.class cookie.
     */
    transient private MetaSlangEditorSupport editorSupport;
    
    /**
     * Holds a reference to the glue between the parser and the dataobject.
     * Lazy initialized from {@link #initializeParsingSupport}
     */
    private transient MetaSlangParserGlue   parserGlue;
    
    /** Lock for parsing and connection support
     */
    transient private Object lock;
    
    /** Holds value of property upToDate. */
    private Boolean upToDate;
    
    static final String PROP_UPTODATE = "upToDate"; // NOI18N
    
    public MetaSlangDataObject(FileObject pf, MetaSlangDataLoader loader) throws DataObjectExistsException {
        super(pf, loader);
        init();
    }
    
    private void init() {
        lock = new Object();
        MultiDataObject.Entry entry = getPrimaryEntry();
        CookieSet cookies = getCookieSet();
        // Add whatever capabilities you need, e.g.:
        
        //cookies.add (new ExecSupport (getPrimaryEntry ()));
        //MetaSlangEditorSupport editor = new MetaSlangEditorSupport (this);
        //cookies.add (new MetaSlangSupport(this, editor));
        cookies.add(new MetaSlangOpenSupport(getPrimaryEntry()));
        // See Editor Support template in Editor API:
        //cookies.add (editor);
        
        //cookies.add (new CompilerSupport.Compile (getPrimaryEntry ()));
        //cookies.add (new CompilerSupport.Build (getPrimaryEntry ()));
        //cookies.add (new CompilerSupport.Clean (getPrimaryEntry ()));
        /*
         cookies.add (new OpenCookie () {
                public void open () {
                    // do something...but usually you want to use OpenSupport instead
                }
            });
         */
        Class[] cookieClasses = new Class[] {
	    /*
            CompilerCookie.Build.class, 
            CompilerCookie.Clean.class,
	    */
            CompilerCookie.Compile.class,
	    /*
	    CompilerSupport.class,
            ExecSupport.class,
	    */
            MetaSlangEditorSupport.class,
            MetaSlangParser.class,
            SourceCookie.Editor.class,
        };
        cookies.add(cookieClasses, this);
    }
    
    public HelpCtx getHelpCtx() {
        return HelpCtx.DEFAULT_HELP;
        // If you add context help, change to:
        // return new HelpCtx (MetaSlangDataObject.class);
    }
    
    protected Node createNodeDelegate() {
        return new MetaSlangDataNode(this);
    }
    
    // If you made an Editor Support you will want to add these methods:
    
    public final void addSaveCookie(SaveCookie save) {
        getCookieSet().add(save);
    }
    
    public final void removeSaveCookie(SaveCookie save) {
        getCookieSet().remove(save);
    }
    
    /** Creates a Node.Cookie of given class. The method
     * may be called more than once.
     */
    public Node.Cookie createCookie(Class klass) {
        //Util.log("*** createCookie(): class = "+klass.getName());
        if (SourceCookie.class.isAssignableFrom(klass) ||
        MetaSlangParser.class.isAssignableFrom(klass)) {
            if (initializeParsingSupport() == null)
                return null;
            if (klass.isAssignableFrom(parserGlue.getClass()))
                return parserGlue;
            else
                return parserGlue.getParser();
        } else if (klass.isAssignableFrom(MetaSlangEditorSupport.class)) {
            //Util.log("*** getMetaSlangEditor()");
            return getMetaSlangEditor();
        }
        
        return null;
    }
    
    /**
     * Creates a parsing support.
     */
    private MetaSlangParser initializeParsingSupport() {
        if (parserGlue != null)
            return parserGlue.getParser();
        synchronized (lock) {
            if (parserGlue != null) {
                return parserGlue.getParser();
            }
            
            parserGlue = new MetaSlangParserGlue(getPrimaryEntry());
            
        }
        return parserGlue.getParser();
    }
    
    /** Get the parsed representation of this source file.
     * May not be fully parsed yet; the source element itself indicates its status.
     * @return the source element for this MetaSlang source file
     */
    public SourceElement getSource() {
        return ((MetaSlangParser)getCookie(MetaSlangParser.class)).getSource();
    }
    
    /** Get the current editor support.
     * Ought not be subclasses; use {@link #createMetaSlangEditor}.
     * @return the editor support
     */
    public MetaSlangEditorSupport getMetaSlangEditor() {
        if (editorSupport == null) {
            synchronized (this) {
                editorSupport = createMetaSlangEditor();
                if (parserGlue != null)
                    parserGlue.cloneableSupportCreated(editorSupport);
            }
        }
        return editorSupport;
    }
    
    /** Create the editor support for this data object.
     * By default, creates a <code>MetaSlangEditor</code> with the source file entry;
     * subclasses may override this.
     * @return the editor support
     */
    protected MetaSlangEditorSupport createMetaSlangEditor() {
        MetaSlangEditorSupport editor = new MetaSlangEditorSupport(this);
        return editor;
    }
    
    /**
     * Finds a cloneableEditorSupport that holds the displayable/parseable source. The implementation
     * currently uses a hack, that extract package-private member from the EditorSupport's
     * implementation.
     */
    protected CloneableEditorSupport findCloneableEditorSupport() {
        MetaSlangEditorSupport supp = (MetaSlangEditorSupport)getCookie(MetaSlangEditorSupport.class);
        return supp;
    }
    
    public void suspendSupports() {
        // initialize support objects. If they were requested after this method,
        // they would be created in an active state.
        initializeParsingSupport();
    }
    
    boolean isMetaSlangFileReadOnly() {
        FileObject primary = getPrimaryFile();
        if (!isValid() || !primary.isValid()) {
            return true;
        }
        return primary.isReadOnly();
    }
    
    // =============== The mechanism for regeisteing node factories ==============
    
    private static NodeFactoryPool explorerFactories;
    private static NodeFactoryPool browserFactories;
    private static ElementNodeFactory basicBrowser;
    
    /**
     * DO NOT USE THIS METHOD!!! <P>
     * This method is intended to be called only during initialization of specware
     * module-provided node factories from the installation layer. It won't
     * be maintained for compatibility reasons.
     */
    synchronized static ElementNodeFactory createBasicExplorerFactory() {
        return MetaSlangElementNodeFactory.DEFAULT;
    }
    
    /**
     * DO NOT USE THIS METHOD!!! <P>
     * This method is intended to be called only during initialization of specware
     * module-provided node factories from the installation layer. It won't
     * be maintained for compatibility reasons.
     */
    synchronized static ElementNodeFactory createBasicBrowserFactory() {
        if (basicBrowser == null) {
            basicBrowser = new MetaSlangElementNodeFactory();
            ((MetaSlangElementNodeFactory)basicBrowser).setGenerateForTree(true);
        }
        return basicBrowser;
    }
    
    public static ElementNodeFactory getExplorerFactory() {
        NodeFactoryPool pool = createExplorerFactory();
        ElementNodeFactory f = null;
        
        if (pool != null)
            f = pool.getHead();
        if (f == null)
            f = createBasicExplorerFactory();
        return f;
    }
    
    public static ElementNodeFactory getBrowserFactory() {
        NodeFactoryPool pool = createBrowserFactory();
        ElementNodeFactory f = null;
        
        if (pool != null)
            f = pool.getHead();
        if (f == null)
            f = createBasicBrowserFactory();
        return f;
    }
    
    static NodeFactoryPool createFactoryPool(String folderName, ElementNodeFactory def) {
        FileObject f = Repository.getDefault().findResource(folderName);
        if (f == null)
            return null;
        try {
            DataFolder folder = (DataFolder)DataObject.find(f).getCookie(DataFolder.class);
            return new NodeFactoryPool(folder, def);
        } catch (DataObjectNotFoundException ex) {
            return null;
        }
    }
    
    synchronized static NodeFactoryPool createBrowserFactory() {
        if (browserFactories != null)
            return browserFactories;
        browserFactories = createFactoryPool("/NodeFactories/specware/objectbrowser", createBasicBrowserFactory());
        return browserFactories;
    }
    
    synchronized static NodeFactoryPool createExplorerFactory() {
        if (explorerFactories != null)
            return explorerFactories;
        explorerFactories = createFactoryPool("/NodeFactories/specware/explorer", createBasicExplorerFactory());
        return explorerFactories;
    }
    
    /**
     * @deprecated use installation layer for registering a factory for the the whole
     * time a module is installed. Note: This feature will be dropped in the next
     * release.
     */
    public static void addExplorerFilterFactory( FilterFactory factory ) {
        NodeFactoryPool p = createExplorerFactory();
        if (p != null)
            p.addFactory(factory);
    }
    
    /**
     * @deprecated use installation layer for registering a factory for the the whole
     * time a module is installed. Note: This feature will be dropped in the next
     * release.
     */
    public static void removeExplorerFilterFactory( FilterFactory factory ) {
        NodeFactoryPool p = createExplorerFactory();
        if (p != null)
            p.removeFactory(factory);
    }
    
    /**
     * @deprecated use installation layer for registering a factory for the the whole
     * time a module is installed. Note: This feature will be dropped in the next
     * release.
     */
    public static void addBrowserFilterFactory(FilterFactory factory) {
        NodeFactoryPool p = createBrowserFactory();
        if (p != null)
            p.addFactory(factory);
    }
    
    /**
     * @deprecated use installation layer for registering a factory for the the whole
     * time a module is installed. Note: This feature will be dropped in the next
     * release.
     */
    public static void removeBrowserFilterFactory( FilterFactory factory ) {
        NodeFactoryPool p = createBrowserFactory();
        if (p != null)
            p.removeFactory(factory);
    }
    
    /** Getter for property upToDate.
     * @return Value of property upToDate.
     */
    Boolean isUpToDate() {
        if (upToDate == null)
            checkUpToDate();
        return upToDate;
    }
    
    /** Setter for property upToDate.
     * @param upToDate New value of property upToDate.
     */
    void setUpToDate(Boolean aUpToDate) {
        if (aUpToDate.equals(upToDate))
            return;
        Boolean old = upToDate;
        upToDate = aUpToDate;
        if (old != null)
            firePropertyChange(PROP_UPTODATE, old, upToDate);
    }
    
    private void checkUpToDate() {
        if (isModified()) {
            setUpToDate(Boolean.FALSE);
            return;
        }
        setUpToDate(Boolean.TRUE);
    }
    
    
}
