/*
 * MetaSlangDataNode.java
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

import java.awt.Component;
import java.awt.Image;
import java.awt.event.ActionEvent;
import java.awt.event.ActionListener;
import java.util.*;
import java.beans.*;
import java.io.IOException;
import javax.swing.Timer;
import javax.swing.event.*;

import org.openide.TopManager;
import org.openide.ErrorManager;
import org.openide.NotifyDescriptor;
import org.openide.loaders.*;
import org.openide.nodes.*;
import org.openide.src.SourceException;
import org.openide.util.NbBundle;
import org.openide.util.*;
import org.openide.util.datatransfer.NewType;
import org.openide.util.actions.SystemAction;
import org.openide.text.CloneableEditorSupport;
import org.openide.actions.OpenAction;
import org.openide.cookies.EditorCookie;
import org.openide.filesystems.*;

import org.netbeans.modules.java.tools.BadgeCache;

import edu.kestrel.netbeans.model.SourceElement;
import edu.kestrel.netbeans.model.SpecElement;
import edu.kestrel.netbeans.nodes.SourceChildren;
import edu.kestrel.netbeans.nodes.MemberCustomizer;
import edu.kestrel.netbeans.parser.MetaSlangParser;
import edu.kestrel.netbeans.settings.MetaSlangSettings;

/** A node to represent this object.
 *
 * @author  becker
 */
public class MetaSlangDataNode extends DataNode // implements ChangeListener
{
    private static final String ICON_BASE = "edu/kestrel/resources/images/"; // NOI18N
    private static final String BADGE_ERROR = ICON_BASE + "error-badge"; // NOI18N
    private static final String BADGE_NEEDS_SAVE = ICON_BASE + "out-of-date-badge"; // NOI18N
    
    private static final String[] ICON_ATTRS_NONE = {};
    protected static final String ICON_ATTR_ERROR = "error"; // NOI18N
    protected static final String ICON_ATTR_NEEDS_SAVE = "needsSave"; // NOI18N
    
    private boolean inUse = false;
    
    private transient boolean preparsed = false;
    
    private static final int ICON_REFRESH_DELAY_MSECS = 1000;
    
    private BadgeCache   iconCache;
    
    private HashSet      currentBadges;
    
    private Task         iconRefreshTask;
    
    private IconResolver iconResolver;
    
    private PropL        mixedListener;
    
    /**
     * Last known/displayed status of the source.
     */
    private int         lastGoodStatus;
    
    /**
     * Up-to-date status that will be used for badging. 1 - OK, 0 - old,
     * 2 - needs to be determined.
     */
    private int         upToDate = 2;
    
    private Object keepAlive;
    
    static final ResourceBundle bundle = NbBundle.getBundle(MetaSlangDataNode.class);
    
    public MetaSlangDataNode(MetaSlangDataObject obj) {
        //this(obj, new MetaSlangChildren((MetaSlangCookie)obj.getCookie(MetaSlangCookie.class)));
        this(obj, new SourceChildren(MetaSlangDataObject.getExplorerFactory(), obj.getSource()));
        currentBadges = new HashSet();
    }
    
    public MetaSlangDataNode(MetaSlangDataObject obj, Children ch) {
        super(obj, ch);
        //setIconBase("edu/kestrel/resources/images/File");
        setIconBase(getBareIconBase());
        
        /*
        MetaSlangCookie metaSlang = (MetaSlangCookie)getCookie(MetaSlangCookie.class);
        if (metaSlang != null) {
            metaSlang.addChangeListener(WeakListener.change(this, metaSlang));
        }
         
        EditorCookie ed = (EditorCookie)getCookie(EditorCookie.class);
        if (ed != null && (ed instanceof CloneableEditorSupport)) {
            ((CloneableEditorSupport)ed).addChangeListener(WeakListener.change(this,ed));
        }
         */
        mixedListener = new PropL();
        obj.addPropertyChangeListener(WeakListener.propertyChange(mixedListener, obj));
        
        MetaSlangParser p = findParser();
        if (p != null) {
            p.addChangeListener(WeakListener.change(mixedListener, p));
        }
    }
    
    public void setIconBase(String base) {
        super.setIconBase(base);
        synchronized (this) {
            iconCache = BadgeCache.getCache(base);
            initializeBadges(iconCache);
        }
    }
    
    private class PropL implements ChangeListener, PropertyChangeListener {
        public void stateChanged(ChangeEvent ev) {
            sourceParsed();
        }
        
        public void propertyChange(PropertyChangeEvent evt) {
        }
    }
    
    private MetaSlangParser findParser() {
        return (MetaSlangParser)getDataObject().getCookie(MetaSlangParser.class);
    }
    
    /*
    public Image getIcon(int type) {
        if (type == BeanInfo.ICON_COLOR_16x16 || type == BeanInfo.ICON_MONO_16x16){
            Image icon = Utilities.loadImage("edu/kestrel/resources/images/File.gif");
            MetaSlangCookie cookie = (MetaSlangCookie)getCookie(MetaSlangCookie.class);
            if (cookie != null){
                if (inUse){
                    cookie.prepare();
                }
                if (! cookie.isValid()){
                    Image badge = Utilities.loadImage("edu/kestrel/resources/images/error-badge.gif");
                    Util.log("MetaSlangDataNode.getIcon => badge = " + badge + " icon = "+ icon);
                    if (icon != null & badge != null) {
                        icon = Utilities.mergeImages(icon, badge, 8,8);
                    }
                }
            }
            DataObject obj = getDataObject();
            if (obj.isModified()) {
                Image badge = Utilities.loadImage("edu/kestrel/resources/images/out-of-date-badge.gif");
                icon = Utilities.mergeImages(icon, badge, 16, 0);
            }
            try {
                icon = obj.getPrimaryFile().getFileSystem().getStatus().annotateIcon(icon, type, obj.files());
            } catch (FileStateInvalidException ex) {
                ErrorManager.getDefault().notify(ErrorManager.INFORMATIONAL, ex);
            }
            return icon;
        } else {
            return null;
        }
    }
     
    public Image getOpenIcon(int type){
        return getIcon(type);
    }
     */
    
    /**
     * This method is called during node initialization and whenever the base icon is
     * replaced to refill the badge cache with custom badges. The MetaSlangDataNode's implementation
     * adds executable and error badges. Override to add your own badges, or replace the
     * default ones.
     */
    protected void initializeBadges(BadgeCache cache) {
        cache.registerBadge(ICON_ATTR_ERROR, BADGE_ERROR, 8, 8);
        cache.registerBadge(ICON_ATTR_NEEDS_SAVE, BADGE_NEEDS_SAVE, 16, 0);
    }
    
    public Image getIcon(int type) {
        preparseSource();
        
        // assume setIconBase was already called.
        String[] badges = getBadges();
        return iconCache.getIcon(super.getIcon(type), badges);
    }
    
    public Image getOpenedIcon(int type) {
        preparseSource();
        String[] badges = getBadges();
        return iconCache.getIcon(super.getOpenedIcon(type), badges);
    }
    
    protected void preparseSource() {
        if (preparsed ||
        !MetaSlangSettings.getDefault().getPrescanSources())
            return;
        preparsed = true;
        // schedule a background reparse so the icon for runnable classes
        // are updated in the background:
        // the listener will be notified after the parse is completed.
        SourceElement source = getMetaSlangDataObject().getSource();
        if (getDataObject().isValid() && source.getStatus() == SourceElement.STATUS_NOT) {
            MetaSlangParser p = findParser();
            if (p != null)
                //Util.log("*** MetaSlangNode.preparseSource: Parsing Source "+getMetaSlangDataObject().getPrimaryEntry().getFile().getName());
                p.parse(MetaSlangParser.PRIORITY_BACKGROUND, false, false);
            // schedule a background reparse so the icon for runnable classes
            // are updated in the background:
        }
    }
    
    /** Get the icon base.
     * This should be a resource path, e.g. <code>/some/path/</code>,
     * where icons are held. Subclasses may override this.
     * @return the icon base
     * @see #getIcons
     * @deprecated the function is not consistent with openide's setIconBase() behaviour.
     * Given the icon badging, there's no need for composing icon names - see
     * {@link #setBadges()}, {@link #getBadges} or {@link #getBareIconBase()}
     */
    protected String getIconBase() {
        return ICON_BASE;
    }
    
    /**
     * Returns the base resource name for the basic icon that identifies object type
     * to the user. Additional images may be superimposed over that icon using icon
     * badging specification. Override in subclasses to provide a different icon for
     * the node.
     * @return the icon base
     */
    protected String getBareIconBase() {
        return getIconBase() + getIcons()[0];
    }
    
    /** Get the icons.
     * This should be a list of bare icon names (i.e. no extension or path) in the icon base.
     * It should contain five icons in order for:
     * <ul>
     * <li>a regular class
     * <li>a class with a main method
     * <li>a class with a parse error
     * <li>a MetaSlangBean class
     * <li>a MetaSlangBean class with a main method
     * </ul>
     * Subclasses may override this.
     * @return the icons
     * @see #getIconBase
     * @deprecated State icons are now handled using icon badging mechanism. If you need
     * to add or modify the badges attached by the java module, override {@link #getBadges}
     */
    protected String[] getIcons() {
        return new String[] { "File" }; // NOI18N
    }
    
    /**
     * Returns badges that should be combined with the base icon.
     * @return array of badges, can be null if no badges should be used.
     */
    protected String[] getBadges() {
        if (currentBadges.isEmpty())
            return null;
        return (String[])currentBadges.toArray(new String[currentBadges.size()]);
    }
    
    /**
     * Replaces the set of badges applied to the base icon. If the new set differs
     * from the current one, the new value is recorded and icon property changes are
     * fired.
     * @param list of badge identifiers; null to clear.
     */
    protected void setBadges(String[] badges) {
        if (badges == null)
            badges = new String[0];
        if (currentBadges.size() == badges.length) {
            boolean match = true;
            
            for (int i = 0; i < badges.length; i++) {
                if (!currentBadges.contains(badges[i])) {
                    match = false;
                    break;
                }
            }
            if (match)
                return;
        }
        currentBadges = new HashSet(Arrays.asList(badges));
        fireIconChange();
        fireOpenedIconChange();
    }
    
    /** Update the icon for this node based on parse status.
     * Called automatically at the proper times.
     * @see #getIconBase
     * @see #getBadges
     * @see #setBadges
     */
    protected void resolveIcons() {
        MetaSlangDataObject obj = getMetaSlangDataObject();
        SourceElement source = obj.getSource();
        String desc = null;
        boolean isTemplate = obj.isTemplate();
        java.util.Collection badges = new java.util.ArrayList(3);
        int status;
        
        if (isTemplate)
            status = SourceElement.STATUS_OK;
        else
            status = translateSourceStatus(source.getStatus());
        
        switch (status) {
            case SourceElement.STATUS_NOT:
                break;
                
            case SourceElement.STATUS_ERROR:
            case SourceElement.STATUS_PARTIAL:
                desc = Util.getString("HINT_ParsingErrors");
                badges.add(ICON_ATTR_ERROR);
                break;
                
            case SourceElement.STATUS_OK:
                //badges.add(ICON_ATTR_OK);
                break;
            default:
                throw new IllegalArgumentException("Unknown status "+status); // NOI18N
        }
        lastGoodStatus = status;
        
        setShortDescription(desc);
        if (badges.isEmpty()) {
            setBadges(ICON_ATTRS_NONE);
        } else {
            setBadges((String[])badges.toArray(new String[badges.size()]));
        }
    }
    
    public NewType[] getNewTypes() {
        if (getMetaSlangDataObject().isMetaSlangFileReadOnly()) {
            return super.getNewTypes();
        }
        return new NewType[] {new NewSpecType()};
    }
    
    /** Encapsulation of creating new spec or interface.
     */
    class NewSpecType extends NewType {
        
        NewSpecType() {
        }
        
        public String getName() {
            return bundle.getString("MENU_CREATE_SPEC");
        }
        
        public HelpCtx getHelpCtx() {
            return null;
        }
        
        public void create() throws IOException {
            String name = "NewSpec"; // NOI18N
            
            final SpecElement e = new SpecElement();
            final SourceElement el = ((MetaSlangDataObject)getDataObject()).getSource();
            Task parsingTask = el.prepare();
            try {
                e.setName(name);
                if (openCustomizer(new MemberCustomizer(e, "Spec"), "TIT_NewSpec")) {
                    if (parsingTask.isFinished()) {
                        addSpec(el, e);
                    } else {
                        parsingTask.addTaskListener(new org.openide.util.TaskListener() {
                            public void taskFinished(Task t) {
                                t.removeTaskListener(this);
                                try {
                                    addSpec(el, e);
                                } catch (IOException exc) {
                                    ErrorManager.getDefault().notify(exc);
                                }
                            }
                        });
                    }
                }
            } catch (SourceException ex) {
                IOException newex = new IOException(ex.getLocalizedMessage());
                ErrorManager.getDefault().annotate(
                newex, ex
                );
                throw newex;
            }
        }
        
        private void addSpec(final SourceElement src, final SpecElement mm) throws IOException {
            final SourceException[] ex  = new SourceException[] { null };
            try {
                src.runAtomicAsUser(new Runnable() {
                    public void run() {
                        try {
                            src.addSpec(mm);
                        } catch (SourceException e) {
                            ex[0] = e;
                        }
                    }
                });
            } catch (SourceException e) {
            }
            if (ex[0] != null) {
                IOException newex = new IOException(ex[0].getLocalizedMessage());
                ErrorManager.getDefault().annotate(
                newex, ex[0]
                );
                throw newex;
            }
        }
    }
    
    public static boolean openCustomizer(Component customizer, String title) {
        NotifyDescriptor desriptor = new NotifyDescriptor(
        customizer,
        title,
        NotifyDescriptor.OK_CANCEL_OPTION,
        NotifyDescriptor.PLAIN_MESSAGE,
        null, null);
        
        Object ret = TopManager.getDefault().notify(desriptor);
        return (ret == NotifyDescriptor.OK_OPTION);
    }
    
    /*
    public void stateChanged(ChangeEvent ev) {
        Object src = ev.getSource();
        if (!inUse && (src instanceof EditorCookie) ){
            inUse = true;
            fireIconChange();
        }
        if (src instanceof MetaSlangCookie){
            fireIconChange();
        }
    }
     */
    
    void sourceParsed() {
        MetaSlangParser p = findParser();
        int status = translateSourceStatus(p.getStatus());
        if (status == SourceElement.STATUS_NOT)
            return;
        keepAlive = findParser().getSourceImpl();
        requestResolveIcons();
    }
    
    /**
     * Translates the source status so it can be compared with the currently
     * displayed one. Eliminates some transitions that should not bother
     * the end-user watching the Explorer.
     */
    int translateSourceStatus(int sourceStatus) {
        if (sourceStatus == SourceElement.STATUS_NOT)
            return lastGoodStatus;
        if (sourceStatus == SourceElement.STATUS_OK ||
        lastGoodStatus == SourceElement.STATUS_NOT)
            return sourceStatus;
        
        if (getMetaSlangDataObject().isModified())
            return lastGoodStatus;
        else
            return sourceStatus;
    }
    
    private class IconResolver implements Runnable {
        public void run() {
            synchronized (MetaSlangDataNode.this) {
                iconRefreshTask = null;
                iconResolver = null;
            }
            upToDate=MetaSlangDataNode.this.getMetaSlangDataObject().isUpToDate().booleanValue()?1:0;
            StateUpdater.getInstance().updateNode(MetaSlangDataNode.this);
        }
    }
    
    /**
     * Schedules a refresh of node's icon, after ICON_REFRESH_DELAY_MSEC.
     * Requests is not scheduled if another one is still pending.
     * @deprecated
     */
    protected void requestResolveIcons() {
        synchronized (this) {
            if (iconRefreshTask != null)
                return;
            iconResolver = new IconResolver();
            iconRefreshTask = RequestProcessor.getDefault().post(iconResolver,
            ICON_REFRESH_DELAY_MSECS);
        }
    }
    
    protected MetaSlangDataObject getMetaSlangDataObject() {
        return (MetaSlangDataObject) getDataObject();
    }
    
    /* Example of adding Executor / Debugger / Arguments to node:
    protected Sheet createSheet () {
        Sheet sheet = super.createSheet ();
        Sheet.Set set = sheet.get (ExecSupport.PROP_EXECUTION);
        if (set == null) {
            set = new Sheet.Set ();
            set.setName (ExecSupport.PROP_EXECUTION);
            set.setDisplayName (NbBundle.getMessage (MetaSlangDataNode.class, "LBL_DataNode_exec_sheet"));
            set.setShortDescription (NbBundle.getMessage (MetaSlangDataNode.class, "HINT_DataNode_exec_sheet"));
        }
        ((ExecSupport) getCookie (ExecSupport.class)).addProperties (set);
        // Maybe:
        ((CompilerSupport) getCookie (CompilerSupport.class)).addProperties (set);
        sheet.put (set);
        return sheet;
    }
     */
    
    /*
    public SystemAction getDefaultAction () {
        return SystemAction.get (MyFavoriteAction.class);
    }
     */
    
    private static class StateUpdater implements PropertyChangeListener, ActionListener {
        private Set     registeredNodes;
        private static StateUpdater     instance;
        private Collection scheduledNodes;
        private Timer   timer;
        
        StateUpdater() {
            MetaSlangSettings.getDefault().addPropertyChangeListener(this);
            scheduledNodes = new LinkedList();
            timer = new Timer(300, this);
            timer.setRepeats(false);
        }
        
        static synchronized StateUpdater getInstance() {
            if (instance == null)
                instance = new StateUpdater();
            return instance;
        }
        
        public void registerNode(Node n) {
            if (registeredNodes == null) {
                synchronized (this) {
                    if (registeredNodes == null)
                        registeredNodes = new org.openide.util.WeakSet(37);
                }
            }
            synchronized (registeredNodes) {
                registeredNodes.add(n);
            }
        }
        
        public void updateNode(MetaSlangDataNode n) {
            synchronized (this) {
                scheduledNodes.add(new java.lang.ref.WeakReference(n));
                if (scheduledNodes.size() == 1) {
                    timer.start();
                }
            }
            timer.restart();
        }
        
        public void propertyChange(PropertyChangeEvent evt) {
        }
        
        public void actionPerformed(ActionEvent actionEvent) {
            Collection n;
            
            synchronized (this) {
                n = scheduledNodes;
                scheduledNodes = new LinkedList();
            }
            for (Iterator it = n.iterator(); it.hasNext(); ) {
                MetaSlangDataNode node = (MetaSlangDataNode)((java.lang.ref.Reference)it.next()).get();
                if (node == null)
                    continue;
                node.resolveIcons();
            }
        }
    }
}
