/*
 * MetaSlangPanel.java
 *
 * $Id$
 *
 *
 *
 * $Log$
 * Revision 1.1  2003/01/30 02:01:36  gilham
 * Initial version.
 *
 *
 *
 */

package edu.kestrel.netbeans;

import java.awt.*;
import java.awt.event.*;
import java.beans.*;
import java.io.*;
import java.util.*;
import java.util.List;
import javax.swing.*;
import javax.swing.event.*;
import javax.swing.table.*;
import javax.swing.text.*;
import javax.swing.tree.*;

import org.openide.ErrorManager;
import org.openide.TopManager;
import org.openide.loaders.*;
import org.openide.nodes.*;
import org.openide.text.CloneableEditorSupport;
import org.openide.util.*;
import org.openide.windows.*;
import org.openide.util.*;


public class MetaSlangPanel extends CloneableTopComponent {
    private static final long serialVersionUID = 7204432764586558961L;
    private MultiDataObject.Entry entry;
    //private MetaSlangCookie cookie;
    private MetaSlangOpenSupport support;
    //private MetaSlang metaSlang;
    private NodeListener listener;
    
    
    // Variables declaration - do not modify
    private javax.swing.JPanel GraphPanel;
    
    public MetaSlangPanel(MultiDataObject.Entry entry) {
        super(entry.getDataObject());
        this.entry = entry;
        Util.log("\n\nMetaSlangPanel.MetaSlangPanel -- initialization of panel entry = "+entry);
        init();
    }
    protected CloneableTopComponent createClonedObject() {
        return new MetaSlangPanel(entry);
    }
    /**
     * @serialData Super, then the MultiDataObject.Entry to represent. */
    public void writeExternal(ObjectOutput oo) throws IOException {
        super.writeExternal(oo);
        oo.writeObject(entry);
    }
    /** for externalization only */
    public MetaSlangPanel() {
    }
    /**
     * @serialData #see writeExternal */
    public void readExternal(ObjectInput oi) throws IOException, ClassNotFoundException {
        super.readExternal(oi);
        entry = (MultiDataObject.Entry)oi.readObject();
        init();
    }
    public void open(Workspace ws) {
        if (ws == null) {
            ws = WindowManager.getDefault().getCurrentWorkspace();
        }
        Mode mode = ws.findMode(CloneableEditorSupport.EDITOR_MODE);
        if (mode != null) {
            mode.dockInto(this);
        }
        super.open(ws);
    }
    protected boolean closeLast() {
        if (support == null) {
            // Should not happen.
            ErrorManager.getDefault().log(ErrorManager.WARNING, "WARNING: no MetaSlangOpenSupport, will just close");
            return true;
        }
        boolean ok = support.canClose();
        return ok;
    }
    protected void updateNameAndIcon(DataObject o, Node n) {
        String displayName = n.getDisplayName();
        if (o.isModified()) {
            setName(NbBundle.getMessage(MetaSlangPanel.class, "LBL_modified_name", displayName));
        } else {
            setName(displayName);
        }
        setIcon(n.getIcon(BeanInfo.ICON_COLOR_16x16));
    }
    private void init() {
        if (!SwingUtilities.isEventDispatchThread()) {
            SwingUtilities.invokeLater(new Runnable() {
                public void run() {
                    init();
                }
            });
            return;
        }
        putClientProperty("PersistenceType", "OnlyOpened");
        // [PENDING] Should also fire Env.PROP_VALID when DataObject.PROP_VALID
        // changes. Presumably editor supports do this for you, somewhere, though
        // it is not clear where.
        final DataObject o = entry.getDataObject();
        final Node n = o.getNodeDelegate();
        updateNameAndIcon(o, n);
        listener = new NodeAdapter() {
            public void propertyChange(PropertyChangeEvent ev) {
                String prop = ev.getPropertyName();
                if (prop == null ||
                prop.equals(Node.PROP_DISPLAY_NAME) ||
                prop.equals(Node.PROP_ICON) ||
                prop.equals(DataObject.PROP_MODIFIED)) {
                    Util.log("MetaSlangPannel Property change --> ev "+ ev + " prop = "+prop);
                    updateNameAndIcon(o, n);
                }
            }
        };
        n.addNodeListener(WeakListener.node(listener, n));
        o.addPropertyChangeListener(WeakListener.propertyChange(listener, o));
        setLayout(new BorderLayout());
        
        //add(new GraphPanel(this,o), BorderLayout.CENTER);
        JPanel graphPanel = new JPanel();
        //PlanwareGraphDisplay graph = new PlanwareGraphDisplay(o);
        graphPanel.setLayout(new BorderLayout());
        //graphPanel.add(new JScrollPane(graph), "Center");
        //graphPanel.add(graph.createToolBar(JToolBar.HORIZONTAL),"North");      
        add(graphPanel, BorderLayout.CENTER);
        // WLP
        
        revalidate();
        support = (MetaSlangOpenSupport)entry.getDataObject().getCookie(MetaSlangOpenSupport.class);
    }
    
    
    
}
