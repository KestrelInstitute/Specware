/*
 * XModelTree.java
 *
 * Created on November 27, 2002, 9:21 AM
 */

package edu.kestrel.graphs;

import edu.kestrel.graphs.spec.*;
import edu.kestrel.graphs.event.*;
import edu.kestrel.graphs.io.*;
import javax.swing.event.*;
import javax.swing.tree.*;
import javax.swing.*;
import java.io.*;
import java.awt.event.*;
import java.util.*;

/**
 * The class implements a tree view panels for ModelContainerNodes.
 * @author  ma
 */
public class XModelTree extends JTree implements TreeModelListener, XGraphDisplayValueListener, MouseListener {
    
    protected TreeModel tm = null;
    protected XGraphApplication appl;
    
    protected TreePath[] savedExpandedPaths;
    
    /** Creates a new instance of XModelTree */
    public XModelTree(XGraphApplication appl, TreeModel tm) {
        super(tm);
        this.tm = tm;
        this.appl = appl;
        addMouseListener(this);
        setEditable(true);
        setShowsRootHandles(true);
        //appl.registerGraph(appl.getClipboard());
    }
    
    public String convertValueToText(Object value, boolean selected, boolean expanded, boolean leaf, int row, boolean hasFocus) {
        if (value instanceof ModelNode) {
            ModelNode mnode = (ModelNode)value;
            XGraphElement elem = mnode.getReprExemplar();
            if (elem instanceof XTextNode) {
                XTextNode tnode = (XTextNode)elem;
                //if (!tnode.isCollapsed()) {
                    return tnode.getCollapsedValue().toString();
                //}
            }
        }
        return super.convertValueToText(value, selected, expanded, leaf, row, hasFocus);
    }
    
    /** saves the currently expanded paths.
     */
    public void saveExpandedPaths() {
        ArrayList paths = new ArrayList();
        Enumeration iter = getExpandedDescendants(new TreePath(getModel().getRoot()));
        if (iter != null) {
            while(iter.hasMoreElements()) {
                TreePath p = (TreePath)iter.nextElement();
                paths.add(p);
            }
        }
        savedExpandedPaths = new TreePath[paths.size()];
        paths.toArray(savedExpandedPaths);
    }
    
    public void restoreExpandedPaths() {
        if (savedExpandedPaths == null) return;
        for(int i=0;i<savedExpandedPaths.length;i++) {
            setExpandedState(savedExpandedPaths[i],true);
        }
    }
    
    /** <p>Invoked after a node (or a set of siblings) has changed in some
     * way. The node(s) have not changed locations in the tree or
     * altered their children arrays, but other attributes have
     * changed and may affect presentation. Example: the name of a
     * file has changed, but it is in the same location in the file
     * system.</p>
     * <p>To indicate the root has changed, childIndices and children
     * will be null. </p>
     *
     * <p>Use <code>e.getPath()</code>
     * to get the parent of the changed node(s).
     * <code>e.getChildIndices()</code>
     * returns the index(es) of the changed node(s).</p>
     *
     */
    public void treeNodesChanged(TreeModelEvent e) {
        Dbg.pr("treeNodesChanged...");
        //treeChanged(e);
        for(int i=0;i<e.getChildren().length;i++) {
            Object obj = e.getChildren()[i];
            Object val = getCellEditor().getCellEditorValue();
            if (val != null) {
                if (obj instanceof ModelElement) {
                    ModelElement elem = (ModelElement) obj;
                    Dbg.pr(" new value: "+val);
                    elem.setValue(val);
                    elem.sync();
                }
                else if (obj instanceof XGraphDisplayTreeNode) {
                    XGraphDisplayTreeNode tn = (XGraphDisplayTreeNode)obj;
                    XGraphDisplay graph = tn.getGraph();
                    graph.setValue(val);
                }
            }
        }
    }
    
    /** <p>Invoked after nodes have been inserted into the tree.</p>
     *
     * <p>Use <code>e.getPath()</code>
     * to get the parent of the new node(s).
     * <code>e.getChildIndices()</code>
     * returns the index(es) of the new node(s)
     * in ascending order.</p>
     *
     */
    public void treeNodesInserted(TreeModelEvent e) {
        Dbg.pr("treeNodesInserted: "+e);
        treeChanged(e);
        if (e != null) {
            Dbg.pr("expanding path of inserted node...");
            expandPath(e.getTreePath());
        }
    }
    
    /** <p>Invoked after nodes have been removed from the tree.  Note that
     * if a subtree is removed from the tree, this method may only be
     * invoked once for the root of the removed subtree, not once for
     * each individual set of siblings removed.</p>
     *
     * <p>Use <code>e.getPath()</code>
     * to get the former parent of the deleted node(s).
     * <code>e.getChildIndices()</code>
     * returns, in ascending order, the index(es)
     * the node(s) had before being deleted.</p>
     *
     */
    public void treeNodesRemoved(TreeModelEvent e) {
        Dbg.pr("treeNodesRemoved...");
        treeChanged(e);
    }
    
    /** <p>Invoked after the tree has drastically changed structure from a
     * given node down.  If the path returned by e.getPath() is of length
     * one and the first element does not identify the current root node
     * the first element should become the new root of the tree.<p>
     *
     * <p>Use <code>e.getPath()</code>
     * to get the path to the node.
     * <code>e.getChildIndices()</code>
     * returns null.</p>
     *
     */
    public void treeStructureChanged(TreeModelEvent e) {
        Dbg.pr("treeStructureChanged...");
        //treeChanged(e);
        if (e != null) {
            expandPath(e.getTreePath());
            setSelectionPath(e.getTreePath());
        }
    }
    
    public void treeChanged(TreeModelEvent e) {
        Dbg.pr("tree changed.");
        TreeModel tm = getModel();
        //setModel(null);
        //setModel(tm);
    }
    
    public void graphValueChanged(XGraphDisplay graph, Object oldvalue, Object newvalue) {
        treeChanged(null);
    }
    
    
    /** returns a popup menu depending on the type of obj.
     */
    protected JPopupMenu getPopupMenu(Object obj, final TreePath path) {
        JPopupMenu m = new JPopupMenu();
        JMenuItem item;
        if (obj instanceof Storable) {
            if (obj instanceof XGraphDisplayTreeNode) {
                final XGraphDisplay graph = ((XGraphDisplayTreeNode)obj).getGraph();
                item = new JMenuItem("open");
                item.addActionListener(new ActionListener() {
                    public void actionPerformed(ActionEvent e) {
                        appl.getDesktop().ensureDisplayGraphAction(graph);
                    }
                });
                m.add(item);
                item = new JMenuItem("close");
                item.addActionListener(new ActionListener() {
                    public void actionPerformed(ActionEvent e) {
                        appl.getDesktop().closeGraphAction(graph);
                    }
                });
                m.add(item);
                item = new JMenuItem("rename");
                item.addActionListener(new ActionListener() {
                    public void actionPerformed(ActionEvent e) {
                        startEditingAtPath(path);
                        //folder.addSubfolder(subfolder);
                    }
                });
                m.add(item);
            } else {
                if (obj instanceof ModelElement) {
                    final ModelElement melem = (ModelElement) obj;
                    if (!(obj instanceof RootContainerNode)) {
                        item = new JMenuItem("rename");
                        item.addActionListener(new ActionListener() {
                            public void actionPerformed(ActionEvent e) {
                                startEditingAtPath(path);
                            }
                        });
                        m.add(item);
                        item = new JMenuItem("remove model element");
                        item.addActionListener(new ActionListener() {
                            public void actionPerformed(ActionEvent e) {
                                String msg = "Do you really want to remove the model element \""+melem+"\"? ";
                                //msg += "Note, that all descendant of the node and all representations will be removed as well.";
                                int answ = JOptionPane.showConfirmDialog(XModelTree.this,msg,"remove model element",JOptionPane.YES_NO_OPTION);
                                if (answ == JOptionPane.YES_OPTION) {
                                    melem.removeModelElement(appl);
                                }
                                //folder.addSubfolder(subfolder);
                            }
                        });
                        m.add(item);
                        item = new JMenuItem("copy");
                        item.addActionListener(new ActionListener() {
                            public void actionPerformed(ActionEvent e) {
                                appl.clearClipboard();
                                XGraphDisplay clipboard = appl.getClipboard();
                                appl.insertModelElementsIntoGraph(clipboard, new ModelElement[]{melem});
                            }
                        });
                        //m.add(item);
                    }
                    if (obj instanceof Folder) {
                        final Folder folder = (Folder) obj;
                        item = new JMenuItem("new folder");
                        item.addActionListener(new ActionListener() {
                            public void actionPerformed(ActionEvent e) {
                                Folder subfolder = new Folder(folder);
                                //folder.addSubfolder(subfolder);
                            }
                        });
                        m.add(item);
                        item = new JMenuItem("adopt selected node(s)");
                        item.addActionListener(new ActionListener() {
                            public void actionPerformed(ActionEvent e) {
                                TreePath[] sel = getSelectionPaths();
                                if (sel != null) {
                                    for(int i=0;i<sel.length;i++) {
                                        TreePath p = sel[i];
                                        Object obj = p.getLastPathComponent();
                                        Dbg.pr("adding child "+obj);
                                        if (obj instanceof ModelContainerNode) {
                                            ModelContainerNode mnode = (ModelContainerNode) obj;
                                            try {
                                                folder.addChild(mnode);
                                            } catch (Exception me) {
                                                JOptionPane.showMessageDialog(XModelTree.this,me.getMessage(),"error",JOptionPane.ERROR_MESSAGE);
                                            }
                                        }
                                    }
                                }
                                //folder.addSubfolder(subfolder);
                            }
                        });
                        m.add(item);
                    }
                }
            }
            final Storable elem = (Storable) obj;
            final String elemfilename = elem.toString()+".xml";
            item = new JMenuItem("save to \""+elemfilename+"\"...");
            item.addActionListener(new ActionListener() {
                public void actionPerformed(ActionEvent e) {
                    String xml = appl.toXml(elem);
                    String filename = elemfilename;
                    try {
                        PrintStream ps = new PrintStream(new FileOutputStream(filename),true);
                        ps.print(xml);
                        ps.close();
                        System.out.println("file "+filename+" written.");
                    } catch (IOException ex) {
                        System.err.println(ex.getMessage());
                    }
                }
            });
            m.add(item);
        } else {
            item = new JMenuItem("refresh");
            item.addActionListener(new ActionListener() {
                public void actionPerformed(ActionEvent e) {
                    appl.reloadTreeModel();
                }
            });
            m.add(item);
        }
        return m;
    }
    
    
    /** Invoked when the mouse button has been clicked (pressed
     * and released) on a component.
     *
     */
    public void mouseClicked(MouseEvent e) {
    }
    
    /** Invoked when the mouse enters a component.
     *
     */
    public void mouseEntered(MouseEvent e) {
    }
    
    /** Invoked when the mouse exits a component.
     *
     */
    public void mouseExited(MouseEvent e) {
    }
    
    /** Invoked when a mouse button has been pressed on a component.
     *
     */
    public void mousePressed(MouseEvent e) {
        int x = e.getX(), y = e.getY();
        TreePath p = getClosestPathForLocation(x,y);
        Object obj = p.getLastPathComponent();
        Dbg.pr("clicked at object of class "+obj.getClass().getName());
        if (SwingUtilities.isRightMouseButton(e) || e.isControlDown()) {
            JPopupMenu m = getPopupMenu(obj,p);
            if (m != null) {
                m.show(this,x,y);
            }
        }
    }
    
    /** Invoked when a mouse button has been released on a component.
     *
     */
    public void mouseReleased(MouseEvent e) {
    }
    
}
