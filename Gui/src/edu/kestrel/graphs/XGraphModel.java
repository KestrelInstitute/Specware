/*
 * XGraphModel.java
 *
 * Created on October 31, 2002, 6:59 PM
 */

package edu.kestrel.graphs;

import edu.kestrel.graphs.spec.*;
import com.jgraph.graph.*;
import java.io.*;
import java.util.*;
import javax.swing.undo.*;
import javax.swing.tree.*;
import javax.swing.undo.UndoableEdit;
import java.awt.Rectangle;
import javax.swing.event.*;
import com.jgraph.JGraph;
import com.jgraph.event.*;


/**
 *
 * @author  ma
 */
public class XGraphModel extends DefaultGraphModel {
    
    /** Creates a new instance of XGraphModel */
    public XGraphModel() {
        super();
    }
    /**
     * Applies <code>cells</code> to the model. Returns
     * a parent map that may be used to undo this change.
     */
    protected ParentMap handleParentMap(ParentMap parentMap) {
        if (parentMap != null) {
            ParentMap undo = new ParentMap();
            Iterator it = parentMap.entries();
            while (it.hasNext()) {
                ParentMap.Entry entry = (ParentMap.Entry) it.next();
                MutableTreeNode child = (MutableTreeNode) entry.getChild();
                DefaultMutableTreeNode parent = (DefaultMutableTreeNode) entry.getParent();
                undo.addEntry(child, getParent(child));
                if (parent == null)
                    child.removeFromParent();
                else
                    parent.add(child);
                boolean isRoot = roots.contains(child);
                if (parent == null && !isRoot)
                    roots.add(child);
                else if (parent != null && isRoot)
                    roots.remove(child);
            }
            return undo;
        }
        return null;
    }
    
    /** (dis)connect edge */
    protected void connect(Object edge, Object port, boolean isSource, boolean remove) {
        if (Dbg.isDebug()) {
            String s0 = (remove?"removing":"adding");
            String s1 = (isSource?"source":"target");
            if (edge instanceof XEdge) {
                XEdge xedge = (XEdge) edge;
                String s2 = "???";
                if (port instanceof DefaultPort) {
                    DefaultPort p = (DefaultPort) port;
                    s2 = p.getParent().toString();
                }
                Dbg.pr(s0+" connection to "+s1+" node \""+s2+"\" for edge \""+edge+"\"...");
            }
        }
        super.connect(edge,port,isSource,remove);
        /*
        if (edge instanceof XEdge) {
            XEdge xedge = (XEdge) edge;
            XNode srcnode = xedge.getSourceNode();
            XNode trgnode = xedge.getTargetNode();
            XContainerNode cnode;
            if (srcnode == null && trgnode == null) return;
            if (srcnode == null)
                cnode = trgnode.getParentNode();
            else if (trgnode == null)
                cnode = srcnode.getParentNode();
            else
                cnode = srcnode.getLeastCommonAncestor(trgnode);
            if (cnode != null) {
                Dbg.pr("adding edge to container node "+cnode);
                cnode.add(xedge);
            }
        }
         */
    }
    
    
    
    public List getAllGraphElements(XContainerNode node) {
        ArrayList res = new ArrayList();
        if (node == null) {
            int rootCnt = getRootCount();
            for(int i=0;i<rootCnt;i++) {
                Object obj = getRootAt(i);
                if (obj instanceof XGraphElement) {
                    res.add(obj);
                    if (obj instanceof XContainerNode) {
                        List children = getAllGraphElements((XContainerNode)obj);
                        res.addAll(children);
                    }
                }
            }
        } else {
            Dbg.pr("getAllGraphElements: adding children of container node \""+node+"\"...");
        }
        return res;
    }
    
    public List getAllGraphElements() {
        return getAllGraphElements(null);
    }
    
    public void insert(Object[] roots, ConnectionSet cs, ParentMap pm, Map attributeMap) {
        Object[] newRootsArray;
        if (roots != null) {
            ArrayList newRoots = new ArrayList();
            List allNodes = getAllGraphElements();
            for(int i=0;i<roots.length;i++) {
                Dbg.pr("XGraphModel.insert(): inserting \""+roots[i]+"\"");
                if (!allNodes.contains(roots[i])) {
                    newRoots.add(roots[i]);
                } else {
                    Dbg.pr("skipping insertion of "+roots[i]+" of class "+roots[i].getClass().getName()+"; it's already inserted.");
                }
            }
            newRootsArray = newRoots.toArray();
        } else {
            newRootsArray = roots;
        }
        super.insert(newRootsArray,cs,pm,attributeMap);
    }
    
    public void edit(ConnectionSet cs, Map propertyMap, ParentMap pm, UndoableEdit[] e) {
        //System.out.println("editing...");
        super.edit(cs,propertyMap, pm, e);
    }
    
    /** removes all elements in the graph; throws a VetoException, if an element cannot be removed.
     */
    public void removeAll() throws VetoException {
        removeAll(false);
    }
    
    /** removes all cells from the model, if ignoreVetos is true, no check is made, whether the elements
     * in the graph can be removed.
     */
    public void removeAll(boolean ignoreVetos) throws VetoException {
        int cnt = getRootCount();
        ArrayList rem = new ArrayList();
        ArrayList rlist = new ArrayList();
        for(int i=0;i<cnt;i++) {
            Object obj = getRootAt(i);
            if (obj instanceof XGraphElement) {
                rlist.add(obj);
                //((XGraphElement)obj).remove(this);
            } else {
                rem.add(obj);
            }
        }
        remove(rem.toArray());
        removeNodes(rlist.toArray(),ignoreVetos);
        /*
        remove(rem.toArray());
        Iterator iter = rlist.iterator();
        while (iter.hasNext()) {
            XGraphElement elem = (XGraphElement)iter.next();
            Dbg.pr("trying to remove "+elem+"...");
            elem.remove(this);
        }
         */
    }
    
    /** removes the cells from the model; if instances of XGraphElements are among the cells, the remove method
     * of the element is called instead of directly removing the cell. It throws a veto exception, if an element
     * cannot be removed.
     */
    public void removeNodes(Object[] cells) throws VetoException {
        removeNodes(cells,false);
    }
    
    /** removes the cells from the model; if instances of XGraphElements are among the cells, the remove method
     * of the element is called instead of directly removing the cell. It only throws a veto exception in case an
     * element cannot be removed, if the ignoreVetos parameter is false.
     */
    public void removeNodes(Object[] cells, boolean ignoreVetos_) throws VetoException {
        boolean ignoreVetos = true;
        int cnt = cells.length;
        Dbg.pr("removing "+cnt+" cells...");
        boolean couldnotRemoveSome = false;
        boolean somethingRemoved = false;
        ArrayList rem = new ArrayList();
        for(int i=0;i<cnt;i++) {
            Object obj = cells[i];
            if (obj instanceof XGraphElement) {
                XGraphElement elem = (XGraphElement)obj;
                if (ignoreVetos || elem.removeOk(false)) {
                    elem.remove(this);
                    somethingRemoved = true;
                } else {
                    Dbg.pr("can not remove "+elem);
                    couldnotRemoveSome = true;
                }
            } else {
                rem.add(obj);
            }
        }
        remove(rem.toArray());
        if ((!ignoreVetos) && couldnotRemoveSome) {
            String s = (somethingRemoved?"some elements":"anything");
            throw new VetoException("Could not remove "+s+".");
        }
    }
    
    /** returns all "toplevel" cells of the model; this method takes care of "inner edges" which are also root cells for
     * jgraph; but they belong to some container node and will not be returned by this method.
     */
    public Object[] getRootCells() {
        int cnt = getRootCount();
        ArrayList roots = new ArrayList();
        for(int i=0;i<cnt;i++) {
            Object obj = getRootAt(i);
            if (obj instanceof XEdge) {
                if (!((XEdge)obj).isInnerEdge())
                    roots.add(obj);
            } else {
                roots.add(obj);
            }
        }
        return roots.toArray();
    }
    
    /** returns true, if this graph model is empty.
     */
    public boolean isEmpty() {
        int cnt = getRootCount();
        //Dbg.pr("root count="+cnt);
        return cnt == 0;
    }
    
}
