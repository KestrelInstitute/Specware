/*
 * XTreeModelEvent.java
 *
 * Created on December 3, 2002, 1:24 AM
 */

package edu.kestrel.graphs.event;

import edu.kestrel.graphs.*;
import edu.kestrel.graphs.spec.*;
import javax.swing.tree.*;
/**
 *
 * @author  ma
 */
public class XTreeModelEvent {
    
    final static public int NODES_CHANGED = 0;
    final static public int NODES_INSERTED = 1;
    final static public int NODES_REMOVED = 2;
    final static public int STRUCTURE_CHANGED = 3;
    
    protected ModelNode n;
    protected int[] childIndices;
    protected Object[] children;
    
    protected int type;
    
    /** Creates a new instance of XTreeModelEvent */
    public XTreeModelEvent(int type, ModelNode n, int[] childIndices, Object[] children) {
        this.n = n;
        this.childIndices = childIndices;
        this.children = children;
        this.type = type;
    }
    
    public XTreeModelEvent(int type, ModelNode n) {
        this.n = n;
        this.type = type;
        this.childIndices = new int[]{};
        this.children = new Object[]{};
    }
    
    public XTreeModelEvent(XGraphApplication appl) {
        n = appl.getModelNode();
        childIndices = new int[] {};
        children = new Object[] {};
        type = STRUCTURE_CHANGED;
    }
    
    public void fireEvent(XGraphApplication appl) {
        if (appl == null) return;
        appl.cleanupGraphDisplays();
        if (type == NODES_CHANGED)
            appl.treeNodesChanged(n,childIndices,children);
        else if (type == NODES_INSERTED)
            appl.treeNodesInserted(n,childIndices,children);
        else if (type == NODES_REMOVED)
            appl.treeNodesRemoved(n,childIndices,children);
        else 
            appl.treeStructureChanged(n,childIndices,children);
    }
    
}
