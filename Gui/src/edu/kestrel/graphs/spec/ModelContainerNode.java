/*
 * ModelContainerNode.java
 *
 * Created on November 26, 2002, 7:28 PM
 */

package edu.kestrel.graphs.spec;

import edu.kestrel.graphs.*;
import edu.kestrel.graphs.event.*;
import edu.kestrel.graphs.io.*;
import javax.swing.tree.*;
import javax.swing.event.*;
import java.util.*;
import java.awt.*;
/**
 * Instances of this class represent model nodes for graphical container nodes. It implements the TreeModel interface and can
 * be visualized using a JTree component.
 * @author  ma
 */
public class ModelContainerNode extends ModelNode {
    
    /** vector representing the subnodes of this container node; elements are of type ModelNode.
     */
    protected Vector children;
    
    protected Vector listeners;
    
    /** Creates a new instance of ModelContainerNode */
    public ModelContainerNode() {
        super();
        initModelContainerNode();
    }
    
    protected void initModelContainerNode() {
        children = new Vector();
        listeners = new Vector();
    }
    
    /** returns true if ModelNode n is accepted as subnode of this container node;
     * to be overwritten by subclassers.
     */
    public boolean acceptsChild(ModelNode n) {
        return true;
    }
    
    /** adds a child to this model container node at index. */
    public void addChild(ModelNode n, int index) throws ModelException {
        if (n == null) return;
        if (n.isNodeDescendant(this)) {
            throw new ModelException("Node \""+n+"\" cannot be a sub node of \""+this+"\", because its an ancestor node.");
        }
        if (!children.contains(n)) {
            if (!acceptsChild(n))
                throw new ModelException("Node \""+n+"\" cannot be sub node of \""+this+"\".");
            Dbg.pr("M: adding child "+n+" to container node "+this+"...");
            maybeModifyNewChildsValue(n,true);
            int index0 = (index>=0?index:getChildCount());
            children.add(index0,n);
            n.setParent(this);
            fireModelChange(new XTreeModelEvent(XTreeModelEvent.STRUCTURE_CHANGED,this));
            //fireModelChange(new XTreeModelEvent(XTreeModelEvent.NODES_INSERTED,this,new int[]{index0}, new Object[]{n}));
        }
    }
    
    /** adds a child at the end of the cildren list.
     */
    public void addChild(ModelNode n) throws ModelException {
        addChild(n,-1);
    }
    
    /** string to be used for making the name of the child unique.
     */
    protected String childNameAppend = "'";
    
    /** this method is called prior to actually adding the new child to the list of children and modifies or not modifies the
     * value of the new child so that is meets the requirements for children of this node. The implementation here checks
     * whether there is an existing child with the same value and if yes, "'"'s are added to the new child's value, so that
     * it will be unique.
     * @param newChild the new child that is going to be added
     * @param sync whether or not the sync method shall be called after a possible change of the value
     */
    public void maybeModifyNewChildsValue(ModelNode newChild, boolean sync) {
        Object childValue = newChild.getValue();
        if (childValue instanceof String) {
            String cval = (String)childValue;
            String cval0 = makeChildNameUnique(cval,newChild);
            if (!cval.equals(cval0)) {
                newChild.setValue(cval0,true);
                if (sync) newChild.sync();
            }
        }
    }
    
    private String makeChildNameUnique(String cval, ModelNode child) {
        Enumeration iter = children.elements();
        while(iter.hasMoreElements()) {
            Object obj = iter.nextElement();
            if (obj != null) {
                if (obj instanceof ModelNode) {
                    if (!obj.equals(child)) {
                        String sval = ((ModelNode)obj).getValue().toString();
                        if (sval.equals(cval)) {
                            String cval0 = cval+childNameAppend;
                            return cval0;
                        }
                    }
                }
            }
        }
        return cval;
    }
    
    /** returns the inner edges of this model container node. */
    public ModelEdge[] getInnerEdges() {
        return getConnectedEdges(this);
    }
    
    /** returns the edges that are connected with this model node and stay within the container given as parent node.
     */
    public ModelEdge[] getConnectedEdges(ModelContainerNode parent) {
        ModelEdge[] edges0 = super.getConnectedEdges(parent);
        ArrayList elist = new ArrayList();
        Enumeration iter = children();
        while (iter.hasMoreElements()) {
            Object obj = iter.nextElement();
            if (obj instanceof ModelNode) {
                ModelEdge[] chedges = ((ModelNode)obj).getConnectedEdges(parent);
                for(int i=0;i<chedges.length;i++) {
                    elist.add(chedges[i]);
                }
            }
        }
        for(int i=0;i<edges0.length;i++) {
            elist.add(edges0[i]);
        }
        ModelEdge[] res = new ModelEdge[elist.size()];
        elist.toArray(res);
        return res;
        
    }
    
    public void removeChild(ModelNode n) {
        children.remove(n);
        //fireModelChange(new XTreeModelEvent(XTreeModelEvent.NODES_REMOVED,this));
    }
    
    public void remove(MutableTreeNode n) {
        if (n instanceof ModelNode)
            removeChild((ModelNode)n);
    }
    
    public void remove(int index) {
        children.removeElementAt(index);
        fireModelChange(new XTreeModelEvent(XTreeModelEvent.NODES_REMOVED,this));
    }
    
    /** removes the container node its children and inner edges.
     */
    
    public void removeModelElement(XGraphApplication appl) {
        removeModelElement(appl,false);
    }
    
    /** removes the children and, if the removeOnlyChildren parameter is true, also the container node itself.
     * @param removeOnlyChildren if true, removes only the children of this node, otherwise, the container node itself
     * is also removed.
     */
    public void removeModelElement(XGraphApplication appl, boolean removeOnlyChildren) {
        Vector chlist = new Vector();
        Enumeration iter0 = children();
        while(iter0.hasMoreElements()) {
            Object obj = iter0.nextElement();
            chlist.add(obj);
        }
        Enumeration iter = chlist.elements();
        while(iter.hasMoreElements()) {
            Object obj = iter.nextElement();
            if (obj instanceof ModelElement) {
                ((ModelElement)obj).removeModelElement(appl);
            }
        }
        ModelEdge[] edges = getInnerEdges();
        for(int i=0;i<edges.length;i++) {
            edges[i].removeModelElement(appl);
        }
        if (!removeOnlyChildren)
            super.removeModelElement(appl);
    }
    
    public boolean hasChild(ModelNode n) {
        return children.contains(n);
    }
    
    /** returns the number of children of this container node.
     */
    public int getChildCount() {
        return children.size();
    }
    
    /** returns true for ModelContainerNodes.
     */
    public boolean isLeaf() {
        return false;
    }
    
    /** Messaged when the user has altered the value for the item identified
     * by <code>path</code> to <code>newValue</code>.
     * If <code>newValue</code> signifies a truly new value
     * the model should post a <code>treeNodesChanged</code> event.
     *
     * @param path path to the node that the user has altered
     * @param newValue the new value from the TreeCellEditor
     *
     */
    public void valueForPathChanged(TreePath path, Object newValue) {
    }
    
    /** Returns the children of the receiver as an <code>Enumeration</code>.
     *
     */
    public Enumeration children() {
        return children.elements();
    }
    
    /** Returns true if the receiver allows children.
     *
     */
    public boolean getAllowsChildren() {
        return true;
    }
    
    /** Returns the child <code>TreeNode</code> at index
     * <code>childIndex</code>.
     *
     */
    public TreeNode getChildAt(int childIndex) {
        return (TreeNode) children.elementAt(childIndex);
    }
    
    /** Returns the index of <code>node</code> in the receivers children.
     * If the receiver does not contain <code>node</code>, -1 will be
     * returned.
     *
     */
    public int getIndex(TreeNode node) {
        return children.indexOf(node);
    }
    
    /** Adds <code>child</code> to the receiver at <code>index</code>.
     * <code>child</code> will be messaged with <code>setParent</code>.
     *
     */
    public void insert(MutableTreeNode child, int index) {
        if (child instanceof ModelNode) {
            try {
                addChild((ModelNode)child,index);
            } catch (ModelException me) {}
        }
    }
    /** inserts a freshly created representation element into the given graph.
     *
     */
    public XGraphElement insertIntoGraph(XGraphDisplay graph, XGraphElement elem, Map elemReprMap) {
        XContainerNode cnode = (XContainerNode) super.insertIntoGraph(graph,elem,elemReprMap);
        //XContainerNode cnode = (XContainerNode)elem;
        cnode.setSaveViewData(false);
        //XContainerNode orig = (XContainerNode) reprExemplar;
        ArrayList clist = new ArrayList();
        Enumeration iter = children();
        while(iter.hasMoreElements()) {
            Object obj = iter.nextElement();
            if (obj instanceof ModelNode) {
                ModelNode chmnode = (ModelNode)obj;
                XNode chnode = cnode.getChildNodeWithModelNode(chmnode);
                XNode childnode = (XNode) chmnode.insertIntoGraph(graph,chnode,elemReprMap);
                clist.add(childnode);
            }
        }
        XNode[] childnodes = new XNode[clist.size()];
        clist.toArray(childnodes);
        cnode.addChildNodes(graph,childnodes);
        cnode.setSavedCollapsedBounds(cnode.getCorrectedBounds(cnode.getSavedCollapsedBounds()));
        cnode.restoreCollapsedBounds(graph);
        //cnode.restoreIsExpanded(graph);
        cnode.setSaveViewData(true);
        return cnode;
    }
    
    /** restores the expanded/collapsed state of the node as last step of an insert intoGraph operation.
     */
    public void restoreIsExpandedState(XGraphDisplay graph, XContainerNode cnode, Map elemReprMap) {
        if (elemReprMap.containsKey(this)) {
            //XContainerNode cnode = (XContainerNode) elemReprMap.get(this);
            cnode.restoreIsExpanded(graph);
        }
    }
    
    /** returns the element properties object in the context of a write operation.
     */
    public ElementProperties getElementProperties(ReadWriteOperation wop) {
        ElementProperties props = super.getElementProperties(wop);
        Enumeration iter = children();
        while(iter.hasMoreElements()) {
            Object obj = iter.nextElement();
            if (obj instanceof ModelNode) {
                props.addChildObject("ChildNode",(ModelNode)obj);
            }
        }
        return props;
    }
    
    /** initializes a freshly created element of this class using the information stored in the given
     * ElementProperties instance. Used during io operations.
     */
    public void initFromElementProperties(ReadWriteOperation rwop, ElementProperties props) {
        super.initFromElementProperties(rwop,props);
        initModelContainerNode();
        Dbg.pr("{adding child nodes for model container node "+this+"...");
        Enumeration iter = props.getChildObjectEnumeration("ChildNode");
        while(iter.hasMoreElements()) {
            ElementProperties cprops = (ElementProperties)iter.nextElement();
            Dbg.pr("adding child with id "+cprops.getId()+" to model container node "+this+"...");
            Storable cobj = rwop.getObjectForId(cprops.getId());
            Dbg.pr("...child "+cobj+" created for adding to model container node "+this+".");
            if (cobj instanceof ModelNode) {
                try {
                    addChild((ModelNode)cobj);
                } catch (ModelException me) {}
            }
        }
        Dbg.pr("}");
    }
    
}
