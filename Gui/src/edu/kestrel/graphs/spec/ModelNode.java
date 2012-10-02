/*
 * ModelNode.java
 *
 * Created on November 26, 2002, 4:49 PM
 */

package edu.kestrel.graphs.spec;

import edu.kestrel.graphs.*;
import edu.kestrel.graphs.event.*;
import edu.kestrel.graphs.io.*;
import javax.swing.tree.*;
import java.util.*;
import java.awt.*;
/**
 * Instances of this class represent the logical counterpart to a graphically displayed node. A model node may have 0..n
 * representations in multiple graph displays. The representations are all instances of class XNode. The reason for introducing
 * another level of model/view/controller is that the JGraph models are not "clean" enough; they are "polluted" with graphical
 * information. The existence of two representations of one model node in one graph display is also not supported by the JGraph
 * library, but is possible with this extension. Furthermore, the fact that container nodes can be "collapsed", i.e. that they
 * hide their children is not supported by the model concept of JGraph.
 * @author  ma
 */
public class ModelNode extends ModelElement implements MutableTreeNode {
    
    /** vector containing the outgoing edges as instances of <code>ModelEdge</code>
     */
    protected Vector outgoingEdges;
    /** vector containing the incoming edges as instances of <code>ModelEdge</code>
     */
    protected Vector incomingEdges;
    
    /** the parent of this node.
     */
    protected ModelContainerNode parent;
    
    /** Creates a new instance of ModelNode */
    public ModelNode() {
        super();
        initModelNode();
    }
    
    protected void initModelNode() {
        incomingEdges = new Vector();
        outgoingEdges = new Vector();
    }
    
    /** adds an representation element an fires a model change.
     */
    public void addRepr(XGraphElement repr) {
        super.addRepr(repr);
        fireModelChange(new XTreeModelEvent(XTreeModelEvent.NODES_INSERTED,this));
    }
    
    /** sets this node as model node of all representations.
     */
    protected void setModelElementOfReprs() {
        Enumeration iter = reprs.elements();
        while(iter.hasMoreElements()) {
            XNode node = (XNode) iter.nextElement();
            node.setModelNode(this);
        }
    }
    
    /** removes a representation elements and fires a model change.
     */
    public void removeRepr(XGraphDisplay graph, XGraphElement repr) {
        super.removeRepr(graph,repr);
        fireModelChange(new XTreeModelEvent(XTreeModelEvent.NODES_REMOVED,this));
    }
    
    /** sets the parent of this node; makes sure, that it is contained in the children list of the new parent.
     */
    public void setParent(ModelContainerNode newparent) throws ModelException {
        Dbg.pr("trying to set new parent for node "+this+": "+newparent+"...");
        if (parent != null) {
            if (parent.equals(newparent)) return;
            int ci = parent.getIndex(this);
            parent.removeChild(this);
            fireModelChange(new XTreeModelEvent(XTreeModelEvent.NODES_REMOVED,parent,new int[]{ci},new Object[]{this}));
        }
        parent = newparent;
        if (newparent != null) {
            if (!newparent.hasChild(this)) {
                newparent.addChild(this);
                int ci = newparent.getIndex(this);
                fireModelChange(new XTreeModelEvent(XTreeModelEvent.NODES_INSERTED,newparent, new int[]{ci}, new Object[]{this}));
            }
        }
        //fireModelChange(new XTreeModelEvent(XTreeModelEvent.STRUCTURE_CHANGED,this));
        Dbg.pr("new parent for node "+this+": "+parent);
    }
    
    public TreeNode getParent() {
        return parent;
    }
    
    /** passive operation, always called from ModelEdge.setTarget() */
    public void addIncomingEdge(ModelEdge edge) {
        if (!incomingEdges.contains(edge)) {
            incomingEdges.add(edge);
            Dbg.pr("incoming edge added to "+this);
        }
    }
    
    /** passive operation, always called from ModelEdge.setSource() */
    public void addOutgoingEdge(ModelEdge edge) {
        if (!outgoingEdges.contains(edge)) {
            outgoingEdges.add(edge);
            Dbg.pr("outgoing edge added to "+this);
        }
    }
    
    /** passive operation, always called from ModelEdge.setTarget() */
    public void removeIncomingEdge(ModelEdge edge) {
        incomingEdges.remove(edge);
        Dbg.pr("incoming edge removed from "+this);
    }
    
    /** passive operation, always called from ModelEdge.setSource() */
    public void removeOutgoingEdge(ModelEdge edge) {
        outgoingEdges.remove(edge);
        Dbg.pr("outgoing edge removed from "+this);
    }
    
    /** returns the edges that are connected with this model node and stay within the container given as parent node.
     */
    public ModelEdge[] getConnectedEdges(ModelContainerNode parent) {
        ArrayList elist = new ArrayList();
        Enumeration iter0 = incomingEdges.elements();
        while (iter0.hasMoreElements()) {
            ModelEdge e = (ModelEdge)iter0.nextElement();
            ModelNode otherEnd = e.getTarget();
            if (parent.isNodeDescendant(otherEnd)) {
                elist.add(e);
            }
        }
        Enumeration iter1 = incomingEdges.elements();
        while (iter1.hasMoreElements()) {
            ModelEdge e = (ModelEdge)iter1.nextElement();
            ModelNode otherEnd = e.getSource();
            if (parent.isNodeDescendant(otherEnd)) {
                elist.add(e);
            }
        }
        ModelEdge[] res = new ModelEdge[elist.size()];
        elist.toArray(res);
        return res;
    }
    
    /** removes the model element.  */
    public void removeModelElement() {
        try {
            setParent(null);
        } catch (ModelException me) {}
    }
    
    protected void fireModelChange(XTreeModelEvent e) {
        if (parent != null) {
            parent.fireModelChange(e);
        }
    }
    
    
    /** returns the path of the node wrt. to the toplevel model node.
     */
    public TreePath getPath() {
        if (parent == null) {
            return new TreePath(this);
        } else {
            TreePath p = parent.getPath();
            return p.pathByAddingChild(this);
        }
    }
    
    /** sets the value of this node; if parameter force is false, the method maybeModifyChildsValue() of the parent node
     * (if it exists) is called to prevent name clashes.
     */
    public void setValue(Object value, boolean force) {
        super.setValue(value);
        if (!force) {
            TreeNode p = getParent();
            if (p instanceof ModelContainerNode) {
                ((ModelContainerNode)p).maybeModifyNewChildsValue(this,false);
            }
        }
        fireModelChange(new XTreeModelEvent(XTreeModelEvent.NODES_CHANGED,this));
    }
    
    public void setValue(Object value) {
        setValue(value,false);
    }
    
    /** Returns the children of the receiver as an <code>Enumeration</code>.
     *
     */
    public Enumeration children() {
        return null;
    }
    
    /** Returns true if the receiver allows children.
     *
     */
    public boolean getAllowsChildren() {
        return false;
    }
    
    /** Returns the child <code>TreeNode</code> at index
     * <code>childIndex</code>.
     *
     */
    public TreeNode getChildAt(int childIndex) {
        return null;
    }
    
    /** Returns the number of children <code>TreeNode</code>s the receiver
     * contains.
     *
     */
    public int getChildCount() {
        return 0;
    }
    
    /** Returns the index of <code>node</code> in the receivers children.
     * If the receiver does not contain <code>node</code>, -1 will be
     * returned.
     *
     */
    public int getIndex(TreeNode node) {
        return -1;
    }
    
    /** Returns true if the receiver is a leaf.
     *
     */
    public boolean isLeaf() {
        return true;
    }
    
    /** Adds <code>child</code> to the receiver at <code>index</code>.
     * <code>child</code> will be messaged with <code>setParent</code>.
     *
     */
    public void insert(MutableTreeNode child, int index) {
    }
    
    /** Removes <code>node</code> from the receiver. <code>setParent</code>
     * will be messaged on <code>node</code>.
     *
     */
    public void remove(MutableTreeNode node) {
    }
    
    /** Removes the child at <code>index</code> from the receiver.
     *
     */
    public void remove(int index) {
    }
    
    /** Removes the receiver from its parent.
     *
     */
    public void removeFromParent() {
        try {
            setParent((ModelContainerNode)null);
        } catch (ModelException me) {}
    }
    
    /** Sets the parent of the receiver to <code>newParent</code>.
     *
     */
    public void setParent(MutableTreeNode newParent) {
        try {
            if (newParent instanceof ModelContainerNode)
                setParent((ModelContainerNode)newParent);
        } catch (ModelException me) {}
    }
    
    /** Resets the user object of the receiver to <code>object</code>.
     *
     */
    public void setUserObject(Object object) {
    }
    
    /** returns true if anotherNode is a descendant of this node; also returns true, if anotherNode is this node.
     */
    public boolean isNodeDescendant(ModelNode anotherNode) {
        if (equals(anotherNode)) return true;
        if (anotherNode == null) return false;
        TreeNode parent = anotherNode.getParent();
        if (parent instanceof ModelNode)
            return isNodeDescendant((ModelNode)parent);
        else
            // should not happen:
            return false;
    }
    
    /** inserts a freshly created representation element into the given graph.
     *
     */
    public XGraphElement insertIntoGraph(XGraphDisplay graph, XGraphElement elem, Map elemReprMap) {
        super.insertIntoGraph(graph,elem,elemReprMap);
        //XNode node = ((XNode)reprExemplar).cloneNode();
        XNode node = (XNode) elem;
        node.setModelNode(this);
        node.setSavedBounds(node.getCorrectedBounds(node.getSavedBounds()));
        node.setSaveViewData(false);
        Rectangle b = node.getCorrectedBounds(node.getSavedBounds());
        Dbg.pr("inserting node "+node+" into graph with bounds "+b+"...");
        graph.disableListener();
        graph.insertNode(node,b);
        graph.enableListener();
        addRepr(node);
        node.setSaveViewData(true);
        elemReprMap.put(this,node);
        return node;
    }
    
    /** selects the connected edges that must be inserted into the graph in the context of an insertIntoGraph operation.
     
    public void insertEdgesIntoGraph(XGraphDisplay graph, XNode node, Map elemReprMap) {
        Enumeration iter0 = outgoingEdges.elements();
        while(iter0.hasMoreElements()) {
            ModelEdge edge = (ModelEdge) iter0.nextElement();
            if (!elemReprMap.containsKey(edge)) {
                ModelNode otherEnd = edge.getTarget();
                if (otherEnd != null) {
                    if (elemReprMap.containsKey(otherEnd)) {
                        Dbg.pr("inserting edge "+edge+"...");
                        XEdge connEdge = node.getConnectedEdgeWithModelEdge(edge);
                        edge.insertIntoGraph(graph,connEdge,elemReprMap);
                    }
                }
            }
        }
        Enumeration iter1 = outgoingEdges.elements();
        while(iter1.hasMoreElements()) {
            ModelEdge edge = (ModelEdge) iter1.nextElement();
            if (!elemReprMap.containsKey(edge)) {
                ModelNode otherEnd = edge.getTarget();
                if (otherEnd != null) {
                    if (elemReprMap.containsKey(otherEnd)) {
                        Dbg.pr("inserting edge "+edge+"...");
                        XEdge connEdge = node.getConnectedEdgeWithModelEdge(edge);
                        edge.insertIntoGraph(graph,connEdge,elemReprMap);
                    }
                }
            }
        }
    }*/
    
    protected static String OutgoingEdge = "OutgoingEdge";
    protected static String IncomingEdge = "IncomingEdge";
    
    /** returns the element properties associated with this model node for use in io operations.
     */
    public ElementProperties getElementProperties(ReadWriteOperation wop) {
        ElementProperties props = super.getElementProperties(wop);
        props.setValueProperty(getValue());
        Enumeration iter1 = outgoingEdges.elements();
        while(iter1.hasMoreElements()) {
            ModelEdge edge = (ModelEdge)iter1.nextElement();
            props.addChildObjectAsReference(OutgoingEdge,edge);
        }
        Enumeration iter2 = incomingEdges.elements();
        while(iter2.hasMoreElements()) {
            ModelEdge edge = (ModelEdge)iter2.nextElement();
            props.addChildObjectAsReference(IncomingEdge,edge);
        }
        return props;
    }
    
    /** initializes a freshly created element of this class using the information stored in the given
     * ElementProperties instance. Used during io operations.
     */
    public void initFromElementProperties(ReadWriteOperation rwop, ElementProperties props) {
        Dbg.pr("{ initFromElementProperties("+this+")...");
        super.initFromElementProperties(rwop,props);
        //initModelNode();
        setValue(props.getValueProperty());
        final ModelNode thisnode = this;
        Dbg.pr("{ adding outgoing edges to model node "+this+"...");
        Enumeration iter0 = props.getChildObjectAsReferenceEnumeration(OutgoingEdge);
        while(iter0.hasMoreElements()) {
            String eid = (String) iter0.nextElement();
            Dbg.pr("{ adding outgoing edge "+eid+" to node "+this+"...");
            Storable eobj = rwop.getObjectForId(eid);
            if (eobj instanceof ModelEdge) {
                try {
                    ((ModelEdge)eobj).setSource(this);
                } catch (Exception me) {}
            }
            Dbg.pr("}");
        }
        Dbg.pr("}");
        Dbg.pr("{ adding incoming edges to model node "+this+"...");
        Enumeration iter1 = props.getChildObjectAsReferenceEnumeration(IncomingEdge);
        while(iter1.hasMoreElements()) {
            String eid = (String) iter1.nextElement();
            Dbg.pr("{ adding incoming edge "+eid+" to node "+this+"...");
            Storable eobj = rwop.getObjectForId(eid);
            if (eobj instanceof ModelEdge) {
                try {
                    ((ModelEdge)eobj).setTarget(this);
                } catch (ModelException me) {}
            }
            Dbg.pr("}");
        }
        Dbg.pr("}");
        Dbg.pr("}");
    }
    
}
