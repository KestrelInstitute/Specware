package edu.kestrel.graphs;

import edu.kestrel.graphs.editor.*;
import edu.kestrel.graphs.spec.*;
import edu.kestrel.graphs.io.*;
import com.jgraph.graph.*;
import javax.swing.tree.TreeNode;
import java.awt.*;
import java.util.*;

/**
 * XNode is the topmost class for nodes in the graph. It defines a generic frame for sub classes which represent nodes with
 * a specific shape. See {@link edu.kestrel.graphs.XBoxNode} and {@link edu.kestrel.graphs.XEllipseNode} for example subclasses.
 */

public abstract class XNode extends DefaultGraphCell implements XGraphElement {
    
    /** the model node that is associated with this graphical node.
     */
    protected ModelNode modelNode = null;
    
    protected int defaultNumberOfPortsPerDimension = 6;
    
    protected XGraphDisplay graph;
    
    static int xnodeCnt = 0;
    protected int ID;
    
    protected static int nodeCnt = 0;
    
    /** stores the last parent after <code>detachFromParent</code> has been called.
     */
    protected XContainerNode lastParent = null;
    protected boolean viewWasVisible;
    //protected Rectangle lastParentsBounds = null;
    
    /** if this node is some inner node, and it being cloned into another graph display, this field holds
     * the "lost" parent.
     */
    protected XContainerNode lostParentAfterCloning = null;

    protected Dimension offsetToLastParent = null;

    protected boolean isEditable = true;
    
    protected Rectangle savedBounds;
    protected boolean saveViewData = true;
    
    public XNode() {
        this(null);
    }
    
    public XNode(String name) {
        super(name);
        setInitialValueIfNoValue();
        //setUserObject();
    }
    
    /*
    public XNode(ModelNode mnode) {
        super(mnode.getValue());
        setModelNode(mnode);
        setInitialValue();
    }
     */
    
    
    public void setGraph(XGraphDisplay graph) {
        this.graph = graph;
    }
    
    public XGraphDisplay getGraph() {
        return graph;
    }
    
    
    
    protected void init() {
        Dbg.pr("init node "+this+"...");
        lastParent = null;
        viewWasVisible = false;
        offsetToLastParent = null;
        removeAllChildren();
        isEditable = true;
        //Dbg.pr("end init node "+this);
    }
    
    public void setIsEditable(boolean b) {
        isEditable = b;
        if (getGraph() != null) {
            CellView cv = getGraph().getView().getMapping(this,false);
            if (cv instanceof XNodeView) {
                GraphConstants.setEditable(cv.getAttributes(),b);
            }
        }
    }
    
    public boolean isEditable() {
        return isEditable;
    }
    
    
    
    public void setID(int n) {
        ID = n;
    }
    
    public void setModelNode(ModelNode n) {
        modelNode = n;
    }
    
    /** sets the initial value of the node, if no value has been set.
     */
    protected void setInitialValueIfNoValue() {
        boolean hasValue = true;
        if (getUserObject() == null) {
            hasValue = false;
        } else {
            hasValue = !getUserObject().equals("");
        }
        if (!hasValue) {
            setInitialValue();
        }
    }
    
    /** sets some initial node value using a counter variable.
     */
    protected void setInitialValue() {
        setUserObject("N_"+(nodeCnt++));
    }
    
    /** returns the Model Node of this node; creates a new model node, if this hasn't done before.
     */
    
    public ModelNode getModelNode() {
        if (modelNode == null) {
            modelNode = createModelNode();
            modelNode.addFirstRepr(this);
        }
        return modelNode;
    }
    
    public ModelNode getModelNode(XGraphDisplay graph) {
        getModelNode();
        ModelContainerNode p = getModelParent(graph);
        try {
            modelNode.setParent(p);
        } catch (ModelException me) {/*ignore*/}
        return modelNode;
    }
    
    /** returns the parent node in the underlying model, if this node has a parent. If it is a root object in the
     * graph, then the model node of the graph is returned as model parent.
     */
    public ModelContainerNode getModelParent(XGraphDisplay graph) {
        XContainerNode p = getVirtualParentNode();
        if (p == null) {
            ModelNode mnode = getModelNode();
            if (mnode.getParent() instanceof ModelContainerNode) {
                return (ModelContainerNode) mnode.getParent();
            }
            return graph.getModelNode();
        }
        return (ModelContainerNode) p.getModelNode(graph);
    }
    
    /** creates the model node for this node; this method is used, if this node has been created without an
     * associated model node. It returns an instance of ModelNode; sub-classers can overwrite this method
     * to return instances of sub-classes of ModelNode.
     */
    public ModelNode createModelNode() {
        return new ModelNode();
    }
    
    /** returns the XEdge object that is connected to this node and has the given ModelEdge as its model element;
     * if no such edge is found, a copy of the reprExemplar of the given ModelEdge is returned.
     */
    public XEdge getConnectedEdgeWithModelEdge(ModelEdge medge) {
        XEdge[] edges = getEdges(INCOMING_AND_OUTGOING);
        for(int i=0;i<edges.length;i++) {
            ModelEdge cmedge = edges[i].getModelEdge();
            if (medge.equals(cmedge)) {
                Dbg.pr("XNode: getConnectedEdgeWithModeEdge("+medge+")="+edges[i]);
                return edges[i];
            }
        }
        Dbg.pr("XNode "+this+": no connected edge with ModelEdge "+medge+" found.");
        return (XEdge) medge.getReprExemplar().cloneGraphElement();
    }
    
    /** only used in Debug mode. */
    public void setUserObject() {
        if (Dbg.isDebug2())
            setUserObject("N"+String.valueOf(xnodeCnt++));
    }
    
    public String getName() {
        return (String) getUserObject();
    }
    
    public void setUserObject(Object obj) {
        super.setUserObject(obj);
        if (modelNode != null)
            modelNode.setValue(obj);
    }
    
    /** returns the y-values for the given x value; this method implements the equation of the node
     * shape. For example, for a rectangular shape the result of getYValues(x) would be y0 and y1,
     * where the point (x,y0) lies on the top margin of the box, and (x,y1) on the bottom margin.
     */
    protected abstract double[] getYValues(double x);
    /** @see edu.kestrel.graphs.XNode#getYValues(double) */
    protected abstract double[] getXValues(double y);
    
    /** returns the number of ports for each dimension. For example, if this method returns 10 for a
     * rectangular shaped node, then 10 ports will be created on each side of the rectangle.
     */
    protected abstract int getPortsPerDimension();
    
    static int portCnt = 0;
    
    /** this methods adds ports to the node using the methods getYValues, getXValues, and
     * getPortsPerDimension. The method iterates over x values between 0 and 1 using the
     * step size determined by 1/getPortsPerDimension(). For each x value it calls <code>getYValues(x)</code>
     * and inserts ports for all y's returned. Same for x and y exchanged using <code>getXValues</code>
     */
    protected void addPorts(GraphModel m) {
        int nports = getPortsPerDimension();
        if (nports == 0) return;
        double step = 1.0/nports;
        for(double x=0;x<=1;x+=step) {
            double[] yvalues = getYValues(x);
            for(int i=0;i<yvalues.length;i++) {
                double y = yvalues[i];
                addPort(m,x,y);
            }
        }
        for(double y=0;y<=1;y+=step) {
            double[] xvalues = getXValues(y);
            for(int i=0;i<xvalues.length;i++) {
                double x = xvalues[i];
                addPort(m,x,y);
            }
        }
    }
    
    /** adds a port at the given xoffset and yoffset to the node. xoffset and yoffset have values between 0 and 1,
     * specifying the offset relative to the node's borders. The user object of the port will be generated as
     * an instance of Point with <code>x=(int) (xoffset*p100)</code> and <code>(int) (yoffset*p100)</code>, where
     * <code>p100</code> is <code>GraphConstants.PERCENT</code>.
     */
    protected void addPort(GraphModel m, double xoffset, double yoffset) {
        Map viewMap = new Hashtable();
        int p100 = GraphConstants.PERCENT;
        int px = (int) (xoffset*p100);
        int py = (int) (yoffset*p100);
        Point userObject = new Point(px,py);
        DefaultPort port = new DefaultPort(userObject);
        add(port);
        Map map = GraphConstants.createMap();
        GraphConstants.setOffset(map, new Point(px, py));
        viewMap.put(port,map);
        Object[] cells = new Object[] {this};
        m.edit(null,viewMap,null,null);
        //m.insert(cells,null,null,viewMap);
    }
    
    public void insertHook(XGraphDisplay graph, XGraphElementView viewObject) {
        GraphModel m = graph.getModel();
        add(new DefaultPort());
        addPorts(m);
    }

    public void setBoundsHook(XGraphDisplay graph, XGraphElementView viewObject, Rectangle bounds) {
    }
    
    public boolean hasPorts() {
        Enumeration iter = children();
        while(iter.hasMoreElements()) {
            Object obj = iter.nextElement();
            if (obj instanceof Port)
                return true;
        }
        return false;
    }
    
    public DefaultPort getDefaultPort() {
        Enumeration iter = children();
        while(iter.hasMoreElements()) {
            Object obj = iter.nextElement();
            if (obj instanceof DefaultPort)
                return (DefaultPort) obj;
        }
        return null;
    }
    
    /** returns the port at the given point p where p is expected to be constructed a described in the <code>addPort</code> method.
     * returns null, if no such port is found.
     */
    public DefaultPort getPortAt(Object p, boolean returnDefaultPortIfNotFound) {
        Enumeration iter = children();
        while(iter.hasMoreElements()) {
            Object obj = iter.nextElement();
            if (obj instanceof DefaultPort) {
                DefaultPort port = (DefaultPort) obj;
                Object uobj = port.getUserObject();
                if (uobj == null) {
                    if (p == null)
                        return port;
                } else {
                    if (uobj.equals(p))
                        return port;
                }
            }
        }
        if (returnDefaultPortIfNotFound)
            return getDefaultPort();
        else
            return null;
    }
    
    /** remove this node and all its children (it ports) from the given model.
     */
    public void remove(GraphModel model) {
        java.util.List children = getChildren();
        ArrayList removees = new ArrayList();
        removees.add(this);
        if (children != null)
            for(int i=0;i<children.size();i++) {
                if (children.get(i) instanceof Port) {
                    removees.add(children.get(i));
                }
            }
        // remove connected edges
        XEdge[] edges = getEdges(INCOMING_AND_OUTGOING);
        for(int i=0;i<edges.length;i++) {
            removees.add(edges[i]);
        }
        model.remove(removees.toArray());
        if (modelNode != null)
            modelNode.removeRepr(this);
        setGraph(null);
    }
    
    public XNode[] getSiblings(GraphModel model) {
        ArrayList siblAL = new ArrayList();
        TreeNode parent = getParent();
        if (parent == null) {
            //Dbg.pr("is root object...");
            int rootCnt = model.getRootCount();
            for(int i=0;i<rootCnt;i++) {
                Object rootObj = model.getRootAt(i);
                if (rootObj instanceof XNode)
                    if (!rootObj.equals(this))
                        siblAL.add(rootObj);
            }
        } else {
            //Dbg.pr("is nested object...");
            int siblCnt = parent.getChildCount();
            for(int i=0;i<siblCnt;i++) {
                TreeNode sibl = parent.getChildAt(i);
                if (sibl instanceof XNode)
                    if (!sibl.equals(this))
                        siblAL.add(sibl);
            }
        }
        XNode[] res = new XNode[siblAL.size()];
        siblAL.toArray(res);
        return res;
    }
    
    /** returns the parent of this node, if it exists and if it's an instance of
     * <code>XContainerNode</code>
     */
    public XContainerNode getParentNode() {
        TreeNode parent = getParent();
        if (parent == null) return null;
        if (parent instanceof XContainerNode) {
            return (XContainerNode) parent;
        }
        return null;
    }
    
    /** returns the parent container node, if it exists; if not it checks whether the node is currently detached; if yes,
     * the parent node from which it is detached is returned; otherwise null.
     */
    public XContainerNode getVirtualParentNode() {
        XContainerNode pnode = getParentNode();
        if (pnode == null)
            pnode = lastParent;
        return pnode;
    }
    
    /** returns the "virtual" source port for the given edge, which is the port to which the edge is connected, if
     * it's source node is this node. This method is overwritten in XContainerNode to handle lifted connections.
     */
    public Object getVirtualSourceForEdge(XEdge edge) {
        XNode srcnode = edge.getSourceNode();
        if (equals(srcnode)) {
            return edge.getSource();
        }
        return null;
    }
    
    /** returns the "virtual" target port for the given edge, which is the port to which the edge is connected, if
     * it's target node is this node. This method is overwritten in XContainerNode to handle lifted connections.
     */
    public Object getVirtualTargetForEdge(XEdge edge) {
        XNode trgnode = edge.getTargetNode();
        if (equals(trgnode)) {
            return edge.getTarget();
        }
        return null;
    }
    
    
    public XContainerNode[] getAncestorNodes() {
        XContainerNode pnode = getParentNode();
        if (pnode == null) return new XContainerNode[] {};
        ArrayList anc = new ArrayList();
        while ((pnode = pnode.getParentNode()) != null) {
            anc.add(pnode);
        }
        XContainerNode[] res = new XContainerNode[anc.size()];
        anc.toArray(res);
        return res;
    }
    
    /** detaches the node from the given parent, if it's not a root node. As a side effect it sets the
     * field <code>lastParent</code> to the parent node, if it's not null.
     * @param graph the graph where everything is happening
     * @parem parent the container node from which the node is detached from; normally this is the current parent node
     * but it may also be another node, in case this node has never been a child of some container node. The latter case
     * is true, if the graph is being built up and child nodes are added to "collapsed" container nodes.
     * @param becomeRoot if set to true, the view of the node will be a new root node in the graph, if set to false
     * then the object is added to some "invisible" node, making it itself invisible.
     */
    public XContainerNode detachFromParent(XGraphDisplay graph, XContainerNode parent, boolean becomeRoot, boolean storeLastParent) {
        XContainerNode currentParent = getParentNode();
        if (currentParent != null)
            if (!currentParent.equals(parent)) {
                Dbg.pr("cannot attach node "+this+" from parent "+parent+"!");
                return null;
            }
        if (parent == null) return null;
        graph.disableListener();
        if (storeLastParent)
            lastParent = parent;
        Object newParent = (becomeRoot?null:new javax.swing.tree.DefaultMutableTreeNode("buffer"));
        CellView pcv = graph.getView().getMapping(parent,false);
        if (storeLastParent && pcv != null) {
            //lastParentsBounds = new Rectangle(cv.getBounds());
        }
        ParentMap pm = new ParentMap();
        pm.addEntry(this,newParent);
        graph.getModel().edit(null,null,pm,null);
        if (!becomeRoot) {
            CellView cv = graph.getView().getMapping(this,false);
            if (cv != null) {
                if (storeLastParent && (pcv != null)) {
                    Rectangle childBounds = cv.getBounds();
                    Rectangle parentBounds = pcv.getBounds();
                    offsetToLastParent = new Dimension(childBounds.x-parentBounds.x, childBounds.y-parentBounds.y);
                }
                Map viewMap = new Hashtable();
                Map map = GraphConstants.createMap();
                viewWasVisible = GraphConstants.isVisible(cv.getAttributes());
                GraphConstants.setVisible(map,false);
                viewMap.put(cv,map);
                graph.getView().edit(viewMap);
            }
        }
        Dbg.pr("detaching node "+this+" with offsetToLastParent="+offsetToLastParent);
        graph.enableListener();
        return parent;
    }
    
    /** calls <code>detachFromParent(graph,false)</code>
     */
    public void detachFromParent(XGraphDisplay graph, XContainerNode parent) {
        detachFromParent(graph,parent,false,true);
    }
    
    /** detached the node from its current parent; become either a root object or invisible.
     */
    public void detachFromParent(XGraphDisplay graph, boolean becomeRoot) {
        detachFromParent(graph,getParentNode(),becomeRoot,true);
    }
    
    /** detached the node from its current parent.
     */
    public void detachFromParent(XGraphDisplay graph) {
        XContainerNode parent = getParentNode();
        detachFromParent(graph,parent);
    }
    
    /** inserts the node as root object without storing its last parent.
     */
    public void insertAsRootObject(XGraphDisplay graph) {
        XContainerNode parent = getParentNode();
        detachFromParent(graph,parent,true,false);
    }
    
    /** reattaches the node to the parent node it has been detached from with <code>detachFromParent</code>.
     * @param graph the graph in which the action takes place
     * @param lastParentsNewBounds the new bounds of the last parents; this will be used to compute the suitable
     * translate offset for the node.
     */
    public void reAttachToLastParent(XGraphDisplay graph, Rectangle lastParentsNewBounds) {
        if (lastParent == null) return;
        graph.disableListener();
        Dbg.pr("reattaching node "+this+" to last parent "+lastParent+"...");
        //CellView cv = graph.getView().getMapping(lastParent,false);
        //Rectangle lastParentsNewBounds = null;
        //if (cv != null)
        //    lastParentsNewBounds = new Rectangle(cv.getBounds());
        /*
        if (lastParentsBounds != null && lastParentsNewBounds != null) {
            dx = lastParentsNewBounds.x - lastParentsBounds.x;
            dy = lastParentsNewBounds.y - lastParentsBounds.y;
        }
         **/
        Dbg.pr("   offsetToLastParent="+offsetToLastParent);
        Dbg.pr("   lastParentsNewBounds="+lastParentsNewBounds);
        ParentMap pm = new ParentMap();
        pm.addEntry(this,lastParent);
        graph.getModel().edit(null,null,pm, null);
        //if (dx != 0 || dy != 0) {
        CellView thisview = graph.getView().getMapping(this,false);
        if (thisview != null) {
            Rectangle currentBounds = thisview.getBounds();
            int newx = lastParentsNewBounds.x + offsetToLastParent.width;
            int newy = lastParentsNewBounds.y + offsetToLastParent.height;
            int dx = newx - currentBounds.x;
            int dy = newy - currentBounds.y;
            if (dx != 0 || dy != 0) {
                graph.getXGraphView().translateViewsInGroup(new CellView[]{thisview},dx,dy);
            }
        }
        //Dbg.pr("node "+this+" translated: ("+dx+","+dy+")");
        //}
        // restore previous visibility
        CellView cv = graph.getView().getMapping(this,false);
        if (cv != null) {
            Map viewMap = new Hashtable();
            Map map = GraphConstants.createMap();
            GraphConstants.setVisible(map,viewWasVisible);
            viewMap.put(cv,map);
            graph.getView().edit(viewMap);
        }
        lastParent = null;
        offsetToLastParent = null;
        graph.enableListener();
    }
    
    /** returns true, if the node is currently detached from its parent. */
    public boolean isDetached() {
        return lastParent != null;
    }
    
    /** @param recursive if true, then this method returns true if this node or one of its ancestors is detached; if
     * set to false, this method returns true, only if this node is detached.
     */
    public boolean isDetached(boolean recursive) {
        if (isDetached()) return true;
        if (!recursive) {
            return false;
        }
        XContainerNode pnode = getParentNode();
        if (pnode == null) return false;
        return pnode.isDetached(true);
    }
    
    /** constant used in <code>getEdges</code> */
    final public static int INCOMING_AND_OUTGOING = 0;
    /** constant used in <code>getEdges</code> */
    final public static int ONLY_OUTGOING = 1;
    /** constant used in <code>getEdges</code> */
    final public static int ONLY_INCOMING = 2;
    
    /** returns all edges that have this node as its source and/or target depending on the
     * <code>whichones</code> parameter, which must be one of
     * <code>INCOMING_AND_OUTGOING</code>,
     * <code>ONLY_OUTGOING</code>, or
     * <code>ONLY_INCOMING</code>
     */
    public XEdge[] getEdges(int whichones) {
        ArrayList res = new ArrayList();
        Enumeration iter = children();
        while(iter.hasMoreElements()) {
            Object child = iter.nextElement();
            if (child instanceof Port) {
                Port port = (Port) child;
                Iterator iter1 = port.edges();
                while(iter1.hasNext()) {
                    Object edge = iter1.next();
                    if (edge instanceof XEdge) {
                        if (!res.contains(edge)) {
                            if (whichones == INCOMING_AND_OUTGOING) {
                                res.add(edge);
                            }
                            else if (whichones == ONLY_OUTGOING && ((XEdge)edge).getSource().equals(port)) {
                                res.add(edge);
                            }
                            else if (whichones == ONLY_INCOMING && ((XEdge)edge).getTarget().equals(port)) {
                                res.add(edge);
                            }
                        }
                    }
                }
            }
        }
        XEdge[] edges = new XEdge[res.size()];
        res.toArray(edges);
        return edges;
    }
    
    
    /** returns the Least Common Ancestor of this node and the node given as argument; if they don't share a common ancestor,
     * null is returned. */
    public XContainerNode getLeastCommonAncestor(XNode node) {
        XContainerNode pp;
        if (this instanceof XContainerNode) {
            pp = (XContainerNode) this;
        } else {
            pp = getParentNode();
            if (pp == null) return null;
        }
        while (!pp.isNodeDescendant(node)) {
            pp = pp.getParentNode();
            if (pp == null) return null;
        }
        return pp;
    }
    
    /** returns the nesting level of the current node.
     * @return 0 means the node is a root node, 1 means the node is direct child of a root node, etc.
     */
    public int getNestingLevel() {
        int l = -1;
        XNode n = this;
        do {
            n = n.getParentNode();
            l++;
        } while (n != null);
        return l;
    }
    
    
    /** returns a cloned object of this node; removes all children from the clone.
     */
    public XNode cloneNode() {
        Dbg.pr("cloning XNode "+this+"...");
        XNode node = (XNode) clone();
        //node.setUserObject(getUserObject().toString()+"'");
        node.init();
        //Dbg.pr("cloneNode: "+this+" -> "+node);
        return node;
    }
    
    /** calls cloneNode to create a clone of this node.
     */
    public XGraphElement cloneGraphElement() {
        return cloneNode();
    }
    
    public Object cloneUserObject() {
        if (getUserObject() instanceof XGraphCellEditor.MultiLineUserObject) {
            return ((XGraphCellEditor.MultiLineUserObject)getUserObject()).createClone();
        }
        return super.cloneUserObject();
    }
    
    /** performs the necessary actions after the cell has been cloned.
     * @param tgraph the graph display that will contain the cloned element
     */
    public void cloneHook(XCloneManager mgr, Object original) {
        //Dbg.pr("cloneHook: node "+this);
        Map cellMap = mgr.getCellMap();
        if (lastParent != null) {
            // node is detached
            if (cellMap.containsKey(lastParent)) {
                Object obj = cellMap.get(lastParent);
                if (obj instanceof XContainerNode) {
                    //Dbg.pr("  exchanging lastParent to be "+obj);
                    lastParent = (XContainerNode) obj;
                } else
                    throw new IllegalArgumentException("cloned parent is not a container node?!");
            }
            offsetToLastParent = new Dimension(offsetToLastParent);
            //Dbg.pr("  lastParentsBounds of clone: "+lastParentsBounds);
        } else {
            if (mgr.isCloneOperation()) {
                XContainerNode parent = getParentNode();
                if (parent == null) {
                    boolean parentFound = false;
                    if (lostParentAfterCloning != null) {
                        CellView cv = mgr.getDestGraph().getView().getMapping(lostParentAfterCloning,false);
                        if (cv != null) {
                            parentFound = true;
                            lostParentAfterCloning.addChildNodes(mgr.getDestGraph(),new XNode[] {this});
                            lostParentAfterCloning = null;
                        } else {
                            remove(mgr.getDestGraph().getModel());
                            throw new IllegalArgumentException("Node "+this+" cannot be inserted into this graph.");
                        }
                    }
                    //Dbg.pr("parent of cloned node "+this+" is null.");
                    if (!parentFound) {
                        // check whether we have to add the clone as child of the original's parent
                        if (original instanceof XNode) {
                            XNode onode = (XNode) original;
                            XContainerNode origparent = onode.getParentNode();
                            if (origparent != null) {
                                Dbg.pr("setting parent of node "+this+" to "+origparent+"...");
                                if (mgr.isSameGraphOperation()) {
                                    origparent.addChildNodes(mgr.getDestGraph(),new XNode[]{this});
                                } else {
                                    lostParentAfterCloning = origparent;
                                }
                            }
                        }
                    }
                }
            }
        }
        setGraph(mgr.getDestGraph());
        mgr.cloneCellViews(original,this);
    }
    
    public abstract XGraphElementView createView(XGraphDisplay graph, CellMapper cm);
    
    /** returns the cell view of this container as XNodeView object. */
    public XNodeView getXNodeView(GraphView gview) {
        CellView cv = gview.getMapping(this,false);
        if (cv != null)
            if (cv instanceof XNodeView)
                return (XNodeView) cv;
        return null;
    }
    
    /** method to update the relevant data stored in the view object in this object. This method is called by the
     * view object whenever it is updated.
     *
     */
    public void updateViewData(XGraphElementView view) {
        if (!saveViewData) return;
        if (view instanceof XNodeView) {
            XNodeView nv = (XNodeView) view;
            //savedBounds = nv.getLastBounds();
            //Dbg.pr("XNode.updateViewData(): "+this+", savedBounds = "+savedBounds);
        }
    }
    
    public void setSavedBounds(Rectangle b) {
        if (!saveViewData) return;
        savedBounds = new Rectangle(b);
    }
    public Rectangle getSavedBounds() {return savedBounds;}
    
    public void setSaveViewData(boolean b) {
        Dbg.pr("node "+this+": setting saveViewData to "+b);
        saveViewData = b;
    }
    
    
    public Rectangle getCorrectedBounds(Rectangle bounds) {
        if (bounds == null) return null;
        Rectangle b = new Rectangle(bounds);
        Rectangle b0 = new Rectangle(bounds);
        if (isDetached(true)) {
            XContainerNode pnode = getVirtualParentNode();
            if (pnode != null) {
                Rectangle pbs = pnode.getSavedBounds();
                Rectangle pb = pnode.getCorrectedBounds(pbs);
                //Dbg.pr("pbs="+pbs+", pb="+pb);
                if (pb != null) {
                    if (isDetached()) {
                        b.x = pb.x + offsetToLastParent.width;
                        b.y = pb.y + offsetToLastParent.height;
                    } else {
                        // use the same offset as the parent
                        b.x += (pb.x-pbs.x);
                        b.y += (pb.y-pbs.y);
                    }
                }
            }
        }
        Dbg.pr("XNode "+this+": corrected bounds: "+(b.x-b0.x)+","+(b.y-b0.y));
        return b;
    }
    
    protected static String ModelNode = "ModelNode";
    protected static String Bounds = "Bounds";
    protected static String Graph = "Graph";
    protected static String IsEditable = "IsEditable";
    protected static String IncomingEdge = "IncomingEdge";
    protected static String OutgoingEdge = "OutgoingEdge";
    protected static String OffsetToLastParent = "OffsetToLastParent";
    
    /** returns the element properties object in the context of a write operation.
     */
    public ElementProperties getElementProperties(ReadWriteOperation rwop) {
        ElementProperties props = rwop.createElementProperties(this);
        props.setValueProperty(getUserObject());
        props.setBooleanProperty(IsEditable,isEditable());
        props.addChildObjectAsReference(ModelNode,getModelNode());
        if (getGraph() != null) {
            props.addChildObjectAsReference(Graph,getGraph());
        }
        Rectangle b = getCorrectedBounds(savedBounds);
        if (b != null) {
            props.setRectangleProperty(Bounds,b);
        }
        XEdge[] iedges = getEdges(ONLY_INCOMING);
        for(int i=0;i<iedges.length;i++) {
            props.addChildObjectAsReference(IncomingEdge,iedges[i]);
        }
        XEdge[] oedges = getEdges(ONLY_OUTGOING);
        for(int i=0;i<oedges.length;i++) {
            props.addChildObjectAsReference(OutgoingEdge,oedges[i]);
        }
        if (isDetached()) {
            props.setDimensionProperty(OffsetToLastParent,offsetToLastParent);
        }
        return props;
    }
    
    /** initializes a freshly created element of this class using the information stored in the given
     * ElementProperties instance. Used during io operations.
     */
    public void initFromElementProperties(ReadWriteOperation rwop, ElementProperties props) {
        setUserObject(props.getValueProperty());
        setIsEditable(props.getBooleanProperty(IsEditable));
        Dbg.pr("{ initFromElementPropterties for XNode "+this+"...");
        String graphid = (String) props.getChildObjectAsReference(Graph);
        Storable obj0 = rwop.getObjectForId(graphid);
        if (obj0 instanceof XGraphDisplay) {
            setGraph((XGraphDisplay)obj0);
        }
        Rectangle b = props.getRectangleProperty(Bounds);
        if (b != null) {
            setSavedBounds(b);
        }
        if (getGraph() != null) {
            //rwop.registerGraphDuringRead(getGraph());
            getGraph().disableListener();
            Dbg.pr("inserting node "+this+" into graph "+getGraph()+" with bounds "+b+"...");
            XNodeView cv = getGraph().insertNode(this,b);
            if (cv != null) {
                getGraph().getXGraphView().translateViewsInGroup(new CellView[]{cv},0,0);
            }
            getGraph().getXGraphView().updateAllPorts();
            getGraph().enableListener();
        }
        else {
            Dbg.pr("********* XNode "+this+": graph not set, couldn't insert into graph.");
        }
        // insert before setting the model node
        String modelnodeid = (String) props.getChildObjectAsReference(ModelNode);
        Storable obj1 = rwop.getObjectForId(modelnodeid);
        if (obj1 instanceof ModelNode) {
            setModelNode((ModelNode)obj1);
        }
        // reference the connected edges without doing any action here; the connection is done by the edge object itself
        {
            Enumeration iter = props.getChildObjectAsReferenceEnumeration(IncomingEdge);
            while(iter.hasMoreElements()) {
                String id = (String) iter.nextElement();
                rwop.getObjectForId(id);
            }
        } //
        {
            Enumeration iter = props.getChildObjectAsReferenceEnumeration(OutgoingEdge);
            while(iter.hasMoreElements()) {
                String id = (String) iter.nextElement();
                rwop.getObjectForId(id);
            }
        }
        Dbg.pr("}");
    }
    
}
