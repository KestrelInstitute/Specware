/*
 * XContainerNode.java
 *
 * Created on November 1, 2002, 6:53 PM
 */

package edu.kestrel.graphs;

import edu.kestrel.graphs.spec.*;
import edu.kestrel.graphs.io.*;
import com.jgraph.graph.*;
import javax.swing.tree.*;
import javax.swing.JLabel;
import java.lang.reflect.*;
import java.util.*;
import java.awt.*;

/**
 * This class is the superclass of all classes representing graphical nodes that can have sub nodes.
 * @author  ma
 */
public abstract class XContainerNode extends XNode {
    
    protected java.util.List detachedChildren;
    
    protected ConnectionSet liftedConnections;
    
    protected boolean isExpandable = true;
    
    protected Rectangle savedCollapsedBounds;
    
    protected boolean savedIsExpanded;
    
    /** Creates a new instance of XContainerNode */
    public XContainerNode() {
        super((String)null);
    }
    
    public XContainerNode(String name) {
        super(name);
    }
    
    protected void init() {
        super.init();
        detachedChildren = null;
        liftedConnections = null;
        isExpandable = true;
        isEditable = true;
        Dbg.pr("init "+this+": savedIsExpanded="+savedIsExpanded);
    }
    
    /** returns true, if the container has either "real" children or detached ones (which is the case, if it's collapsed
     * and has children.
     */
    public boolean hasChildren() {
        Enumeration iter = children();
        while (iter.hasMoreElements()) {
            Object obj = iter.nextElement();
            if (obj instanceof XNode)
                return true;
        }
        return (detachedChildren != null);
    }
    
    
    /** overwrites the method in XNode; returns an instance of ModelContainerNode.
     */
    public ModelNode createModelNode() {
        return new ModelContainerNode();
    }
    
    public ModelContainerNode getModelContainerNode() {
        return (ModelContainerNode)getModelNode();
    }
    
    
    /** returns the child node which has the given ModelNode as its model element; if no such node is found,
     * a copy of the model node's representation exemplar is returned.
     */
    public XNode getChildNodeWithModelNode(ModelNode mnode) {
        XNode[] cnodes = getChildNodes();
        for(int i=0;i<cnodes.length;i++) {
            ModelNode cmnode = cnodes[i].getModelNode();
            if (mnode.equals(cmnode)) {
                return cnodes[i];
            }
        }
        Dbg.pr("XNode "+this+": no child node found with model node "+mnode+".");
        return (XNode) mnode.getReprExemplar().cloneGraphElement();
    }
    
    /** creates the view of the container, see {@link edu.kestrel.graphs.XContainerBoxNode#createContainerView(edu.kestrel.graphs.XGraphDisplay, com.jgraph.graph.CellMapper)}
     * for an example implementation of this method.  */
    public abstract XContainerView createContainerView(XGraphDisplay graph, CellMapper cm);
    
    public void installDefaultContainerViewSettings(XContainerView v) {
        v.viewOptionsExpanded.setHorizontalTextPosition(JLabel.LEFT);
        v.viewOptionsExpanded.setVerticalTextPosition(JLabel.TOP);
    }
    
    /** returns the cell view of this container as XContainerView object. */
    public XContainerView getXContainerView(GraphView gview, boolean create) {
        CellView cv = gview.getMapping(this,create);
        if (cv != null)
            if (cv instanceof XContainerView)
                return (XContainerView) cv;
        return null;
    }
    
    /** returns the cell view of this container as XContainerView object. */
    public XContainerView getXContainerView(GraphView gview) {
        return getXContainerView(gview,false);
    }
    
    /** returns always the result of createContainerView; cannot be overwritten.
     */
    final public XGraphElementView createView(XGraphDisplay graph, CellMapper cm) {
        return createContainerView(graph,cm);
    }
    
    public static final int CONNECTED_TO_INNER = 0;
    public static final int CONNECTED_TO_OUTER = 1;
    
    /** returns all edges that start or end inside the container node; the <code>whichones</code> parameter
     * determines, which edges are returned:
     * <ul>
     * <li> <code>CONNECTED_TO_INNER</code> returns all edges that are completely inside the container node
     * <li> <code>CONNECTED_TO_OUTER</code> returns all edges that connect an inner node of the container node with some node outside the container.
     * </ul>
     */
    public XEdge[] getInnerEdges(XContainerNode parent, int whichones, boolean recursive) {
        ArrayList res = new ArrayList();
        Enumeration childIterator = children();
        while(childIterator.hasMoreElements()) {
            Object child = childIterator.nextElement();
            if (child instanceof XNode) {
                XNode node = (XNode) child;
                XEdge[] allEdges = node.getEdges(XNode.INCOMING_AND_OUTGOING);
                for(int i=0;i<allEdges.length;i++) {
                    XNode otherEnd = allEdges[i].getConnectedNode(node);
                    if (otherEnd == null) {
                        res.add(allEdges[i]);
                    }
                    else if (whichones == CONNECTED_TO_INNER) {
                        if (!otherEnd.equals(parent))
                            if (parent.isNodeDescendant(otherEnd)) {
                                if (!res.contains(allEdges[i]))
                                    res.add(allEdges[i]);
                            }
                    }
                    else if (whichones == CONNECTED_TO_OUTER) {
                        if (!parent.isNodeDescendant(otherEnd)) {
                            if (!res.contains(allEdges[i]))
                                res.add(allEdges[i]);
                        }
                    }
                }
                // get inner edges of child, if it's a container node, but use the same parent!
                if (recursive)
                    if (child instanceof XContainerNode) {
                        XContainerNode chnode = (XContainerNode)child;
                        XEdge[] inneredges = chnode.getInnerEdges(parent,whichones,recursive);
                        for(int i=0;i<inneredges.length;i++)
                            if (!res.contains(inneredges[i]))
                                res.add(inneredges[i]);
                    }
            }
        }
        XEdge[] edges = new XEdge[res.size()];
        res.toArray(edges);
        return edges;
    }
    
    /** removes this node along with its children consisting of inner edges and child nodes.
     */
    public void remove(GraphModel model) {
        XEdge[] edges = getInnerEdges(this,CONNECTED_TO_INNER,false);
        for(int i=0;i<edges.length;i++) edges[i].remove(model);
        XNode[] nodes = getChildNodes();
        for(int i=0;i<nodes.length;i++) nodes[i].remove(model);
        if (detachedChildren != null) {
            Iterator iter = detachedChildren.iterator();
            while(iter.hasNext()) {
                Object obj = iter.next();
                if (obj instanceof XGraphElement) {
                    ((XGraphElement)obj).remove(model);
                }
            }
        }
        super.remove(model);
    }
    
    /** returns the direct children that are instance of XNode.
     */
    public XNode[] getChildNodes() {
        int cnt = getChildCount();
        ArrayList chlist = new ArrayList();
        for(int i=0;i<cnt;i++) {
            TreeNode obj = getChildAt(i);
            if (obj instanceof XNode) {
                chlist.add(obj);
            }
        }
        XNode[] res = new XNode[chlist.size()];
        chlist.toArray(res);
        return res;
    }
    
    public XNode[] getVirtualChildNodes() {
        if (detachedChildren == null) return getChildNodes();
        ArrayList clist = new ArrayList();
        Iterator iter = detachedChildren.iterator();
        while(iter.hasNext()) {
            Object obj = iter.next();
            if (obj instanceof XNode) {
                clist.add(obj);
            }
        }
        XNode[] cnodes = new XNode[clist.size()];
        clist.toArray(cnodes);
        return cnodes;
    }
    
    /** returns true, if the given node is a direct child.
     */
    public boolean isChild(XNode node) {
        if (node == null) return false;
        XNode[] children = getChildNodes();
        for(int i=0;i<children.length;i++) {
            if (node.equals(children[i])) {
                Dbg.pr("node "+node+" is a child of "+this+".");
                return true;
            }
        }
        return false;
    }
    
    /** returns all the inner edges that "stay within" the container.
     */
    public XEdge[] getInnerEdges() {
        return getInnerEdges(this,CONNECTED_TO_INNER,true);
    }
    
    /** returns all edges that start/end at an inner node an end/start at an outer node
     * using the given childIterator
     */
    public XEdge[] getInnerConnToOuterEdges() {
        return getInnerEdges(this,CONNECTED_TO_OUTER,true);
    }
    
    /** detached the direct children from the container node, so that this node has no children
     * after this method is being executed. Returns the array of detached children and sets the field
     * <code>detachedChildren</code> to the same value.
     */
    public java.util.List detachChildren(XGraphDisplay graph, Rectangle parentBounds) {
        int cnt = getChildCount();
        if (cnt == 0) return null;
        XEdge[] edges = getInnerEdges();
        detachedChildren = new ArrayList();
        for(int i=0;i<cnt;i++) {
            TreeNode obj = getChildAt(i);
            if (obj instanceof XNode) {
                XNode chnode = (XNode) obj;
                detachedChildren.add(chnode);
            }
        }
        for(int i=0;i<detachedChildren.size();i++) {
            ((XNode)detachedChildren.get(i)).detachFromParent(graph,this,parentBounds);
        }
        // detach inner edges from view
        for(int i=0;i<edges.length;i++) {
            edges[i].detachFromView(graph,this);
            detachedChildren.add(edges[i]);
        }
        return detachedChildren;
    }
    
    /** re-attaches the previously detached children stored in <code>detachedChildren</code>. */
    public void reAttachChildren(XGraphDisplay graph) {
        if (detachedChildren == null) return;
        if (graph.isReattaching()) return;
        graph.startReattaching();
        ArrayList chviews = new ArrayList();
        Rectangle newBounds = null;
        CellView cv = graph.getView().getMapping(this,false);
        if (cv != null) {
            newBounds = new Rectangle(cv.getBounds());
        }
        ParentMap pm = new ParentMap();
        graph.getXGraphView().startGroupTranslate();
        for(int i=0;i<detachedChildren.size();i++) {
            Object obj = detachedChildren.get(i);
            if (obj instanceof XNode) {
                ((XNode)obj).reAttachToLastParent(graph,newBounds);
            }
            else if(obj instanceof XEdge) {
                ((XEdge)obj).reAttachToView(graph,newBounds);
            }
        }
        graph.getXGraphView().endGroupTranslate();
        // mark the end of the reattachment process
        graph.endReattaching();
        // execute the parent map
        graph.getModel().edit(null,null,pm, null);
        detachedChildren = null;
    }
    
    /** connects the edges from inner nodes connected to outer nodes to this container node; this method is used,
     * when the node is collapsed. */
    public void liftEdgesFromChildren(XGraphDisplay graph) {
        GraphModel model = graph.getModel();
        XEdge[] edges = getInnerConnToOuterEdges();
        if (edges.length == 0) return;
        liftedConnections = new ConnectionSet();
        for(int i=0;i<edges.length;i++) {
            //liftedEdges.add(new LiftedEdge(model,edges[i]));
            XEdge edge = edges[i];
            Object liftedPort;
            boolean sourceLifted;
            XNode srcNode = edge.getSourceNode();
            if (srcNode.isNodeAncestor(this)) {
                sourceLifted = true;
                liftedPort = edge.getSource();
            } else {
                sourceLifted = false;
                liftedPort = edge.getTarget();
            }
            // save the old connection
            liftedConnections.connect(edge,liftedPort,sourceLifted);
            DefaultPort p = getDefaultPort();
            if (p != null) {
                ConnectionSet cs = new ConnectionSet();
                cs.connect(edge,p,sourceLifted);
                graph.disableListener(); // don't record these changes in the underlying model
                model.edit(cs,null,null,null);
                graph.enableListener();
            }
        }
    }
    
    /** returns the "virtual" source port for the given edge, i.e. if the container has lifted connections,
     * try to retrieve the internal node which is logically connected to the edge.
     */
    public Object getVirtualSourceForEdge(XEdge edge) {
        if (liftedConnections == null) {
            return super.getVirtualSourceForEdge(edge);
        }
        Iterator iter = liftedConnections.connections();
        while(iter.hasNext()) {
            ConnectionSet.Connection c = (ConnectionSet.Connection) iter.next();
            if (edge.equals(c.getEdge())) {
                if (c.isSource()) {
                    Dbg.pr("return virtual source port for edge "+edge);
                    return c.getPort();
                }
            }
        }
        return super.getVirtualSourceForEdge(edge);
    }
    
    /** returns the "virtual" target port for the given edge, i.e. if the container has lifted connections,
     * try to retrieve the internal node which is logically connected to the edge.
     */
    public Object getVirtualTargetForEdge(XEdge edge) {
        if (liftedConnections == null) {
            return super.getVirtualTargetForEdge(edge);
        }
        Iterator iter = liftedConnections.connections();
        while(iter.hasNext()) {
            ConnectionSet.Connection c = (ConnectionSet.Connection) iter.next();
            if (edge.equals(c.getEdge())) {
                if (!c.isSource()) {
                    Dbg.pr("return virtual target port for edge "+edge);
                    return c.getPort();
                }
            }
        }
        return super.getVirtualTargetForEdge(edge);
    }
    
    /** reconnect "lifted" edges, that means edges that has been connect to some ancestor during a collapse
     * operation are now being reconnected to their original node.
     */
    public void reconnectLiftedEdges(XGraphDisplay graph) {
        GraphModel model = graph.getModel();
        if (liftedConnections == null) return;
        graph.disableListener(); // don't record these changes in the underlying model
        model.edit(liftedConnections,null,null,null);
        graph.enableListener();
        liftedConnections = null;
    }
    
    /** "adopts" new child nodes, returns the array of node, for which the adoption has succeded; subclassers
     * should overwrite this method rather than the addChildNode method with the List parameter.
     */
    public XNode[] addChildNodes(XGraphDisplay graph, XNode[] childnodes) {
        ParentMap pm = new ParentMap();
        for(int i=0;i<childnodes.length;i++) {
            if (!isChild(childnodes[i])) {
                pm.addEntry(childnodes[i],this);
            }
            else Dbg.pr("G: not adding existing child "+childnodes[i]+" to container node "+this);
        }
        if (childnodes.length>0) {
            if (graph != null) {
                XContainerView cv = getXContainerView(graph.getView(),true);
                if (cv != null) {
                    cv.expand();
                }
            }
        }
        graph.getModel().edit(null,null,pm,null);
        return childnodes;
    }
    
    /** collects the element from the list and calls addChildNodes(graph, XNode[]).
     */
    public XNode[] addChildNodes(XGraphDisplay graph, java.util.List chlist) {
        if (chlist == null) {
            return new XNode[] {};
        }
        ArrayList chlist1 = new ArrayList();
        Iterator iter = chlist.iterator();
        while(iter.hasNext()) {
            Object obj = iter.next();
            if (obj instanceof XNode)
                chlist1.add(obj);
        }
        XNode[] childnodes = new XNode[chlist1.size()];
        chlist1.toArray(childnodes);
        return addChildNodes(graph,childnodes);
    }
    
    /** collapse the container node is the given graph display
     */
    public void collapse(XGraphDisplay graph, boolean setBoundsToSavedCollapsedBounds) {
        XContainerView cv = getXContainerView(graph.getView());
        if (cv != null) {
            cv.collapse();
            if (setBoundsToSavedCollapsedBounds) {
                Rectangle b = getSavedCollapsedBounds();
                if (b != null) {
                    Dbg.pr("XContainerNode "+this+": setting bounds to saved collapsed bounds "+b+"...");
                    //cv.exportBounds(b);
                }
            }
        }
    }
    
    public void collapse(XGraphDisplay graph) {
        collapse(graph,false);
    }
    
    public boolean isCollapsed(XGraphDisplay graph) {
        if (graph == null) return false;
        CellView cv = graph.getView().getMapping(this,false);
        if (cv instanceof XContainerView) {
            return ((XContainerView)cv).isCollapsed();
        }
        return false;
    }
    
    /** expand the container node is the given graph display
     */
    public void expand(XGraphDisplay graph) {
        if (!isExpandable()) return;
        XContainerView cv = getXContainerView(graph.getView());
        if (cv != null) {
            cv.expand();
        }
    }
    
    /** sets the flag which determines, whether the node is expandable or not.
     */
    public void setIsExpandable(boolean b) {
        isExpandable = b;
    }
    
    /** returns whether the node is expandable or not.
     */
    public boolean isExpandable() {
        return isExpandable;
    }
    
    /** performs the action that are necessary in the context of a clone operation. This method basically
     * takes care of the detached views of nodes and edges as well as lifted edge connections.
     */
    public void cloneHook(XCloneManager mgr, Object original) {
        super.cloneHook(mgr,original);
        Map cellMap = mgr.getCellMap();
        if (detachedChildren != null) {
            ArrayList dtch = new ArrayList();
            for(int i=0;i<detachedChildren.size();i++) {
                Object obj = detachedChildren.get(i);
                if (cellMap.containsKey(obj)) {
                    Object clone = cellMap.get(obj);
                    dtch.add(clone);
                    Dbg.pr("  exchanged detached child: "+obj+" => "+clone);
                    mgr.cloneCellViews(obj,clone);
                } else {
                    dtch.add(obj);
                }
            }
            detachedChildren = dtch;
        }
        if (liftedConnections != null) {
            Dbg.pr("cloning lifted connections...");
            // cs is not created here, because empty connection sets lead to null pointer exception in GraphModel.edit()
            ConnectionSet cs = null;
            Iterator iter = liftedConnections.connections();
            while (iter.hasNext()) {
                Object obj = iter.next();
                if (obj instanceof ConnectionSet.Connection) {
                    ConnectionSet.Connection conn = (ConnectionSet.Connection) obj;
                    boolean isSource = conn.isSource();
                    Object edgeobj = conn.getEdge();
                    Object portobj = conn.getPort();
                    //Dbg.pr("  lifted connection: "+edgeobj+" "+portobj+"  isSource="+isSource);
                    if (cellMap.containsKey(edgeobj)) {
                        // only update the connection, if it's not from outside
                        // otherwise the edge would be disconnected from the original
                        // node, if the clone is expanded
                        Object medgeobj = cellMap.get(edgeobj);
                        //Dbg.pr("  mapping for edge found: "+medgeobj);
                        Object mportobj = null;
                        if (cellMap.containsKey(portobj)) {
                            mportobj = cellMap.get(portobj);
                            //Dbg.pr("  mapping for port found: "+mportobj);
                        }
                        if (mportobj == null)
                            throw new IllegalArgumentException("no mapping for lifted connection found!? edge->"+medgeobj+", port->"+mportobj);
                        // add the connection to the list of lifted connections:
                        if (cs == null)
                            cs = new ConnectionSet();
                        cs.connect(medgeobj,mportobj,isSource);
                    }
                }
            }
            liftedConnections = cs;
        }
    }
    
    
    /** returns all inner nodes, including detached ones.
     */
    public java.util.List getInnerNodesAndEdges() {
        return getInnerNodesAndEdges(true,true);
    }
    
    
    private java.util.List getInnerNodesAndEdges(boolean recursive, boolean isToplevel) {
        if (detachedChildren != null) {
            return getInnerNodesAndEdges(detachedChildren,recursive);
        } else {
            ArrayList childList = new ArrayList();
            if (isToplevel) {
                XEdge[] edges = getInnerEdges();
                for(int i=0;i<edges.length;i++) {
                    Dbg.pr("adding inner edge...");
                    childList.add(edges[i]);
                }
            }
            Enumeration iter = children();
            while (iter.hasMoreElements()) {
                Object obj = iter.nextElement();
                if (obj instanceof XNode)
                    childList.add(obj);
            }
            return getInnerNodesAndEdges(childList,recursive);
        }
    }
    
    private java.util.List getInnerNodesAndEdges(java.util.List childList, boolean recursive) {
        ArrayList res = new ArrayList();
        if (childList != null) {
            Iterator iter = childList.iterator();
            while (iter.hasNext()) {
                Object obj = iter.next();
                if (obj instanceof XEdge) {
                    if (!res.contains(obj))
                        res.add(obj);
                }
                else if (obj instanceof XNode) {
                    if (!res.contains(obj))
                        res.add(obj);
                    if (recursive) {
                        if (obj instanceof XContainerNode) {
                            java.util.List elems = ((XContainerNode)obj).getInnerNodesAndEdges(recursive,false);
                            for(int i=0;i<elems.size();i++)
                                if (!res.contains(elems.get(i)))
                                    res.add(elems.get(i));
                        }
                    }
                }
            }
        }
        //XGraphElement[] resArray = new XGraphElement[res.size()];
        //res.toArray(resArray);
        return res;
    }
    
    public void updateViewData(XGraphElementView view) {
        if (!saveViewData) return;
        super.updateViewData(view);
        if (view instanceof XContainerView) {
            XContainerView cv = (XContainerView) view;
            //savedCollapsedBounds = cv.getCollapsedBounds();
            //savedIsExpanded = cv.isExpanded();
        }
    }
    
    public void setSavedCollapsedBounds(Rectangle b) {
        if (!saveViewData) return;
        //Dbg.pr("setting savedCollapsedBounds for node "+this+" to "+b+"...");
        savedCollapsedBounds = new Rectangle(b);
    }
    
    public void setSavedIsExpanded(boolean b) {
        if (!saveViewData) return;
        savedIsExpanded = b;
    }
    
    public boolean getSavedIsExpanded() {
        return savedIsExpanded;
    }
    
    public Rectangle getSavedCollapsedBounds() {
        return savedCollapsedBounds;
    }
    
    public void restoreIsExpanded(XGraphDisplay graph, boolean isExpanded) {
        Dbg.pr("restoring collapsed/expanded state of node "+this+" in graph "+graph+": was expanded="+savedIsExpanded);
        if (isExpanded) {
            expand(graph);
        } else {
            collapse(graph,true);
        }
    }
    
    public void restoreIsExpanded(XGraphDisplay graph) {
        restoreIsExpanded(graph,savedIsExpanded);
    }
    
    public void restoreCollapsedBounds(XGraphDisplay graph, Rectangle b) {
        if (b == null) return;
        Dbg.pr("restoring collapsed bounds of node "+this+" in graph "+graph+"...");
        XContainerView cv = getXContainerView(graph.getView(),true);
        if (cv != null) {
            cv.setCollapsedBounds(b);
        }
    }
    
    public void restoreCollapsedBounds(XGraphDisplay graph) {
        restoreCollapsedBounds(graph,savedCollapsedBounds);
        //restoreCollapsedBounds(graph);
    }
    
    protected static String CollapsedBounds = "CollapsedBounds";
    protected static String IsExpandable = "IsExpandable";
    protected static String IsExpanded = "IsExpanded";
    protected static String ChildNode = "ChildNode";
    
    /** returns the element properties object in the context of a write operation.
     */
    public ElementProperties getElementProperties(ReadWriteOperation wop) {
        ElementProperties props = super.getElementProperties(wop);
        XNode[] cnodes = getVirtualChildNodes();
        for(int i=0;i<cnodes.length;i++) {
            props.addChildObjectAsReference(ChildNode,cnodes[i]);
        }
        props.setBooleanProperty(IsExpandable,isExpandable());
        props.setRectangleProperty(CollapsedBounds,/*getCorrectedBounds*/(savedCollapsedBounds));
        props.setBooleanProperty(IsExpanded,savedIsExpanded);
        return props;
    }
    
    /** initializes a freshly created element of this class using the information stored in the given
     * ElementProperties instance. Used during io operations.
     */
    public void initFromElementProperties(ReadWriteOperation rwop, ElementProperties props) {
        super.initFromElementProperties(rwop,props);
        ArrayList clist = new ArrayList();
        Enumeration iter = props.getChildObjectAsReferenceEnumeration(ChildNode);
        while(iter.hasMoreElements()) {
            String cid = (String) iter.nextElement();
            Storable obj = rwop.getObjectForId(cid);
            if (obj instanceof XNode) {
                Dbg.pr("XContainerNode: adding "+obj+" to childNodes...");
                clist.add(obj);
            }
        }
        setIsExpandable(props.getBooleanProperty(IsExpandable));
        Rectangle b = props.getRectangleProperty(CollapsedBounds);
        Dbg.pr("XContainerNode "+this+": collapsed bounds in ElementProperties: "+b);
        setSavedCollapsedBounds(b);
        boolean isExpanded = props.getBooleanProperty(IsExpanded);
        setSavedIsExpanded(isExpanded);
        XNode[] childNodes = new XNode[clist.size()];
        clist.toArray(childNodes);
        if (getGraph() != null) {
            getGraph().disableListener();
            addChildNodes(getGraph(),childNodes);
            restoreCollapsedBounds(getGraph(),b);
            CellView cv = getGraph().getView().getMapping(this,false);
            if (cv != null) {
                getGraph().getView().toBack(new CellView[] {cv});
            }
            restoreIsExpanded(getGraph(),isExpanded);
            getGraph().enableListener();
        }
        Dbg.pr("XContainerNode "+this+": savedCollapsedBounds="+b+", isExpanded="+isExpanded);
    }
    
}
