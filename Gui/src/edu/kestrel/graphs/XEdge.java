package edu.kestrel.graphs;

import edu.kestrel.graphs.editor.*;
import edu.kestrel.graphs.spec.*;
import edu.kestrel.graphs.io.*;
import com.jgraph.graph.*;
import javax.swing.tree.*;
import java.util.*;
import java.awt.*;

public abstract class XEdge extends DefaultEdge implements XGraphElement, XTextEditorEditable {
    
    //protected XNode source;
    //protected XNode target;
    
    /** used in detachFromView to store the last view object. */
    protected CellView detachedView = null;
    protected boolean viewWasVisible;
    protected XContainerNode lastParent = null;
    //private Rectangle lastParentsBounds = null;
    
    private java.util.List savedViewPoints = null;
    
    protected Dimension offsetToLastParent = null;
    
    protected XGraphDisplay graph;
    
    protected ModelEdge modelEdge;
    
    /** the saved list of points for this edge. */
    protected java.util.List savedPoints;
    /** the identification object for the source port of this edge; usually an instance of Point. */
    protected Object savedSrcPort;
    /** the identification object for the target port of this edge; usually an instance of Point. */
    protected Object savedTrgPort;
    
    protected Rectangle savedBounds;
    
    protected boolean collapseLabel = false;
    
    static int xedgeCnt = 0;
    
    protected int ID;
    
    public XEdge() {
        super(null);
    }
    
    public XEdge(String name) {
        super(name);
    }
    
    /*
    public XEdge(ModelEdge e) {
        super(e.getValue());
        setModelEdge(e);
    }
     */
    
    public void setGraph(XGraphDisplay graph) {
        this.graph = graph;
    }
    
    public XGraphDisplay getGraph() {
        return graph;
    }
    
    public void repaintGraph() {
        if (graph != null) {
            graph.repaint();
        }
    }
    
    
    protected void init() {
        detachedView = null;
        lastParent = null;
        offsetToLastParent = null;
    }
    
    public void setID(int n) {
        ID = n;
    }
    
    public void setUserObject() {
        if (Dbg.isDebug2())
            setUserObject("E"+String.valueOf(xedgeCnt++));
    }
    
    public void setUserObject(Object obj) {
        super.setUserObject(obj);
        getModelEdge().setValue(obj);
    }
    
    public void setFullUserObject(Object val) {
        setUserObject(val);
    }
    
    /** returns a short representation of the edge's name to be used in popup windows etc.
     */
    public String getShortName() {
        if (getUserObject() == null) return "";
        String name = getUserObject().toString();
        if (name.length() > XGraphConstants.maxShortNameLength) {
            name = name.substring(0,XGraphConstants.maxShortNameLength) + "...";
        }
        return name;
    }
    
    
    public void setSavedViewPoints(java.util.List points) {
        savedViewPoints = points;
    }
    
    public java.util.List getSavedViewPoints() {
        return savedViewPoints;
    }
    
    
    public void setModelEdge(ModelEdge e) {
        modelEdge = e;
    }
    
    /** returns the Model Edge of this edge; creates it, if it doesn't exist. */
    public ModelEdge getModelEdge() {
        if (modelEdge == null) {
            modelEdge = createModelEdge();
            modelEdge.addFirstRepr(this);
            XNode srcnode = getSourceNode();
            if (srcnode != null) {
                try {
                    modelEdge.setSource(srcnode.getModelNode());
                } catch (ModelException me) {
                }
            }
            XNode trgnode = getTargetNode();
            if (trgnode != null) {
                try {
                    modelEdge.setTarget(trgnode.getModelNode());
                } catch (ModelException me) {
                }
            }
        }
        return modelEdge;
    }
    
    /** returns the model node that is associated to the source node. */
    public ModelNode getModelSource() {
        XNode src = getSourceNode();
        if (src == null) return null;
        return src.getModelNode();
    }
    
    /** returns the model node that is associated to the source node. */
    public ModelNode getModelTarget() {
        XNode trg = getTargetNode();
        if (trg == null) return null;
        return trg.getModelNode();
    }
    
    /** creates the model edge for this edge; this method is used, if this edge has been created without an
     * associated model edge. It returns an instance of ModelEdge; sub-classers can overwrite this method
     * to return instances of sub-classes of ModelEdge.
     */
    public ModelEdge createModelEdge() {
        return new ModelEdge();
    }
    
    
    
    public abstract void insertHook(XGraphDisplay graph, XGraphElementView viewObject);
    
    /** this method is call when the edge is initially connected to its source and target node
     */
    public void initialConnectHook(XEdgeView ev) {
    }
    
    public void setBoundsHook(XGraphDisplay graph, XGraphElementView viewObject, Rectangle bounds) {
    }
    
    
    public XGraphElementView createView(XGraphDisplay graph, CellMapper cm) {
        XEdgeView res = new XEdgeView(this,graph,cm);
        return res;
    }
    
    public void remove(GraphModel model) {
        java.util.List children = getChildren();
        ArrayList removees = new ArrayList();
        removees.add(this);
        model.remove(removees.toArray());
        if (modelEdge != null)
            modelEdge.removeRepr(this);
        setGraph(null);
    }
    
    /** returns the source node of this edge */
    public XNode getSourceNode() {
        return getXNodeParentOfPort(getSource());
    }
    
    /** returns the target node of this edge. */
    public XNode getTargetNode() {
        return getXNodeParentOfPort(getTarget());
    }
    
    /** returns the "virtual" source node for the edge, i.e. the "real" source node without taking collapsed
     * containers into account.
     */
    public XNode getVirtualSourceNode() {
        Object obj = getVirtualSource();
        if (obj != null)
            return getXNodeParentOfPort(obj);
        return null;
    }
    
    /** returns the port to which the edge is connected "virtually", without taking collapsed containers into account.
     */
    public Object getVirtualSource() {
        XNode n = getSourceNode();
        if (n != null) {
            return n.getVirtualSourceForEdge(this);
        }
        return null;
    }
    
    /** returns the "virtual" target node for the edge, i.e. the "real" target node without taking collapsed
     * containers into account.
     */
    public XNode getVirtualTargetNode() {
        Object obj = getVirtualTarget();
        if (obj != null)
            return getXNodeParentOfPort(obj);
        return null;
    }
    
    /** returns the port to which the edge is connected "virtually", without taking collapsed containers into account.
     */
    public Object getVirtualTarget() {
        XNode n = getTargetNode();
        if (n != null) {
            return n.getVirtualTargetForEdge(this);
        }
        return null;
    }
    
    /** returns the other end of the edge given that one end is <code>node</code>, that means, if the node is
     * the source, return the target and vice versa.
     */
    public XNode getConnectedNode(XNode node) {
        if (getSource() != null)
            if (getSourceNode().equals(node)) return getTargetNode();
        if (getTargetNode() != null)
            if (getTargetNode().equals(node)) return getSourceNode();
        return null;
    }
    
    /** helper method used to implement <code>getSourceNode</code> and <code>getTargetNode</code> */
    private XNode getXNodeParentOfPort(Object obj) {
        if (obj == null) return null;
        if (obj == null) return null;
        if (obj instanceof DefaultPort) {
            TreeNode parent = ((DefaultPort)obj).getParent();
            if (parent instanceof XNode)
                return (XNode) parent;
        }
        return null;
    }
    
    /** return true, if the edge is an inner edge of some container.
     */
    public boolean isInnerEdge() {
        XNode src = getSourceNode();
        XNode trg = getTargetNode();
        if (src == null || trg == null)
            return false;
        XContainerNode p = src.getLeastCommonAncestor(trg);
        return (p != null);
    }
    
    public CellView detachFromView(XGraphDisplay graph, XContainerNode parent) {
        Dbg.pr("detaching edge "+this+"...");
        detachedView = graph.getView().getMapping(this,false);
        if (detachedView == null) return null;
        lastParent = parent;
        Map viewMap = new Hashtable();
        Map map = GraphConstants.createMap();
        viewWasVisible = GraphConstants.isVisible(detachedView.getAttributes());
        GraphConstants.setVisible(map,false);
        viewMap.put(detachedView,map);
        graph.getView().edit(viewMap);
        CellView pcv = graph.getView().getMapping(lastParent,false);
        CellView cv = graph.getView().getMapping(this,false);
        if (pcv != null && cv != null) {
            Rectangle childBounds = cv.getBounds();
            Rectangle parentBounds = pcv.getBounds();
            offsetToLastParent = new Dimension(childBounds.x-parentBounds.x, childBounds.y-parentBounds.y);
            //lastParentsBounds = cv.getBounds();
        }
        return detachedView;
    }
    
    public void reAttachToView(XGraphDisplay graph, Rectangle lastParentsNewBounds) {
        if (detachedView == null) return;
        Dbg.pr("reattaching edge "+this+"...");
        Map viewMap = new Hashtable();
        Map map = GraphConstants.createMap();
        GraphConstants.setVisible(map,true);//viewWasVisible);
        viewMap.put(detachedView,map);
        graph.getView().edit(viewMap);
        //CellView cv = graph.getView().getMapping(lastParent,false);
        //Rectangle lastParentsNewBounds = null;
        //if (cv != null)
        //    lastParentsNewBounds = cv.getBounds();
        /*
        int dx = 0, dy = 0;
        if (lastParentsBounds != null && lastParentsNewBounds != null) {
            dx = lastParentsNewBounds.x - lastParentsBounds.x;
            dy = lastParentsNewBounds.y - lastParentsBounds.y;
        }
        if (dx != 0 || dy != 0) {
            //CellView thisview = graph.getView().getMapping(this,false);
            //if (detachedView instanceof XEdgeView) {
            //    ((XEdgeView)detachedView).translate(dx,dy);
            //} else {
            if (false)
                graph.getXGraphView().translateViewsInGroup(new CellView[]{detachedView},dx,dy);
                //}
        }
         */
        detachedView = null;
        offsetToLastParent = null;
        lastParent = null;
    }
    
    public boolean isDetached() {
        return (detachedView != null);
    }
    
    /** creates a clone of this edge; calls init() for initializing the cloned edge.
     */
    public XEdge cloneEdge() {
        //Dbg.pr("cloning XEdge "+this+"...");
        XEdge edge = (XEdge) clone();
        edge.init();
        return edge;
    }
    
    /** calls cloneEdge to create a clone of this node.
     */
    public XGraphElement cloneGraphElement() {
        return cloneEdge();
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
        Dbg.pr2("cloneHook: edge "+this);
        XGraphDisplay tgraph = mgr.getDestGraph();
        Map cellMap = mgr.getCellMap();
        if (detachedView != null) {
            // node is detached
            if (lastParent != null) {
                if (cellMap.containsKey(lastParent)) {
                    Object obj = cellMap.get(lastParent);
                    if (obj instanceof XContainerNode) {
                        Dbg.pr2("  exchanging lastParent to be "+obj);
                        lastParent = (XContainerNode) obj;
                    } else
                        throw new IllegalArgumentException("cloned parent is not a container node?!");
                }
            }
            //detachedView = graph.getXGraphUI().cloneCellViews(original,this);
            //detachedView = graph.getView().getMapping(this,true);
            // reconnect edges
            if (original instanceof Edge) {
                Edge oedge = (Edge) original;
                Object srcp = oedge.getSource();
                Object trgp = oedge.getTarget();
                ConnectionSet cs = new ConnectionSet();
                if (cellMap.containsKey(srcp)) {
                    Dbg.pr2("   setting new source...");
                    srcp = cellMap.get(srcp);
                    if (srcp instanceof Port) {
                        cs.connect(this,(Port)srcp,true);
                        setSource(srcp);
                        ((Port)srcp).add(this);
                    }
                }
                if (cellMap.containsKey(trgp)) {
                    Dbg.pr2("   setting new target...");
                    trgp = cellMap.get(trgp);
                    if (trgp instanceof Port) {
                        cs.connect(this,(Port)trgp,false);
                        setTarget(trgp);
                        ((Port)trgp).add(this);
                    }
                }
                //graph.getModel().edit(cs,null,null,null);
                tgraph.getModel().edit(cs,null,null,null);
            }
            offsetToLastParent = new Dimension(offsetToLastParent);
            detachedView = tgraph.getView().getMapping(this,true);
            if (detachedView instanceof XEdgeView) {
                ((XEdgeView)detachedView).setSavedPoints();
            }
            if (Dbg.isDebug2()) {
                Dbg.pr2("new attributes of detachedView:");
                XGraphDisplay.showAttributes(detachedView);
                XNode srcnode = getSourceNode();
                XNode trgnode = getTargetNode();
                Dbg.pr2("*** source node: "+srcnode);
                Dbg.pr2("*** target node: "+trgnode);
            }
        }
        setGraph(mgr.getDestGraph());
        //graph.getXGraphUI().cloneCellViews(original,this);
    }
    
    public void setCollapseLabel(boolean b) {
        collapseLabel = b;
    }
    
    public boolean isCollapseLabel() {
        return collapseLabel;
    }
    
    /** this method computes the short form of the given text string and is used to computer the collapsed
     * label in case the edge supports expanding/collapsing of its label text.
     */
    public String getCollapsedLabel(String fullLabel) {
        return XTextNode.getCollapsedString(fullLabel);
    }
    
    /** method to update the relevant data stored in the view object in this object. This method is called by the
     * view object whenever it is updated.
     *
     */
    public void updateViewData(XGraphElementView view) {
        if (view instanceof XEdgeView) {
            //Dbg.pr("XEdge.updateViewData()...");
            XEdgeView ev = (XEdgeView) view;
            savedPoints = new ArrayList();
            int cnt = ev.getPointCount();
            for(int i=0;i<cnt;i++) {
                savedPoints.add(ev.getPoint(i));
            }
            Object srcPort = getSource();
            savedSrcPort = null;
            if (srcPort != null) {
                if (srcPort instanceof DefaultPort) {
                    savedSrcPort = ((DefaultPort)srcPort).getUserObject();
                    //Dbg.pr("savedSrcPort="+savedSrcPort);
                }
            }
            Object trgPort = getTarget();
            savedTrgPort = null;
            if (trgPort != null) {
                if (trgPort instanceof DefaultPort) {
                    savedTrgPort = ((DefaultPort)trgPort).getUserObject();
                    //Dbg.pr("savedTrgPort="+savedTrgPort);
                }
            }
        }
        setSavedBounds(view.getBounds());
    }
    
    public Object getSavedSrcPort() {return savedSrcPort;}
    public Object getSavedTrgPort() {return savedTrgPort;}
    public void setSavedSrcPort(Object obj) {savedSrcPort = obj;}
    public void setSavedTrgPort(Object obj) {savedTrgPort = obj;}
    
    
    public void setSavedBounds(Rectangle b) {
        savedBounds = new Rectangle(b);
    }
    
    protected Dimension getOffsetForSavedPoints() {
        int dx = 0;
        int dy = 0;
        if (isDetached())
            if (lastParent != null && offsetToLastParent != null) {
                Rectangle pb = lastParent.getCorrectedBounds(lastParent.getSavedBounds());
                if (pb != null)
                    if (savedBounds != null) {
                        dx = pb.x + offsetToLastParent.width - savedBounds.x;
                        dy = pb.y + offsetToLastParent.height - savedBounds.y;
                    }
            }
        Dbg.pr("XEdge "+this+": offset for saved points: "+dx+","+dy);
        return new Dimension(dx,dy);
    }
    
    public Point[] getSavedIntermediatePoints() {
        Dimension offset = getOffsetForSavedPoints();
        ArrayList p = new ArrayList();
        for(int i=1;i<savedPoints.size()-1;i++) {
            Object obj = savedPoints.get(i);
            if (obj instanceof Point) {
                Point p0 = new Point((Point)obj);
                p0.x += offset.width;
                p0.y += offset.height;
                p.add(p0);
            }
        }
        Point[] res = new Point[p.size()];
        p.toArray(res);
        return res;
    }
    
    /** sets the array of saved points according to the given intermediate points; the first and the last
     * element of the resulting saved points list will be dummy elements, because they are not used, when
     * the saved intermediate points are accessed.
     */
    protected void setSavedPoints(Point[] ipoints) {
        savedPoints = new ArrayList();
        savedPoints.add(new Point(0,0));
        for(int i=0;i<ipoints.length;i++) {
            savedPoints.add(ipoints[i]);
        }
        savedPoints.add(new Point(100,100));
    }
    
    static protected String ModelEdge = "ModelEdge";
    static protected String Graph = "Graph";
    static protected String SourcePortId = "SourcePortId";
    static protected String TargetPortId = "TargetPortId";
    static protected String SourceNode = "SourceNode";
    static protected String TargetNode = "TargetNode";
    static protected String PointPrefix = "Point";
    static protected String LabelPosition = "LabelPosition";
    static protected String CollapseLabel = "CollapseLabel";
    
    /** returns the element properties object in the context of a write operation.
     */
    public ElementProperties getElementProperties(ReadWriteOperation wop) {
        ElementProperties props = wop.createElementProperties(this);
        props.setValueProperty(getUserObject());
        props.addChildObjectAsReference(ModelEdge,getModelEdge());
        Dimension offset = new Dimension(0,0);
        if (getGraph() != null) {
            props.addChildObjectAsReference(Graph,getGraph());
            CellView cv = getGraph().getView().getMapping(this,false);
            if (cv != null) {
                Point lpos = GraphConstants.getLabelPosition(cv.getAttributes());
                props.setPointProperty(LabelPosition,lpos);
            }
        }
        //Object srcpid = getSavedSrcPort();
        Object srcpid = null;
        Object srcp = getVirtualSource();
        if (srcp instanceof DefaultPort) {
            srcpid = ((DefaultPort)srcp).getUserObject();
        }
        if (srcpid instanceof Point) {
            props.setPointProperty(SourcePortId,(Point)srcpid);
        } else {
            props.setProperty(SourcePortId,srcpid);
        }
        //Object trgpid = getSavedTrgPort();
        Object trgpid = null;
        Object trgp = getVirtualTarget();
        if (trgp instanceof DefaultPort) {
            trgpid = ((DefaultPort)trgp).getUserObject();
        }
        if (trgpid instanceof Point) {
            props.setPointProperty(TargetPortId,(Point)trgpid);
        } else {
            props.setProperty(TargetPortId,trgpid);
        }
        Point[] ipoints = getSavedIntermediatePoints();
        for(int i=0;i<ipoints.length;i++) {
            props.setPointProperty(PointPrefix+i,ipoints[i]);
        }
        XNode srcnode = getVirtualSourceNode();
        if (srcnode != null) {
            props.addChildObjectAsReference(SourceNode,srcnode);
        }
        XNode trgnode = getVirtualTargetNode();
        if (trgnode != null) {
            props.addChildObjectAsReference(TargetNode,trgnode);
        }
        props.setBooleanProperty(CollapseLabel,collapseLabel);
        return props;
    }
    
    /** initializes a freshly created element of this class using the information stored in the given
     * ElementProperties instance. Used during io operations.
     */
    public void initFromElementProperties(ReadWriteOperation rwop, ElementProperties props) {
        setUserObject(props.getValueProperty());  //
        Dbg.pr("{ initFromElementPropterties for XEdge "+this+"...");
        collapseLabel = props.getBooleanProperty(CollapseLabel);
        // source node
        XNode srcnode = null;
        String srcnodeid = props.getChildObjectAsReference(SourceNode);
        Storable obj2 = rwop.getObjectForId(srcnodeid);
        if (obj2 instanceof XNode) {
            srcnode = (XNode)obj2;
        }
        // target node
        XNode trgnode = null;
        String trgnodeid = props.getChildObjectAsReference(TargetNode);
        Storable obj3 = rwop.getObjectForId(trgnodeid);
        if (obj3 instanceof XNode) {
            trgnode = (XNode) obj3;
        }
        //mode edge
        String modeledgeid = props.getChildObjectAsReference(ModelEdge);
        Storable obj0 = rwop.getObjectForId(modeledgeid);
        if (obj0 instanceof ModelEdge) {
            setModelEdge((ModelEdge)obj0);
        }
        String graphid = props.getChildObjectAsReference(Graph);
        Storable obj1 = rwop.getObjectForId(graphid);
        if (obj1 instanceof XGraphDisplay) {
            setGraph((XGraphDisplay)obj1);
        }
        
        Object srcPortId = null;
        if (props.hasPointProperty(SourcePortId)) {
            setSavedSrcPort(srcPortId = props.getPointProperty(SourcePortId));
        } else {
            setSavedSrcPort(srcPortId = props.getProperty(SourcePortId));
        }
        Object trgPortId = null;
        if (props.hasPointProperty(TargetPortId)) {
            setSavedSrcPort(trgPortId = props.getPointProperty(TargetPortId));
        } else {
            setSavedSrcPort(trgPortId = props.getProperty(TargetPortId));
        }
        int i = 0;
        ArrayList iplist = new ArrayList();
        while(props.hasPointProperty(PointPrefix+i)) {
            iplist.add(props.getPointProperty(PointPrefix+i));
            i++;
        }
        Point[] ipoints = new Point[iplist.size()];
        iplist.toArray(ipoints);
        setSavedPoints(ipoints);
        if (getGraph() != null) {
            //rwop.registerGraphDuringRead(getGraph());
            Dbg.pr("{ inserting edge "+this+" in graph "+getGraph()+": ");
            Dbg.pr("  srcnode="+srcnode+", srcPortId="+srcPortId);
            Dbg.pr("  trgnode="+trgnode+", trgPortId="+trgPortId);
            getGraph().disableListener();
            XEdgeView ev = getGraph().insertEdge(this,srcnode,srcPortId,trgnode,trgPortId,ipoints);
            if (ev != null) {
                ev.setSavedPoints();
                if (props.hasPointProperty(LabelPosition)) {
                    getGraph().setLabelPositionOfEdge(this,props.getPointProperty(LabelPosition));
                }
                ev.configureCollapseLabelMenuItem();
            }
            getGraph().enableListener();
            Dbg.pr("}");
        }
        Dbg.pr("}");
    }

    
    
    // interface XTextEditorEditable methods:
    
    public String getText() {
            return getUserObject().toString();
    }
    
    public String getTitleText() {
        return XTextNode.getCollapsedString(getText());
    }
    
    public void setText(String t) {
        setUserObject(t.trim());
        getModelEdge().sync();
    }
    
    public XElementEditor createEditorPane() {
        return new XTextEditor(this);
    }    
    
}
