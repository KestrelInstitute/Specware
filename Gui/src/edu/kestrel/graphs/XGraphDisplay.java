package edu.kestrel.graphs;

import edu.kestrel.graphs.drawingmode.*;
import edu.kestrel.graphs.editor.*;
import edu.kestrel.graphs.event.*;
import edu.kestrel.graphs.spec.*;
import edu.kestrel.graphs.io.*;

import com.jgraph.*;
import com.jgraph.graph.*;
import com.jgraph.event.*;
import javax.swing.undo.*;
import javax.swing.tree.*;
import javax.swing.*;
import java.util.*;
import java.io.*;
import java.awt.font.*;
import java.awt.event.*;
import java.awt.geom.*;
import java.text.*;
import java.awt.*;

/**
 * The main "canvas" for displaying a graph. It's behavior is
 * specified by an instance of XGraphSpec.
 */

public class XGraphDisplay extends JGraph implements Storable {
    
    protected XGraphSpec graphSpec;
    //public Vector  elementViews;
    
    protected XGraphApplication appl = null;
    
    /** the title string to be used for internal frames etc.
     */
    protected String titleString = "";
    
    protected Object value;
    
    /** the clipboard to be used, if this graph display is <em>not</em> part of an application; if it is, then
     * this field will not be used; instead the clipboard of the XGraphApplication is used.
     */
    protected XGraphDisplay clipboard = null;
    
    /** if the graph display is part of an XGraphApplication,
     * this field will not be used; the model of the XGraphApplication instance is used instead. If the graph display is a "stand-alone"
     * application, then this field holds the information about the associated model node.
     */
    protected ModelContainerNode modelNode = null;
    
    /** this field holds the explcitly set model node of this graph.
     */
    protected ModelContainerNode explicitModelRootNode = null;
    
    protected PortView highlightedPortView = null;
    
    /**
     * field storing the current drawing mode
     */
    
    protected DrawingMode currentDrawingMode;
    
    protected XGraphModelListener modelListener = null;
    
    /** listeners which are interested in the value change of this graph; element type: XGraphDisplayValueListener
     */
    protected Vector graphValueListener;
    
    /** flag controlling the behaviour when the graph display is closed; if set to true, all representation
     * elements contained in the graph will be removed, which is the default.
     */
    protected boolean removeAllOnClosing = false;
    
    /** saved bounds of the graph if displayed as an internal frame in an desktop
     */
    protected Rectangle bounds;
    
    /**
     * @param graphSpec the object containing the graph spec
     */
    public XGraphDisplay(Object value, XGraphSpec graphSpec) {
        super(null);
        setValue(value);
        init(graphSpec,null);
        //setPortsVisible(true);
        /*
        setGraphSpec(graphSpec);
        setView(new XGraphView(getXGraphModel(),this));
        getSelectionModel().setSelectionMode(GraphSelectionModel.MULTIPLE_GRAPH_SELECTION);
        //setPortsVisible(true);
        //setGridEnabled(true);
        setScale(1.0);
         */
        getModel().addGraphModelListener(modelListener = createGraphModelListener());
            /*
        setCloneable(false);
             */
        setSizeable(true);
    }
    
    public XGraphDisplay(XGraphSpec graphSpec) {
        this("", graphSpec);
    }
    
    /**
     * constructs an XGraphDisplay with a default XGraphSpec. See XGraphSpec documentation
     * for a description of the default XGraphSpec.
     **/
    public XGraphDisplay() {
        this("",XGraphSpec.getDefaultSpec());
    }
    
    
    /** creates the graph model listener that is used for synchronizing the graphical representation objects
     * with the model nodes and edges. This method returns an instance of XGraphModelListener; subclassers
     * can overwrite this method to return customized versions of a GraphModelListener.
     */
    protected XGraphModelListener createGraphModelListener() {
        return new XGraphModelListener(this);
    }
    
    /** sets the value of this graph; notifies the listeners (XGraphValueListener).
     */
    public void setValue(Object value) {
        Object oldvalue = this.value;
        if (oldvalue != null)
            if (oldvalue.equals(value)) return;
        this.value = value;
        if (graphValueListener != null) {
            Enumeration iter = graphValueListener.elements();
            while(iter.hasMoreElements()) {
                XGraphDisplayValueListener l = (XGraphDisplayValueListener)iter.nextElement();
                l.graphValueChanged(this,oldvalue,value);
            }
        }
    }
    
    /** returns the content of the <code>value</code> field.
     */
    public Object getValue() {
        return value;
    }
    
    public void addGraphDisplayValueListener(XGraphDisplayValueListener l) {
        if (graphValueListener == null) {
            graphValueListener = new Vector();
        }
        if (!graphValueListener.contains(l)) {
            graphValueListener.add(l);
            l.graphValueChanged(this,null,getValue());
        }
    }
    
    public void removeGraphDisplayValueListener(XGraphDisplayValueListener l) {
        if (graphValueListener == null) return;
        graphValueListener.remove(l);
    }
    
    public String toString() {
        if (value == null) return "";
        return value.toString();
    }
    
    /** disables the listener from triggering actions caused by a model change.
     */
    public void disableListener() {
        modelListener.disable();
    }
    
    /** enables the model listener again after it has been disabled.
     */
    public void enableListener() {
        modelListener.enable();
    }
    
    public void updateUI() {
        setUI(new XGraphUI());
        invalidate();
    }
    
    /*
    public XGraphDisplay(XGraphSpec graphSpec, GraphView view) {
        super(graphSpec.getGraphModel(),view);
        init(graphSpec,view);
    }
     */
    
    protected void init(XGraphSpec graphSpec, GraphView view) {
        setGraphSpec(graphSpec);
        if (view == null)
            setView(new XGraphView(getXGraphModel(),this));
        getSelectionModel().setSelectionMode(GraphSelectionModel.MULTIPLE_GRAPH_SELECTION);
        //setPortsVisible(true);
        //setGridEnabled(true);
        setScale(1.0);
        getModel().addGraphModelListener(new GraphModelListener() {
            public void graphChanged(GraphModelEvent e) {
                //writeToFile("xgraphdb");
            }});
            setCloneable(false);
    }
    
    /** sets the application for this graph display; an application is the overall control instance of the
     * application; it e.g. registers all instances of graph displays and keeps track of model changes etc.
     */
    public void setApplication(XGraphApplication appl) {
        this.appl = appl;
    }
    
    public XGraphApplication getApplication() {
        return appl;
    }
    
    /** returns the model node that is associated with this graph display. The model node is either the "global" model
     * node associated with the XGraphApplication instance, if this graph display is part of an application, or a "local"
     * model node, which is created using <code>createModelNode</code>, in case this graph display is a "stand-alone"
     * application.
     */
    public ModelContainerNode getModelRootNode() {
        if (appl != null) {
            return appl.getModelNode();
        }
        if (modelNode == null) {
            modelNode = createModelNode();
        }
        return modelNode;
    }
    
    /** sets the root node of this graph explicitly; all nodes in the graph will be children of this node; the graph must
     * be empty to do this.
     */
    public void setModelRootNode(ModelContainerNode mnode) {
        if (isEmpty()) {
            explicitModelRootNode = mnode;
        }
    }
    
    /** returns the model node of the graph, which is either 
     * <ul>
     * <li> determined by looking for the common parent node of the root
     * nodes of the graph; if they don't have a common parent node, then the model root node of the graph is returned.
     * <li> the mode node which has explicitly been set for this graph.
     * </ul>
     */
    public ModelContainerNode getModelNode() {
        ModelNode[] rootNodes = getModelNodesOfRoots();
        TreeNode parent = null;
        try {
            if (rootNodes.length > 0) {
                parent = rootNodes[0].getParent();
                if (parent != null) {
                    for(int i=1;i<rootNodes.length && (parent != null);i++) {
                        if (!parent.equals(rootNodes[i].getParent())) {
                            parent = null;
                        }
                    }
                    if (parent instanceof ModelContainerNode) {
                        return (ModelContainerNode) parent;
                    } else {
                        parent = null;
                    }
                }
            }
        } catch (Exception e) {
            Dbg.pr("caught an exception in getModelNode()");
            parent = null;
        }
        if (parent == null)
            return getModelRootNode();
        else
            return (ModelContainerNode)parent;
    }
    
    /** method for creating the model node that is associated with this graph display in case this graph display is
     * <em>not</em> part of an XGraphApplication. Subclasser may overwrite
     * this method to return an instance of a subclass of ModelContainerNode.
     */
    protected ModelContainerNode createModelNode() {
        return new ModelContainerNode();
    }
    
    /** returns the ModelNodes of the root XNodes.
     */
    public ModelNode[] getModelNodesOfRoots() {
        ArrayList nodes = new ArrayList();
        Object[] roots = getRoots();
        for(int i=0;i<roots.length;i++) {
            if (roots[i] instanceof XNode) {
                ModelNode mnode = ((XNode)roots[i]).getModelNode();
                if (mnode != null)
                    if (!nodes.contains(mnode))
                        nodes.add(mnode);
            }
        }
        ModelNode[] res = new ModelNode[nodes.size()];
        nodes.toArray(res);
        return res;
    }
    
    /** creates a graph display that is used as clipboard in case this graph display is a "standalone" graph display.
     * If it is part of an application then the clipboard of the application is used and this method will be ignored.
     */
    protected XGraphDisplay createClipboard() {
        return new XGraphDisplay("Clipboard", new XGraphSpec());
    }
    
    /** returns the clipboard that is used for cut/cop/paste actions.
     */
    public XGraphDisplay getClipboard() {
        // if this graph display is part of an application, take the application's clipboard
        if (appl != null) {
            return appl.getClipboard();
        }
        // if this is a "standalone" XGraphDisplay, create an own clipboard
        if (clipboard == null) {
            clipboard = createClipboard();
        }
        return clipboard;
    }
    
    /** clears the clipboard that is used by this grpah display.
     */
    
    public void clearClipboard() {
        XGraphDisplay clipboard = getClipboard();
        if (clipboard != null)
            clipboard.clear();
    }
    
    /** sets the flag that controls whether all elements in the graph will be removed when the graph display is closed
     * or not. */
    public void setRemoveAllOnClosing(boolean b) {
        removeAllOnClosing = b;
    }
    
    /**
     * sets the graph spec of this display. The drawing mode is changed to the initial
     * drawing mode of the spec.
     */
    
    protected void setGraphSpec(XGraphSpec graphSpec) {
        this.graphSpec = graphSpec;
        updateModel();
        switchDrawingMode(graphSpec.getInitialDrawingMode());
    }
    
    public void setTitleString(String t) {
        titleString = t;
    }
    
    public String getTitleString() {
        return value.toString();
    }
    
    /** updates the model with the model stored in the graphSpec
     */
    public void updateModel() {
        setModel(graphSpec.getGraphModel());
        //System.out.println("model.isAttributeStore() = "+getModel().isAttributeStore());
    }
    
    /**
     * returns the drawing modes currently defined for this graph display
     */
    
    public XGraphModel getXGraphModel() {
        return (XGraphModel) getModel();
    }
    
    public XGraphView getXGraphView() {
        return (XGraphView) getView();
    }
    
    public XGraphUI getXGraphUI() {
        return (XGraphUI) getUI();
    }
    
    public Vector getDrawingModes() {
        return graphSpec.getDrawingModes();
    }
    
    /** removes all elements from this graph.
     */
    public void clear() {
        getXGraphModel().removeAll();
    }
    
    /** switches the drawing mode. First the exit() method of the current drawing mode is called,
     * then the currentDrawingMode is changed to the new mode, and finally the enter() method of
     * the new drawing mode is invoked. If the current drawing mode is equal to the new one, no
     * action is performed.
     * @param dm the new drawing mode; currentDrawingMode is set to dm
     */
    public void switchDrawingMode(DrawingMode dm) {
        if (dm == null)
            return;
        if (currentDrawingMode == dm) {
            // do nothing
            return;
        }
        if (!getDrawingModes().contains(dm)) {
            //throw new NoSuchDrawingModeException(dm);
            return;
        }
        if (currentDrawingMode != null) {
            currentDrawingMode.exit(this);
        }
        Dbg.pr("switching to drawing mode \""+dm+"\"");
        currentDrawingMode = dm;
        currentDrawingMode.enter(this);
    }
    
    /**
     * searches for a drawing mode dmStr and calls switchDrawingMode with the resulting
     * DrawingMode object. Does nothing, if a drawing mode with the given name is not
     * registered for the graph display.
     */
    
    public void switchDrawingMode(String dmStr) {
        int index;
        if ((index = getDrawingModes().indexOf(dmStr)) >= 0) {
            switchDrawingMode((DrawingMode) getDrawingModes().elementAt(index));
        } else {
            //throw new NoSuchDrawingModeException(dmStr);
            return;
        }
    }
    
    /** checks for the class of the object <code>v</code>: if it's an <code>XContainerElement</code> the method
     * <code>createContainerView</code> is invoked; if it's an <code>XGraphElement</code> the method
     * <code>createVertexView</code> is used.
     */
    
    protected VertexView createVertexView(Object v, CellMapper cm) {
        VertexView view = null;
        if (v instanceof XContainerNode) {
            XContainerNode cont = (XContainerNode) v;
            view = (VertexView) cont.createContainerView(this,cm);
        }
        if (view == null) {
            if (v instanceof XGraphElement) {
                XGraphElement elem = (XGraphElement) v;
                view = (VertexView) elem.createView(this,cm);
            }
            if (view == null)
                view = super.createVertexView(v,cm);
        }
        return view;
    }
    
    
    /** calls createView in the corresponding object, if it's an instance of XGraphElement.
     */
    
    protected EdgeView createEdgeView(Edge edge, CellMapper cm) {
        if (edge instanceof XGraphElement) {
            XGraphElement elem = (XGraphElement) edge;
            XGraphElementView view0 = elem.createView(this,cm);
            if (view0 instanceof XEdgeView) {
                XEdgeView view = (XEdgeView) view0;
                if (view == null)
                    return super.createEdgeView(edge, cm);
                else {
                    return view;
                }
            } else {
                return super.createEdgeView(edge,cm);
            }
        } else {
            return super.createEdgeView(edge,cm);
        }
    }
    
    
    
    
    /** inserts a graph element in this graph display (either a node or an edge). It calls <code>insertHook</code>
     * method of the element and the <code>mode.insert</code> (in that order).
     */
    public XGraphElementView insertGraphElement(XGraphElement element) {
        CellView cv = getView().getMapping(element,true);
        boolean viewOk = false;
        if (cv != null)
            if (cv instanceof XGraphElementView)
                viewOk = true;
        element.insertHook(this,(viewOk?(XGraphElementView)cv:null));
        getModel().insert(new Object[]{element},null,null,null);
        element.setGraph(this);
        if (cv instanceof XGraphElementView)
            return (XGraphElementView)cv;
        return null;
    }
    
    /** (conv. method) sets the bounds of the graph element view in the graph display.
     * If the element is an <code>XContainerNode</code>, then the <code>collapsedBounds</code> are
     * set to the given rectangle.
     */
    public void setBoundsOfGraphElement(XGraphElement element, Rectangle bounds) {
        if (bounds == null) return;
        Map a = GraphConstants.createMap();
        GraphConstants.setBounds(a, bounds);
        Map ga = new Hashtable();
        CellView cv = getView().getMapping(element,false);
        if (cv != null) {
            ga.put(cv,a);
            getView().edit(ga);
            if (cv instanceof XContainerView) {
                ((XContainerView)cv).setCollapsedBounds(bounds);
            }
            if (cv instanceof XGraphElementView) {
                element.setBoundsHook(this,(XGraphElementView)cv,bounds);
            }
        }
    }
    
    
    /** inserts a graph element and sets its bounds in this graph display using the
     * methods <code>insertGraphElement()</code> with 1 argument and <code>setBoundsOfGraphElement</code>
     */
    protected XGraphElementView insertGraphElement(XGraphElement element, Rectangle bounds) {
        XGraphElementView cv = insertGraphElement(element);
        setBoundsOfGraphElement(element,bounds);
        return cv;
    }
    
    /** inserts a node into the graph and returns the corresponding view object.
     */
    public XNodeView insertNode(XNode node) {
        XGraphElementView cv = insertGraphElement(node);
        ModelNode mnode = node.getModelNode();
        ModelContainerNode mc = getModelNode();
        /*
        try {
            mc.addChild(mnode);
            if (cv instanceof XNodeView)
                return (XNodeView)cv;
        } catch (ModelException me) {
            JOptionPane.showConfirmDialog(this,me.getMessage());
            getModel().remove(new Object[]{node});
        }
         */
        if (cv instanceof XNodeView)
            return (XNodeView)cv;
        return null;
    }
    
    /** inserts a node into the graph and sets its bounds; returns the corresponding view object.
     */
    public XNodeView insertNode(XNode node, Rectangle bounds) {
        XNodeView nv = insertNode(node);
        setBoundsOfGraphElement(node,bounds);
        return nv;
    }
    
    /** insert an edge into the graph; same as <code>insertGraphElement</code>, only that the result is returned as
     * an <code>XEdgeView</code>
     */
    public XEdgeView insertEdge(XEdge edge) {
        XGraphElementView cv = insertGraphElement(edge);
        edge.getModelEdge();
        if (cv instanceof XEdgeView)
            return (XEdgeView)cv;
        return null;
    }
    
    /** sets the points of the view object of an existing edge */
    public void setPointsOfEdge(XGraphElement edge, java.util.List edgePoints) {
        Map viewMap = new Hashtable();
        Map edgeMap = GraphConstants.createMap();
        GraphConstants.setPoints(edgeMap, edgePoints);
        GraphConstants.setBendable(edgeMap, true);
        CellView cv = getView().getMapping(edge, false);
        if (cv != null) {
            viewMap.put(cv,edgeMap);
            getView().edit(viewMap);
        }
        //Object[] cells = new Object[]{edge};
        //getModel().insert(null, null,null,viewMap);
        //getModel().edit(null,viewMap,null,null);
        //getView().edit(viewMap);
    }
    
    public void setLabelPositionOfEdge(XEdge edge, Point lpos) {
        Map viewMap = new Hashtable();
        Map edgeMap = GraphConstants.createMap();
        GraphConstants.setLabelPosition(edgeMap,lpos);
        CellView cv = getView().getMapping(edge, false);
        if (cv != null) {
            viewMap.put(cv,edgeMap);
            getView().edit(viewMap);
        }
    }
    
    /** insert an edge with the given list of points, calls <code>setPointsOfEdge()</code> and <code>insertEdge</code>
     */
    public XEdgeView insertEdge(XEdge edge, ArrayList edgePoints) {
        XEdgeView ev = insertEdge(edge);
        setPointsOfEdge(edge,edgePoints);
        return ev;
    }
    
    /** connects the edge in the graph with the given start and end ports.
     */
    public void connectEdge(XEdge edge, Port startPort, Port endPort) {
        ConnectionSet cs = new ConnectionSet(edge,startPort,endPort);
        //graph.getModel().insert(null,cs,null,null);
        getModel().edit(cs,null,null,null);
    }
    
    /** connects the edge in the graph with the default ports of the given start and end nodes.
     */
    public void connectEdge(XEdge edge, XNode startNode, XNode endNode) {
        connectEdge(edge,startNode.getDefaultPort(),endNode.getDefaultPort());
    }
    
    /** inserts and connects the edge in the graph and adds intermediate points to it; connects to the default
     * ports of the start and end node.
     */
    public XEdgeView insertEdge(XEdge edge, XNode startNode, XNode endNode, Point[] intermediatePoints) {
        return insertEdge(edge,startNode.getDefaultPort(),endNode.getDefaultPort(),intermediatePoints);
    }
    
    /** inserts and connects the edge in the graph using the start and end node ports with the given id; also adds
     * intermediate points.
     */
    
    public XEdgeView insertEdge(XEdge edge, XNode startNode, Object startPortId, XNode endNode, Object endPortId, Point[] intermediatePoints) {
        Port startPort = startNode.getPortAt(startPortId,true);
        Port endPort = endNode.getPortAt(endPortId,true);
        return insertEdge(edge,startPort,endPort,intermediatePoints);
    }
    
    /** inserts and connects the edge in the graph and adds intermediate points to it.
     */
    public XEdgeView insertEdge(XEdge edge, Port startPort, Port endPort, Point[] intermediatePoints) {
        XEdgeView ev = insertEdge(edge);
        connectEdge(edge,startPort,endPort);
        if (ev != null) {
            ev.addIntermediatePoints(intermediatePoints);
        }
        return ev;
    }
    
    public void updateViews(CellView[] views) {
        if (!getModel().isAttributeStore()) {
            Map attributeMap = GraphConstants.createAttributeMap(views, getView());
            GraphView.GraphViewEdit edit = getView().createEdit(attributeMap);
            getModel().edit(null, null, null, new UndoableEdit[]{edit});
            edit.execute();
        } else {
            Map propertyMap = GraphConstants.createPropertyMap(views, null);
            getModel().edit(null, propertyMap, null, null);
        }
    }
    
    /** set the port view that should be highlighted in the graph display. This method is
     * used by the mouse event handlers, if the element under the mouse is a port view. */
    public void setHighlightedPortView(PortView pv) {
        this.highlightedPortView = pv;
    }
    
    /** unsets the port view, that means no port view will be highlighted. This method is
     * used by the mouse event handlers, if no port view element is found at the current
     * mouse position. */
    public void unsetHighlightedPortView() {
        this.highlightedPortView = null;
    }
    
    /** returns all instances of XNode that are currently selected in the graph. */
    public XNode[] getSelectedNodes() {
        Object[] selected = getSelectionCells();
        ArrayList sel = new ArrayList();
        for(int i=0;i<selected.length;i++) {
            if (selected[i] instanceof XNode) {
                sel.add(selected[i]);
            }
        }
        XNode[] res = new XNode[sel.size()];
        sel.toArray(res);
        return res;
    }
    
    /** translates all views according to the given dx,dy values.
     * @param allowNegativeCoordinates if true, views are translated as given by dx,dy; if false,
     * the views are only translated, so that no view gets negative coordinates. In any case, all
     * views are translated with the same values.
     */
    public void translateAllViews(int dx, int dy, boolean allowNegativeCoordinates) {
        if (dx == 0 && dy == 0) return;
        int dx0 = dx, dy0 = dy;
        XGraphView gv = getXGraphView();
        //CellView[] views = gv.getRoots();
        XNodeView[] views = gv.getRootNodeViews();
        if (views.length == 0) return;
        //System.out.println("found "+views.length+" views:");
        if (!allowNegativeCoordinates)
            for(int i=0;i<views.length;i++) {
                Rectangle b = views[i].getBounds();
                if (b.x+dx0<0) dx0=-b.x;
                if (b.y+dy0<0) dy0=-b.y;
            }
        gv.startGroupTranslate();
        gv.translateViews(views,dx0,dy0);
        gv.endGroupTranslate();
        updateViews(views);
    }
    
    /** translates the all views, so that the topleft corner of the topleftmose view element
     * is a (0,0). */
    public void moveAllViewsToOrigin() {
        XGraphView gv = getXGraphView();
        CellView[] views = gv.getRoots();//gv.getAllDescendants(gv.getRoots());
        int minx=0, miny=0;
        boolean firstIteration = true;
        if (views.length == 0) return;
        ArrayList viewsAL = new ArrayList();
        for(int i=0;i<views.length;i++) {
            boolean translateOk = true;
            if (views[i] instanceof EdgeView)
                translateOk = false;
            if (translateOk) {
                Rectangle b = views[i].getBounds();
                if (firstIteration) {
                    minx = b.x;
                    miny = b.y;
                    firstIteration = false;
                } else {
                    minx = Math.min(b.x,minx);
                    miny = Math.min(b.y,miny);
                }
                viewsAL.add(views[i]);
            }
        }
        if (viewsAL.size()==0) return;
        CellView[] tviews = new CellView[viewsAL.size()];
        viewsAL.toArray(tviews);
        gv.startGroupTranslate();
        gv.translateViewsInGroup(tviews, -minx,-miny);
        gv.endGroupTranslate();
        //updateViews(tviews);
    }
    
    /** flag signaling whether a reattachment process is currently carried out by some container node in the graph.
     */
    protected boolean isReattaching = false;
    
    public boolean isReattaching() {
        return isReattaching;
    }
    
    public void startReattaching() {
        Dbg.pr2("start reattaching...");
        isReattaching = true;
    }
    
    public void endReattaching() {
        Dbg.pr2("end reattaching.");
        isReattaching = false;
    }
    
    /** can be called to let the graph show that something is going on in the background.
     */
    public void busy() {
        setCursor(new Cursor(Cursor.WAIT_CURSOR));
    }
    
    /** can be called to undo the effects of the <code>busy</code> method.
     */
    public void done() {
        setCursor(new Cursor(Cursor.DEFAULT_CURSOR));
    }
    
    /** calls paint in JGraph and paints the highlightedPortView, if it's set. */
    public void paint(Graphics g) {
        try {
            super.paint(g);
            Graphics2D g2d = (Graphics2D) g;
            if (highlightedPortView != null) {
                Rectangle r = toScreen(highlightedPortView.getBounds());
                int w = 8;
                int h = 8;
                int x = r.x + r.width/2 - w/2;
                int y = r.y + r.height/2 - h/2;
                Color col1 = Color.red;
                Color col2 = Color.white;
                GradientPaint gp = new GradientPaint(0,0,col1,w/2,h/2,col2,true);
                //getUI().paintCell(g, highlightedPortView, r ,  true);
                g2d.setColor(Color.blue);
                g2d.fill3DRect(x,y,w,h,true);
            }
        } catch (Exception e) {
            System.err.println("error while painting graph display: "+e.getMessage());
        }
    }
    
    /**
     * returns the innermost cell
     */
    public Object getInnerMostCellForLocation(int x, int y) {
        Object cell = super.getFirstCellForLocation(x,y);
        if (cell == null) return null;
        Vector visited = new Vector();
        visited.add(cell);
        for(;;) {
            //System.out.println("current cell: "+cell);
            Object cell1 = getNextCellForLocation(cell,x,y);
            if (visited.contains(cell1)) {
                return cell;
            }
            cell = cell1;
        }
        //return null;
    }
    
    /** flag that determines the behaviour of the <code>getNextViewAt</code> method (and with it all methods that call it
     * like <code>getFirstCellForLocation</code>, <code>getFirstViewAt</code>; if set to true it means that if a selected cell
     * found at the position, it it always returned; if set to false, selected cells have no special treatment.
     */
    protected boolean selectionAlwaysWins = true;
    
    /** sets the flag that determines the behaviour of the <code>getNextViewAt</code> method (and with it all methods that call it
     * like <code>getFirstCellForLocation</code>, <code>getFirstViewAt</code>; if set to true it means that if a selected cell
     * found at the position, it it always returned; if set to false, selected cells have no special treatment.
     */
    public void setSelectionAlwaysWins(boolean b) {
        selectionAlwaysWins = b;
    }
    
    protected Class nextViewClass = null;
    
    /** resets the fields controlling the behaviour of the <code>NextViewAt</code> method to the default values;
     * that means:
     * <ul>
     *<li> <code>setSelectionAlwaysWins(false)</code>
     *<li> <code>setNextViewClass(null)</code>
     *<li> <code>SetNextViewIgnoredViews(null)</code>
     *</ul>
     */
    public void resetNextViewBehaviour() {
        nextViewClass = null;
        nextViewIgnoredViews = null;
        setSelectionAlwaysWins(false);
    }
    
    /** sets the class of the object that is expected from the subsequent calls to <code>getNextViewAt()</code>. This can be used to
     * restrict the result of this method to certain kinds of nodes. For example, if you are only interested in the container nodes
     * at the given point, you might call <code>setNextViewClass("edu.kestrel.graphs.XContainerView")</code>.
     */
    public void setNextViewClass(String classname) {
        if (classname == null) {
            nextViewClass = null;
            return;
        }
        try {
            nextViewClass = Class.forName(classname);
        } catch (ClassNotFoundException e) {
            Dbg.pr(e.getMessage());
        }
    }
    
    protected CellView[] nextViewIgnoredViews = null;
    /** sets the list of views that should be ignored in subsequent calls to <code>getNextViewAt()</code>. This can be used to
     * make certain views transparent concerning which view is chosen to be at a given location.
     */
    public void setNextViewIgnoredViews(CellView[] ignoredViews) {
        nextViewIgnoredViews = ignoredViews;
    }
    
    /** helper method used in <code>getNextViewAt</code> to check whether the cell view complies with the
     * <code>nextViewClass</code> it it has been set
     */
    private boolean checkCellViewClass(CellView cv) {
        if (nextViewClass == null)
            // no restriction on cell view
            return true;
        else
            if (nextViewClass.isInstance(cv))
                // cv has the right class
                return true;
        return false;
    }
    
    private boolean checkCellViewIgnored(CellView cv) {
        if (nextViewIgnoredViews == null) return true;
        for(int i=0;i<nextViewIgnoredViews.length;i++) {
            if (nextViewIgnoredViews[i].equals(cv))
                return false;
        }
        return true;
    }
    
    private CellView checkCellView(CellView cv) {
        if (!checkCellViewClass(cv))
            return null;
        if (!checkCellViewIgnored(cv))
            return null;
        return cv;
    }
    
    /** overwrites the method in the superclass to allow also inner nodes to be selected. The behaviour of this method can
     * be modified as follows:
     * <ul>
     * <li> <code>selectionAlwaysWins(boolean b)</code> sets the flag that determines the behaviour of the <code>getNextViewAt</code> method (and with it all methods that call it
     * like <code>getFirstCellForLocation</code>, <code>getFirstViewAt</code>; if set to true it means that if a selected cell
     * found at the position, it it always returned; if set to false, selected cells have no special treatment.
     * <li> <code>setNextViewClass(String classname)</code> ets the class of the object that is expected from the subsequent calls to <code>getNextViewAt()</code>. This can be used to
     * restrict the result of this method to certain kinds of nodes. For example, if you are only interested in the container nodes
     * at the given point, you might call <code>setNextViewClass("edu.kestrel.graphs.XContainerView")</code>.
     * <li> <code>setNextViewIgnoredViews(CellView[] ignored)</code> can be used to a priori exclude certain views from the list
     * of views to be considered in <code>getNextViewAt()</code>.
     * </ul>
     */
    public CellView getNextViewAt(CellView[] cellviews, CellView c0, int x, int y) {
        CellView c = null;
        CellView candidate = null;
        if (cellviews != null) {
            //System.out.println("checking "+cells.length+" cells, current: "+c);
            Rectangle r = new Rectangle(x-snapSize,y-snapSize,2*snapSize,2*snapSize);
            // contstruct a list of candidate views consisting of the given cell views and
            // all children of the views; only consider those view, which are around (x,y)
            for(int i = 0;i<cellviews.length;i++) {
                boolean candidateFound = false;
                if (GraphConstants.isVisible(cellviews[i].getAttributes()) &&
                cellviews[i].intersects(getGraphics(),r)) {
                    // if an edge is found, return it
                    if (cellviews[i] instanceof EdgeView) {
                        return cellviews[i];
                    }
                    // if an selected element is found, return it (if the flag is set)
                    if (selectionAlwaysWins)
                        if (isCellSelected(cellviews[i].getCell())) {
                            Dbg.pr("returning selected cell as next view at ("+x+","+y+")");
                            return cellviews[i];
                        }
                    if (!candidateFound) {
                        // this is the winner, if there is no child of it at this position
                        if (candidate == null) {
                            CellView cv0 = checkCellView(cellviews[i]);
                            if (cv0 != null)
                                candidate = cv0;
                            // check the children, if any
                            if (cellviews[i] instanceof XContainerView) {
                                java.util.List chviews = ((XContainerView)cellviews[i]).getChildElementViews(true);
                                Iterator iter = chviews.iterator();
                                while(iter.hasNext()) {
                                    CellView cv = (CellView) iter.next();
                                    if (GraphConstants.isVisible(cv.getAttributes()) && cv.intersects(getGraphics(),r)) {
                                        // this must be the winner, because getChildElementViews returns a breadth-first enumeration
                                        if (!candidateFound) {
                                            CellView cv1 = checkCellView(cv);
                                            if (cv1 != null) {
                                                candidate = cv1;
                                                candidateFound = true;
                                            }
                                        }
                                    }
                                }
                            }
                        }
                    }
                }
            }
        }
        return candidate;
    }
    
    /** the string representing the line separator as returned by <code>System.getProperty("line.separator")</code>
     */
    static public String newline = System.getProperty("line.separator");
    
    /** returns the dimentsion of the given text string; the text can consist of
     * multiple lines.
     * @param g underlying graphics object
     * @param text0 the text to be drawn/analyzed
     * @param borderwidth number of pixel to add as extra space around the text box
     * @param minDimension if != null the returned dimension will be at least as big as this
     * @param drawit flag signaling whether the string should actually be drawn, if false, then only the
     * dimensions are computed without drawing the string
     * @param dx if the string is drawn, use this value as x offset
     * @param dy if the string is drawn, use this value as y offset
     */
    
    public Dimension getStringDimension(Graphics g, String text0, int borderwidth, Dimension minDimension, boolean drawit, int dx, int dy) {
        Graphics2D g2d = (Graphics2D) g;
        int xmax = 0;
        int ymax = 0;
        if (minDimension != null) {
            xmax = minDimension.width;
            ymax = minDimension.height;
        }
        if (g==null) return new Dimension(xmax,ymax);
        String text = text0;
        Enumeration iter = getLines(text);
        if (text != null) {
            boolean lastline = false;
            int y = borderwidth;
            while (!lastline) {
                String line = (String)iter.nextElement();
                lastline = !(iter.hasMoreElements());
                if (line.length() > 0) {
                    AttributedString astr = new AttributedString(line);
                    FontMetrics fm = g2d.getFontMetrics();
                    AttributedCharacterIterator ci = astr.getIterator();
                    Rectangle2D trect = fm.getStringBounds(ci,0,line.length(),g2d);
                    int tw = (int)trect.getWidth();
                    int th = (int)trect.getHeight();
                    xmax = Math.max(tw,xmax);
                    if (drawit)
                        g2d.drawString(line,dx+borderwidth,dy+y+th);
                    if (!lastline)
                        y += th + (th/3.0);
                    else
                        y += 0;//th;
                }
            }
            ymax = Math.max(y,ymax);
            //return new Dimension(xmax,ymax);
            return new Dimension(xmax+2*borderwidth,ymax+2*borderwidth);
        }
        return null;
    }
    
    /** utility method returning an enumeration of the lines contained in the given text argument. */
    static public Enumeration getLines(String text0) {
        Vector v = new Vector();
        String text = text0;
        if (text != null) {
            boolean lastline = false;
            while (!lastline) {
                String line;
                int ind = 0;
                if ((ind = text.indexOf(newline)) < 0) {
                    lastline = true;
                    line = text;
                } else {
                    line = text.substring(0,ind);
                    text = text.substring(ind+newline.length());
                }
                v.add(line);
            }
        }
        return v.elements();
    }
    
    //public Object getFirstCellForLocation(int x, int y) {
    //    return getInnerMostCellForLocation(x,y);
    //}
    
    public String convertValueToString_(Object obj) {
        if (obj instanceof XGraphElement) {
            XGraphElement elem = (XGraphElement) obj;
            if (elem.getUserObject() instanceof XGraphCellEditor.MultiLineUserObject) {
                return ((XGraphCellEditor.MultiLineUserObject)elem.getUserObject()).getText();
            }
        }
        return super.convertValueToString(obj);
    }
    
    /** clones cells from this graph display to the given destGraph. It creates an instance of XCloneManager, sets it's
     * createReadOnlyClone flag accordingly and calls its cloneCells() method.
     * @param cells the cells in this graph display to be cloned
     * @param createReadOnlyClone whether or not the clones shall be readonly
     * @param destGraph the graph display to hold the cloned cells
     * @return the cellMap consisting of Object->Object pairs representing original->clone relations as the result of
     * this cloning operation.
     */
    public Map cloneCells(Object[] cells, boolean createReadOnlyClone, XGraphDisplay destGraph) {
        XCloneManager mgr = new XCloneManager(this, cells, destGraph);
        mgr.setCreateReadOnlyClone(createReadOnlyClone);
        mgr.setCreateNewModelElements(false);
        return mgr.cloneCells();
    }
    
    public Map cloneCells(Object[] cells, XGraphDisplay destGraph) {
        return cloneCells(cells,false,destGraph);
    }
    
    public Map copyCells(Object[] cells, XGraphDisplay destGraph) {
        XCloneManager mgr = new XCloneManager(this,cells,destGraph);
        mgr.setCreateNewModelElements(true);
        mgr.setCreateReadOnlyClone(false);
        return mgr.cloneCells();
    }
    
    public Map copyCells(Object[] cells) {
        return copyCells(cells,this);
    }
    
    /** calls cloneCells() with destGraph = this. See documentation there.*/
    public Map cloneCells(Object[] cells, boolean createReadOnlyClone) {
        return cloneCells(cells,createReadOnlyClone,this);
    }
    
    /** the action performed for a copy operation; copies the current selection to the clipboard
     * @return the original nodes that have been copied to the clipboard
     */
    public Object[] copyAction() {
        clearClipboard();
        XGraphDisplay clipboard = getClipboard();
        Object[] selection = getSelectionCells();
        if (selection.length > 0) {
            copyCells(selection,clipboard);
            clipboard.translateAllViews(50,50,true);
        }
        return selection;
    }
    
    /** the action performed for a copy operation; copies the current selection to the clipboard
     * @return the original nodes that have been copied to the clipboard
     */
    public Object[] cloneAction() {
        clearClipboard();
        XGraphDisplay clipboard = getClipboard();
        Object[] selection = getSelectionCells();
        if (selection.length > 0) {
            cloneCells(selection,clipboard);
            clipboard.translateAllViews(50,50,true);
        }
        return selection;
    }
    
    /** the action performed for a cut operation; copies the current selection to the clipboard and removes
     * the original cells.
     * @return the selected cells that have been removed
     */
    public Object[] cutAction() {
        Object[] selection = cloneAction();
        if (selection.length > 0) {
            getXGraphModel().removeNodes(selection);
        }
        return selection;
    }
    
    /** the action performed for a paste operation.
     */
    public void pasteAction() {
        XGraphDisplay clipboard = getClipboard();
        Object[] clipboardCells = clipboard.getXGraphModel().getRootCells();
        clipboard.setSelectionCells(clipboardCells);
        try {
            Map cloneMap = clipboard.cloneCells(clipboardCells,this);
            ArrayList clones = new ArrayList();
            Iterator iter = cloneMap.values().iterator();
            while(iter.hasNext()) {
                clones.add(iter.next());
            }
            setSelectionCells(clones.toArray());
            clipboard.deleteAction();
        } catch (IllegalArgumentException e) {
            JOptionPane.showMessageDialog(this,e.getMessage());
        } finally {
            done();
        }
    }
    
    /** action performed when the graph window is closed. */
    public void closeAction(Rectangle oldbounds) {
        if (removeAllOnClosing) {
            getXGraphModel().removeAll();
        }
        if (oldbounds != null) {
            setSavedBounds(oldbounds);
        }
        if (isEmpty()) {
            appl.unregisterGraph(this);
        }
    }
    
    /** dangerous! Deletes all elements in the graph and closes it.
     */
    public void deleteAction() {
        getXGraphModel().removeAll();
        closeAction(null);
    }
    
    /** returns true, if the graph is empty.
     */
    public boolean isEmpty() {
        return getXGraphModel().isEmpty();
    }
    
    /** sets the bounds of the graph's internal frame; used to re-open the graph at the same position with the same size.
     */
    public void setSavedBounds(Rectangle b) {
        bounds = b;
    }
    
    /** returns previously stored bounds; this information is used to reopen the graph frame at the same position and with
     * the same size as before.
     */
    public Rectangle getSavedBounds() {
        return bounds;
    }
    
    /** overwrites the method in JGraph in order to exclude inner edges from the list of selected cells
     * to avoid undesired effects.
     */
    public void setSelectionCells(Object[] cells) {
        ArrayList l = new ArrayList();
        for(int i=0;i<cells.length;i++) {
            boolean selok = true;
            if (cells[i] instanceof XEdge) {
                if (((XEdge)cells[i]).isInnerEdge())
                    selok = false;
            }
            if (selok)
                l.add(cells[i]);
        }
        super.setSelectionCells(XCloneManager.makeCellsUnique(l.toArray()));
    }
    
    protected static String Element = "Element";
    
    /** returns an element properties object representing this graph for use in io operations.
     */
    public ElementProperties getElementProperties(ReadWriteOperation wop) {
        ElementProperties props = wop.createElementProperties(this);
        props.setValueProperty(getValue());
        Object[] cells = getXGraphModel().getRootCells();
        for(int i=0;i<cells.length;i++) {
            if (cells[i] instanceof Storable) {
                props.addChildObjectAsReference(Element, (Storable)cells[i]);
            }
        }
        return props;
    }
    
    /** initializes a freshly created element of this class using the information stored in the given
     * ElementProperties instance. Used during io operations.
     */
    public void initFromElementProperties(ReadWriteOperation rwop, ElementProperties props) {
        setValue(props.getValueProperty());
        setApplication(rwop.getAppl());
        Dbg.pr("{ initFromElementProperties in XGraphDisplay "+this+"...");
        /*
        ArrayList elist = new ArrayList();
        Map elemReprMap = new Hashtable();
        Enumeration iter = props.getChildObjectAsReferenceEnumeration(Element);
        while (iter.hasMoreElements()) {
            String elemid = (String) iter.nextElement();
            Storable obj = rwop.getObjectForId(elemid);
            if (obj instanceof XNode) {
                XNode node = (XNode)obj;
                Dbg.pr("{ inserting XNode "+node+" into graph "+this+"...");
                ModelNode mnode = node.getModelNode();
                if (mnode != null) {
                    elist.add(mnode);
                    elemReprMap.put(mnode,node);
                }
                Dbg.pr("}");
            }
            if (obj instanceof XEdge) {
                XEdge edge = (XEdge)obj;
                Dbg.pr("{ inserting XEdge "+edge+" into graph "+this+"...");
                ModelEdge medge = edge.getModelEdge();
                if (medge != null) {
                    elist.add(medge);
                    elemReprMap.put(medge,edge);
                }
                Dbg.pr("}");
            }
        }
        ModelElement[] elems = new ModelElement[elist.size()];
        elist.toArray(elems);
        appl.insertModelElementsIntoGraph(this,elems,elemReprMap);
         */
        Dbg.pr("}");
    }
    
    
    /**
     * convenience method creating/extending a JToolBar containing JButtons for switching between the
     * drawing modes defined for this graph display.
     * @param toolBar the toolBar where the button will be added. If toolBar == null, then a
     * new JToolBar instance is created and returned.
     * @param direction JToolBar.HORIZONTAL or JToolBar.VERTICAL; ignored if toolBar != null
     * @return the extended toolBar, if it existed before; otherwise the newly created toolBar containing
     * the new buttons.
     */
    
    public JToolBar getDrawingModesToolBar(JToolBar toolBar, int direction) {
        JToolBar tb = toolBar;
        if (tb == null) {
            tb = new JToolBar(direction);
            tb.setFloatable(false);
        }
        ButtonGroup grp = new ButtonGroup();
        JToggleButton btn;
        Enumeration iter = getDrawingModes().elements();
        while (iter.hasMoreElements()) {
            DrawingMode dm = (DrawingMode) iter.nextElement();
            if (dm.getImageIcon() == null)
                btn = new JToggleButton(dm.getMenuString(),true);
            else
                btn = new JToggleButton(dm.getImageIcon(),true);
            btn.setMargin(new Insets(0,0,0,0));
            btn.setToolTipText("drawing mode: "+dm.getMenuString());
            btn.addActionListener(new ActionListenerForDrawingModeToolBar(dm));
            tb.add(btn);
            grp.add(btn);
        }
        return tb;
    }
    
    /** creates the toolbar containing the drawing mode buttons and the action buttons like copy/cut/paste.
     */
    public JToolBar createToolBar(int direction) {
        JToolBar tb = getDrawingModesToolBar(null,direction);
        tb.addSeparator();
        tb.setFloatable(false);
        JButton btn;
        // cut
        btn = new JButton(IconImageData.cut24Icon);
        btn.setMargin(new Insets(0,0,0,0));
        btn.setToolTipText("cut");
        btn.addActionListener(new ActionListener() {
            public void actionPerformed(ActionEvent e) {
                Dbg.pr("cut");
                cutAction();
            }
        });
        tb.add(btn);
        // copy
        btn = new JButton(IconImageData.copy24Icon);
        btn.setMargin(new Insets(0,0,0,0));
        btn.setToolTipText("copy");
        btn.addActionListener(new ActionListener() {
            public void actionPerformed(ActionEvent e) {
                Dbg.pr("copy...");
                copyAction();
            }
        });
        tb.add(btn);
        // clone
        btn = new JButton(IconImageData2.clone24Icon);
        btn.setMargin(new Insets(0,0,0,0));
        btn.setToolTipText("clone");
        btn.addActionListener(new ActionListener() {
            public void actionPerformed(ActionEvent e) {
                Dbg.pr("clone...");
                cloneAction();
            }
        });
        tb.add(btn);
        // paste
        btn = new JButton(IconImageData.paste24Icon);
        btn.setMargin(new Insets(0,0,0,0));
        btn.setToolTipText("paste");
        btn.addActionListener(new ActionListener() {
            public void actionPerformed(ActionEvent e) {
                Dbg.pr("paste");
                pasteAction();
            }
        });
        tb.add(btn);
        return tb;
    }
    
    class ActionListenerForDrawingModeToolBar implements ActionListener {
        private DrawingMode dm;
        public ActionListenerForDrawingModeToolBar(DrawingMode dm) {
            this.dm = dm;
        }
        public void actionPerformed(ActionEvent e) {
            //System.out.println("drawing mode: "+dm);
            switchDrawingMode(dm);
        }
    }
    
    public XBasicMarqueeHandler getXMarqueeHandler() {
        return (XBasicMarqueeHandler) getMarqueeHandler();
    }
    
    
    /** overrides the method in JGraph to avoid adding a sample model. */
    static public void addSampleData(GraphModel m) {
        //System.out.println("no sample data...");
    }
    
    /** static utility method, mainly for debuggin purposes. */
    static public void showAttributes(Map map) {
        Set keys = map.keySet();
        Iterator iter = keys.iterator();
        while (iter.hasNext()) {
            Object obj = iter.next();
            Dbg.pr(obj+": "+map.get(obj));
        }
    }
    
    /** static utility method, mainly for debuggin purposes. */
    static public void showAttributes(CellView v) {
        showAttributes(v.getAttributes());
    }
    
    /** static utility method, mainly for debuggin purposes. */
    static public void showAttributes(GraphCell c) {
        Dbg.pr("graph cell \""+c+"\":");
        showAttributes(c.getAttributes());
        if (c instanceof TreeNode) {
            Dbg.pr("children:");
            Enumeration iter = ((TreeNode)c).children();
            while (iter.hasMoreElements()) {
                Object obj = iter.nextElement();
                Dbg.pr("   "+obj+" ("+obj.getClass().getName()+")");
            }
        }
        if (c instanceof XNode) {
            XNode n = (XNode)c;
            ModelNode mnode = n.getModelNode();
            if (n.equals(mnode.getReprExemplar())) {
                Dbg.pr(".. is reprExemplar of model node");
            }
        }
        if (c instanceof XContainerNode) {
            XContainerNode n = (XContainerNode) c;
            Dbg.pr("savedCollapsedBounds="+n.getSavedCollapsedBounds());
            Dbg.pr("savedIsExpanded="+n.getSavedIsExpanded());
        }
        if (c instanceof XEdge) {
            XEdge e = (XEdge) c;
            Object p = e.getSource();
            Dbg.pr("getSource(): "+p);
            if (p instanceof DefaultPort) {
                DefaultPort dp = (DefaultPort) p;
                Dbg.pr("   edges: ");
                Iterator iter = dp.edges();
                while(iter.hasNext()) {
                    Dbg.pr("   "+iter.next());
                }
            }
            p = e.getTarget();
            Dbg.pr("getTarget(): "+p);
            if (p instanceof DefaultPort) {
                DefaultPort dp = (DefaultPort) p;
                Dbg.pr("   edges: ");
                Iterator iter = dp.edges();
                while(iter.hasNext()) {
                    Dbg.pr("   "+iter.next());
                }
            }
            Dbg.pr("getSourceNode(): "+e.getSourceNode());
            Dbg.pr("getTargetNode(): "+e.getTargetNode());
            if (e.isDetached())
                Dbg.pr("isDetached(): true");
        }
    }
    
    
    /**
     * test of XGraphDisplay class
     */
    
    static public void main(String[] args) {
        Dbg.pr("Running Java version "+System.getProperty("java.version"));
        //String[] fontNames = GraphicsEnvironment.getLocalGraphicsEnvironment().getAvailableFontFamilyNames();
        //for(int i=0;i<fontNames.length;i++) {
        //    Dbg.pr("font: \""+fontNames[i]+"\"");
        //}
        JFrame frame = new JFrame("Test XGraphDisplay");
        frame.getContentPane().setLayout(new BorderLayout());
        Dbg.setDebugLevel(1);
        
        XGraphDisplay graph = new XGraphDisplay();
        frame.addWindowListener(new WindowAdapter() {
            public void windowClosing(WindowEvent e) {
                System.exit(0);
            }
        });
        frame.getContentPane().add(new JScrollPane(graph));
        frame.getContentPane().add(graph.createToolBar(JToolBar.HORIZONTAL),"North");
        frame.setSize(500,500);
        frame.show();
    }
}
