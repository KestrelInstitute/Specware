/*
 * XContainerView.java
 *
 * Created on November 1, 2002, 5:54 PM
 */

package edu.kestrel.graphs;

import com.jgraph.graph.*;
import javax.swing.*;
import java.awt.font.*;
import java.awt.event.*;
import java.awt.geom.*;
import java.awt.*;
import java.util.*;

/**
 * The super class for all views of container nodes.
 *
 * @author  ma
 */
public abstract class XContainerView extends XNodeView implements XGraphElementView {
    
    protected XContainerNode node;
    
    //private Rectangle savedBounds = null;
    //private Rectangle boundsBeforeCollapsing = null;
    //private Rectangle boundsBeforeExpanding = null;
    private Rectangle collapsedBounds;
    
    protected boolean expanded;
    
    protected boolean isSwitchingState = false;
    
    private Map savedChildrensBounds = null;
    
    public ViewOptions viewOptionsExpanded;
    public ViewOptions viewOptionsCollapsed;
    
    protected JMenuItem expandCollapseMenuItem;
    
    protected XGraphDisplay xgraph;
    
    /** Creates a new instance of XContainerView */
    public XContainerView(XContainerNode node, XGraphDisplay graph, CellMapper cm) {
        super(node,graph,cm);
        this.node = node;
        this.viewOptionsExpanded = new ViewOptions();
        this.viewOptionsCollapsed = new ViewOptions();
        this.expanded = false;
        this.xgraph = graph;
        Rectangle b = node.getSavedCollapsedBounds();
        if (b != null) {
            //Dbg.pr("XContainerView for node "+node+": collapsedBounds initialized with "+b);
            collapsedBounds = new Rectangle(b);
        }
        //refreshAfterStateChange();
        //Dbg.pr("new container view created for "+node+", #children: "+getChildViews().length);
    }
    
    protected void initPopupMenu() {
        super.initPopupMenu();
        boolean isEditable = true;
        if (node != null)
            isEditable = node.isEditable();
        expandCollapseMenuItem = new JMenuItem();
        expandCollapseMenuItem.addActionListener(new ActionListener() {
            public void actionPerformed(ActionEvent e) {
                toggleExpandCollapse();
                graph.repaint();
            }
        });
        configureExpandCollapseMenuItem();
        popupMenu.add(expandCollapseMenuItem,0);
        JMenuItem menuItem;
        menuItem = new JMenuItem("update bounds");
        menuItem.addActionListener(new ActionListener() {
            public void actionPerformed(ActionEvent e) {
                setBoundsToChildrenBounds();
                graph.repaint();
            }
        });
        menuItem.setEnabled(isEditable);
        popupMenu.add(menuItem);
        menuItem = new JMenuItem("add contained nodes as children");
        menuItem.addActionListener(new ActionListener() {
            public void actionPerformed(ActionEvent e) {
                addContainedNodes(false);
            }
        });
        menuItem.setEnabled(isEditable);
        popupMenu.add(menuItem);
        if (Dbg.isDebug()) {
            menuItem = new JMenuItem("select inner edges");
            menuItem.addActionListener(new ActionListener() {
                public void actionPerformed(ActionEvent e) {
                    XEdge[] edges = node.getInnerEdges();
                    graph.getSelectionModel().setSelectionCells(edges);
                }
            });
            popupMenu.add(menuItem);
            menuItem = new JMenuItem("select inner to outer edges");
            menuItem.addActionListener(new ActionListener() {
                public void actionPerformed(ActionEvent e) {
                    XEdge[] edges = node.getInnerConnToOuterEdges();
                    graph.getSelectionModel().setSelectionCells(edges);
                }
            });
            popupMenu.add(menuItem);
            menuItem = new JMenuItem("select all children");
            menuItem.addActionListener(new ActionListener() {
                public void actionPerformed(ActionEvent e) {
                    java.util.List children = getChildElementViews(true);
                    Iterator iter = children.iterator();
                    int i = 0;
                    Object[] sel = new Object[children.size()];
                    while(iter.hasNext())
                        sel[i++] = ((CellView)iter.next()).getCell();
                    graph.getSelectionModel().setSelectionCells(sel);
                    
                }
            });
            popupMenu.add(menuItem);
            menuItem = new JMenuItem("detach all children");
            menuItem.addActionListener(new ActionListener() {
                public void actionPerformed(ActionEvent e) {
                    node.detachChildren((XGraphDisplay)graph);
                }
            });
            menuItem.setEnabled(false);
            popupMenu.add(menuItem);
            menuItem = new JMenuItem("re-attach children");
            menuItem.addActionListener(new ActionListener() {
                public void actionPerformed(ActionEvent e) {
                    node.reAttachChildren((XGraphDisplay)graph);
                }
            });
            popupMenu.add(menuItem);
            menuItem = new JMenuItem("lift edges");
            menuItem.addActionListener(new ActionListener() {
                public void actionPerformed(ActionEvent e) {
                    node.liftEdgesFromChildren((XGraphDisplay)graph);
                }
            });
            popupMenu.add(menuItem);
            menuItem = new JMenuItem("reconnect lifted edges");
            menuItem.addActionListener(new ActionListener() {
                public void actionPerformed(ActionEvent e) {
                    node.reconnectLiftedEdges((XGraphDisplay)graph);
                }
            });
            popupMenu.add(menuItem);
        }
    }
    
    public void showPopupMenu(Component c, int x, int y) {
        configureExpandCollapseMenuItem();
        super.showPopupMenu(c,x,y);
    }
    
    
    
    public void setCollapsedBounds(Rectangle b) {
        collapsedBounds = new Rectangle(b);
        node.setSavedCollapsedBounds(b);
    }
    
    public Rectangle getCollapsedBounds() {
        return collapsedBounds;
    }
    
    private XEdgeView[] getEdgeViewArrayFromEdgeArray(XEdge[] edges) {
        ArrayList res = new ArrayList();
        for(int i=0;i<edges.length;i++) {
            CellView cv = graph.getView().getMapping(edges[i],false);
            if (cv instanceof XEdgeView) {
                res.add(cv);
            }
        }
        XEdgeView[] edgeViews = new XEdgeView[res.size()];
        res.toArray(edgeViews);
        return edgeViews;
    }
    
    static private boolean isAddingContainedNodes = false;
    
    protected static boolean addingOfContainedNodesEnabled = true;
    
    /** enable or disable the automatically asking the user whether geomertrically contained nodes should be added
     * as children to the container.
     */
    public static void enableAddingOfContainedNodes(boolean enable) {
        addingOfContainedNodesEnabled = enable;
    }
    
    /** adds the nodes whose views are contained in this view to the associated container node. */
    public void addContainedNodes(boolean interactive) {
        if (isAddingContainedNodes) return;
        if (isTemporaryView()) return;
        if (node == null) return;
        isAddingContainedNodes = true;
        XNode[] siblings = node.getSiblings(graph.getModel());
        ArrayList sel = new ArrayList();
        for(int i=0;i<siblings.length;i++) {
            if (!node.isNodeDescendant(siblings[i]))
                if (containsNode(siblings[i])) {
                    if (sel.size() == 0) graph.clearSelection();
                    sel.add(siblings[i]);
                    graph.addSelectionCell(siblings[i]);
                }
        }
        if (sel.size() > 0) {
            graph.repaint();
            XNode[] selNodes = new XNode[sel.size()];
            sel.toArray(selNodes);
            addChildNodes(selNodes,interactive);
        }
        isAddingContainedNodes = false;
    }
    /** returns the views of the inner edges returned by <code>getInnerEdge</code> from the corresponding model element.
     */
    public XEdgeView[] getInnerEdgeViews() {
        if (node == null) return new XEdgeView[]{};
        XEdge[] edges = node.getInnerEdges();
        return getEdgeViewArrayFromEdgeArray(edges);
    }
    
    public XEdgeView[] getInnerConnToOuterEdgeViews() {
        if (node == null) return new XEdgeView[]{};
        XEdge[] edges = node.getInnerConnToOuterEdges();
        return getEdgeViewArrayFromEdgeArray(edges);
    }
    
    /** deletes the container node and the entire contents of it. */
    public void delete_(boolean interactive) {
        Dbg.pr("deleting container view...");
        if (interactive) {
            int anws = JOptionPane.showConfirmDialog(graph, "Do you really want to delete this node?", "Delete?", JOptionPane.OK_CANCEL_OPTION);
            if (anws != JOptionPane.YES_OPTION) return;
        }
        node.remove(graph.getModel());
    }
    
    protected void configureExpandCollapseMenuItem() {
        if (isExpanded()) {
            expandCollapseMenuItem.setText("collapse");
        } else {
            expandCollapseMenuItem.setText("expand");
        }
        if (node != null) {
            if (!node.isExpandable()) {
                expandCollapseMenuItem.setEnabled(false);
            }
        }
    }
    
    /** the action that is invoked when a double click is made: if the node has no children, then edit, else expand or collapse.
     */
    public void doubleClickAction() {
        if (!node.hasChildren()) {
            graph.startEditingAtCell(node);
        } else {
            if (isExpanded())
                collapse();
            else
                expand();
        }
    }
    
    public XContainerNode getContainerNode() {
        Object cell = getCell();
        if (cell instanceof XContainerNode) {
            return (XContainerNode) cell;
        }
        throw new IllegalArgumentException("cell object of container view is not a container node.");
    }
    
    public boolean isExpanded() {
        return expanded;
    }
    
    public boolean isCollapsed() {
        return !isExpanded();
    }
    
    public void setChildrensVisibility(boolean visible) {
        CellView[] chviews = getDescendantViews(getChildViews());
        if (chviews.length > 0) {
            Map viewMap = new Hashtable();
            for(int i=0;i<chviews.length;i++) {
                Object cell = chviews[i].getCell();
                Map map = GraphConstants.createMap();
                GraphConstants.setVisible(map, visible);
                viewMap.put(cell,map);
                if (cell instanceof XNode) {
                    XNode n = (XNode) cell;
                    java.util.List grandchildren = n.getChildren();
                    for(int j=0;j<grandchildren.size();j++) {
                        //System.out.println("object of class "+grandchildren.get(i).getClass().getName());
                        Map map0 = GraphConstants.createMap();
                        GraphConstants.setVisible(map0, visible);
                        viewMap.put(grandchildren.get(i),map0);
                    }
                }
            }
            graph.getModel().edit(null,viewMap,null,null);
        }
    }
    
    /** returns all child views that are instance of <code>XGraphElementView</code>.
     * @param recurse if set to true, collect all views recursively.
     */
    public java.util.List getChildElementViews(boolean recurse) {
        ArrayList res = new ArrayList();
        CellView[] views = getChildViews();
        for(int i=0;i<views.length;i++) {
            if (views[i] instanceof XGraphElementView) {
                if (recurse) {
                    if (views[i] instanceof XContainerView) {
                        res.addAll(((XContainerView)views[i]).getChildElementViews(recurse));
                    }
                }
                res.add(views[i]);
            }
        }
        return res;
    }
    
    /** adds the nodes as children to the associated container node.
     * @return the XNodeViews of the nodes, for which the adding as child has succeeded.
     */
    public XNodeView[] addChildNodes(XNode[] childnodes0, boolean interactive) {
        // first filter out those node, which already have this node as parent
        ArrayList newchildren = new ArrayList();
        for(int i=0;i<childnodes0.length;i++) {
            if (childnodes0[i].getParent() == null) {
                newchildren.add(childnodes0[i]);
            }
            else if (!childnodes0[i].isNodeAncestor(node))
                //else if (!childnodes0[i].getParent().equals(node))
                newchildren.add(childnodes0[i]);
        }
        XNode[] childnodes = new XNode[newchildren.size()];
        newchildren.toArray(childnodes);
        if (childnodes.length == 0) return null;
        if (interactive) {
            int answ = JOptionPane.showConfirmDialog(graph, "Do you want to insert these "+childnodes.length+" node(s) into this node?", "Insert?", JOptionPane.OK_CANCEL_OPTION);
            if (answ != JOptionPane.YES_OPTION) return null;
        }
        expand();
        XNode[] adopted = node.addChildNodes((XGraphDisplay)graph, childnodes);
        graph.setSelectionCell(node);
        ArrayList res = new ArrayList();
        for(int i=0;i<adopted.length;i++) {
            CellView cv = graph.getView().getMapping(adopted[i],false);
            if (cv != null)
                if (cv instanceof XNodeView)
                    res.add(cv);
        }
        XNodeView[] resArray = new XNodeView[res.size()];
        res.toArray(resArray);
        return resArray;
    }
    
    /** checks whether the view of the node lies inside the container */
    public boolean containsNode(XNode node) {
        CellView cv = graph.getView().getMapping(node, false);
        if (cv == null) return false;
        return bounds.contains(cv.getBounds());
    }
    
    public void showChildren() {
        setChildrensVisibility(true);
    }
    
    public void hideChildren() {
        setChildrensVisibility(false);
    }
    
    /** expands the node, that means that inner nodes and edges will be shown */
    public void expand() {
        if (!node.isExpandable()) return;
        if (isExpanded()) return;
        ((XGraphDisplay)graph).busy();
        Dbg.pr("expanding "+node+" in graph "+(((XGraphDisplay)graph).getValue())+"...");
        isSwitchingState = true;
        ((XGraphDisplay)graph).getXGraphView().updateAllPorts();
        collapsedBounds = new Rectangle(getBounds());
        node.setSavedCollapsedBounds(collapsedBounds);
        //Dbg.pr("in expand: setting collapsed bounds to "+collapsedBounds);
        node.reAttachChildren((XGraphDisplay)graph);
        expanded = true;
        configureExpandCollapseMenuItem();
        setSizeable(false);
        node.reconnectLiftedEdges((XGraphDisplay)graph);
        isSwitchingState = false;
        //makeChildrenFit(bounds,false);
        Rectangle b0 = getBounds();
        exportBounds(b0);
        //alignToCenterOf(collapsedBounds);
        setBoundsToChildrenBounds();
        ((XGraphDisplay)graph).getXGraphView().updateAllPorts();
        ((XGraphDisplay)graph).done();
        node.setSavedIsExpanded(true);
    }
    
    /** collapse the node, that means that inner nodes and edges will not be shown. */
    public void collapse() {
        if (!isExpanded()) return;
        ((XGraphDisplay)graph).busy();
        Dbg.pr("collapsing "+node+", bounds="+getBounds()+"...");
        Rectangle b = getBounds();
        isSwitchingState = true;
        node.liftEdgesFromChildren((XGraphDisplay)graph);
        node.detachChildren((XGraphDisplay)graph);
        expanded = false;
        configureExpandCollapseMenuItem();
        setSizeable(true);
        if (collapsedBounds != null) {
            Rectangle b0 = (new Rectangle(b.x,b.y,collapsedBounds.width,collapsedBounds.height));
            exportBounds(b0);
        }
        isSwitchingState = false;
        //alignToCenterOf(b);
        ((XGraphDisplay)graph).getXGraphView().updateAllPorts();
        ((XGraphDisplay)graph).done();
        node.setSavedIsExpanded(false);
    }
    
    protected void setSizeable(boolean b) {
        Map viewMap = new Hashtable();
        Map map = GraphConstants.createMap();
        GraphConstants.setSizeable(map,b);
        //GraphConstants.setMoveable(map,b);
        viewMap.put(this, map);
        graph.getView().edit(viewMap);
    }
    
    public void toggleExpandCollapse() {
        if (isExpanded())
            collapse();
        else
            expand();
    }
    
    /** saves the bounds of the children relatively to the top-left corner of the container */
    protected void saveChildrensBounds_() {
        savedChildrensBounds = new Hashtable();
        CellView[] chviews = getChildViews();
        for(int i=0;i<chviews.length;i++) {
            Rectangle b = chviews[i].getBounds();
            //Rectangle rect = new Rectangle(b.x-bounds.x,b.y-bounds.y,b.width,b.height);
            //System.out.println("saving rect "+rect);
            savedChildrensBounds.put(chviews[i],b);
        }
    }
    
    private boolean isChildView(CellView v) {
        CellView[] cviews = getChildViews();
        for(int i=0;i<cviews.length;i++) {
            if (v.equals(cviews[i]))
                return true;
        }
        return false;
    }
    
    protected void restoreChildrensBounds_(int dx, int dy) {
        if (savedChildrensBounds == null) return;
        Dbg.pr("restoring children's bounds...");
        Set keys = savedChildrensBounds.keySet();
        Iterator iter = keys.iterator();
        Map viewMap = new Hashtable();
        while(iter.hasNext()) {
            CellView cview = (CellView) iter.next();
            if (Dbg.isDebug()) {
                if (!isChildView(cview))
                    Dbg.pr("restoring bounds of view that's not a child view!??");
            }
            Rectangle b = (Rectangle) savedChildrensBounds.get(cview);
            //Map map = GraphConstants.createMap();
            //GraphConstants.setBounds(map,b);
            if (cview instanceof AbstractCellView) {
                AbstractCellView acview = (AbstractCellView) cview;
                acview.setBounds(b);
            }
            graph.getView().translateViews(new CellView[]{cview},dx,dy);
        }
        //graph.getModel().edit(null,viewMap,null,null);
    }
    
    public Rectangle getBounds() {
        //Dbg.pr("getBounds() for node "+node+" ("+node.getClass().getName()+")");
        Rectangle bounds = GraphConstants.getBounds(getAttributes());
        Rectangle cbounds = bounds;//super.getBounds();
        //if (!isExpanded()) {
        //    collapsedBounds = bounds;
        //}
        //makeChildrenFit(bounds, true);
        //System.out.println("  new: "+cbounds);
        //savedBounds = cbounds;
        //Rectangle cbounds = bounds;
        if (!isLeaf()) {
            //int bw = 10;
            //cbounds = AbstractCellView.getBounds(getChildViews());
            //cbounds = new Rectangle(cbounds.x-bw,cbounds.y-bw,cbounds.width+2*bw,cbounds.height+2*bw);
            cbounds = getChildrenBounds(getChildViews(),null);
        }
        if (isExpanded()) bounds.add(cbounds);
        if (collapsedBounds == null) {
            collapsedBounds = new Rectangle(bounds);
            node.setSavedCollapsedBounds(collapsedBounds);
        }
        //Dbg.pr("in getBounds(): collapsedBounds="+collapsedBounds);
        if (node != null) {
            node.setSavedBounds(bounds);
            if (isCollapsed()) {
                node.setSavedCollapsedBounds(new Rectangle(bounds));
            }
        }
        node.setSavedIsExpanded(isExpanded());
        return bounds;
    }
    
    /** align the center of the view and the given rectangle; used in expanding and collapsing. */
    protected void alignToCenterOf(Rectangle b) {
        Rectangle bounds = getBounds();
        int dx = b.width/2 - bounds.width/2;
        int dy = b.height/2 - bounds.height/2;
        //GraphView.translateViews(new CellView[]{this},dx,dy);
        translate(dx,dy);
        XEdgeView[] eviews = getInnerEdgeViews();
        for(int i=0;i<eviews.length;i++) {
            eviews[i].translate(dx,dy);
            eviews[i].update();
        }
    }
    
    /** returns the bounds of the node and edges inside the container */
    protected Rectangle getChildrenBounds() {
        return getChildrenBounds(getChildViews(),getInnerEdgeViews());
    }
    
    private Rectangle getChildrenBounds(CellView[] chviews, XEdgeView[] edgeviews) {
        //CellView[] chviews = getChildViews();
        Rectangle cbounds = AbstractCellView.getBounds(chviews);
        Rectangle ebounds = AbstractCellView.getBounds(edgeviews);
        if (cbounds == null) return bounds;
        if (ebounds != null) cbounds.add(ebounds);
        int bw = viewOptionsExpanded.internalBorderWidth;
        // add some pixels border width
        cbounds.grow(bw,bw);
        return cbounds;
    }
    
    public void setBoundsToChildrenBounds() {
        Rectangle b0 = getChildrenBounds();
        //Rectangle b0 = getChildrenBounds(getChildViews(),null);
        exportBounds(b0);
    }
    
    public void exportBounds(Rectangle b) {
        GraphConstants.setBounds(getAttributes(),b);
        Map viewMap = new Hashtable();
        Map map = GraphConstants.createMap();
        GraphConstants.setBounds(map,b);
        viewMap.put(this, map);
        graph.getView().edit(viewMap);
    }
    
    public void update() {
        //Dbg.pr("updating container "+node);
        if (getChildViews().length > 0) {
            if (!expanded) {
                //repair
                //expand();
                expanded = true;
                configureExpandCollapseMenuItem();
                //setSizeable(false);
            }
        }
        super.update();
    }
    
    public void refresh(boolean b) {
        super.refresh(b);
    }
    
    
    public void translate(int dx, int dy) {
        //Dbg.pr("translating container view...");
        super.translate(dx,dy);
    }
    
    protected abstract class XContainerRenderer extends XNodeRenderer {
        
        public XContainerRenderer(XContainerView view) {
            super(view);
        }
        
        public void paint(Graphics g) {
            if (isExpanded()) {
                viewOptions = viewOptionsExpanded;
            } else {
                viewOptions = viewOptionsCollapsed;
            }
            super.paint(g);
        }
        
    }
    
    /**
     * Returns a cell handle for the view, if the graph and the view
     * are sizeable.
     */
    public CellHandle getHandle(GraphContext context) {
        if (GraphConstants.isSizeable(getAttributes()) &&
        context.getGraph().isSizeable())
            return new SizeHandle(this, context);
        return null;
    }
    
    public class SizeHandle extends VertexView.SizeHandle {
        public SizeHandle(VertexView vertexview, GraphContext ctx) {
            super(vertexview, ctx);
            //System.out.println("SizeHandle in XContainerView created.");
        }
        public void mousePressed(MouseEvent e) {
            if (vertex instanceof XContainerView) {
                //Dbg.pr("mouse pressed in size handle of container.");
                //((XContainerView)vertex).getContainerNode().detachChildren((XGraphDisplay)graph);
            }
            super.mousePressed(e);
        }
        public void mouseReleased(MouseEvent e) {
            if (vertex instanceof XContainerView) {
                ((XContainerView)vertex).addContainedNodes(true);
                //((XContainerView)vertex).getContainerNode().reAttachChildren((XGraphDisplay)graph);
            }
            super.mouseReleased(e);
        }
    }
    
}
