package edu.kestrel.especs.graphs;

import com.jgraph.graph.*;

import edu.kestrel.especs.graphs.spec.*;
import edu.kestrel.graphs.*;
import edu.kestrel.graphs.spec.*;
import java.util.*;
import java.awt.*;

/**
 * This class implements an espec node.
 *
 * @author  ma
 */
public class EspecNode extends XContainerNode {
    
    protected static int especCnt = 0;
    
    /** Creates a new instance of XEspecNode */
    public EspecNode() {
        super((String)null);
    }
    
    public EspecNode(String name) {
        super(name);
    }
    
    public ModelNode createModelNode() {
        return new EspecModelNode();
    }
    
    
    
    /*
    public EspecNode(ModelNode mnode) {
        super(mnode);
    }
     */
    
    public void setInitialValue() {
        setUserObject("E"+(especCnt++));
    }
    
    /*
    public EspecNode(String name, XGraphDisplay graph, java.util.List childNodes) {
        super(name,graph,childNodes);
    }
     
    public EspecNode(String name, XGraphDisplay graph, XNode[] childNodes) {
        super(name,graph,childNodes);
    }
     */
    
    /** creates the view of the container; to sets of view options have to be given: viewOptionsExpanded and viewOptionsCollapsed
     * determining the appearance depending on whether the node is expanded (showing its contents) or collapsed (hiding
     * its contents).
     */
    public XContainerView createContainerView(XGraphDisplay graph, CellMapper cm) {
        EspecView v = new EspecView(this, graph, cm);
        installDefaultContainerViewSettings(v);
        Color bgColor = new Color(97,206,197);
        // collapsed
        v.viewOptionsCollapsed.setUseBorder(true);
        v.viewOptionsCollapsed.setBorderWidth(1);
        v.viewOptionsCollapsed.setUseGradientPaint(true);
        v.viewOptionsCollapsed.setGradientPaintTopLeftColor(bgColor);
        //v.viewOptionsCollapsed.setUseIcon(true);
        //v.viewOptionsCollapsed.setImageIconFileName("/tmp/engine.gif");
        //v.viewOptionsCollapsed.setImageIcon(EConstants.e24Icon);
        // expanded
        v.viewOptionsExpanded.setUseBorder(true);
        v.viewOptionsExpanded.setBorderWidth(1);
        v.viewOptionsExpanded.setUseSolidPaint(true);
        v.viewOptionsExpanded.setSolidPaintColor(graph.getBackground());
        //v.viewOptionsExpanded.setKeepBoundsWhenCollapsing(true);
        //v.viewOptionsCollapsed.setGradientPaintTopLeftColor(bgColor);
        return v;
        
    }
    
    /** returns the number of ports for each dimension. For example, if this method returns 10 for a
     * rectangular shaped node, then 10 ports will be created on each side of the rectangle.
     *
     */
    protected int getPortsPerDimension() {
        return defaultNumberOfPortsPerDimension;
    }
    
    /** see {@link edu.kestrel.graphs.XBoxNode#getYValues} */
    protected double[] getYValues(double x) {
        double[] res = new double[2];
        res[0] = 0;
        res[1] = 1;
        return res;
    }
    
    /** see {@link edu.kestrel.graphs.XBoxNode#getXValues} */
    protected double[] getXValues(double y) {
        return getYValues(y);
    }
    
    /** see {@link edu.kestrel.graphs.XBoxNode#insertHook} */
    public void insertHook(XGraphDisplay graph, XGraphElementView viewObject) {
        super.insertHook(graph,viewObject);
        GraphModel model = graph.getModel();
        Map viewMap = new Hashtable();
        Map map = GraphConstants.createMap();
        GraphConstants.setFontSize(map,12);
        GraphConstants.setFontStyle(map,Font.PLAIN);
        GraphConstants.setOpaque(map, false);
        viewMap.put(this,map);
        model.edit(null,viewMap,null,null);
        createImportEdgeInGraph(graph);
    }
    
    private Map copyCellsForImport() {
        ImportManager mgr = new ImportManager(getGraph(),new Object[]{this},getGraph().getClipboard());
        mgr.setCreateNewModelElements(true);
        mgr.setCreateReadOnlyClone(false);
        return mgr.cloneCells();
    }
    
    public EspecNode createImport(Object newName) {
        if (getGraph() == null) return null;
        Map cellMap = copyCellsForImport();
        if (cellMap == null) return null;
        if (!cellMap.containsKey(this)) return null;
        Object obj0 = cellMap.get(this);
        if (!(obj0 instanceof EspecNode)) return null;
        EspecNode res = (EspecNode)obj0;
        res.setFullUserObject(newName);
        getGraph().getClipboard().translateAllViews(50,50,true);
        return res;
    }
    
    protected boolean hasImportEdgeTo(XGraphDisplay graph, EspecNode n) {
        XEdge[] edges = getEdges(XNode.ONLY_OUTGOING);
        for(int i=0;i<edges.length;i++) {
            if (edges[i] instanceof ImportEdge) {
                if (n.equals(edges[i].getTargetNode())) {
                    Dbg.pr(this+" has already an import edge to "+n);
                    return true;
                }
            }
        }
        return false;
    }
    
    /** checks whether this edge has either imported especs or is imported by other especs that are in the same
     * graph. If yes, it draws an import edge between them, if it does not already exist.
     */
    public void createImportEdgeInGraph(XGraphDisplay graph) {
        EspecModelNode mymnode = (EspecModelNode)getModelNode();
        XNode[] nodes = graph.getRootNodes();
        for(int i=0;i<nodes.length;i++) {
            if (!nodes[i].equals(this)) {
                if (nodes[i] instanceof EspecNode) {
                    EspecModelNode othermnode = (EspecModelNode)nodes[i].getModelNode();
                    EspecNode src = null, trg = null;
                    if (mymnode.importsEspec(othermnode)) {
                        src = (EspecNode)nodes[i];
                        trg = this;
                    } else if (othermnode.importsEspec(mymnode)) {
                        src = this;
                        trg = (EspecNode)nodes[i];
                    }
                    if (src != null && trg != null) {
                        if (!src.hasImportEdgeTo(graph,trg)) {
                            // create the import edge:
                            ImportEdge impedge = new ImportEdge();
                            graph.insertEdge(impedge,src,trg,new Point[]{});
                            CellView cv = graph.getView().getMapping(src,false);
                            if (cv instanceof XNodeView) {
                                ((XNodeView)cv).adjustGraphAfterResizing();
                            }
                        }
                    } 
                }
            }
        }
    }
    
}


