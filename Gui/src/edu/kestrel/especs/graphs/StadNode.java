package edu.kestrel.especs.graphs;

import com.jgraph.graph.*;

import edu.kestrel.especs.graphs.spec.*;
import edu.kestrel.graphs.*;
import edu.kestrel.graphs.spec.*;
import java.util.*;
import java.awt.*;

/**
 * This class implements a stad node.
 *
 * @author  ma
 */
public class StadNode extends XContainerNode {
    
    protected static int stadCnt = 0;
    
    /** Creates a new instance of XStadNode */
    public StadNode() {
        super((String)null);
    }
    
    public StadNode(String name) {
        super(name);
    }
    
    public ModelNode createModelNode() {
        return new StadModelNode();
    }
    
    
    /*
    public StadNode(ModelNode mnode) {
        super(mnode);
    }
     */
    
    public void setInitialValue() {
        setUserObject("S"+(stadCnt++));
    }
    
    
    
    /*
    public StadNode(String name, XGraphDisplay graph, java.util.List childNodes) {
        super(name,graph,childNodes);
    }
     
    public StadNode(String name, XGraphDisplay graph, XNode[] childNodes) {
        super(name,graph,childNodes);
    }
     */
    
    /** creates the view of the container; to sets of view options have to be given: viewOptionsExpanded and viewOptionsCollapsed
     * determining the appearance depending on whether the node is expanded (showing its contents) or collapsed (hiding
     * its contents).
     */
    public XContainerView createContainerView(XGraphDisplay graph, CellMapper cm) {
        XContainerBoxView v = new XContainerBoxView(this, graph, cm);
        installDefaultContainerViewSettings(v);
        Color bgColor = new Color(141,148,194);
        // collapsed
        v.viewOptionsCollapsed.setUseBorder(true);
        v.viewOptionsCollapsed.setBorderWidth(1);
        v.viewOptionsCollapsed.setUseGradientPaint(true);
        v.viewOptionsCollapsed.setGradientPaintTopLeftColor(bgColor);
        // expanded
        v.viewOptionsExpanded.setUseBorder(true);
        v.viewOptionsExpanded.setBorderWidth(1);
        v.viewOptionsExpanded.setUseSolidPaint(true);
        v.viewOptionsExpanded.setSolidPaintColor(graph.getBackground());
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
    }
    
    
}


