/*
 * XContainerBoxNode.java
 *
 * Created on November 1, 2002, 7:18 PM
 */

package edu.kestrel.graphs;

import edu.kestrel.graphs.spec.*;
import com.jgraph.graph.*;
import javax.swing.JLabel;
import java.util.*;
import java.awt.*;

/**
 * This class implements a box-shaped container node that accepts instances of {@link edu.kestrel.graphs.XBoxNode} as children.
 *
 * @author  ma
 */
public class XContainerBoxNode extends XContainerNode {
    
    /** Creates a new instance of XContainerBoxNode */
    public XContainerBoxNode() {
        super((String)null);
    }
    
    public XContainerBoxNode(String name) {
        super(name);
    }
    
    /*
    public XContainerBoxNode(ModelNode mnode) {
        super(mnode);
    }
     */
    
    /*
    public XContainerBoxNode(String name, XGraphDisplay graph, java.util.List childNodes) {
        super(name,graph,childNodes);
    }
    
    public XContainerBoxNode(String name, XGraphDisplay graph, XNode[] childNodes) {
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
        Color bgColor = new Color(198,158,151);
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
        GraphConstants.setFontSize(map,14);
        GraphConstants.setFontStyle(map,Font.ITALIC);
        GraphConstants.setOpaque(map, false);
        viewMap.put(this,map);
        model.edit(null,viewMap,null,null);
    }
    
    
}
