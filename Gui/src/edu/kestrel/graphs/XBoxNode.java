/*
 * XBoxNode.java
 *
 * Created on October 24, 2002, 6:47 PM
 */

package edu.kestrel.graphs;

import com.jgraph.graph.*;
import java.awt.*;
import java.util.*;

/**
 * This class is an example extension of the abstract class {@link edu.kestrel.graphs.XNode}. It instantiates the methods
 * that are specific for a box shaped node. Also, in the {@link edu.kestrel.graphs#createVertexView} method the color and
 * paint setting are made.
 * @author  ma
 */
public class XBoxNode extends XNode {
    
    /** Creates a new instance of XBoxNode */
    public XBoxNode() {
        this(null);
    }
    
    public XBoxNode(String name) {
        super(name);
    }
    
    /** #ports/side */
    protected int getPortsPerDimension() {
        return defaultNumberOfPortsPerDimension;
    }
    
    protected double[] getYValues(double x) {
        double[] res = new double[2];
        res[0] = 0;
        res[1] = 1;
        return res;
    }
    
    protected double[] getXValues(double y) {
        return getYValues(y);
    }
    
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
    
    public XGraphElementView createView(XGraphDisplay graph, CellMapper cm) {
        XBoxView v = new XBoxView(this, graph, cm);
        //v.viewOptions.setUsePaint(false);
        v.viewOptions.setUseBorder(true);
        //v.viewOptions.setBorderColor(Color.red);
        v.viewOptions.setBorderWidth(1);
        //v.viewOptions.setSolidPaintColor(Color.gray);
        v.viewOptions.setUseGradientPaint(true);
        //v.viewOptions.setUseBorder(true);
        //v.viewOptions.setUseShadow(false);
        v.viewOptions.setGradientPaintTopLeftColor(new Color(141,148,198));
        return v;
    }
    
}
