/*
 * XEllipseNode.java
 *
 * Created on October 24, 2002, 7:06 PM
 */

package edu.kestrel.graphs;

import com.jgraph.graph.*;
import java.util.*;
import java.awt.*;

/**
 *
 * @author  ma
 */
public class XEllipseNode extends XNode {
    
    /** Creates a new instance of XEllipseNode */
    public XEllipseNode() {
        this(null);
    }
    
    public XEllipseNode(String name) {
        super(name);
    }

    protected int getPortsPerDimension() {
        return defaultNumberOfPortsPerDimension;
    }
    
    protected double[] getYValues(double x) {
        return getXValues(x);
    }
    
    protected double[] getXValues(double y) {
        double a = 0.5, b = 0.5;
        double x0 = 0.5, y0 = 0.5;
        double f = a*(Math.sqrt(1-(Math.pow((y-y0),2)/Math.pow(b,2))));
        double[] res = new double[2];
        res[0] = x0 + f;
        res[1] = x0 - f;
        return res;
    }    
    
    public void insertHook(XGraphDisplay graph, XGraphElementView viewObject) {
        super.insertHook(graph,viewObject);
        GraphModel model = graph.getModel();
        Map viewMap = new Hashtable();
        Map map = GraphConstants.createMap();
        GraphConstants.setFontSize(map,12);
        GraphConstants.setFontStyle(map,Font.ITALIC);
        GraphConstants.setOpaque(map, false);
        viewMap.put(this,map);
        model.edit(null,viewMap,null,null);
    }
    
    public XGraphElementView createView(XGraphDisplay graph, CellMapper cm) {
        XEllipseView v = new XEllipseView(this, graph, cm);
        v.viewOptions.setUseGradientPaint(true);
        v.viewOptions.setGradientPaintTopLeftColor(Color.yellow);
        v.viewOptions.setGradientPaintBottomRightColor(Color.white);
        //v.viewOptions.setUsePaint(true);
        //v.viewOptions.setSolidPaintColor(Color.yellow);
        v.viewOptions.setUseBorder(true);
        //v.viewOptions.setBorderColor(Color.red);
        //v.viewOptions.setBorderWidth(1);
        v.viewOptions.setUseShadow(true);
        return v;
    }
    
}
