/*
 * XTextNode.java
 *
 * Created on October 24, 2002, 6:47 PM
 */

package edu.kestrel.graphs;

import edu.kestrel.graphs.io.*;
import com.jgraph.graph.*;
import javax.swing.*;
import java.awt.*;
import java.util.*;

/**
 * This class is an example extension of the abstract class {@link edu.kestrel.graphs.XNode}. It instantiates the methods
 * that are specific for a box shaped node. Also, in the {@link edu.kestrel.graphs#createVertexView} method the color and
 * paint setting are made.
 * @author  ma
 */
public class XTextNode extends XNode {
    
    protected Object expandedValue;
    protected Object collapsedValue;
    protected boolean isCollapsed = false;
    
    /** Creates a new instance of XTextNode */
    public XTextNode() {
        this(null);
    }
    
    public XTextNode(String name) {
        super(name);
    }
    
    /** sets some initial node value using a counter variable.
     */
    protected void setInitialValue() {
        setUserObject("double-click to "+System.getProperty("line.separator")+"enter text.");
    }
    
    public void setCollapsedValue(Object val) {
        collapsedValue = val;
    }
    
    /** returns the collapsed value for the expanded value given as argument. By default,
     * the first word of the expanded value + "..." is returned
     */
    public Object getCollapsedValue(Object expandedValue) {
        String newline = System.getProperty("line.separator");
        String s = "";
        if (expandedValue != null)
            s = expandedValue.toString();
        return getCollapsedString(s);
//        s.trim();
//        char[] chars = s.toCharArray();
//        String res = "";
//        for(int i=0;i<chars.length;i++) {
//            if (Character.isLetterOrDigit(chars[i])) {
//                res += String.valueOf(chars[i]);
//            } else {
//                return res+"...";
//            }
//        }
//        return res+"...";
    }
    
    /** utility method, also used in XEdgeView.
     */
    static public String getCollapsedString(String expandedString) {
        String s = expandedString;
        s.trim();
        if (s.length() == 0) {
            return "";
        }
        char[] chars = s.toCharArray();
        String res = "";
        for(int i=0;i<chars.length;i++) {
            if (Character.isLetterOrDigit(chars[i])) {
                res += String.valueOf(chars[i]);
            } else {
                return res+"...";
            }
        }
        return res+"...";
    }
    
    /** if the node is expanded, this method returns the previous collapsed value.
     */
    public Object getCollapsedValue() {
        if (collapsedValue == null) {
            return getCollapsedValue(getUserObject());
        }
        return collapsedValue;
    }
    
    /** returns true, if the text node is collapsed, i.e. if the node is showing its collapsed value
     */
    public boolean isCollapsed() {
        return isCollapsed;
    }
    
    /** "collapse" the text node, i.e. set its value to the String returned by <code>getCollapsedValue()</code>
     */
    public void collapse() {
        if (isCollapsed) return;
        expandedValue = getUserObject();
        setUserObject(getCollapsedValue(expandedValue));
        isCollapsed = true;
        if (graph != null) {
            CellView cv = graph.getView().getMapping(this,false);
            if (cv != null) {
                GraphConstants.setEditable(cv.getAttributes(),false);
            }
        }
    }
    
    /** "expand" the text node, i.e. set its value back to the full text.
     */
    public void expand() {
        if (!isCollapsed) return;
        collapsedValue = getUserObject();
        setUserObject(expandedValue);
        isCollapsed = false;
        if (graph != null) {
            CellView cv = graph.getView().getMapping(this,false);
            if (cv != null) {
                GraphConstants.setEditable(cv.getAttributes(),isEditable());
            }
        }
    }
    
    public Object getExpandedValue() {
        return expandedValue;
    }
    
    public void setUserObject(Object val) {
        super.setUserObject(val);
        if (!isCollapsed) {
            collapsedValue = getCollapsedValue(val);
        }
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
    
    public void insertHook(XGraphDisplay graph) {
        //super.insertHook(graph);
        GraphModel model = graph.getModel();
        Map viewMap = new Hashtable();
        Map map = GraphConstants.createMap();
        viewMap.put(this,map);
        model.edit(null,viewMap,null,null);
        CellView cv = graph.getView().getMapping(this,true);
        if (cv != null) {
            viewMap = new Hashtable();
            viewMap.put(cv, map);
            graph.getView().edit(viewMap);
        }
    }
    
    public XGraphElementView createView(XGraphDisplay graph, CellMapper cm) {
        XTextView v = new XTextView(this, graph, cm);
        v.setFont(new Font("Courier", Font.PLAIN, 14));
        v.viewOptions.setUsePaint(false);
        v.viewOptions.setSolidPaintColor(graph.getBackground());
        //v.viewOptions.setUseBorder(true);
        v.viewOptions.setUseBorder(false);
        //v.viewOptions.setBorderColor(new Color(141,148,198));
        v.viewOptions.setBorderWidth(1);
        //v.viewOptions.setSolidPaintColor(Color.gray);
        v.viewOptions.setUseGradientPaint(false);
        //v.viewOptions.setUseBorder(true);
        v.viewOptions.setUseShadow(false);
        //v.viewOptions.setGradientPaintTopLeftColor(new Color(141,148,198));
        v.viewOptions.setTextDisplayOption(v.viewOptions.BOUNDS_ARE_ADJUSTED_TO_TEXT);
        return v;
    }
    
    static final protected String IsCollapsed = "IsCollapsed";
    static final protected String ExpandedValue = "ExpandedValue";
    static final protected String CollapsedValue = "CollapsedValue";
    
    public ElementProperties getElementProperties(ReadWriteOperation rwop) {
        ElementProperties props = super.getElementProperties(rwop);
        props.setBooleanProperty(IsCollapsed,isCollapsed());
        if (isCollapsed()) {
            props.setProperty(ExpandedValue,expandedValue);
        } else {
            props.setProperty(CollapsedValue,collapsedValue);
        }
        return props;
    }
    
    public void initFromElementProperties(ReadWriteOperation rwop, ElementProperties props) {
        super.initFromElementProperties(rwop,props);
        isCollapsed = props.getBooleanProperty(IsCollapsed);
        if (isCollapsed()) {
            expandedValue = props.getProperty(ExpandedValue);
        } else {
            collapsedValue = props.getProperty(CollapsedValue);
        }
    }
    
}
