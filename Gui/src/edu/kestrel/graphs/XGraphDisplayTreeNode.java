package edu.kestrel.graphs;

import edu.kestrel.graphs.io.*;
import javax.swing.tree.*;
import java.util.*;
import java.awt.*;

public class XGraphDisplayTreeNode extends DefaultMutableTreeNode implements Storable {
    
    protected XGraphApplication appl;
    protected XGraphDisplay graph;
    
    public XGraphDisplayTreeNode() {
        super();
        setAllowsChildren(false);
    }
    
    public XGraphDisplayTreeNode(XGraphApplication appl, XGraphDisplay graph) {
        this();
        setAppl(appl);
        setGraph(graph);
    }
    
    public void setGraph(XGraphDisplay graph) {
        this.graph = graph;
        setUserObject(graph.getValue());
    }
    
    public void setAppl(XGraphApplication appl) {
        this.appl = appl;
    }
    
    public XGraphDisplay getGraph() {
        return graph;
    }
    
    public boolean showsGraph(XGraphDisplay graph1) {
        if (graph == null) return false;
        return graph.equals(graph1);
    }
    
    public String toString() {
        if (graph == null) return "";
        return graph.getValue().toString();
    }
    
    /** returns the element properties object representing this object in the context of an io operation.
     */
    public ElementProperties getElementProperties(ReadWriteOperation rwop) {
        ElementProperties props = rwop.createElementProperties(this);
        //ElementProperties gprops = graph.getElementProperties(rwop);
        if (graph != null)
            props.addChildObject("GraphDisplay",graph);
        XGraphDisplayInternalFrame f = appl.getDesktop().getXGraphDisplay(graph);
        Point p = null;
        Dimension dim = null;
        boolean isIcon = false;
        boolean isClosed = false;
        if (f != null) {
            p = f.getLocation();
            dim = f.getSize();
            isIcon = f.isIcon();
            isClosed = false;
        } else {
            Rectangle b = graph.getSavedBounds();
            if (b != null) {
                p = new Point(b.x,b.y);
                dim = new Dimension(b.width,b.height);
            }
            isClosed = true;
        }
        if (p != null) {
            props.setPointProperty("",p);
        }
        if (dim != null) {
            props.setDimensionProperty("",dim);
        }
        props.setProperty("IsIcon",String.valueOf(isIcon));
        props.setProperty("IsClosed",String.valueOf(isClosed));
        props.setValueProperty(getUserObject());
        return props;
    }
    
    public void initFromElementProperties(ReadWriteOperation rwop, ElementProperties props) {
        Dbg.pr("initFromElementProperties in XGraphDisplayTreeNode...");
        setAppl(rwop.getAppl());
        setUserObject(props.getValueProperty());
        Rectangle b = props.getRectangleProperty("");
        boolean isClosed = props.getBooleanProperty("IsClosed");
        boolean isIcon = props.getBooleanProperty("IsIcon");
        Enumeration iter = props.getChildObjectEnumeration("GraphDisplay");
        while(iter.hasMoreElements()) {
            ElementProperties gprops = (ElementProperties)iter.nextElement();
            XGraphDisplay graph = (XGraphDisplay) rwop.getObjectForId(gprops.getId());
            setGraph(graph);
            appl.registerGraph(graph);
            if (isClosed) {
                graph.setSavedBounds(b);
            } else {
                appl.getDesktop().ensureDisplayGraphAction(graph);
                XGraphDisplayInternalFrame f = appl.getDesktop().getXGraphDisplay(graph);
                f.setLocation(b.x,b.y);
                f.setSize(b.width,b.height);
                if (isIcon) {
                    try {
                        f.setIcon(true);
                    } catch (Exception e) {}
                }
            }
        }
    }
}



