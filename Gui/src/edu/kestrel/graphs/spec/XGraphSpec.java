package edu.kestrel.graphs.spec;

import edu.kestrel.graphs.drawingmode.*;

import edu.kestrel.graphs.*;
import com.jgraph.graph.*;
import java.lang.reflect.*;
import java.util.*;

/** contains the specification of an XGraphDisplay. */
public class XGraphSpec implements java.io.Serializable {
    
    public Collection nodeClasses;
    public Collection edgeClasses;
    
    protected Vector  connectionRules;
    protected Vector  containerRules;
    
    protected Vector drawingModes;
    protected DrawingMode initialDrawingMode;
    
    /** the interface that must be implemented by all model elements of a graph */
    protected Class elementInterface = null;
    /** the interface that must be implemented by all view objects of a graph */
    protected Class elementViewInterface = null;
    
    protected XGraphModel model;
    
    /**
     * default constructor creates an empty spec (not the default spec!)
     */
    public XGraphSpec() {
        connectionRules = new Vector();
        containerRules = new Vector();
        drawingModes = new Vector();
        initialDrawingMode = null;
        model = new XGraphModel();
        try {
            elementInterface = Class.forName("edu.kestrel.graphs.XGraphElement");
            elementViewInterface = Class.forName("edu.kestrel.graphs.XGraphElementView");
        } catch (ClassNotFoundException ex) {
            System.err.println(ex.getMessage());
        }
    }
    
    /**
     * generates the graph model used by the XGraphDisplay from this spec
     */
    public XGraphModel getGraphModel() {
        return model;
    }
    
    /**
     * returns the initial drawing mode of the graph spec, that is the mode that is active when
     * the corresponding graph display is created.
     */
    public DrawingMode getInitialDrawingMode() {
        return initialDrawingMode;
    }
    
    public void setInitialDrawingMode(DrawingMode dm) {
        initialDrawingMode = dm;
    }
    
    /**
     * add a drawing mode to the list of modes. The new mode must have a different id then the existing ones.
     */
    
    protected void addDrawingMode(DrawingMode dm) {
        if (drawingModes.contains(dm)) {
            System.err.println("drawing mode \""+dm+"\" already registered.");
            return;
        } else {
            drawingModes.add(dm);
        }
    }
    
    /**
     * returns the drawing modes of the graph spec.
     */
    
    public Vector getDrawingModes() {
        return drawingModes;
    }
    
    /**
     * @return the spec for a default graph
     */
    static public XGraphSpec getDefaultSpec() {
        XGraphSpec spec = new XGraphSpec();
        DrawingMode basic = new DrawingModeBasic();
        spec.addDrawingMode(basic);
        spec.addDrawingMode(new DrawingModeAddBox());
        spec.addDrawingMode(new DrawingModeAddEllipse());
        spec.addDrawingMode(new DrawingModeAddText());
        spec.addDrawingMode(new DrawingModeAddStraightEdge());
        spec.addDrawingMode(new DrawingModeAddBezierEdge());
        spec.addDrawingMode(new DrawingModeAddContainerBox());
        spec.addDrawingMode(new DrawingModeZoom());
        spec.addDrawingMode(new DrawingModeDebug());
        spec.setInitialDrawingMode(basic);
        //spec.registerViewMapping("edu.kestrel.graphs.XBoxNode","edu.kestrel.graphs.BoxView");
        //spec.registerViewMapping("edu.kestrel.graphs.XEllipseNode","edu.kestrel.graphs.EllipseView");
        return spec;
    }
    
}
