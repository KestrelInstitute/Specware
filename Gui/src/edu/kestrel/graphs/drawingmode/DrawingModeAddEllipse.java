/*
 * DrawingModeAddEllipse.java
 *
 * Created on October 24, 2002, 6:44 PM
 */

package edu.kestrel.graphs.drawingmode;

import edu.kestrel.graphs.*;
import com.jgraph.graph.*;
import javax.swing.*;

/**
 *
 * @author  ma
 */
public class DrawingModeAddEllipse extends DrawingModeAddNode {
    
    /** Creates a new instance of DrawingModeAddEllipse */
    public DrawingModeAddEllipse() {
        super();
        id = "AddEllipse";
    }
    
    protected XNode createXNode(XGraphDisplay graph) {
        return new XEllipseNode();
    }
    
    public ImageIcon getImageIcon() {
        return IconImageData.ellipse24Icon;
    }
    
    public String getMenuString() {
        return "Add Ellipse";
    }
    
}
